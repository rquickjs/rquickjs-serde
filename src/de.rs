use alloc::string::{String, ToString as _};
use alloc::vec::Vec;

use rquickjs::{
    Exception, Filter, Function, Null, Object, String as JSString, Value,
    atom::PredefinedAtom,
    function::This,
    object::ObjectIter,
    qjs::{
        JS_GetClassID, JS_GetProperty, JS_GetPropertyUint32, JS_TAG_EXCEPTION,
        JS_VALUE_GET_NORM_TAG,
    },
};
use serde::{
    de::{self, IntoDeserializer},
    forward_to_deserialize_any,
};

use crate::err::{Error, Result};
use crate::utils::{as_key, to_string_lossy};
use crate::{MAX_SAFE_INTEGER, MIN_SAFE_INTEGER};

// Class IDs, for internal, deserialization purposes only.
// FIXME: This can change since the ABI is not stable.
// See https://github.com/quickjs-ng/quickjs/issues/758
#[derive(Debug, Copy, Clone)]
enum ClassId {
    Number = 4,
    String = 5,
    Bool = 6,
    BigInt = 35,
}

impl PartialEq<ClassId> for u32 {
    fn eq(&self, other: &ClassId) -> bool {
        *self == *other as u32
    }
}

/// `Deserializer` is a deserializer for [Value] values, implementing the `serde::Deserializer` trait.
///
/// This struct is responsible for converting [Value], into Rust types using the Serde deserialization framework.
///
/// # Example
///
/// ```
/// # use rquickjs::{Runtime, Context, Value};
/// # use rquickjs_serde::Deserializer;
/// # use serde::Deserializer as _;
/// #
/// let rt = Runtime::new().unwrap();
/// let ctx = Context::full(&rt).unwrap();
/// ctx.with(|ctx| {
///     let value = ctx.eval::<Value<'_>, _>("42").unwrap();
///     let mut deserializer = Deserializer::from(value);
///     let number: i32 = serde::Deserialize::deserialize(&mut deserializer).unwrap();
///     assert_eq!(number, 42);
/// });
/// ```
pub struct Deserializer<'js> {
    value: Value<'js>,
    /// In strict mode, only JSON-able values are allowed.
    strict: bool,
    map_key: bool,
    /// Whether `toJSON` has been applied at the current value's position.
    to_json_applied: bool,
    use_to_json: bool,
    remaining_recursion: usize,
    current_kv: Option<(Value<'js>, Value<'js>)>,
    /// Stack to track circular dependencies.
    stack: Vec<Value<'js>>,
}

impl<'js> Deserializer<'js> {
    pub fn new(value: Value<'js>) -> Self {
        Self::from(value)
    }

    /// Sets the maximum recursion depth, which defaults to 128.
    ///
    /// Entering an array, object, object-form enum, or recursive conversion
    /// consumes one level. A limit of zero allows only non-recursive values.
    /// Increasing the limit may cause a native stack overflow. This does not
    /// limit JavaScript execution inside getters or conversion hooks.
    ///
    /// Defaults to 128.
    pub fn with_recursion_limit(self, limit: usize) -> Self {
        Self {
            remaining_recursion: limit,
            ..self
        }
    }

    /// Disables `toJSON` lookups and calls, including for nested values.
    ///
    /// Other JavaScript code, such as property getters, proxy traps, and
    /// `valueOf` or `toString` methods, may still run during deserialization.
    pub fn without_to_json(self) -> Self {
        Self {
            use_to_json: false,
            ..self
        }
    }

    /// Enables strict mode, restricting deserialization to JSON-compatible values
    /// without fallback conversions.
    ///
    /// `toJSON` hooks remain enabled unless disabled with [`Self::without_to_json`].
    pub fn with_strict(self) -> Self {
        Self {
            strict: true,
            ..self
        }
    }
}

impl<'de> From<Value<'de>> for Deserializer<'de> {
    fn from(value: Value<'de>) -> Self {
        Self {
            value,
            strict: false,
            map_key: false,
            to_json_applied: false,
            use_to_json: true,
            remaining_recursion: 128,
            current_kv: None,
            // We are probaby over allocating here. But it's probably fine to
            // over allocate to avoid paying the cost of subsequent allocations.
            stack: Vec::with_capacity(100),
        }
    }
}

impl<'js> Deserializer<'js> {
    fn with_recursion<T>(&mut self, f: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        if self.remaining_recursion == 0 {
            return Err(Error::new(Exception::throw_range(
                self.value.ctx(),
                "Recursion limit exceeded",
            )));
        }
        self.remaining_recursion -= 1;
        let result = f(self);
        self.remaining_recursion += 1;
        result
    }

    fn apply_to_json(&mut self) -> Result<()> {
        if self.use_to_json && !self.map_key && !self.to_json_applied {
            // Property and array access apply the hook with their own key before
            // deserializing. Only the root reaches here without it applied.
            self.to_json_applied = true;
            if (self.value.is_object() || self.value.is_big_int())
                && let Some(f) = get_to_json(&self.value)
            {
                self.value = f.call((This(self.value.clone()), "")).map_err(Error::new)?;
            }
        }
        Ok(())
    }

    fn deserialize_number<'de, V>(&mut self, visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        if let Some(i) = self.value.as_int() {
            return visitor.visit_i32(i);
        }

        if let Some(f64_representation) = self.value.as_float() {
            let is_positive = f64_representation.is_sign_positive();
            let safe_integer_range = (MIN_SAFE_INTEGER as f64)..=(MAX_SAFE_INTEGER as f64);
            let whole = (f64_representation % 1.0) == 0.0;

            if whole && is_positive && f64_representation <= u32::MAX as f64 {
                return visitor.visit_u32(f64_representation as u32);
            }

            if whole && safe_integer_range.contains(&f64_representation) {
                let x = f64_representation as i64;
                return visitor.visit_i64(x);
            }

            return visitor.visit_f64(f64_representation);
        }

        Err(Error::new(Exception::throw_type(
            self.value.ctx(),
            "Unsupported number type",
        )))
    }

    /// Pops the last visited value present in the stack.
    fn pop_visited(&mut self) -> Result<Value<'js>> {
        let v = self
            .stack
            .pop()
            .ok_or_else(|| Error::new("No entries found in the deserializer stack"))?;
        Ok(v)
    }

    /// When stringifying, circular dependencies are not allowed. This function
    /// checks the current value stack to ensure that if the same value (tag and
    /// bits) is found again a proper error is raised.
    fn check_cycles(&self) -> Result<()> {
        for val in self.stack.iter().rev() {
            if self.value.eq(val) {
                return Err(Error::new(Exception::throw_type(
                    val.ctx(),
                    "circular dependency",
                )));
            }
        }
        Ok(())
    }
}

impl<'de> de::Deserializer<'de> for &mut Deserializer<'de> {
    type Error = Error;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        self.apply_to_json()?;

        if self.value.is_number() {
            return self.deserialize_number(visitor);
        }

        if get_class_id(&self.value) == ClassId::Number {
            let value_of = get_valueof(&self.value);
            if let Some(f) = value_of {
                let v = f.call((This(self.value.clone()),)).map_err(Error::new)?;
                self.value = v;
                return self.deserialize_number(visitor);
            }
        }

        if let Some(b) = self.value.as_bool() {
            return visitor.visit_bool(b);
        }

        if get_class_id(&self.value) == ClassId::Bool {
            let value_of = get_valueof(&self.value);
            if let Some(f) = value_of {
                let v = f.call((This(self.value.clone()),)).map_err(Error::new)?;
                return visitor.visit_bool(v);
            }
        }

        if self.value.is_null() || self.value.is_undefined() {
            return visitor.visit_unit();
        }

        if get_class_id(&self.value) == ClassId::String {
            let to_string = get_to_string(&self.value);
            if let Some(f) = to_string {
                let v = f.call(((This(self.value.clone())),)).map_err(Error::new)?;
                self.value = v;
            }
        }

        if self.value.is_string() {
            if self.map_key {
                self.map_key = false;
                let key = as_key(&self.value)?;
                return visitor.visit_str(&key);
            } else {
                let val = self
                    .value
                    .as_string()
                    .map(|s| {
                        s.to_string()
                            .unwrap_or_else(|e| to_string_lossy(self.value.ctx(), s, e))
                    })
                    .unwrap();
                return visitor.visit_str(&val);
            }
        }

        if is_array_or_proxy_of_array(&self.value)
            && let Some(seq) = self.value.as_object().cloned()
        {
            return self.with_recursion(|de| {
                let seq_access = SeqAccess::new(de, seq)?;
                visitor.visit_seq(seq_access)
            });
        }

        if (get_class_id(&self.value) == ClassId::BigInt || self.value.is_big_int())
            && let Some(f) = get_to_string(&self.value)
            && !self.strict
        {
            let v: Value = f.call((This(self.value.clone()),)).map_err(Error::new)?;
            self.value = v;
            return self.with_recursion(|de| de.deserialize_any(visitor));
        }

        if self.value.is_object() {
            ensure_supported(&self.value)?;

            return self.with_recursion(|de| {
                let map_access = MapAccess::new(de, de.value.clone().into_object().unwrap())?;
                visitor.visit_map(map_access)
            });
        }

        Err(Error::new(Exception::throw_type(
            self.value.ctx(),
            "Unsupported type",
        )))
    }

    fn is_human_readable(&self) -> bool {
        false
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        self.apply_to_json()?;

        if self.value.is_null() || self.value.is_undefined() {
            visitor.visit_none()
        } else {
            visitor.visit_some(self)
        }
    }

    fn deserialize_newtype_struct<V>(self, _name: &'static str, visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        self.apply_to_json()?;

        if get_class_id(&self.value) == ClassId::String
            && let Some(f) = get_to_string(&self.value)
        {
            let v = f.call((This(self.value.clone()),)).map_err(Error::new)?;
            self.value = v;
        }

        if let Some(obj) = self.value.as_object() {
            let (variant, value): (String, Value<'de>) = obj
                .props::<String, Value>()
                .next()
                .ok_or_else(|| Error::new("expected enum object with one key"))?
                .map_err(Error::new)?;

            self.with_recursion(|de| {
                visitor.visit_enum(EnumAccessImpl {
                    variant,
                    value: Some(value.clone()),
                    use_to_json: de.use_to_json,
                    remaining_recursion: de.remaining_recursion,
                })
            })
        } else if let Some(s) = self.value.as_string() {
            // Now require a primitive string.
            let s = s
                .to_string()
                .unwrap_or_else(|e| to_string_lossy(self.value.ctx(), s, e));

            visitor.visit_enum(EnumAccessImpl {
                variant: s,
                value: None,
                use_to_json: self.use_to_json,
                remaining_recursion: self.remaining_recursion,
            })
        } else {
            Err(Error::new("expected a string or object for enum"))
        }
    }

    forward_to_deserialize_any! {
        bool i8 i16 i32 i64 u8 u16 u32 u64 f32 f64 char str string
        bytes byte_buf unit unit_struct seq tuple
        tuple_struct map struct identifier ignored_any
    }
}

/// A helper struct for deserializing objects.
struct MapAccess<'a, 'de: 'a> {
    /// The deserializer.
    de: &'a mut Deserializer<'de>,
    /// The object properties.
    properties: ObjectIter<'de, Value<'de>, Value<'de>>,
    /// The current object.
    obj: Object<'de>,
}

impl<'a, 'de> MapAccess<'a, 'de> {
    fn new(de: &'a mut Deserializer<'de>, obj: Object<'de>) -> Result<Self> {
        let filter = Filter::new().enum_only().string();
        let properties: ObjectIter<'_, _, Value<'_>> =
            obj.own_props::<Value<'_>, Value<'_>>(filter);

        let val = obj.clone().into_value();
        de.stack.push(val.clone());

        Ok(Self {
            de,
            properties,
            obj,
        })
    }

    /// Pops the top level value representing this sequence.
    /// Errors if a different value is popped.
    fn pop(&mut self) -> Result<()> {
        let v = self.de.pop_visited()?;
        if v != self.obj.clone().into_value() {
            return Err(Error::new(
                "Popped a mismatched value. Expected the top level sequence value",
            ));
        }

        Ok(())
    }
}

impl<'de> de::MapAccess<'de> for MapAccess<'_, 'de> {
    type Error = Error;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>>
    where
        K: de::DeserializeSeed<'de>,
    {
        loop {
            if let Some(kv) = self.properties.next() {
                let (k, v) = kv.map_err(Error::new)?;

                let to_json = self.de.use_to_json.then(|| get_to_json(&v)).flatten();
                let v = if let Some(f) = to_json {
                    f.call((This(v.clone()), k.clone())).map_err(Error::new)?
                } else {
                    v
                };

                // Entries with non-JSONable values are skipped to respect
                // JSON.stringify's spec
                if !ensure_supported(&v)? || k.is_symbol() {
                    continue;
                }

                let class_id = get_class_id(&v);

                if class_id == ClassId::Bool || class_id == ClassId::Number {
                    let value_of = get_valueof(&v);
                    if let Some(f) = value_of {
                        let v = f.call((This(v.clone()),)).map_err(Error::new)?;
                        self.de.current_kv = Some((k.clone(), v));
                    }
                } else if class_id == ClassId::String {
                    let to_string = get_to_string(&v);
                    if let Some(f) = to_string {
                        let v = f.call((This(v.clone()),)).map_err(Error::new)?;
                        self.de.current_kv = Some((k.clone(), v));
                    }
                } else {
                    self.de.current_kv = Some((k.clone(), v));
                }
                self.de.value = k;
                self.de.map_key = true;

                return seed.deserialize(&mut *self.de).map(Some);
            } else {
                self.pop()?;
                return Ok(None);
            }
        }
    }

    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value>
    where
        V: de::DeserializeSeed<'de>,
    {
        self.de.value = self.de.current_kv.clone().unwrap().1;
        self.de.to_json_applied = true;
        self.de.check_cycles()?;
        seed.deserialize(&mut *self.de)
    }
}

/// A helper struct for deserializing sequences.
struct SeqAccess<'a, 'de: 'a> {
    /// The deserializer.
    de: &'a mut Deserializer<'de>,
    /// The sequence, represented as a JavaScript object.
    // Using Object instead of Array because `SeqAccess` needs to support
    // proxies of arrays and a proxy Value cannot be converted into Array.
    seq: Object<'de>,
    /// The sequence length.
    length: usize,
    /// The current index.
    index: usize,
}

impl<'a, 'de: 'a> SeqAccess<'a, 'de> {
    /// Creates a new `SeqAccess` ensuring that the top-level value is added
    /// to the `Deserializer` visitor stack.
    fn new(de: &'a mut Deserializer<'de>, seq: Object<'de>) -> Result<Self> {
        de.stack.push(seq.clone().into_value());

        // Retrieve the `length` property from the object itself rather than
        // using the bindings `Array::len` given that according to the spec
        // it's fine to return any value, not just a number from the
        // `length` property.
        let value: Value = seq.get(PredefinedAtom::Length).map_err(Error::new)?;
        let length: usize = if let Some(n) = value.as_number() {
            n as usize
        } else {
            let value_of: Function = value
                .as_object()
                .expect("length to be an object")
                .get(PredefinedAtom::ValueOf)
                .map_err(Error::new)?;
            value_of.call(()).map_err(Error::new)?
        };

        Ok(Self {
            de,
            seq,
            length,
            index: 0,
        })
    }

    /// Pops the top level value representing this sequence.
    /// Errors if a different value is popped.
    fn pop(&mut self) -> Result<()> {
        let v = self.de.pop_visited()?;
        if v != self.seq.clone().into_value() {
            return Err(Error::new(
                "Popped a mismatched value. Expected the top level sequence value",
            ));
        }

        Ok(())
    }
}

impl<'de> de::SeqAccess<'de> for SeqAccess<'_, 'de> {
    type Error = Error;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>>
    where
        T: de::DeserializeSeed<'de>,
    {
        if self.index < self.length {
            let el = get_index(&self.seq, self.index).map_err(Error::new)?;
            let to_json = self.de.use_to_json.then(|| get_to_json(&el)).flatten();

            if let Some(f) = to_json {
                let index_value = JSString::from_str(el.ctx().clone(), &self.index.to_string());
                self.de.value = f
                    .call((This(el.clone()), index_value))
                    .map_err(Error::new)?;
            } else if ensure_supported(&el)? {
                self.de.value = el
            } else {
                self.de.value = Null.into_value(self.seq.ctx().clone())
            }
            self.de.to_json_applied = true;
            self.index += 1;
            // Check cycles right before starting the deserialization for the
            // sequence elements.
            self.de.check_cycles()?;
            seed.deserialize(&mut *self.de).map(Some)
        } else {
            // Pop the sequence when there are no more elements.
            self.pop()?;
            Ok(None)
        }
    }
}

/// Checks if the value is an object and contains a single `toJSON` function.
pub(crate) fn get_to_json<'a>(value: &Value<'a>) -> Option<Function<'a>> {
    get_function(value, PredefinedAtom::ToJSON)
}

/// Checks if the value is an object and contains a `valueOf` function.
fn get_valueof<'a>(value: &Value<'a>) -> Option<Function<'a>> {
    get_function(value, PredefinedAtom::ValueOf)
}

/// Checks if the value is an object and contains a `toString` function.
fn get_to_string<'a>(value: &Value<'a>) -> Option<Function<'a>> {
    get_function(value, PredefinedAtom::ToString)
}

fn get_function<'a>(value: &Value<'a>, atom: PredefinedAtom) -> Option<Function<'a>> {
    let f = unsafe { JS_GetProperty(value.ctx().as_raw().as_ptr(), value.as_raw(), atom as u32) };
    let f = unsafe { Value::from_raw(value.ctx().clone(), f) };
    if f.is_function()
        && let Some(f) = f.into_function()
    {
        Some(f)
    } else {
        None
    }
}

/// Gets the underlying class id of the value.
fn get_class_id(v: &Value) -> u32 {
    unsafe { JS_GetClassID(v.as_raw()) }
}

/// Ensures that the value can be stringified.
fn ensure_supported(value: &Value<'_>) -> Result<bool> {
    let class_id = get_class_id(value);
    if class_id == ClassId::Bool || class_id == ClassId::Number {
        return Ok(true);
    }

    if class_id == ClassId::BigInt {
        return Err(Error::new(Exception::throw_type(
            value.ctx(),
            "BigInt not supported",
        )));
    }

    Ok(!matches!(
        value.type_of(),
        rquickjs::Type::Undefined
            | rquickjs::Type::Symbol
            | rquickjs::Type::Function
            | rquickjs::Type::Uninitialized
            | rquickjs::Type::Constructor
    ))
}

fn is_array_or_proxy_of_array(val: &Value) -> bool {
    if val.is_array() {
        return true;
    }
    let mut val = val.clone();
    loop {
        let Some(proxy) = val.into_proxy() else {
            return false;
        };
        let Ok(target) = proxy.target() else {
            return false;
        };
        val = target.into_value();
        if val.is_array() {
            return true;
        }
    }
}

fn get_index<'a>(obj: &Object<'a>, idx: usize) -> rquickjs::Result<Value<'a>> {
    unsafe {
        let ctx = obj.ctx();
        let val = JS_GetPropertyUint32(ctx.as_raw().as_ptr(), obj.as_raw(), idx as _);
        if JS_VALUE_GET_NORM_TAG(val) == JS_TAG_EXCEPTION {
            return Err(rquickjs::Error::Exception);
        }
        Ok(Value::from_raw(ctx.clone(), val))
    }
}

/// A helper struct for deserializing enums
struct EnumAccessImpl<'de> {
    /// selected enum variant
    variant: String,
    /// value of selected variant, `None` for unit variant
    value: Option<Value<'de>>,
    use_to_json: bool,
    remaining_recursion: usize,
}

impl<'de> de::EnumAccess<'de> for EnumAccessImpl<'de> {
    type Error = Error;
    type Variant = VariantAccessImpl<'de>;

    fn variant_seed<V>(self, seed: V) -> Result<(V::Value, Self::Variant)>
    where
        V: de::DeserializeSeed<'de>,
    {
        let val = seed.deserialize(self.variant.into_deserializer())?;
        Ok((
            val,
            VariantAccessImpl {
                value: self.value,
                use_to_json: self.use_to_json,
                remaining_recursion: self.remaining_recursion,
            },
        ))
    }
}

struct VariantAccessImpl<'de> {
    value: Option<Value<'de>>,
    use_to_json: bool,
    remaining_recursion: usize,
}

impl<'de> de::VariantAccess<'de> for VariantAccessImpl<'de> {
    type Error = Error;

    fn unit_variant(self) -> Result<()> {
        match self.value {
            None => Ok(()),
            Some(_) => Err(Error::new("expected unit variant")),
        }
    }

    fn newtype_variant_seed<T>(self, seed: T) -> Result<T::Value>
    where
        T: de::DeserializeSeed<'de>,
    {
        let value = self
            .value
            .ok_or_else(|| Error::new("expected value for newtype variant"))?;

        seed.deserialize(&mut Deserializer {
            use_to_json: self.use_to_json,
            remaining_recursion: self.remaining_recursion,
            ..Deserializer::from(value)
        })
    }

    fn tuple_variant<V>(self, _len: usize, visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        let value = self
            .value
            .ok_or_else(|| Error::new("expected tuple variant"))?;

        de::Deserializer::deserialize_seq(
            &mut Deserializer {
                use_to_json: self.use_to_json,
                remaining_recursion: self.remaining_recursion,
                ..Deserializer::from(value)
            },
            visitor,
        )
    }

    fn struct_variant<V>(self, _fields: &'static [&'static str], visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        let value = self
            .value
            .ok_or_else(|| Error::new("expected struct variant"))?;

        de::Deserializer::deserialize_map(
            &mut Deserializer {
                use_to_json: self.use_to_json,
                remaining_recursion: self.remaining_recursion,
                ..Deserializer::from(value)
            },
            visitor,
        )
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use rquickjs::Value;
    use serde::de::DeserializeOwned;
    use serde::{Deserialize, Serialize};

    use super::{ClassId, Deserializer as ValueDeserializer, get_class_id};
    use crate::test::Runtime;
    use crate::{MAX_SAFE_INTEGER, from_value, to_value};

    fn deserialize_value<T>(v: Value<'_>) -> T
    where
        T: DeserializeOwned,
    {
        let ctx = v.ctx().clone();
        let mut deserializer = ValueDeserializer::from(v);
        match T::deserialize(&mut deserializer) {
            Ok(val) => val,
            Err(e) => panic!("{}", e.catch(&ctx)),
        }
    }

    #[test]
    fn test_recursion_limit() {
        for (source, depth) in [
            ("42", 0),
            ("null", 0),
            ("[]", 1),
            ("({})", 1),
            ("[42, 43, 44]", 1),
            ("({ a: 1, b: 2, c: 3 })", 1),
            ("[[], [], []]", 2),
            ("({ a: {}, b: {}, c: {} })", 2),
            ("[{ a: [42] }]", 3),
            ("new Proxy([[42]], {})", 2),
        ] {
            for limit in 0..=3 {
                let rt = Runtime::default();
                rt.context().with(|cx| {
                    let value = cx.eval::<Value<'_>, _>(source).unwrap();
                    let mut de = ValueDeserializer::new(value).with_recursion_limit(limit);
                    let result = serde::de::IgnoredAny::deserialize(&mut de);
                    if limit >= depth {
                        assert!(result.is_ok(), "{source}, limit {limit}");
                    } else {
                        assert!(
                            result
                                .unwrap_err()
                                .catch(&cx)
                                .to_string()
                                .contains("Recursion limit exceeded")
                        );
                    }
                    assert_eq!(de.remaining_recursion, limit);
                });
            }
        }
    }

    #[test]
    fn test_default_recursion_limit_and_override() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            for (depth, succeeds) in [(128, true), (129, false)] {
                let value = cx.eval::<Value<'_>, _>(format!(
                    "(() => {{ let value = 42; for (let i = 0; i < {depth}; i++) value = [value]; return value; }})()"
                )).unwrap();
                let result = from_value::<serde::de::IgnoredAny>(value.clone());
                if succeeds {
                    assert!(result.is_ok());
                } else {
                    assert!(result.unwrap_err().catch(&cx).to_string().contains("Recursion limit exceeded"));
                }
                let mut de = ValueDeserializer::new(value).with_recursion_limit(129);
                assert!(serde::de::IgnoredAny::deserialize(&mut de).is_ok());
            }
        });
    }

    #[test]
    fn test_recursion_limit_generated_children() {
        for source in [
            "(() => { function node() { return { toJSON() { return { child: node() }; } }; } return node(); })()",
            "(() => { function node() { return { toJSON() { return [node()]; } }; } return node(); })()",
        ] {
            let rt = Runtime::default();
            rt.context().with(|cx| {
                let value = cx.eval::<Value<'_>, _>(source).unwrap();
                let mut de = ValueDeserializer::new(value).with_recursion_limit(4);
                let error = serde::de::IgnoredAny::deserialize(&mut de).unwrap_err();
                assert!(
                    error
                        .catch(&cx)
                        .to_string()
                        .contains("Recursion limit exceeded")
                );
            });
        }
    }

    #[test]
    fn test_recursion_limit_bigint_conversion() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            cx.eval::<(), _>("BigInt.prototype.toString = function() { return this; };")
                .unwrap();
            let value = cx.eval::<Value<'_>, _>("1n").unwrap();
            let mut de = ValueDeserializer::new(value)
                .without_to_json()
                .with_recursion_limit(4);
            let error = String::deserialize(&mut de).unwrap_err();
            assert!(
                error
                    .catch(&cx)
                    .to_string()
                    .contains("Recursion limit exceeded")
            );
        });
    }

    #[test]
    fn test_recursion_limit_enum_payloads() {
        #[allow(dead_code)]
        #[derive(Debug, Deserialize)]
        enum Tree {
            Leaf,
            Node(Box<Tree>),
            Pair(Box<Tree>, Box<Tree>),
            Branch { child: Box<Tree> },
        }
        for (source, depth) in [
            (r#""Leaf""#, 0),
            (r#"({ Node: "Leaf" })"#, 1),
            (r#"({ Node: { Node: "Leaf" } })"#, 2),
            (r#"({ Pair: ["Leaf", "Leaf"] })"#, 2),
            (r#"({ Branch: { child: "Leaf" } })"#, 2),
        ] {
            for limit in 0..=2 {
                let rt = Runtime::default();
                rt.context().with(|cx| {
                    let value = cx.eval::<Value<'_>, _>(source).unwrap();
                    let mut de = ValueDeserializer::new(value).with_recursion_limit(limit);
                    let result = Tree::deserialize(&mut de);
                    if limit >= depth {
                        assert!(result.is_ok());
                    } else {
                        assert!(
                            result
                                .unwrap_err()
                                .catch(&cx)
                                .to_string()
                                .contains("Recursion limit exceeded")
                        );
                    }
                });
            }
        }
    }

    #[test]
    fn test_without_to_json() {
        for source in [
            "({ answer: 42, toJSON() { throw new Error('hook called'); } })",
            "Object.defineProperty({ answer: 42 }, 'toJSON', { get() { throw new Error('getter called'); } })",
            "new Proxy({ answer: 42 }, { get(target, key, receiver) { if (key === 'toJSON') throw new Error('trap called'); return Reflect.get(target, key, receiver); } })",
        ] {
            let rt = Runtime::default();
            rt.context().with(|cx| {
                // Exercise root, property, and array-element lookups separately.
                let value = cx.eval::<Value<'_>, _>(source).unwrap();
                let mut de = ValueDeserializer::new(value).without_to_json();
                let expected = BTreeMap::from([("answer".to_owned(), 42)]);
                assert_eq!(
                    BTreeMap::<String, i32>::deserialize(&mut de).unwrap(),
                    expected
                );

                let value = cx
                    .eval::<Value<'_>, _>(format!("({{ child: {source} }})"))
                    .unwrap();
                let mut de = ValueDeserializer::new(value).without_to_json();
                assert_eq!(
                    BTreeMap::<String, BTreeMap<String, i32>>::deserialize(&mut de).unwrap(),
                    BTreeMap::from([("child".into(), expected.clone())])
                );

                let value = cx.eval::<Value<'_>, _>(format!("Object.defineProperty([{source}], 'toJSON', {{ get() {{ throw new Error('array getter called'); }} }})")).unwrap();
                let mut de = ValueDeserializer::new(value).without_to_json();
                assert_eq!(
                    Vec::<BTreeMap<String, i32>>::deserialize(&mut de).unwrap(),
                    vec![expected]
                );
            });
        }
    }

    #[test]
    fn test_without_to_json_bigint() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            cx.eval::<(), _>(
                "Object.defineProperty(BigInt.prototype, 'toJSON', { get() { throw new Error('getter called'); } });",
            ).unwrap();
            for source in ["1n", "Object(1n)"] {
                let value = cx.eval::<Value<'_>, _>(source).unwrap();
                let mut de = ValueDeserializer::new(value).without_to_json();
                assert_eq!(String::deserialize(&mut de).unwrap(), "1");

                let value = cx.eval::<Value<'_>, _>(source).unwrap();
                let mut de = ValueDeserializer::new(value).with_strict().without_to_json();
                let error = String::deserialize(&mut de).unwrap_err();
                let expected = if source == "1n" { "Unsupported type" } else { "BigInt not supported" };
                assert!(error.catch(&cx).to_string().contains(expected));
            }
        });
    }

    #[test]
    fn test_without_to_json_enum_payloads() {
        #[derive(Debug, Deserialize, PartialEq)]
        enum Test {
            Newtype(BTreeMap<String, i32>),
            Tuple(BTreeMap<String, i32>, i32),
            Struct { child: BTreeMap<String, i32> },
        }
        let child = BTreeMap::from([("answer".into(), 42)]);
        for (source, expected) in [
            ("({ Newtype: child })", Test::Newtype(child.clone())),
            (
                "({ Tuple: Object.defineProperty([child, 7], 'toJSON', descriptor) })",
                Test::Tuple(child.clone(), 7),
            ),
            (
                "({ Struct: Object.defineProperty({ child }, 'toJSON', descriptor) })",
                Test::Struct { child },
            ),
        ] {
            let rt = Runtime::default();
            rt.context().with(|cx| {
                cx.eval::<(), _>(
                    "const descriptor = { get() { throw new Error('getter called'); } }; const child = Object.defineProperty({ answer: 42 }, 'toJSON', descriptor);",
                ).unwrap();
                let value = cx.eval::<Value<'_>, _>(source).unwrap();
                let mut de = ValueDeserializer::new(value).without_to_json();
                assert_eq!(Test::deserialize(&mut de).unwrap(), expected);
            });
        }
    }

    #[test]
    fn test_to_json_returns_this() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            let value = cx
                .eval::<Value<'_>, _>(
                    r#"
                    var calls = [];
                    ({
                        answer: 42,
                        toJSON(key) {
                            calls.push(key);
                            if (calls.length > 1) throw new Error("toJSON called again");
                            return this;
                        }
                    })
                    "#,
                )
                .unwrap();
            let result = deserialize_value::<BTreeMap<String, i32>>(value);
            assert_eq!(result, BTreeMap::from([("answer".into(), 42)]));
            assert_eq!(
                cx.globals().get::<_, Vec<String>>("calls").unwrap(),
                vec![""]
            );
        });
    }

    #[test]
    fn test_to_json_does_not_call_returned_objects_hook() {
        for source in [
            r#"
            const a = { toJSON() { return b; } };
            const b = { answer: 42, toJSON() { throw new Error("returned hook called"); } };
            a
            "#,
            r#"
            var calls = 0;
            const a = {
                toJSON() {
                    if (++calls > 1) throw new Error("toJSON called again");
                    return b;
                }
            };
            const b = { answer: 42, toJSON() { return a; } };
            a
            "#,
            r#"
            function toJSON() {
                if (++calls > 1) throw new Error("toJSON called again");
                return { answer: 42, toJSON };
            }
            var calls = 0;
            ({ toJSON })
            "#,
        ] {
            let rt = Runtime::default();
            rt.context().with(|cx| {
                let value = cx.eval::<Value<'_>, _>(source).unwrap();
                let result = deserialize_value::<BTreeMap<String, i32>>(value);
                assert_eq!(result, BTreeMap::from([("answer".into(), 42)]));
            });
        }
    }

    #[test]
    fn test_to_json_runs_once_for_each_child_with_its_key() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            let value = cx
                .eval::<Value<'_>, _>(
                    r#"
                    var calls = [];
                    function child() {
                        return {
                            answer: 42,
                            toJSON(key) {
                                calls.push(key);
                                if (calls.length > 4) throw new Error("toJSON called again");
                                return this;
                            }
                        };
                    }
                    ({
                        toJSON(key) {
                            calls.push(key);
                            return { property: child(), elements: [child(), child()] };
                        }
                    })
                    "#,
                )
                .unwrap();
            #[derive(Debug, Deserialize, PartialEq)]
            struct Output {
                property: BTreeMap<String, i32>,
                elements: Vec<BTreeMap<String, i32>>,
            }
            let child = BTreeMap::from([("answer".into(), 42)]);
            assert_eq!(
                deserialize_value::<Output>(value),
                Output {
                    property: child.clone(),
                    elements: vec![child.clone(), child],
                }
            );
            // Object property order is preserved, and array indices are strings.
            assert_eq!(
                cx.globals().get::<_, Vec<String>>("calls").unwrap(),
                vec!["", "property", "0", "1"]
            );
        });
    }

    #[test]
    fn test_to_json_returns_array_with_its_own_hook() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            let value = cx
                .eval::<Value<'_>, _>(
                    r#"
                    const result = [42];
                    result.toJSON = () => { throw new Error("returned hook called"); };
                    ({ toJSON() { return result; } })
                    "#,
                )
                .unwrap();
            assert_eq!(deserialize_value::<Vec<i32>>(value), vec![42]);
        });
    }

    #[test]
    fn test_root_array_to_json() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            let value = cx
                .eval::<Value<'_>, _>(
                    r#"
                    var calls = [];
                    const value = [42];
                    value.toJSON = function(key) {
                        calls.push(key);
                        if (calls.length > 1) throw new Error("toJSON called again");
                        return this;
                    };
                    value
                    "#,
                )
                .unwrap();
            assert_eq!(deserialize_value::<Vec<i32>>(value), vec![42]);
            assert_eq!(
                cx.globals().get::<_, Vec<String>>("calls").unwrap(),
                vec![""]
            );
        });
    }

    #[test]
    fn test_enum_to_json() {
        #[derive(Debug, Deserialize, PartialEq)]
        enum Test {
            One,
        }
        let rt = Runtime::default();
        rt.context().with(|cx| {
            let value = cx
                .eval::<Value<'_>, _>(r#"({ toJSON() { return "One"; } })"#)
                .unwrap();
            assert_eq!(deserialize_value::<Test>(value), Test::One);
        });
    }

    #[test]
    fn test_bigint_to_json_returns_this() {
        for source in ["1n", "Object(1n)"] {
            let rt = Runtime::default();
            rt.context().with(|cx| {
                cx.eval::<(), _>(
                    r#"
                    var calls = 0;
                    BigInt.prototype.toJSON = function(key) {
                        if (key !== "" || ++calls > 1) throw new Error("unexpected toJSON call");
                        return this;
                    };
                    "#,
                )
                .unwrap();
                let value = cx.eval::<Value<'_>, _>(source).unwrap();
                assert_eq!(deserialize_value::<String>(value), "1");
                assert_eq!(cx.eval::<i32, _>("calls").unwrap(), 1);

                cx.eval::<(), _>("calls = 0").unwrap();
                let value = cx.eval::<Value<'_>, _>(source).unwrap();
                assert!(crate::from_value_strict::<String>(value).is_err());
                cx.catch();
                assert_eq!(cx.eval::<i32, _>("calls").unwrap(), 1);
            });
        }
    }

    #[test]
    fn test_to_json_returns_none() {
        for result in ["null", "undefined"] {
            let rt = Runtime::default();
            rt.context().with(|cx| {
                let value = cx
                    .eval::<Value<'_>, _>(format!("({{ toJSON() {{ return {result}; }} }})"))
                    .unwrap();
                assert_eq!(deserialize_value::<Option<i32>>(value), None);
            });
        }
    }

    #[test]
    fn test_to_json_preserves_cycle_detection() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            let value = cx
                .eval::<Value<'_>, _>(
                    r#"
                    var calls = 0;
                    const value = {
                        toJSON() {
                            if (++calls > 2) throw new Error("toJSON called again");
                            return this;
                        }
                    };
                    value.child = value;
                    value
                    "#,
                )
                .unwrap();
            let err = from_value::<BTreeMap<String, BTreeMap<String, i32>>>(value).unwrap_err();
            assert!(err.catch(&cx).to_string().contains("circular dependency"));
            assert_eq!(cx.eval::<i32, _>("calls").unwrap(), 2);
        });
    }

    #[test]
    fn test_null() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            let val = Value::new_null(cx);
            deserialize_value::<()>(val);
        });
    }

    #[test]
    fn test_undefined() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            let val = Value::new_undefined(cx);
            deserialize_value::<()>(val);
        });
    }

    #[test]
    fn test_boxed_boolean() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            cx.eval::<Value<'_>, _>("var a = new Boolean(true);")
                .unwrap();
            let v = cx.globals().get("a").unwrap();
            assert!(deserialize_value::<bool>(v));

            cx.eval::<Value<'_>, _>("var b = new Boolean(false);")
                .unwrap();
            let v = cx.globals().get("b").unwrap();
            assert!(!deserialize_value::<bool>(v));
        });
    }

    #[test]
    fn test_boxed_number() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            cx.eval::<Value<'_>, _>("var a = new Number(42);").unwrap();
            let v = cx.globals().get("a").unwrap();
            assert_eq!(42, deserialize_value::<i32>(v));

            cx.eval::<Value<'_>, _>("var b = new Number(1.5);").unwrap();
            let v = cx.globals().get("b").unwrap();
            assert_eq!(1.5, deserialize_value::<f64>(v));
        });
    }

    #[test]
    fn test_boxed_string() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            cx.eval::<Value<'_>, _>("var a = new String('hello');")
                .unwrap();
            let v = cx.globals().get("a").unwrap();
            assert_eq!("hello", deserialize_value::<String>(v));
        });
    }

    #[test]
    fn test_nan() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            let val = Value::new_float(cx, f64::NAN);
            let actual = deserialize_value::<f64>(val);
            assert!(actual.is_nan());
        });
    }

    #[test]
    fn test_infinity() {
        let rt = Runtime::default();

        rt.context().with(|cx| {
            let val = Value::new_float(cx, f64::INFINITY);
            let actual = deserialize_value::<f64>(val);
            assert!(actual.is_infinite() && actual.is_sign_positive());
        });
    }

    #[test]
    fn test_negative_infinity() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            let val = Value::new_float(cx, f64::NEG_INFINITY);
            let actual = deserialize_value::<f64>(val);
            assert!(actual.is_infinite() && actual.is_sign_negative());
        })
    }

    #[test]
    fn test_map_always_converts_keys_to_string() {
        let rt = Runtime::default();
        // Sanity check to make sure the quickjs VM always store object
        // object keys as a string an not a numerical value.
        rt.context().with(|c| {
            c.eval::<Value<'_>, _>("var a = {1337: 42};").unwrap();
            let val = c.globals().get("a").unwrap();
            let actual = deserialize_value::<BTreeMap<String, i32>>(val);

            assert_eq!(42, *actual.get("1337").unwrap())
        });
    }

    #[test]
    fn test_map_with_boxed_primitives() {
        #[derive(Debug, Deserialize, PartialEq)]
        struct Boxed {
            b: bool,
            n: i32,
            s: String,
        }

        let rt = Runtime::default();
        rt.context().with(|cx| {
            cx.eval::<Value<'_>, _>(
                r#"
                var a = {
                    b: new Boolean(true),
                    n: new Number(42),
                    s: new String("hello"),
                };
                "#,
            )
            .unwrap();
            let v = cx.globals().get("a").unwrap();
            assert_eq!(
                Boxed {
                    b: true,
                    n: 42,
                    s: "hello".to_string(),
                },
                deserialize_value::<Boxed>(v)
            );
        });
    }

    #[test]
    fn test_u64_bounds() {
        let rt = Runtime::default();
        rt.context().with(|c| {
            let max = u64::MAX;
            let val = Value::new_number(c.clone(), max as f64);
            let actual = deserialize_value::<f64>(val);
            assert_eq!(max as f64, actual);

            let min = u64::MIN;
            let val = Value::new_number(c.clone(), min as f64);
            let actual = deserialize_value::<f64>(val);
            assert_eq!(min as f64, actual);
        });
    }

    #[test]
    fn test_i64_bounds() {
        let rt = Runtime::default();

        rt.context().with(|c| {
            let max = i64::MAX;
            let val = Value::new_number(c.clone(), max as _);
            let actual = deserialize_value::<f64>(val);
            assert_eq!(max as f64, actual);

            let min = i64::MIN;
            let val = Value::new_number(c.clone(), min as _);
            let actual = deserialize_value::<f64>(val);
            assert_eq!(min as f64, actual);
        });
    }

    #[test]
    fn test_float_to_integer_conversion() {
        let rt = Runtime::default();

        rt.context().with(|c| {
            let expected = MAX_SAFE_INTEGER - 1;
            let val = Value::new_float(c.clone(), expected as _);
            let actual = deserialize_value::<i64>(val);
            assert_eq!(expected, actual);

            let expected = MAX_SAFE_INTEGER + 1;
            let val = Value::new_float(c.clone(), expected as _);
            let actual = deserialize_value::<f64>(val);
            assert_eq!(expected as f64, actual);
        });
    }

    #[test]
    fn test_u32_upper_bound() {
        let rt = Runtime::default();

        rt.context().with(|c| {
            let expected = u32::MAX;
            let val = Value::new_number(c, expected as _);
            let actual = deserialize_value::<u32>(val);
            assert_eq!(expected, actual);
        });
    }

    #[test]
    fn test_u32_lower_bound() {
        let rt = Runtime::default();

        rt.context().with(|cx| {
            let expected = i32::MAX as u32 + 1;
            let val = Value::new_number(cx, expected as _);
            let actual = deserialize_value::<u32>(val);
            assert_eq!(expected, actual);
        });
    }

    #[test]
    fn test_array() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            cx.eval::<Value<'_>, _>("var a = [1, 2, 3];").unwrap();
            let v = cx.globals().get("a").unwrap();

            let val = deserialize_value::<Vec<u8>>(v);

            assert_eq!(vec![1, 2, 3], val);
        });
    }

    #[test]
    fn test_array_with_boxed_primitives() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            cx.eval::<Value<'_>, _>(
                r#"
                var a = [new Boolean(false), new Number(7), new String("x")];
                "#,
            )
            .unwrap();
            let v = cx.globals().get("a").unwrap();
            assert_eq!(
                (false, 7, "x".to_string()),
                deserialize_value::<(bool, i32, String)>(v)
            );
        });
    }

    #[test]
    fn test_array_proxy() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            cx.eval::<Value<'_>, _>(
                r#"
                var arr = [1, 2, 3];
                var a = new Proxy(arr, {});
            "#,
            )
            .unwrap();
            let v = cx.globals().get("a").unwrap();
            let val = deserialize_value::<Vec<u8>>(v);
            assert_eq!(vec![1, 2, 3], val);
        });
    }

    #[test]
    fn test_non_json_object_values_are_dropped() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            cx.eval::<Value<'_>, _>(
                r#"
                var unitialized;
                var a = {
                    a: undefined,
                    b: function() {},
                    c: Symbol(),
                    d: () => {},
                    e: unitialized,
                };"#,
            )
            .unwrap();
            let v = cx.globals().get("a").unwrap();

            let val = deserialize_value::<BTreeMap<String, ()>>(v);
            assert_eq!(BTreeMap::new(), val);
        });
    }

    #[test]
    fn test_non_json_array_values_are_null() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            cx.eval::<Value<'_>, _>(
                r#"
                var unitialized;
                var a = [
                    undefined,
                    function() {},
                    Symbol(),
                    () => {},
                    unitialized,
                ];"#,
            )
            .unwrap();
            let v = cx.globals().get("a").unwrap();

            let val = deserialize_value::<Vec<Option<()>>>(v);
            assert_eq!(vec![None; 5], val);
        });
    }

    #[test]
    fn test_enum_unit() {
        let rt = Runtime::default();

        #[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
        enum Test {
            One,
            Two,
            Three,
        }

        rt.context().with(|cx| {
            let left = Test::Two;
            let value = to_value(cx, left).unwrap();
            let right: Test = from_value(value).unwrap();
            assert_eq!(left, right);
        });
    }

    #[test]
    fn test_enum_boxed_string() {
        #[derive(Debug, PartialEq, Deserialize)]
        enum Test {
            One,
            Two,
        }

        let rt = Runtime::default();
        rt.context().with(|cx| {
            cx.eval::<Value<'_>, _>("var a = new String('Two');")
                .unwrap();
            let v = cx.globals().get("a").unwrap();
            assert_eq!(Test::Two, deserialize_value::<Test>(v));
        });
    }

    #[test]
    fn test_enum_newtype() {
        let rt = Runtime::default();

        #[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
        enum Test {
            One(i32),
            Two(i32),
        }

        rt.context().with(|cx| {
            let left = Test::One(6);
            let value = to_value(cx, left).unwrap();
            let right: Test = from_value(value).unwrap();
            assert_eq!(left, right);
        });
    }

    #[test]
    fn test_enum_struct() {
        let rt = Runtime::default();

        #[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
        enum Test {
            One { a: i32 },
            Two(i32),
        }

        rt.context().with(|cx| {
            let left = Test::One { a: 6 };
            let value = to_value(cx, left).unwrap();
            let right: Test = from_value(value).unwrap();
            assert_eq!(left, right);
        });
    }

    #[test]
    fn test_enum_tuple() {
        let rt = Runtime::default();

        #[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
        enum Test {
            One(i32, i32),
        }

        rt.context().with(|cx| {
            let left = Test::One(1, 2);
            let value = to_value(cx, left).unwrap();
            let right: Test = from_value(value).unwrap();
            assert_eq!(left, right);
        });
    }

    #[test]
    fn test_short_bigint() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            cx.eval::<Value<'_>, _>("var a = BigInt(1);").unwrap();
            let v = cx.globals().get("a").unwrap();
            let val = deserialize_value::<String>(v);
            assert_eq!(val, "1");
        });
    }

    #[test]
    fn test_boxed_bigint() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            cx.eval::<Value<'_>, _>("var a = Object(1n);").unwrap();
            let v = cx.globals().get("a").unwrap();
            let val = deserialize_value::<String>(v);
            assert_eq!(val, "1");
        });
    }

    #[test]
    fn test_bigint() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            cx.eval::<Value<'_>, _>(
                r#"
                const left = 12345678901234567890n;
                const right = 98765432109876543210n;
                var a = left * right;
            "#,
            )
            .unwrap();
            let v = cx.globals().get("a").unwrap();
            let val = deserialize_value::<String>(v);
            assert_eq!(val, "1219326311370217952237463801111263526900");
        });
    }

    #[test]
    fn test_class_ids_have_not_changed() {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            let cases = [
                ("new Number(1)", ClassId::Number),
                ("new String('x')", ClassId::String),
                ("new Boolean(true)", ClassId::Bool),
                ("Object(1n)", ClassId::BigInt),
            ];

            for (expr, expected) in cases {
                let val = cx.eval::<Value<'_>, _>(expr).unwrap();
                assert_eq!(get_class_id(&val), expected, "{expr} class id changed");
            }
        });
    }
}
