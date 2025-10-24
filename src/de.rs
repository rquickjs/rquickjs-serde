use rquickjs::{
    Array, Exception, Filter, Function, Null, Object, String as JSString, Value,
    atom::PredefinedAtom,
    function::This,
    object::ObjectIter,
    qjs::{JS_GetClassID, JS_GetProperty},
};
use serde::{
    de::{self, IntoDeserializer, Unexpected},
    forward_to_deserialize_any,
};

use crate::err::{Error, Result};
use crate::utils::{as_key, to_string_lossy};
use crate::{MAX_SAFE_INTEGER, MIN_SAFE_INTEGER};

// Class IDs, for internal, deserialization purposes only.
// FIXME: This can change since the ABI is not stable.
// See https://github.com/quickjs-ng/quickjs/issues/758
enum ClassId {
    Number = 4,
    String = 5,
    Bool = 6,
    BigInt = 33,
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
    map_key: bool,
    current_kv: Option<(Value<'js>, Value<'js>)>,
    /// Stack to track circular dependencies.
    stack: Vec<Value<'js>>,
}

impl<'de> From<Value<'de>> for Deserializer<'de> {
    fn from(value: Value<'de>) -> Self {
        Self {
            value,
            map_key: false,
            current_kv: None,
            // We are probaby over allocating here. But it's probably fine to
            // over allocate to avoid paying the cost of subsequent allocations.
            stack: Vec::with_capacity(100),
        }
    }
}

impl<'js> Deserializer<'js> {
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
            let whole = f64_representation.fract() == 0.0;

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
        if self.value.is_number() {
            return self.deserialize_number(visitor);
        }

        if get_class_id(&self.value) == ClassId::Number as u32 {
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

        if get_class_id(&self.value) == ClassId::Bool as u32 {
            let value_of = get_valueof(&self.value);
            if let Some(f) = value_of {
                let v = f.call((This(self.value.clone()),)).map_err(Error::new)?;
                return visitor.visit_bool(v);
            }
        }

        if self.value.is_null() || self.value.is_undefined() {
            return visitor.visit_unit();
        }

        if get_class_id(&self.value) == ClassId::String as u32 {
            let value_of = get_to_string(&self.value);
            if let Some(f) = value_of {
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

        if let Some(arr) = self.value.as_array() {
            let seq_access = SeqAccess::new(self, arr.clone())?;
            return visitor.visit_seq(seq_access);
        }

        if self.value.is_object() {
            ensure_supported(&self.value)?;

            if let Some(f) = get_to_json(&self.value) {
                let v: Value = f.call((This(self.value.clone()),)).map_err(Error::new)?;

                if v.is_undefined() {
                    self.value = Value::new_undefined(v.ctx().clone());
                } else {
                    self.value = v;
                }
                return self.deserialize_any(visitor);
            }

            let map_access = MapAccess::new(self, self.value.clone().into_object().unwrap())?;
            let result = visitor.visit_map(map_access);
            return result;
        }

        // FIXME: Replace type_of when https://github.com/DelSkayn/rquickjs/pull/458 is merged.
        if (get_class_id(&self.value) == ClassId::BigInt as u32
            || self.value.type_of() == rquickjs::Type::BigInt)
            && let Some(f) = get_to_json(&self.value)
        {
            let v: Value = f.call((This(self.value.clone()),)).map_err(Error::new)?;
            self.value = v;
            return self.deserialize_any(visitor);
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
        if get_class_id(&self.value) == ClassId::String as u32
            && let Some(f) = get_to_string(&self.value)
        {
            let v = f.call((This(self.value.clone()),)).map_err(Error::new)?;
            self.value = v;
        }

        // Now require a primitive string.
        let s = if let Some(s) = self.value.as_string() {
            s.to_string()
                .unwrap_or_else(|e| to_string_lossy(self.value.ctx(), s, e))
        } else {
            return Err(Error::new("expected a string for enum unit variant"));
        };

        // Hand Serde an EnumAccess that only supports unit variants.
        visitor.visit_enum(UnitEnumAccess { variant: s })
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

                let to_json = get_to_json(&v);
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

                if class_id == ClassId::Bool as u32 || class_id == ClassId::Number as u32 {
                    let value_of = get_valueof(&v);
                    if let Some(f) = value_of {
                        let v = f.call((This(v.clone()),)).map_err(Error::new)?;
                        self.de.current_kv = Some((k.clone(), v));
                    }
                } else if class_id == ClassId::String as u32 {
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
        self.de.check_cycles()?;
        seed.deserialize(&mut *self.de)
    }
}

/// A helper struct for deserializing sequences.
struct SeqAccess<'a, 'de: 'a> {
    /// The deserializer.
    de: &'a mut Deserializer<'de>,
    /// The sequence, represented as a JavaScript array.
    seq: Array<'de>,
    /// The sequence length.
    length: usize,
    /// The current index.
    index: usize,
}

impl<'a, 'de: 'a> SeqAccess<'a, 'de> {
    /// Creates a new `SeqAccess` ensuring that the top-level value is added
    /// to the `Deserializer` visitor stack.
    fn new(de: &'a mut Deserializer<'de>, seq: Array<'de>) -> Result<Self> {
        de.stack.push(seq.clone().into_value());

        // Retrieve the `length` property from the object itself rather than
        // using the bindings `Array::len` given that according to the spec
        // it's fine to return any value, not just a number from the
        // `length` property.
        let value: Value = seq
            .as_object()
            .get(PredefinedAtom::Length)
            .map_err(Error::new)?;
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
            let el = self.seq.get(self.index).map_err(Error::new)?;
            let to_json = get_to_json(&el);

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
    let f = unsafe {
        JS_GetProperty(
            value.ctx().as_raw().as_ptr(),
            value.as_raw(),
            PredefinedAtom::ToJSON as u32,
        )
    };
    let f = unsafe { Value::from_raw(value.ctx().clone(), f) };

    if f.is_function()
        && let Some(f) = f.into_function()
    {
        Some(f)
    } else {
        None
    }
}

/// Checks if the value is an object and contains a `valueOf` function.
fn get_valueof<'a>(value: &Value<'a>) -> Option<Function<'a>> {
    if let Some(o) = value.as_object() {
        let value_of = o.get("valueOf").ok();
        value_of.clone()
    } else {
        None
    }
}

/// Checks if the value is an object and contains a `valueOf` function.
fn get_to_string<'a>(value: &Value<'a>) -> Option<Function<'a>> {
    if let Some(o) = value.as_object() {
        let value_of = o.get("toString").ok();
        value_of.clone()
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
    if class_id == (ClassId::Bool as u32) || class_id == (ClassId::Number as u32) {
        return Ok(true);
    }

    if class_id == ClassId::BigInt as u32 {
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

/// A helper struct for deserializing enums containing unit variants.
struct UnitEnumAccess {
    variant: String,
}

impl<'de> de::EnumAccess<'de> for UnitEnumAccess {
    type Error = Error;
    type Variant = UnitOnlyVariant;

    fn variant_seed<V>(self, seed: V) -> Result<(V::Value, Self::Variant)>
    where
        V: de::DeserializeSeed<'de>,
    {
        let v = seed.deserialize(self.variant.into_deserializer())?;
        Ok((v, UnitOnlyVariant))
    }
}

struct UnitOnlyVariant;

impl<'de> de::VariantAccess<'de> for UnitOnlyVariant {
    type Error = Error;

    fn unit_variant(self) -> Result<()> {
        Ok(())
    }

    fn newtype_variant_seed<T>(self, _seed: T) -> Result<T::Value>
    where
        T: de::DeserializeSeed<'de>,
    {
        Err(de::Error::invalid_type(
            Unexpected::NewtypeVariant,
            &"unit variant",
        ))
    }

    fn tuple_variant<V>(self, _len: usize, _visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        Err(de::Error::invalid_type(
            Unexpected::TupleVariant,
            &"unit variant",
        ))
    }

    fn struct_variant<V>(self, _fields: &'static [&'static str], _visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        Err(de::Error::invalid_type(
            Unexpected::StructVariant,
            &"unit variant",
        ))
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use rquickjs::Value;
    use serde::de::DeserializeOwned;
    use serde::{Deserialize, Serialize};

    use super::Deserializer as ValueDeserializer;
    use crate::test::Runtime;
    use crate::{MAX_SAFE_INTEGER, from_value, to_value};

    fn deserialize_value<T>(v: Value<'_>) -> T
    where
        T: DeserializeOwned,
    {
        let mut deserializer = ValueDeserializer::from(v);
        T::deserialize(&mut deserializer).unwrap()
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
    #[should_panic]
    fn test_map_does_not_support_non_string_keys() {
        let rt = Runtime::default();
        // Sanity check to make sure it's not possible to deserialize
        // to a map where keys are not strings (e.g. numerical value).
        rt.context().with(|c| {
            c.eval::<Value<'_>, _>("var a = {1337: 42}; ").unwrap();
            let val = c.globals().get("a").unwrap();
            deserialize_value::<BTreeMap<i32, i32>>(val);
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
    fn test_enum() {
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
}
