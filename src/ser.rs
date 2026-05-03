use alloc::string::ToString as _;

use rquickjs::{Array, Ctx, Object, String as JSString, Value};
use serde::{Serialize, ser};

use crate::err::{Error, Result};

/// `Serializer` is a serializer for [Value] values, implementing the `serde::Serializer` trait.
///
/// This struct is responsible for converting Rust types into [Value] using the Serde
/// serialization framework.
///
/// ```
/// # use rquickjs::{Runtime, Context, Value};
/// # use rquickjs_serde::Serializer;
/// # use serde::Serializer as _;
/// #
/// let rt = Runtime::new().unwrap();
/// let ctx = Context::full(&rt).unwrap();
/// ctx.with(|ctx| {
///     let mut serializer = Serializer::from_context(ctx.clone()).unwrap();
///     let value = serializer.serialize_u32(42).unwrap();
///     assert!(value.is_number());
/// });
/// ```
pub struct Serializer<'js> {
    pub context: Ctx<'js>,
}

pub struct SeqSerializer<'se, 'js> {
    ser: &'se mut Serializer<'js>,
    value: Array<'js>,
}

pub struct TupleVariantSerializer<'se, 'js> {
    ser: &'se mut Serializer<'js>,
    wrapper: Object<'js>,
    value: Array<'js>,
}

pub struct MapSerializer<'se, 'js> {
    ser: &'se mut Serializer<'js>,
    value: Object<'js>,
    /** current map key, will be left `None` for structs */
    key: Option<Value<'js>>,
}

pub struct StructVariantSerializer<'se, 'js> {
    ser: &'se mut Serializer<'js>,
    wrapper: Object<'js>,
    value: Object<'js>,
}

impl<'se, 'js> SeqSerializer<'se, 'js> {
    fn new(ser: &'se mut Serializer<'js>) -> Result<Self> {
        let value = Array::new(ser.context.clone()).map_err(Error::new)?;

        Ok(Self { ser, value })
    }
}

impl<'se, 'js> TupleVariantSerializer<'se, 'js> {
    fn new(ser: &'se mut Serializer<'js>, variant: &'static str) -> Result<Self> {
        let wrapper = Object::new(ser.context.clone()).map_err(Error::new)?;
        let value = Array::new(ser.context.clone()).map_err(Error::new)?;
        wrapper.set(variant, value.clone()).map_err(Error::new)?;

        Ok(Self {
            ser,
            wrapper,
            value,
        })
    }
}

impl<'se, 'js> MapSerializer<'se, 'js> {
    fn new(ser: &'se mut Serializer<'js>) -> Result<Self> {
        let value = Object::new(ser.context.clone()).map_err(Error::new)?;
        Ok(Self {
            ser,
            value,
            key: None,
        })
    }
}
impl<'se, 'js> StructVariantSerializer<'se, 'js> {
    fn new(ser: &'se mut Serializer<'js>, variant: &'static str) -> Result<Self> {
        let wrapper = Object::new(ser.context.clone()).map_err(Error::new)?;
        let value = Object::new(ser.context.clone()).map_err(Error::new)?;
        wrapper.set(variant, value.clone()).map_err(Error::new)?;

        Ok(Self {
            ser,
            wrapper,
            value,
        })
    }
}

impl<'js> Serializer<'js> {
    pub fn from_context(context: Ctx<'js>) -> Result<Self> {
        Ok(Self {
            context: context.clone(),
        })
    }
}
impl<'js, 'se> ser::Serializer for &'se mut Serializer<'js> {
    type Ok = Value<'js>;
    type Error = Error;

    type SerializeSeq = SeqSerializer<'se, 'js>;
    type SerializeTuple = SeqSerializer<'se, 'js>;
    type SerializeTupleStruct = SeqSerializer<'se, 'js>;
    type SerializeTupleVariant = TupleVariantSerializer<'se, 'js>;
    type SerializeMap = MapSerializer<'se, 'js>;
    type SerializeStruct = MapSerializer<'se, 'js>;
    type SerializeStructVariant = StructVariantSerializer<'se, 'js>;

    fn serialize_i8(self, v: i8) -> Result<Self::Ok> {
        self.serialize_i32(i32::from(v))
    }

    fn serialize_i16(self, v: i16) -> Result<Self::Ok> {
        self.serialize_i32(i32::from(v))
    }

    fn serialize_i32(self, v: i32) -> Result<Self::Ok> {
        Ok(Value::new_int(self.context.clone(), v))
    }

    fn serialize_i64(self, v: i64) -> Result<Self::Ok> {
        Ok(Value::new_number(self.context.clone(), v as _))
    }

    fn serialize_u8(self, v: u8) -> Result<Self::Ok> {
        self.serialize_i32(i32::from(v))
    }

    fn serialize_u16(self, v: u16) -> Result<Self::Ok> {
        self.serialize_i32(i32::from(v))
    }

    fn serialize_u32(self, v: u32) -> Result<Self::Ok> {
        // NOTE: See optimization note in serialize_f64.
        self.serialize_f64(f64::from(v))
    }

    fn serialize_u64(self, v: u64) -> Result<Self::Ok> {
        Ok(Value::new_number(self.context.clone(), v as _))
    }

    fn serialize_f32(self, v: f32) -> Result<Self::Ok> {
        // NOTE: See optimization note in serialize_f64.
        self.serialize_f64(f64::from(v))
    }

    fn serialize_f64(self, v: f64) -> Result<Self::Ok> {
        // NOTE: QuickJS will create a number value backed by an i32 when the value is within
        // the i32::MIN..=i32::MAX as an optimization. Otherwise the value will be backed by a f64.
        Ok(Value::new_float(self.context.clone(), v))
    }

    fn serialize_bool(self, b: bool) -> Result<Self::Ok> {
        Ok(Value::new_bool(self.context.clone(), b))
    }

    fn serialize_char(self, v: char) -> Result<Self::Ok> {
        self.serialize_str(&v.to_string())
    }

    fn serialize_str(self, v: &str) -> Result<Self::Ok> {
        let js_string = JSString::from_str(self.context.clone(), v).map_err(Error::new)?;
        Ok(Value::from(js_string))
    }

    fn serialize_none(self) -> Result<Self::Ok> {
        self.serialize_unit()
    }

    fn serialize_unit(self) -> Result<Self::Ok> {
        Ok(Value::new_null(self.context.clone()))
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok> {
        self.serialize_unit()
    }

    fn serialize_some<T>(self, value: &T) -> Result<Self::Ok>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(self)
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
    ) -> Result<Self::Ok> {
        self.serialize_str(variant)
    }

    fn serialize_newtype_struct<T>(self, _name: &'static str, value: &T) -> Result<Self::Ok>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(self)
    }

    fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq> {
        SeqSerializer::new(self)
    }

    fn serialize_tuple(self, _len: usize) -> Result<Self::SerializeTuple> {
        SeqSerializer::new(self)
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct> {
        self.serialize_seq(Some(len))
    }

    fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap> {
        MapSerializer::new(self)
    }

    fn serialize_struct(self, _name: &'static str, _len: usize) -> Result<Self::SerializeStruct> {
        MapSerializer::new(self)
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant> {
        StructVariantSerializer::new(self, variant)
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant> {
        TupleVariantSerializer::new(self, variant)
    }

    fn serialize_newtype_variant<T>(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok>
    where
        T: ?Sized + Serialize,
    {
        let obj = Object::new(self.context.clone()).map_err(Error::new)?;
        let value = value.serialize(&mut *self)?;
        obj.set(variant, value).map_err(Error::new)?;
        Ok(obj.into())
    }

    fn serialize_bytes(self, _: &[u8]) -> Result<Self::Ok> {
        Err(Error::new("Cannot serialize bytes"))
    }
}

impl<'se, 'js> ser::SerializeSeq for SeqSerializer<'se, 'js> {
    type Ok = Value<'js>;
    type Error = Error;

    fn serialize_element<T>(&mut self, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        self.value
            .set(self.value.len(), value.serialize(&mut *self.ser)?)
            .map_err(Error::new)
    }

    fn end(self) -> Result<Self::Ok> {
        Ok(self.value.into())
    }
}

impl<'se, 'js> ser::SerializeTuple for SeqSerializer<'se, 'js> {
    type Ok = Value<'js>;
    type Error = Error;

    fn serialize_element<T>(&mut self, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        self.value
            .set(self.value.len(), value.serialize(&mut *self.ser)?)
            .map_err(Error::new)
    }

    fn end(self) -> Result<Self::Ok> {
        Ok(self.value.into())
    }
}

impl<'se, 'js> ser::SerializeTupleStruct for SeqSerializer<'se, 'js> {
    type Ok = Value<'js>;
    type Error = Error;

    fn serialize_field<T>(&mut self, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        self.value
            .set(self.value.len(), value.serialize(&mut *self.ser)?)
            .map_err(Error::new)
    }

    fn end(self) -> Result<Self::Ok> {
        Ok(self.value.into())
    }
}

impl<'se, 'js> ser::SerializeTupleVariant for TupleVariantSerializer<'se, 'js> {
    type Ok = Value<'js>;
    type Error = Error;

    fn serialize_field<T>(&mut self, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        self.value
            .set(self.value.len(), value.serialize(&mut *self.ser)?)
            .map_err(Error::new)
    }

    fn end(self) -> Result<Self::Ok> {
        Ok(self.wrapper.into())
    }
}

impl<'se, 'js> ser::SerializeMap for MapSerializer<'se, 'js> {
    type Ok = Value<'js>;
    type Error = Error;

    fn serialize_key<T>(&mut self, key: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        self.key = Some(key.serialize(&mut *self.ser)?);
        Ok(())
    }

    fn serialize_value<T>(&mut self, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        let key = self
            .key
            .take()
            .ok_or_else(|| Error::new("serialize_value before serialize_key"))?;

        let value = value.serialize(&mut *self.ser)?;
        self.value.set(key, value).map_err(Error::new)
    }

    fn end(self) -> Result<Self::Ok> {
        Ok(self.value.into())
    }
}

impl<'se, 'js> ser::SerializeStruct for MapSerializer<'se, 'js> {
    type Ok = Value<'js>;
    type Error = Error;

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        let value = value.serialize(&mut *self.ser)?;
        self.value.set(key, value).map_err(Error::new)?;
        Ok(())
    }

    fn end(self) -> Result<Self::Ok> {
        Ok(self.value.into())
    }
}

impl<'se, 'js> ser::SerializeStructVariant for StructVariantSerializer<'se, 'js> {
    type Ok = Value<'js>;
    type Error = Error;

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        let value = value.serialize(&mut *self.ser)?;
        self.value.set(key, value).map_err(Error::new)?;
        Ok(())
    }

    fn end(self) -> Result<Self::Ok> {
        Ok(self.wrapper.into())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use rquickjs::{Ctx, Function, Object, Value};
    use serde::{Serialize, Serializer};

    use super::Serializer as ValueSerializer;
    use crate::err::Result;
    use crate::test::Runtime;
    use crate::{MAX_SAFE_INTEGER, MIN_SAFE_INTEGER};
    use quickcheck::quickcheck;

    fn with_serializer<F: FnMut(&mut ValueSerializer) -> Result<bool>>(
        rt: &Runtime,
        mut w: F,
    ) -> Result<bool> {
        rt.context().with(|c| {
            let mut serializer = ValueSerializer::from_context(c.clone()).unwrap();
            w(&mut serializer)
        })
    }

    quickcheck! {
        fn test_i16(v: i16) -> Result<bool> {
            let rt = Runtime::default();
            with_serializer(&rt, |serializer| {
                let value = serializer.serialize_i16(v)?;
                Ok(value.is_int())
            })
        }

        fn test_i32(v: i32) -> Result<bool> {
            let rt = Runtime::default();
            with_serializer(&rt, |serializer| {
                let value = serializer.serialize_i32(v)?;
                Ok(value.is_int())
            })
        }

        fn test_i64(v: i64) -> Result<bool> {
            let rt = Runtime::default();
            with_serializer(&rt, |serializer| {
                if (MIN_SAFE_INTEGER..=MAX_SAFE_INTEGER).contains(&v) {
                    let value = serializer.serialize_i64(v)?;
                    Ok(value.is_number())
                } else {
                    let value = serializer.serialize_f64(v as f64)?;
                    Ok(value.is_number())
                }
            })
        }

        fn test_u64(v: u64) -> Result<bool> {
            let rt = Runtime::default();
            with_serializer(&rt, |serializer| {
                if v <= MAX_SAFE_INTEGER as u64 {
                    let value =  serializer.serialize_u64(v)?;
                    Ok(value.is_number())
                } else {
                    let value =  serializer.serialize_f64(v as f64)?;
                    Ok(value.is_number())
                }
            })
        }

        fn test_u16(v: u16) -> Result<bool> {
            let rt = Runtime::default();

            with_serializer(&rt, |serializer| {
                let value = serializer.serialize_u16(v)?;
                Ok(value.is_int())
            })
        }

        fn test_u32(v: u32) -> Result<bool> {
            let rt = Runtime::default();
            with_serializer(&rt, |serializer| {
                let value = serializer.serialize_u32(v)?;
                // QuickJS optimizes numbers in the range of [i32::MIN..=i32::MAX]
                // as ints
                if v > i32::MAX as u32 {
                    Ok(value.is_float())
                } else {
                    Ok(value.is_int())
                }
            })

        }

        fn test_f32(v: f32) -> Result<bool> {
            let rt = Runtime::default();
            with_serializer(&rt, |serializer| {
                let value = serializer.serialize_f32(v)?;

                if v == 0.0_f32 {
                    if v.is_sign_positive() {
                        return  Ok(value.is_int());
                    }


                    if v.is_sign_negative() {
                        return Ok(value.is_float());
                    }
                }

                // The same (int) optimization is happening at this point,
                // but here we need to account for signs
                let zero_fractional_part = v.fract() == 0.0;
                let range = (i32::MIN as f32)..=(i32::MAX as f32);

                if zero_fractional_part && range.contains(&v) {
                    Ok(value.is_int())
                } else {
                    Ok(value.is_float())
                }
            })
        }

        fn test_f64(v: f64) -> Result<bool> {
            let rt = Runtime::default();
            with_serializer(&rt, |serializer| {
                let value = serializer.serialize_f64(v)?;

                if v == 0.0_f64 {
                    if v.is_sign_positive() {
                        return  Ok(value.is_int());
                    }


                    if v.is_sign_negative() {
                        return Ok(value.is_float());
                    }
                }

                // The same (int) optimization is happening at this point,
                // but here we need to account for signs
                let zero_fractional_part = v.fract() == 0.0;
                let range = (i32::MIN as f64)..=(i32::MAX as f64);

                if zero_fractional_part && range.contains(&v) {
                    Ok(value.is_int())
                } else {
                    Ok(value.is_float())
                }
            })
        }

        fn test_bool(v: bool) -> Result<bool> {
            let rt = Runtime::default();
            with_serializer(&rt, |serializer| {
                let value =  serializer.serialize_bool(v)?;
                Ok(value.is_bool())
            })
        }

        fn test_str(v: String) -> Result<bool> {
            let rt = Runtime::default();
            with_serializer(&rt, |serializer| {
                let value = serializer.serialize_str(v.as_str())?;

                Ok(value.is_string())
            })
        }
    }

    #[test]
    fn test_null() -> Result<()> {
        let rt = Runtime::default();

        rt.context().with(|cx| {
            let mut serializer = ValueSerializer::from_context(cx.clone()).unwrap();
            let value = serializer.serialize_unit().unwrap();

            assert!(value.is_null());
        });
        Ok(())
    }

    #[test]
    fn test_nan() -> Result<()> {
        let rt = Runtime::default();

        rt.context().with(|cx| {
            let mut serializer = ValueSerializer::from_context(cx.clone()).unwrap();
            let value = serializer.serialize_f64(f64::NAN).unwrap();
            assert!(value.is_number());
        });
        Ok(())
    }

    #[test]
    fn test_infinity() -> Result<()> {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            let mut serializer = ValueSerializer::from_context(cx.clone()).unwrap();
            let value = serializer.serialize_f64(f64::INFINITY).unwrap();
            assert!(value.is_number());
        });
        Ok(())
    }

    #[test]
    fn test_negative_infinity() -> Result<()> {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            let mut serializer = ValueSerializer::from_context(cx.clone()).unwrap();
            let value = serializer.serialize_f64(f64::NEG_INFINITY).unwrap();
            assert!(value.is_number());
        });
        Ok(())
    }

    #[test]
    fn test_map() {
        let rt = Runtime::default();

        rt.context().with(|cx| {
            let mut serializer = ValueSerializer::from_context(cx.clone()).unwrap();

            let mut map = BTreeMap::new();
            map.insert("foo", "bar");
            map.insert("toto", "titi");

            let value = map.serialize(&mut serializer).unwrap();

            assert!(value.is_object())
        });
    }

    #[test]
    fn test_struct_into_map() {
        let rt = Runtime::default();

        rt.context().with(|cx| {
            let mut serializer = ValueSerializer::from_context(cx.clone()).unwrap();

            #[derive(serde::Serialize)]
            struct MyObject {
                foo: String,
                bar: u32,
            }

            let my_object = MyObject {
                foo: "hello".to_string(),
                bar: 1337,
            };
            let value = my_object.serialize(&mut serializer).unwrap();

            assert!(value.is_object());
        });
    }

    #[test]
    fn test_sequence() {
        let rt = Runtime::default();

        rt.context().with(|cx| {
            let mut serializer = ValueSerializer::from_context(cx.clone()).unwrap();

            let sequence = vec!["hello", "world"];

            let value = sequence.serialize(&mut serializer).unwrap();

            assert!(value.is_array());
            assert_eq!(r#"["hello","world"]"#, json_stringify(cx.clone(), value));
        });
    }

    #[test]
    fn test_enum_unit() {
        let rt = Runtime::default();

        #[derive(Debug, Clone, Copy, PartialEq, Serialize)]
        enum Test {
            One,
        }

        rt.context().with(|cx| {
            let mut serializer = ValueSerializer::from_context(cx.clone()).unwrap();

            let src = Test::One;

            let value = src.serialize(&mut serializer).unwrap();

            let inner: String = value.as_string().unwrap().to_string().unwrap();
            assert_eq!("One", inner);
        });
    }

    #[test]
    fn test_enum_newtype() {
        let rt = Runtime::default();

        #[derive(Debug, Clone, Copy, PartialEq, Serialize)]
        enum Test {
            Item(i32),
        }

        rt.context().with(|cx| {
            let mut serializer = ValueSerializer::from_context(cx.clone()).unwrap();
            let src = Test::Item(10);
            let value = src.serialize(&mut serializer).unwrap();

            assert_eq!(r#"{"Item":10}"#, json_stringify(cx.clone(), value));
        });
    }

    #[test]
    fn test_enum_struct() {
        let rt = Runtime::default();

        #[derive(Debug, Clone, Copy, PartialEq, Serialize)]
        enum Test {
            One { a: i32 },
        }

        rt.context().with(|cx| {
            let src = Test::One { a: 6 };

            let mut serializer = ValueSerializer::from_context(cx.clone()).unwrap();
            let value = src.serialize(&mut serializer).unwrap();

            assert_eq!(r#"{"One":{"a":6}}"#, json_stringify(cx.clone(), value));
        });
    }

    #[test]
    fn test_enum_tuple() {
        let rt = Runtime::default();

        #[derive(Debug, Clone, Copy, PartialEq, Serialize)]
        enum Test {
            One(i32, i32),
        }

        rt.context().with(|cx| {
            let mut serializer = ValueSerializer::from_context(cx.clone()).unwrap();
            let src = Test::One(1, 2);
            let value = src.serialize(&mut serializer).unwrap();

            assert_eq!(r#"{"One":[1,2]}"#, json_stringify(cx.clone(), value));
        });
    }

    fn json_stringify<'js>(cx: Ctx<'js>, value: Value<'js>) -> String {
        let obj: Object = cx.globals().get("JSON").unwrap();
        let stringify: Function = obj.get("stringify").unwrap();
        let str: String = stringify.call((value,)).unwrap();
        str
    }
}
