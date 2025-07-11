use rquickjs::{Ctx, Value};
use serde::Serialize;
use serde::de::DeserializeOwned;

#[doc(inline)]
pub use crate::de::Deserializer;
#[doc(inline)]
pub use crate::err::{Error, Result};
#[doc(inline)]
pub use crate::ser::Serializer;

pub mod de;
pub mod err;
pub mod ser;
#[cfg(test)]
mod test;
mod utils;

// https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Number/MAX_SAFE_INTEGER#description
pub const MAX_SAFE_INTEGER: i64 = 2_i64.pow(53) - 1;

// https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Number/MIN_SAFE_INTEGER#description
pub const MIN_SAFE_INTEGER: i64 = -MAX_SAFE_INTEGER;

/// Convert a `T` into `rquickjs::Value`
///
/// # Example
///
/// ```
/// use std::error::Error;
///
/// use serde::Serialize;
/// use rquickjs::{Runtime, Context};
///
/// #[derive(Serialize)]
/// struct User {
///     fingerprint: String,
///     location: String,
/// }
///
/// fn serialize_to_value() -> Result<(), Box<dyn Error>> {
///     let u = User {
///         fingerprint: "0xF9BA143B95FF6D82".to_owned(),
///         location: "Menlo Park, CA".to_owned(),
///     };
///
///     let rt = Runtime::new().unwrap();
///     let ctx = Context::full(&rt).unwrap();
///
///     ctx.with(|ctx| {
///         let v = rquickjs_serde::to_value(ctx, u).unwrap();
///         let obj = v.into_object().unwrap();
///
///         let fingerprint: String = obj.get("fingerprint").unwrap();
///         assert_eq!(fingerprint, "0xF9BA143B95FF6D82");
///
///         let location: String = obj.get("location").unwrap();
///         assert_eq!(location, "Menlo Park, CA");
///     });
///
///     Ok(())
/// }
/// #
/// # serialize_to_value().unwrap();
/// ```
#[inline]
pub fn to_value<T>(context: Ctx<'_>, value: T) -> Result<Value<'_>>
where
    T: Serialize,
{
    let mut serializer = Serializer::from_context(context)?;
    value.serialize(&mut serializer)?;
    Ok(serializer.value)
}

/// Interpret a `rquickjs::Value` as an instance of type `T`.
///
/// # Example
///
/// ```
/// use std::error::Error;
///
/// use serde::Deserialize;
/// use rquickjs::{Runtime, Context, Value};
///
/// #[derive(Deserialize, Debug)]
/// struct User {
///     fingerprint: String,
///     location: String,
/// }
///
/// fn deserialize_from_value() -> Result<(), Box<dyn Error>> {
///     let rt = Runtime::new().unwrap();
///     let ctx = Context::full(&rt).unwrap();
///
///     let v = ctx.with(|ctx| {
///          ctx.eval::<Value<'_>, _>("var a = {fingerprint: '0xF9BA143B95FF6D82', location: 'Menlo Park, CA'};").unwrap();
///          let val = ctx.globals().get("a").unwrap();
///          let u: User = rquickjs_serde::from_value(val).unwrap();
///          u
///     });
///
///     assert_eq!(v.fingerprint, "0xF9BA143B95FF6D82");
///     assert_eq!(v.location, "Menlo Park, CA");
///
///     Ok(())
/// }
/// #
/// # deserialize_from_value().unwrap();
/// ```
///
/// # Errors
///
/// This conversion can fail if the structure of the Value does not match the
/// structure expected by `T`, for example if `T` is a struct type but the Value
/// contains something other than a JS Object. It can also fail if the structure
/// is correct but `T`'s implementation of `Deserialize` decides that something
/// is wrong with the data, for example required struct fields are missing from
/// the JS Object or some number is too big to fit in the expected primitive
/// type.
#[inline]
pub fn from_value<T>(value: Value) -> Result<T>
where
    T: DeserializeOwned,
{
    let mut deserializer = Deserializer::from(value);
    T::deserialize(&mut deserializer)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use quickcheck::quickcheck;
    use serde::de::DeserializeOwned;
    use serde::{Deserialize, Serialize};

    use crate::de::Deserializer as ValueDeserializer;
    use crate::err::Result;
    use crate::ser::Serializer as ValueSerializer;
    use crate::test::Runtime;
    use crate::{MAX_SAFE_INTEGER, MIN_SAFE_INTEGER};

    quickcheck! {
        fn test_str(expected: String) -> Result<bool> {
            let actual = do_roundtrip::<_, String>(&expected);
            Ok(expected == actual)
        }

        fn test_u8(expected: u8) -> Result<bool> {
            let actual = do_roundtrip::<_, u8>(&expected);
            Ok(expected == actual)
        }

        fn test_u16(expected: u16) -> Result<bool> {
            let actual = do_roundtrip::<_, u16>(&expected);
            Ok(expected == actual)
        }

        fn test_f32(expected: f32) -> quickcheck::TestResult {
            if expected.is_nan() {
                return quickcheck::TestResult::discard();
            }

            let actual = do_roundtrip::<_, f32>(&expected);
            quickcheck::TestResult::from_bool(expected == actual)
        }

        fn test_i32(expected: i32) -> Result<bool> {
            let actual = do_roundtrip::<_, i32>(&expected);
            Ok(expected == actual)
        }

        // This test is not representative of what is happening in the real world. Since we are transcoding
        // from msgpack, only values greather than or equal to u32::MAX would be serialized as `BigInt`. Any other values would
        // be serialized as a `number`.
        //
        // See https://github.com/3Hren/msgpack-rust/blob/aa3c4a77b2b901fe73a555c615b92773b40905fc/rmp/src/encode/sint.rs#L170.
        //
        // This test works here since we are explicitly calling serialize_i64 and deserialize_i64.
        fn test_i64(expected: i64) -> Result<bool> {
            if (MIN_SAFE_INTEGER..=MAX_SAFE_INTEGER).contains(&expected) {
                let actual = do_roundtrip::<_, i64>(&expected);
                Ok(expected == actual)
            } else {
                let expected_f64 = expected as f64;
                let actual = do_roundtrip::<_, f64>(&expected_f64);
                Ok(expected_f64 == actual)
            }
        }

        fn test_u32(expected: u32) -> Result<bool> {
            let actual = do_roundtrip::<_, u32>(&expected);
            Ok(expected == actual)
        }

        // This test is not representative of what is happening in the real world. Since we are transcoding
        // from msgpack, only values larger than i64::MAX would be serialized as BigInt. Any other values would
        // be serialized as a number.
        //
        // See https://github.com/3Hren/msgpack-rust/blob/aa3c4a77b2b901fe73a555c615b92773b40905fc/rmp/src/encode/sint.rs#L170.
        //
        // This test works here since we are explicitly calling serialize_u64 and deserialize_u64.
        fn test_u64(expected: u64) -> Result<bool> {
            if expected <= MAX_SAFE_INTEGER as u64 {
                let actual = do_roundtrip::<_, u64>(&expected);
                Ok(expected == actual)
            } else {
                let expected_f64 = expected as f64;
                let actual = do_roundtrip::<_, f64>(&expected_f64);
                Ok(expected_f64 == actual)
            }
        }

        fn test_bool(expected: bool) -> Result<bool> {
            let actual = do_roundtrip::<_, bool>(&expected);
            Ok(expected == actual)
        }
    }

    #[test]
    fn test_map() {
        let mut expected = BTreeMap::<String, String>::new();
        expected.insert("foo".to_string(), "bar".to_string());
        expected.insert("hello".to_string(), "world".to_string());

        let actual = do_roundtrip::<_, BTreeMap<String, String>>(&expected);

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_struct_into_map() {
        #[derive(Debug, Serialize, Deserialize, PartialEq)]
        struct MyObject {
            foo: String,
            bar: u32,
        }
        let expected = MyObject {
            foo: "hello".to_string(),
            bar: 1337,
        };

        let actual = do_roundtrip::<_, MyObject>(&expected);

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_nested_maps() {
        let mut expected = BTreeMap::<String, BTreeMap<String, String>>::new();
        let mut a = BTreeMap::new();
        a.insert("foo".to_string(), "bar".to_string());
        a.insert("hello".to_string(), "world".to_string());
        let mut b = BTreeMap::new();
        b.insert("toto".to_string(), "titi".to_string());
        expected.insert("aaa".to_string(), a);
        expected.insert("bbb".to_string(), b);

        let actual = do_roundtrip::<_, BTreeMap<String, BTreeMap<String, String>>>(&expected);

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_nested_structs_into_maps() {
        #[derive(Debug, Serialize, Deserialize, PartialEq)]
        struct MyObjectB {
            toto: String,
            titi: i32,
        }

        #[derive(Debug, Serialize, Deserialize, PartialEq)]
        struct MyObjectA {
            foo: String,
            bar: u32,
            b: MyObjectB,
        }
        let expected = MyObjectA {
            foo: "hello".to_string(),
            bar: 1337,
            b: MyObjectB {
                toto: "world".to_string(),
                titi: -42,
            },
        };

        let actual = do_roundtrip::<_, MyObjectA>(&expected);

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_sequence() {
        let expected = vec!["hello".to_string(), "world".to_string()];

        let actual = do_roundtrip::<_, Vec<String>>(&expected);

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_nested_sequences() {
        let mut expected = Vec::new();
        let a = vec!["foo".to_string(), "bar".to_string()];
        let b = vec!["toto".to_string(), "tata".to_string()];
        expected.push(a);
        expected.push(b);

        let actual = do_roundtrip::<_, Vec<Vec<String>>>(&expected);

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_sanity() {
        #[derive(Debug, Serialize, Deserialize, PartialEq)]
        struct MyObject {
            a: u8,
            b: u16,
            c: u32,
            d: u64,
            e: i8,
            f: i16,
            g: i32,
            h: i64,
            i: f32,
            j: f64,
            k: String,
            l: bool,
            m: BTreeMap<String, u32>,
            n: Vec<u32>,
            o: BTreeMap<String, BTreeMap<String, u32>>,
            p: Vec<Vec<u32>>,
            bb: MyObjectB,
        }

        #[derive(Debug, Serialize, Deserialize, PartialEq)]
        struct MyObjectB {
            a: u32,
            cc: MyObjectC,
        }

        #[derive(Debug, Serialize, Deserialize, PartialEq)]
        struct MyObjectC {
            a: Vec<u32>,
            b: BTreeMap<String, u32>,
        }

        let mut cc_b = BTreeMap::new();
        cc_b.insert("a".to_string(), 123);
        cc_b.insert("b".to_string(), 456);
        let cc = MyObjectC {
            a: vec![1337, 42],
            b: cc_b,
        };

        let bb = MyObjectB { a: 789, cc };

        let mut m = BTreeMap::new();
        m.insert("a".to_string(), 123);
        m.insert("b".to_string(), 456);
        m.insert("c".to_string(), 789);

        let mut oo = BTreeMap::new();
        oo.insert("e".to_string(), 123);

        let mut o = BTreeMap::new();
        o.insert("d".to_string(), oo);

        let expected = MyObject {
            a: u8::MAX,
            b: u16::MAX,
            c: u32::MAX,
            d: MAX_SAFE_INTEGER as u64,
            e: i8::MAX,
            f: i16::MAX,
            g: i32::MAX,
            h: MIN_SAFE_INTEGER,
            i: f32::MAX,
            j: f64::MAX,
            k: "hello world".to_string(),
            l: true,
            m,
            n: vec![1, 2, 3, 4, 5],
            o,
            p: vec![vec![1, 2], vec![3, 4, 5]],
            bb,
        };

        let actual = do_roundtrip::<_, MyObject>(&expected);

        assert_eq!(expected, actual);
    }

    fn do_roundtrip<E, A>(expected: &E) -> A
    where
        E: Serialize,
        A: DeserializeOwned,
    {
        let rt = Runtime::default();
        rt.context().with(|cx| {
            let mut serializer = ValueSerializer::from_context(cx).unwrap();
            expected.serialize(&mut serializer).unwrap();
            let mut deserializer = ValueDeserializer::from(serializer.value);
            let actual = A::deserialize(&mut deserializer).unwrap();
            actual
        })
    }
}
