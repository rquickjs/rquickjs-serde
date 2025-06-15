use std::str;

use rquickjs::{Ctx, Error as JSError, String as JSString, Value, qjs};

use crate::err::{Error, Result};

pub fn as_key(v: &Value) -> Result<String> {
    if v.is_string() {
        let js_str = v.as_string().unwrap();
        let v = js_str
            .to_string()
            .unwrap_or_else(|e| to_string_lossy(js_str.ctx(), js_str, e));
        Ok(v)
    } else {
        Err(Error::new("map keys must be a string"))
    }
}

/// Converts the JavaScript value to a string, replacing any invalid UTF-8 sequences with the
/// Unicode replacement character (U+FFFD).
pub fn to_string_lossy<'js>(cx: &Ctx<'js>, string: &JSString<'js>, error: JSError) -> String {
    let mut len: qjs::size_t = 0;
    let ptr = unsafe {
        #[allow(clippy::useless_conversion)]
        qjs::JS_ToCStringLen2(
            cx.as_raw().as_ptr(),
            &mut len,
            string.as_raw(),
            (false).into(),
        )
    };
    let buffer = unsafe { std::slice::from_raw_parts(ptr as *const u8, len as usize) };

    // The error here *must* be a Utf8 error; the `JSString::to_string()` may
    // return `JSError::Unknown`, but at that point, something else has gone
    // wrong too.

    let mut utf8_error = match error {
        JSError::Utf8(e) => e,
        _ => unreachable!("expected Utf8 error"),
    };
    let mut res = String::new();
    let mut buffer = buffer;
    loop {
        let (valid, after_valid) = buffer.split_at(utf8_error.valid_up_to());
        res.push_str(unsafe { str::from_utf8_unchecked(valid) });
        res.push(char::REPLACEMENT_CHARACTER);

        // see https://simonsapin.github.io/wtf-8/#surrogate-byte-sequence
        let lone_surrogate = matches!(after_valid, [0xED, 0xA0..=0xBF, 0x80..=0xBF, ..]);

        // https://simonsapin.github.io/wtf-8/#converting-wtf-8-utf-8 states that each
        // 3-byte lone surrogate sequence should be replaced by 1 UTF-8 replacement
        // char. Rust's `Utf8Error` reports each byte in the lone surrogate byte
        // sequence as a separate error with an `error_len` of 1. Since we insert a
        // replacement char for each error, this results in 3 replacement chars being
        // inserted. So we use an `error_len` of 3 instead of 1 to treat the entire
        // 3-byte sequence as 1 error instead of as 3 errors and only emit 1
        // replacement char.
        let error_len = if lone_surrogate {
            3
        } else {
            utf8_error
                .error_len()
                .expect("Error length should always be available on underlying buffer")
        };

        buffer = &after_valid[error_len..];
        match str::from_utf8(buffer) {
            Ok(valid) => {
                res.push_str(valid);
                break;
            }
            Err(e) => utf8_error = e,
        }
    }
    res
}
