# rquickjs serde

[![github](https://img.shields.io/badge/github-rquickjs/rquickjs-serde.svg?style=for-the-badge&logo=github)](https://github.com/rquickjs/rquickjs-serde)
[![crates](https://img.shields.io/crates/v/rquickjs-serde.svg?style=for-the-badge&color=fc8d62&logo=rust)](https://crates.io/crates/rquickjs-serde)

This is a serde serializer/deserializer for [rquickjs](https://github.com/DelSkayn/rquickjs) `Value`.

## Usage

```rust
use std::error::Error;

use serde::Serialize;
use rquickjs::{Runtime, Context};

#[derive(Serialize)]
struct User {
    fingerprint: String,
    location: String,
}

fn main() {
    let rt = Runtime::new().unwrap();
    let ctx = Context::full(&rt).unwrap();

    // Serialize to a Value<'_>
    let u = User {
        fingerprint: "0xF9BA143B95FF6D82".to_owned(),
        location: "Menlo Park, CA".to_owned(),
    };
    ctx.with(|ctx| {
        let v = rquickjs_serde::to_value(ctx, u).unwrap();
        let obj = v.into_object().unwrap();

        let fingerprint: String = obj.get("fingerprint").unwrap();
        assert_eq!(fingerprint, "0xF9BA143B95FF6D82");

        let location: String = obj.get("location").unwrap();
        assert_eq!(location, "Menlo Park, CA");
    });

    // Deserialize from a Value<'_>
    let v = ctx.with(|ctx| {
        ctx.eval::<Value<'_>, _>("var a = {fingerprint: '0xF9BA143B95FF6D82', location: 'Menlo Park, CA'};").unwrap();
        let val = ctx.globals().get("a").unwrap();
        let u: User = rquickjs_serde::from_value(val).unwrap();
        u
    });
    assert_eq!(v.fingerprint, "0xF9BA143B95FF6D82");
    assert_eq!(v.location, "Menlo Park, CA");
}
```

## Acknowledgements

This project includes code derived from the [Javy](https://github.com/bytecodealliance/javy) project. See [`NOTICE`](./NOTICE) for more details.
