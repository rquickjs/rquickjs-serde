#[allow(dead_code)]
pub(crate) struct Runtime {
    /// The QuickJS context.
    context: rquickjs::Context,
    /// The inner QuickJS runtime representation.
    inner: rquickjs::Runtime,
}

impl Runtime {
    pub fn new() -> Self {
        let rt = rquickjs::Runtime::new().unwrap();
        let context = rquickjs::Context::full(&rt).unwrap();
        Self { inner: rt, context }
    }

    pub fn context(&self) -> &rquickjs::Context {
        &self.context
    }
}

impl Default for Runtime {
    fn default() -> Self {
        Self::new()
    }
}
