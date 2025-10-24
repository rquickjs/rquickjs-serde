use std::{error, fmt};

use rquickjs::Error as JSError;
use serde::{de, ser};

/// This type represents all possible errors that can occur when serializing or
/// deserializing JS values.
pub struct Error(Box<ErrorImpl>);

impl Error {
    pub(crate) fn new(msg: impl Into<ErrorImpl>) -> Self {
        Error(Box::new(msg.into()))
    }
}

/// Alias for a `Result` with the error type `rquickjs_serde::Error`.
pub type Result<T> = std::result::Result<T, Error>;

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Error({})", self.0)
    }
}

impl error::Error for Error {}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&*self.0, f)
    }
}

impl de::Error for Error {
    fn custom<T: fmt::Display>(msg: T) -> Self {
        Error(Box::new(ErrorImpl::Message(msg.to_string())))
    }
}

impl ser::Error for Error {
    fn custom<T: fmt::Display>(msg: T) -> Self {
        Error(Box::new(ErrorImpl::Message(msg.to_string())))
    }
}

/// The internal representation of an error.
///
/// This enum represents various errors that can occur during JS value serialization or deserialization,
/// including UTF-8 conversion errors, and errors originating from the `rquickjs` library.
#[derive(Debug)]
pub enum ErrorImpl {
    /// A generic error message
    Message(String),
    /// An error originating from the `rquickjs` library.
    Rquickjs(JSError),
}

impl fmt::Display for ErrorImpl {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ErrorImpl::Message(msg) => write!(f, "{msg}"),
            ErrorImpl::Rquickjs(e) => write!(f, "{e}"),
        }
    }
}

impl From<&str> for ErrorImpl {
    fn from(value: &str) -> Self {
        ErrorImpl::Message(value.to_string())
    }
}

impl From<JSError> for ErrorImpl {
    fn from(value: JSError) -> Self {
        ErrorImpl::Rquickjs(value)
    }
}
