use nasl_syntax::NaslValue;

use crate::{FunctionErrorKind, NaslResult};

/// A type that can be converted to a NaslResult.
/// The conversion is fallible to make it possible to convert from other Result
/// types. Most generic types should always succeed with the conversion.
pub trait ToNaslResult {
    /// Perform the conversion
    fn to_nasl_result(self) -> NaslResult;
}

impl ToNaslResult for NaslValue {
    fn to_nasl_result(self) -> NaslResult {
        Ok(self)
    }
}

impl<T: ToNaslResult> ToNaslResult for Option<T> {
    fn to_nasl_result(self) -> NaslResult {
        Ok(match self {
            Some(x) => x.to_nasl_result()?,
            None => NaslValue::Null,
        })
    }
}

impl<T: ToNaslResult, E: Into<FunctionErrorKind>> ToNaslResult for Result<T, E> {
    fn to_nasl_result(self) -> NaslResult {
        self.map_err(|e| e.into()).and_then(|x| x.to_nasl_result())
    }
}

impl ToNaslResult for () {
    fn to_nasl_result(self) -> NaslResult {
        Ok(NaslValue::Null)
    }
}

impl ToNaslResult for String {
    fn to_nasl_result(self) -> NaslResult {
        Ok(NaslValue::String(self))
    }
}

impl ToNaslResult for &str {
    fn to_nasl_result(self) -> NaslResult {
        Ok(NaslValue::String(self.to_owned()))
    }
}

impl ToNaslResult for &[u8] {
    fn to_nasl_result(self) -> NaslResult {
        Ok(NaslValue::Data(self.to_vec()))
    }
}

impl ToNaslResult for Vec<u8> {
    fn to_nasl_result(self) -> NaslResult {
        Ok(NaslValue::Data(self))
    }
}

impl ToNaslResult for Vec<&str> {
    fn to_nasl_result(self) -> NaslResult {
        Ok(NaslValue::Array(
            self.into_iter()
                .map(|s| s.to_nasl_result())
                .collect::<Result<Vec<_>, FunctionErrorKind>>()?,
        ))
    }
}

impl ToNaslResult for Vec<String> {
    fn to_nasl_result(self) -> NaslResult {
        Ok(NaslValue::Array(
            self.into_iter()
                .map(|s| s.to_nasl_result())
                .collect::<Result<Vec<_>, FunctionErrorKind>>()?,
        ))
    }
}

impl ToNaslResult for bool {
    fn to_nasl_result(self) -> NaslResult {
        Ok(NaslValue::Boolean(self))
    }
}

macro_rules! impl_to_nasl_result_for_numeric_type {
    ($ty: ty) => {
        impl ToNaslResult for $ty {
            fn to_nasl_result(self) -> NaslResult {
                Ok(NaslValue::Number(self as i64))
            }
        }
    };
}

impl_to_nasl_result_for_numeric_type!(u8);
impl_to_nasl_result_for_numeric_type!(i32);
impl_to_nasl_result_for_numeric_type!(i64);
impl_to_nasl_result_for_numeric_type!(u32);
impl_to_nasl_result_for_numeric_type!(u64);
impl_to_nasl_result_for_numeric_type!(isize);
impl_to_nasl_result_for_numeric_type!(usize);
