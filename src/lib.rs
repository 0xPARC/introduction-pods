#![feature(trait_upcasting)]
use std::fmt;

use pod2::middleware::TypedValue;

pub mod ecdsapod;

pub enum PodType {
    Ecdsa = 1001,
}

impl fmt::Display for PodType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PodType::Ecdsa => write!(f, "Ecdsa"),
        }
    }
}
impl From<PodType> for TypedValue {
    fn from(t: PodType) -> Self {
        TypedValue::from(t as i64)
    }
}
