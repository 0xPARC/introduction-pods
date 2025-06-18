#![feature(trait_upcasting)]
use std::fmt;

use pod2::middleware::TypedValue;

pub mod ecdsapod;
pub mod ed25519pod;

pub enum PodType {
    Ecdsa = 1001,
    Ed25519 = 1002,
}

impl fmt::Display for PodType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PodType::Ed25519 => write!(f, "Ed25519"),
            PodType::Ecdsa => write!(f, "Ecdsa"),
        }
    }
}
impl From<PodType> for TypedValue {
    fn from(t: PodType) -> Self {
        TypedValue::from(t as i64)
    }
}
