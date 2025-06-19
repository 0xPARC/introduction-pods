// mdlpod.rs
use anyhow::{Context, Result};

use p256::{
    AffinePoint, ProjectivePoint, PublicKey, Scalar,
};
use p256::elliptic_curve::{
    point::AffineCoordinates,   // for `x()`
    PrimeField,                 // for `from_repr`
    Group,                      // for `ProjectivePoint::generator()`
};
use serde_cbor::Value;
use sha2::{Digest, Sha256};
use std::fs::File;

fn manual_verify(pk_sec1: &[u8], sig_r_s: &[u8; 64], msg: &[u8]) -> bool {
    println!("pk_sec1: {:?}", pk_sec1);
    // --------------------------------------------------- curve constants
    let g = ProjectivePoint::generator();          // base point G

    // -------------------------------------------------------- pub-key Q
    let q = PublicKey::from_sec1_bytes(pk_sec1)
        .expect("bad point")
        .to_projective();

    // ------------------------------------------------ signature r ‖ s
    let r = {
        let mut tmp = [0u8; 32];
        tmp.copy_from_slice(&sig_r_s[..32]);
        Scalar::from_repr(tmp.into()).unwrap()
    };
    let s = {
        let mut tmp = [0u8; 32];
        tmp.copy_from_slice(&sig_r_s[32..]);
        Scalar::from_repr(tmp.into()).unwrap()
    };
    if r == Scalar::ZERO || s == Scalar::ZERO {
        return false;
    }

    // ----------------------------------------------------------- hash e

    println!("msg: {:?}", msg);
    println!("digest: {:?}", Sha256::digest(msg));
    let e = {
        let digest = Sha256::digest(msg);
        Scalar::from_repr(digest.into()).unwrap()
    };

    // ----------------------------------------------- classic ECDSA math
    let w  = s.invert().unwrap();   // s⁻¹ mod n
    let u1 = e * w;
    let u2 = r * w;
    let p  = (g * u1) + (q * u2);   // (u1·G + u2·Q)
    if p.is_identity().into() {
        return false;
    }

    // x-coordinate of P, reduced mod n, must equal r
    let x_scalar = Scalar::from_repr(AffinePoint::from(p).x()).unwrap();
    x_scalar == r
}

pub fn verify_mdl() -> Result<()> {
    // ------------------------------------------------------------------
    // 1.  Load decoded.bin and slice out the COSE_Sign1 parts
    // ------------------------------------------------------------------
    println!("Loading decoded.bin");
    let root: Value = serde_cbor::from_reader(File::open("test_keys/mdl/decoded.bin")?)?;
    println!("Loaded decoded.bin");

    let issuer_auth = match &root {
        Value::Map(map) => map
            .iter()
            .find(|(k, _)| matches!(k, Value::Text(t) if t == "issuer_auth"))
            .and_then(|(_, v)| match v {
                Value::Array(arr) => Some(arr),
                _ => None,
            })
            .context("issuer_auth missing / not an array")?,
        _ => anyhow::bail!("Root is not a CBOR map"),
    };

    let protected_bstr = match &issuer_auth[0] {
        Value::Bytes(b) => b,
        _ => anyhow::bail!("bad protected"),
    };
    let payload_bstr = match &issuer_auth[2] {
        Value::Bytes(b) => b,
        _ => anyhow::bail!("bad payload"),
    };
    let sig_r_s = match &issuer_auth[3] {
        Value::Bytes(b) => <&[u8; 64]>::try_from(&b[..]).context("sig length")?,
        _ => anyhow::bail!("bad signature"),
    };

    // Build Sig_structure = ["Signature1", protected, external_aad, payload]
    let sig_structure = Value::Array(vec![
        Value::Text("Signature1".into()),
        Value::Bytes(protected_bstr.clone()),
        Value::Bytes(Vec::new()), // external_aad = b""
        Value::Bytes(payload_bstr.clone()),
    ]);
    let sig_bytes = serde_cbor::to_vec(&sig_structure)?; // canonical CBOR


    // ------------------------------------------------------------------
    // 2.  Extract public key from issuer-cert.pem
    // ------------------------------------------------------------------
    println!("Loading issuer-cert.pem");
    let pem_data = std::fs::read("test_keys/mdl/issuer-cert.pem")?;
    let (_, pem) = x509_parser::pem::parse_x509_pem(&pem_data)?;
    let (_, cert) = x509_parser::parse_x509_certificate(&pem.contents)?;
    let pk_sec1 = cert.public_key().subject_public_key.data.as_ref();

    // let verifying_key = VerifyingKey::from_sec1_bytes(pk_sec1)?;

    // ------------------------------------------------------------------
    // 3.  Verify (SHA-256 is implicit for P-256)
    // ------------------------------------------------------------------

    assert!(manual_verify(pk_sec1, sig_r_s, &sig_bytes));
    println!("✅ COSE_Sign1 signature is VALID");

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mdl_verify() -> anyhow::Result<()> {
        verify_mdl()
    }
}
