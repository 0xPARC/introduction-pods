/**
 * This code taken/adapted from github.com/dgulotta/double-blind/src/rsa.rs
 */


use std::sync::LazyLock;

use anyhow::anyhow;
use num::{BigUint, Num};
use plonky2::{
    field::types::Field,
    iop::{target::Target, witness::PartialWitness},
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_rsa::gadgets::{
    biguint::{CircuitBuilderBigUint, WitnessBigUint, split_biguint},
    rsa::pow_65537,
};
use ssh_key::{
    PublicKey, SshSig, Mpint,
    public::{KeyData, RsaPublicKey},
};
use pod2::backends::plonky2::basetypes::{D, F};

pub(super) const BITS: usize = 27;
type BigUintTarget = plonky2_rsa::gadgets::biguint::BigUintTarget<BITS>;

pub(super) const RSA_LIMBS: usize = 4096usize.div_ceil(BITS);


static DB_MSG_RSA_STR: &str = "1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff003051300d060960864801650304020305000440bed2662fe0f7b308ad3b5d19ca0d77af4235ce8b0e39a2986440658df91a32e503813121336ac764a10fb6e508d205b5ebaf0a291876385634a86cfea2d688cd";
static DB_MSG_RSA: LazyLock<BigUint> =
    LazyLock::new(|| BigUint::from_str_radix(DB_MSG_RSA_STR, 16).unwrap());


fn mpint_to_biguint(x: &Mpint) -> BigUint {
    BigUint::from_bytes_be(x.as_positive_bytes().unwrap())
}

//#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
// TODO do I care about serialization?
#[derive(Clone, Debug)]
pub struct RSATargets {
    pub signature: BigUintTarget,
    pub modulus: BigUintTarget,
}

impl RSATargets {
    /// Returns the targets containing the public key.
    pub fn public_key_targets(&self) -> Vec<Target> {
        self.modulus.limbs.clone()
    }
    /// Returns the targets containing the signature.
    pub fn signature_targets(&self) -> Vec<Target> {
        self.signature.limbs.clone()
    }
}

fn public_key_modulus(key: &RsaPublicKey) -> BigUint {
    mpint_to_biguint(&key.n)
}

/// Returns the internal representation of the public key.  This function
/// should be consistent with `RSATargets::public_key_targets`.
pub fn rsa_key_target_data(key: &RsaPublicKey) -> Vec<F> {
    let modulus = public_key_modulus(key);
    let digits: Vec<_> = split_biguint::<BITS>(&modulus);
    digits
        .into_iter()
        .map(|d| F::from_canonical_u32(d))
        .collect()
}

pub fn rsa_example_signature() -> SshSig {
    SshSig::from_pem(include_bytes!("../test_keys/id_rsa_helloworld.sig")).unwrap()
}

pub fn rsa_example_public_key() -> PublicKey {
    PublicKey::from_openssh(include_str!("../test_keys/id_rsa.pub")).unwrap()
}

pub fn rsa_example_public_key_2() -> PublicKey {
    PublicKey::from_openssh(include_str!("../test_keys/id_rsa_2.pub")).unwrap()
}

/// Builds the RSA part of the circuit.  Returns the targets containing the public
/// key and Double Blind key.
pub fn build_rsa(builder: &mut CircuitBuilder<F, D>) -> RSATargets {
    let signature = builder.add_virtual_biguint_target(RSA_LIMBS);
    let modulus = builder.add_virtual_biguint_target(RSA_LIMBS);
    let digest = pow_65537(builder, &signature, &modulus);
    let expected = builder.constant_biguint(&DB_MSG_RSA);
    builder.connect_biguint(&digest, &expected);
    RSATargets { signature, modulus }
}

pub fn is_rsa_key_supported(key: &RsaPublicKey) -> bool {
    key.n.as_positive_bytes().is_some_and(|b| b.len() == 512)
        && key.e.as_positive_bytes() == Some(&[1, 0, 1])
}

pub fn set_rsa_targets(
    pw: &mut PartialWitness<F>,
    targets: &RSATargets,
    sig: &SshSig,
) -> anyhow::Result<()> {
    let signature = BigUint::from_bytes_be(sig.signature_bytes());
    pw.set_biguint_target(&targets.signature, &signature)?;
    if let KeyData::Rsa(key) = sig.public_key() {
        let modulus = public_key_modulus(key);
        pw.set_biguint_target(&targets.modulus, &modulus)?;
        if key.e.as_positive_bytes() == Some(&[1, 0, 1]) {
            Ok(())
        } else {
            Err(anyhow!("Exponents other than 65537 are unsupported"))
        }
    } else {
        Err(anyhow!("Not an RSA signature"))
    }
}
