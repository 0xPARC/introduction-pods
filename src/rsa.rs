/**
 * This code taken/adapted from github.com/dgulotta/double-blind/src/rsa.rs
 */


use anyhow::anyhow;
use num::BigUint;
use plonky2::{
    iop::{
        target::Target, witness::PartialWitness
    },
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_rsa::gadgets::{
    biguint::{
        CircuitBuilderBigUint, WitnessBigUint
    },
    rsa::pow_65537,
};
use ssh_key::{
    SshSig, Mpint,
    public::{
        KeyData, RsaPublicKey
    },
};
use pod2::backends::plonky2::basetypes::{
    D, F
};

pub(super) const BITS: usize = 27;
pub type BigUintTarget = plonky2_rsa::gadgets::biguint::BigUintTarget<BITS>;

pub(super) const RSA_LIMBS: usize = 4096usize.div_ceil(BITS);


fn mpint_to_biguint(x: &Mpint) -> BigUint {
    BigUint::from_bytes_be(x.as_positive_bytes().unwrap())
}

//#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
#[derive(Clone, Debug)]
pub struct RSATargets {
    pub signature: BigUintTarget,
    pub modulus: BigUintTarget,
    pub padded_data: BigUintTarget
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


/// Builds the RSA part of the circuit.  Returns the targets containing the public
/// key and Double Blind key.
pub fn build_rsa(builder: &mut CircuitBuilder<F, D>) -> RSATargets {
    let signature = builder.add_virtual_biguint_target(RSA_LIMBS);
    let modulus = builder.add_virtual_biguint_target(RSA_LIMBS);
    let computed_padded_data = pow_65537(builder, &signature, &modulus);
    let padded_data = builder.add_virtual_biguint_target(RSA_LIMBS);
    builder.connect_biguint(&padded_data, &computed_padded_data);
    RSATargets { signature, modulus, padded_data }

}

pub fn set_rsa_targets(
    pw: &mut PartialWitness<F>,
    targets: &RSATargets,
    sig: &SshSig,
    padded_data: &Vec<u8>
) -> anyhow::Result<()> {
    let signature = BigUint::from_bytes_be(sig.signature_bytes());
    pw.set_biguint_target(&targets.signature, &signature)?;
    let padded_data_int = BigUint::from_bytes_be(padded_data);
    pw.set_biguint_target(&targets.padded_data, &padded_data_int)?;
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
