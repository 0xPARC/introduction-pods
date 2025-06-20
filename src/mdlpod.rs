//! Implements the MdlPod, a POD that proves that the given `pk` has signed
//! the `msg` with the ES256 signature scheme.
//!
//! This POD is build through two steps:
//! - first it generates a plonky2 proof of correct signature verification
//! - then, verifies the previous proof in a new plonky2 proof, using the
//!   `standard_recursion_config`, padded to match the `RecursiveCircuit<MainPod>`
//!   configuration.

use std::sync::LazyLock;

use base64::{Engine, prelude::BASE64_STANDARD};
use itertools::Itertools;
use num::bigint::BigUint;
use plonky2::{
    field::{types::Field},
    hash::{
        hash_types::{HashOut, HashOutTarget},
        poseidon::PoseidonHash,
    },
    iop::{
        target::Target,
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CircuitData, VerifierOnlyCircuitData},
        config::Hasher,
        proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget},
    },
};
use plonky2_sha256::circuit::{array_to_bits, make_circuits, Sha256Targets};
use plonky2_ecdsa::{
    curve::{
        ecdsa::{ECDSAPublicKey, ECDSASignature},
        p256::P256,
    },
    gadgets::{
        biguint::{BigUintTarget, WitnessBigUint},
        curve::CircuitBuilderCurve,
        ecdsa::{verify_p256_message_circuit, ECDSAPublicKeyTarget, ECDSASignatureTarget},
        nonnative::{CircuitBuilderNonNative, NonNativeTarget},
    },
};
use plonky2_u32::gadgets::arithmetic_u32::U32Target;
use pod2::{
    backends::plonky2::{
        Error, Result,
        basetypes::{C, D, Proof},
        circuits::{
            common::{
                CircuitBuilderPod, Flattenable, StatementArgTarget, StatementTarget, ValueTarget,
            },
            mainpod::CalculateIdGadget,
        },
        deserialize_proof, mainpod,
        mainpod::{calculate_id, get_common_data},
        serialize_proof,
    },
    measure_gates_begin, measure_gates_end,
    middleware::{
        self, AnchoredKey, DynError, F, Hash, KEY_TYPE, Key, NativePredicate, Params, 
        Pod, PodId, RawValue, RecursivePod, SELF, Statement, ToFields, Value,
    },
    timed,
};
use serde::{Deserialize, Serialize};
use crate::PodType;
use plonky2_ecdsa::field::p256_scalar::P256Scalar;
use sha2::{Digest, Sha256};
use serde_cbor;

const KEY_SIGNED_MSG: &str = "signed_msg";
const KEY_P256_PK: &str = "p256_pk";

static P256_VERIFY_DATA: LazyLock<(P256VerifyTarget, CircuitData<F, C, D>)> =
    LazyLock::new(|| build_p256_verify().expect("successful build"));

fn build_p256_verify() -> Result<(P256VerifyTarget, CircuitData<F, C, D>)> {
    let config = CircuitConfig::wide_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let p256_verify_target = P256VerifyTarget::add_targets(&mut builder)?;

    let data = timed!("P256Verify build", builder.build::<C>());
    Ok((p256_verify_target, data))
}

#[derive(Serialize, Deserialize)]
struct Data {
    msg: Vec<u8>,
    pk: ECDSAPublicKey<P256>,
    proof: String,
}


/// Note: this circuit requires the CircuitConfig's standard_ecc_config or
/// wide_ecc_config.
struct P256VerifyTarget {
    sha256_targets: Sha256Targets,
    pk: ECDSAPublicKeyTarget<P256>,
    signature: ECDSASignatureTarget<P256>,
}

impl P256VerifyTarget {
    fn add_targets(builder: &mut CircuitBuilder<F, D>) -> Result<Self> {
        let measure = measure_gates_begin!(builder, "P256VerifyTarget");

        let max_msg_len_bits = 23160;  // 2895 bytes * 8 bits
        let sha256_targets = make_circuits(builder, max_msg_len_bits);
        
        // Pre-compute constants outside the closure
        let zero = builder.zero();
        let one = builder.one();
        
        // Convert the 256-bit digest output to bytes
        let digest_bytes_targets: Vec<Target> = (0..32)
            .map(|i| {
                // Convert 8 bits to a byte
                let mut byte_val = zero;
                for j in 0..8 {
                    let bit_val = builder.select(
                        sha256_targets.digest[i * 8 + j],
                        one,
                        zero
                    );
                    let shift = builder.constant(F::from_canonical_u32(1 << (7 - j)));
                    let shifted = builder.mul(bit_val, shift);
                    byte_val = builder.add(byte_val, shifted);
                }
                byte_val
            })
            .collect();
        // Convert bytes to u32 limbs (8 limbs, 4 bytes each)
        let mut limbs = Vec::new();
        for limb_idx in 0..8 {
            let mut limb = builder.zero();
            for byte_idx in 0..4 {
                // Take bytes from the end first (big-endian)
                let byte_index = 31 - (limb_idx * 4 + byte_idx);
                let byte_target = digest_bytes_targets[byte_index];
                let shift = builder.constant(F::from_canonical_u64(1u64 << (8 * byte_idx)));
                let shifted = builder.mul(byte_target, shift);
                limb = builder.add(limb, shifted);
            }
            limbs.push(limb);
        }
        
        // Create BigUintTarget from u32 limbs
        let msg_big_uint = BigUintTarget {
            limbs: limbs.into_iter().map(|l| U32Target(l)).collect(),
        };
        
        // Create NonNativeTarget from limbs
        let msg = builder.biguint_to_nonnative(&msg_big_uint);
        let pk = ECDSAPublicKeyTarget(builder.add_virtual_affine_point_target::<P256>());
        let r = builder.add_virtual_nonnative_target();
        let s = builder.add_virtual_nonnative_target();
        let sig = ECDSASignatureTarget::<P256> { r, s };

        verify_p256_message_circuit(builder, msg.clone(), sig.clone(), pk.clone());

        // register public inputs
        for l in msg.value.limbs.iter() {
            builder.register_public_input(l.0);
        }
        // register pk as public input
        for l in pk.0.x.value.limbs.iter() {
            builder.register_public_input(l.0);
        }
        for l in pk.0.y.value.limbs.iter() {
            builder.register_public_input(l.0);
        }

        measure_gates_end!(builder, measure);
        Ok(P256VerifyTarget {
            sha256_targets,
            pk,
            signature: sig,
        })
    }

    fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        msg: Vec<u8>,
        pk: ECDSAPublicKey<P256>,
        signature: ECDSASignature<P256>,
    ) -> Result<()> {
        let msg_bits = array_to_bits(&msg);
        for (i, &bit) in msg_bits.iter().enumerate() {
            pw.set_bool_target(self.sha256_targets.message[i], bit)?;
        }
        pw.set_biguint_target(&self.pk.0.x.value, &biguint_from_array(pk.0.x.0))?;
        pw.set_biguint_target(&self.pk.0.y.value, &biguint_from_array(pk.0.y.0))?;
        pw.set_biguint_target(&self.signature.r.value, &biguint_from_array(signature.r.0))?;
        pw.set_biguint_target(&self.signature.s.value, &biguint_from_array(signature.s.0))?;

        Ok(())
    }
}

#[derive(Clone, Debug)]
struct MdlPodVerifyTarget {
    vds_root: HashOutTarget,
    id: HashOutTarget,
    proof: ProofWithPublicInputsTarget<D>,
}

pub struct MdlPodVerifyInput {
    vds_root: Hash,
    id: PodId,
    proof: ProofWithPublicInputs<F, C, D>,
}

impl MdlPodVerifyTarget {
    fn add_targets(builder: &mut CircuitBuilder<F, D>, params: &Params) -> Result<Self> {
        let measure = measure_gates_begin!(builder, "MdlPodVerifyTarget");

        // Verify P256VerifyTarget's proof (with verifier_data hardcoded as constant)
        let (_, circuit_data) = &*P256_VERIFY_DATA;
        let verifier_data_targ = builder.constant_verifier_data(&circuit_data.verifier_only);
        let proof_targ = builder.add_virtual_proof_with_pis(&circuit_data.common);
        builder.verify_proof::<C>(&proof_targ, &verifier_data_targ, &circuit_data.common);

        // calculate id
        let msg = &proof_targ.public_inputs[0..8];
        let pk = &proof_targ.public_inputs[8..24];
        let statements = pub_self_statements_target(builder, params, msg, pk);
        let id = CalculateIdGadget {
            params: params.clone(),
        }
        .eval(builder, &statements);

        // register the public inputs
        let vds_root = builder.add_virtual_hash();
        builder.register_public_inputs(&id.elements);
        builder.register_public_inputs(&vds_root.elements);

        measure_gates_end!(builder, measure);
        Ok(MdlPodVerifyTarget {
            vds_root,
            id,
            proof: proof_targ,
        })
    }

    fn set_targets(&self, pw: &mut PartialWitness<F>, input: &MdlPodVerifyInput) -> Result<()> {
        pw.set_proof_with_pis_target(&self.proof, &input.proof)?;
        pw.set_hash_target(self.id, HashOut::from_vec(input.id.0.0.to_vec()))?;
        pw.set_target_arr(&self.vds_root.elements, &input.vds_root.0)?;

        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct MdlPod {
    params: Params,
    id: PodId,
    msg: Vec<u8>,
    pk: ECDSAPublicKey<P256>,
    proof: Proof,
    vds_root: Hash,
}

impl RecursivePod for MdlPod {
    fn verifier_data(&self) -> VerifierOnlyCircuitData<C, D> {
        let (_, circuit_data) = &*STANDARD_MDL_POD_DATA;
        circuit_data.verifier_data().verifier_only
    }
    fn proof(&self) -> Proof {
        self.proof.clone()
    }
    fn vds_root(&self) -> Hash {
        self.vds_root
    }
    fn deserialize_data(
        params: Params,
        data: serde_json::Value,
        vds_root: Hash,
        id: PodId,
    ) -> Result<Box<dyn RecursivePod>, Box<DynError>> {
        let data: Data = serde_json::from_value(data)?;
        let common = get_common_data(&params)?;
        let proof = deserialize_proof(&common, &data.proof)?;
        Ok(Box::new(Self {
            params,
            id,
            msg: data.msg,
            pk: data.pk,
            proof,
            vds_root,
        }))
    }
}

static STANDARD_MDL_POD_DATA: LazyLock<(MdlPodVerifyTarget, CircuitData<F, C, D>)> =
    LazyLock::new(|| build().expect("successful build"));

fn build() -> Result<(MdlPodVerifyTarget, CircuitData<F, C, D>)> {
    let params = &*pod2::backends::plonky2::DEFAULT_PARAMS;
    let rec_circuit_data = &*pod2::backends::plonky2::STANDARD_REC_MAIN_POD_CIRCUIT_DATA;
    let config = rec_circuit_data.common.config.clone();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let mdl_pod_verify_target = MdlPodVerifyTarget::add_targets(&mut builder, params)?;
    let rec_circuit_data = &*pod2::backends::plonky2::STANDARD_REC_MAIN_POD_CIRCUIT_DATA;
    pod2::backends::plonky2::recursion::pad_circuit(&mut builder, &rec_circuit_data.common);

    let data = timed!("MdlPod build", builder.build::<C>());
    assert_eq!(rec_circuit_data.common, data.common);
    Ok((mdl_pod_verify_target, data))
}

pub fn bytes_to_u64_array(bytes: &[u8; 32]) -> [u64; 4] {
    let mut arr = [0u64; 4];
    for i in 0..4 {
        let mut val = 0u64;
        for j in 0..8 {
            val |= (bytes[i * 8 + j] as u64) << (j * 8);
        }
        arr[i] = val;
    }
    arr
}

/// Convert a 32-byte **big-endian** array into four little-endian u64 limbs
pub fn bytes_to_u64_array_be(bytes: &[u8; 32]) -> [u64; 4] {
    let mut limbs = [0u64; 4];

    for limb_idx in 0..4 {
        let mut limb = 0u64;
        for byte_idx in 0..8 {
            // Take bytes from the *end* of the array first
            let b = bytes[31 - (limb_idx * 8 + byte_idx)];
            limb |= (b as u64) << (8 * byte_idx);
        }
        limbs[limb_idx] = limb;
    }
    limbs
}


/// Extract P-256 signature and message from MDL COSE data
pub fn extract_mdl_signature_data(
    issuer_auth: &[serde_cbor::Value],
) -> Result<(Vec<u8>, ECDSASignature<P256>), Box<DynError>> {
    // Extract protected, payload, and signature from COSE_Sign1 structure
    let protected_bstr = match &issuer_auth[0] {
        serde_cbor::Value::Bytes(b) => b,
        _ => return Err("bad protected".into()),
    };
    let payload_bstr = match &issuer_auth[2] {
        serde_cbor::Value::Bytes(b) => b,
        _ => return Err("bad payload".into()),
    };
    let sig_r_s = match &issuer_auth[3] {
        serde_cbor::Value::Bytes(b) => <&[u8; 64]>::try_from(&b[..])
            .map_err(|_| "signature length must be 64 bytes")?,
        _ => return Err("bad signature".into()),
    };

    // Build Sig_structure = ["Signature1", protected, external_aad, payload]
    let sig_structure = serde_cbor::Value::Array(vec![
        serde_cbor::Value::Text("Signature1".into()),
        serde_cbor::Value::Bytes(protected_bstr.clone()),
        serde_cbor::Value::Bytes(Vec::new()), // external_aad = b""
        serde_cbor::Value::Bytes(payload_bstr.clone()),
    ]);
    let msg_bytes = serde_cbor::to_vec(&sig_structure)
        .map_err(|e| format!("Failed to serialize sig_structure: {}", e))?;


    // Extract r and s from signature
    let r = P256Scalar(bytes_to_u64_array_be(&sig_r_s[..32].try_into().unwrap()));
    let s = P256Scalar(bytes_to_u64_array_be(&sig_r_s[32..].try_into().unwrap()));

    let signature = ECDSASignature { r, s };
    
    Ok((msg_bytes, signature))
}


impl MdlPod {
    fn _prove(
        params: &Params,
        vds_root: Hash,
        msg: Vec<u8>,
        pk: ECDSAPublicKey<P256>,
        signature: ECDSASignature<P256>,
    ) -> Result<MdlPod> {


        let (p256_verify_target, p256_circuit_data) = &*P256_VERIFY_DATA;
        let mut pw = PartialWitness::<F>::new();
        p256_verify_target.set_targets(&mut pw, msg.clone(), pk, signature)?;

        let p256_verify_proof = timed!(
            "prove the p256 signature verification with SHA256 (P256VerifyTarget)",
            p256_circuit_data.prove(pw)?
        );

        // sanity check
        p256_circuit_data
            .verifier_data()
            .verify(p256_verify_proof.clone())?;

        // 2. verify the p256_verify proof in a MdlPodVerifyTarget circuit
        let (mdl_pod_target, circuit_data) = &*STANDARD_MDL_POD_DATA;

        // For ID calculation, we still need the hash
        let digest = Sha256::digest(&msg);
        let digest_bytes: [u8; 32] = digest.into();
        let msg_scalar = P256Scalar(bytes_to_u64_array_be(&digest_bytes));
        
        let statements = pub_self_statements(msg_scalar, pk)
            .into_iter()
            .map(mainpod::Statement::from)
            .collect_vec();
        let id: PodId = PodId(calculate_id(&statements, params));


        // set targets
        let input = MdlPodVerifyInput {
            vds_root,
            id,
            proof: p256_verify_proof,
        };
        let mut pw = PartialWitness::<F>::new();
        mdl_pod_target.set_targets(&mut pw, &input)?;
        let proof_with_pis = timed!(
            "prove the p256-verification proof verification (MdlPod proof)",
            circuit_data.prove(pw)?
        );

        // sanity check
        circuit_data
            .verifier_data()
            .verify(proof_with_pis.clone())?;

        Ok(MdlPod {
            params: params.clone(),
            id,
            msg,
            pk,
            proof: proof_with_pis.proof,
            vds_root,
        })
    }

    #[allow(clippy::new_ret_no_self)]
    pub fn new(
        params: &Params,
        vds_root: Hash,
        msg: Vec<u8>,
        pk: ECDSAPublicKey<P256>,
        signature: ECDSASignature<P256>,
    ) -> Result<Box<dyn RecursivePod>, Box<DynError>> {
        Ok(Self::_prove(params, vds_root, msg, pk, signature).map(Box::new)?)
    }

    /// Create MdlPod from MDL issuer_auth array
    pub fn from_issuer_auth(
        params: &Params,
        vds_root: Hash,
        issuer_auth: &[serde_cbor::Value],
        pk: ECDSAPublicKey<P256>,
    ) -> Result<Box<dyn RecursivePod>, Box<DynError>> {
        let (msg, signature) = extract_mdl_signature_data(issuer_auth)?;
        Self::new(params, vds_root, msg, pk, signature)
    }

    fn _verify(&self) -> Result<()> {
        let digest = Sha256::digest(&self.msg);
        let digest_bytes: [u8; 32] = digest.into();
        let msg_scalar = P256Scalar(bytes_to_u64_array_be(&digest_bytes));

        let statements = pub_self_statements(msg_scalar, self.pk)
            .into_iter()
            .map(mainpod::Statement::from)
            .collect_vec();
        let id: PodId = PodId(calculate_id(&statements, &self.params));
        if id != self.id {
            return Err(Error::id_not_equal(self.id, id));
        }

        let (_, circuit_data) = &*STANDARD_MDL_POD_DATA;

        let public_inputs = id
            .to_fields(&self.params)
            .iter()
            .chain(self.vds_root().0.iter())
            .cloned()
            .collect_vec();

        circuit_data
            .verify(ProofWithPublicInputs {
                proof: self.proof.clone(),
                public_inputs,
            })
            .map_err(|e| Error::custom(format!("MdlPod proof verification failure: {:?}", e)))
    }
}

impl Pod for MdlPod {
    fn params(&self) -> &Params {
        &self.params
    }
    fn verify(&self) -> Result<(), Box<DynError>> {
        Ok(self._verify().map_err(Box::new)?)
    }

    fn id(&self) -> PodId {
        self.id
    }

    fn pub_self_statements(&self) -> Vec<middleware::Statement> {
        let digest = Sha256::digest(&self.msg);
        let digest_bytes: [u8; 32] = digest.into();
        let msg_scalar = P256Scalar(bytes_to_u64_array_be(&digest_bytes));
        pub_self_statements(msg_scalar, self.pk)
    }

    fn pod_type(&self) -> (usize, &'static str) {
        (PodType::Mdl as usize, "Mdl")
    }


    fn serialize_data(&self) -> serde_json::Value {
        serde_json::to_value(Data {
            proof: serialize_proof(&self.proof),
            msg: self.msg.clone(),
            pk: self.pk.clone(),
        })
        .expect("serialization to json")
    }
}

fn type_statement() -> Statement {
    Statement::equal(
        AnchoredKey::from((SELF, KEY_TYPE)),
        Value::from(PodType::Mdl),
    )
}

fn pub_self_statements_target(
    builder: &mut CircuitBuilder<F, D>,
    params: &Params,
    msg: &[Target],
    pk: &[Target],
) -> Vec<StatementTarget> {
    let st_type = StatementTarget::from_flattened(
        params,
        &builder.constants(&type_statement().to_fields(params)),
    );

    let ak_podid = builder.constant_value(RawValue::from(SELF.0));

    let msg_hash = builder.hash_n_to_hash_no_pad::<PoseidonHash>(msg.to_vec());
    let ak_key = builder.constant_value(Key::from(KEY_SIGNED_MSG).raw());
    let ak_msg = StatementArgTarget::anchored_key(builder, &ak_podid, &ak_key);
    let value = StatementArgTarget::literal(builder, &ValueTarget::from_slice(&msg_hash.elements));
    let st_msg =
        StatementTarget::new_native(builder, params, NativePredicate::Equal, &[ak_msg, value]);

    let pk_hash = builder.hash_n_to_hash_no_pad::<PoseidonHash>(pk.to_vec());
    let ak_key = builder.constant_value(Key::from(KEY_P256_PK).raw());
    let ak_pk = StatementArgTarget::anchored_key(builder, &ak_podid, &ak_key);
    let value = StatementArgTarget::literal(builder, &ValueTarget::from_slice(&pk_hash.elements));
    let st_pk =
        StatementTarget::new_native(builder, params, NativePredicate::Equal, &[ak_pk, value]);

    vec![st_type, st_msg, st_pk]
}

// compatible with the same method in-circuit (pub_self_statements_target)
fn pub_self_statements(
    msg: P256Scalar,
    pk: ECDSAPublicKey<P256>,
) -> Vec<middleware::Statement> {
    let st_type = type_statement();

    // hash the msg as in-circuit
    let msg_limbs = p256_field_to_limbs(msg.0);
    let msg_hash = PoseidonHash::hash_no_pad(&msg_limbs);

    let st_msg = Statement::equal(
        AnchoredKey::from((SELF, KEY_SIGNED_MSG)),
        Value::from(RawValue(msg_hash.elements)),
    );

    // hash the pk as in-circuit
    let pk_x_limbs = p256_field_to_limbs(pk.0.x.0);
    let pk_y_limbs = p256_field_to_limbs(pk.0.y.0);
    let pk_hash = PoseidonHash::hash_no_pad(&[pk_x_limbs, pk_y_limbs].concat());

    let st_pk = Statement::equal(
        AnchoredKey::from((SELF, KEY_P256_PK)),
        Value::from(RawValue(pk_hash.elements)),
    );

    vec![st_type, st_msg, st_pk]
}

fn p256_field_to_limbs(v: [u64; 4]) -> Vec<F> {
    let max_num_limbs = 8;
    let v_biguint = biguint_from_array(std::array::from_fn(|i| v[i]));
    let mut limbs = v_biguint.to_u32_digits();
    assert!(max_num_limbs >= limbs.len());
    limbs.resize(max_num_limbs, 0);
    let limbs_f: Vec<F> = limbs.iter().map(|l| F::from_canonical_u32(*l)).collect();
    limbs_f
}

fn biguint_from_array(arr: [u64; 4]) -> BigUint {
    BigUint::from_slice(&[
        arr[0] as u32,
        (arr[0] >> 32) as u32,
        arr[1] as u32,
        (arr[1] >> 32) as u32,
        arr[2] as u32,
        (arr[2] >> 32) as u32,
        arr[3] as u32,
        (arr[3] >> 32) as u32,
    ])
}

#[cfg(test)]
pub mod tests {
    use std::any::Any;
    use std::fs::File;

    use plonky2::iop::target::BoolTarget;
    use plonky2_ecdsa::curve::{
        curve_types::AffinePoint,
        ecdsa::ECDSAPublicKey,
        p256::P256,
    };
    use plonky2_ecdsa::field::p256_base::P256Base;
    use p256::PublicKey;
    use p256::elliptic_curve::sec1::ToEncodedPoint;
    use plonky2_sha256::circuit::array_to_bits;
    use pod2::middleware::VDSet;
    use pod2::{self, frontend::MainPodBuilder, op};
    use anyhow::Context;

    use super::*;

    fn extract_pk_from_cert(cert_path: &str) -> Result<ECDSAPublicKey<P256>, Box<DynError>> {
        let pem_data = std::fs::read(cert_path)?;
        let (_, pem) = x509_parser::pem::parse_x509_pem(&pem_data)
            .map_err(|e| format!("Failed to parse PEM: {:?}", e))?;
        let (_, cert) = x509_parser::parse_x509_certificate(&pem.contents)
            .map_err(|e| format!("Failed to parse certificate: {:?}", e))?;
        let pk_sec1 = cert.public_key().subject_public_key.data.as_ref();
        
        // Parse SEC1 encoded public key
        let pk = PublicKey::from_sec1_bytes(pk_sec1)
            .map_err(|e| format!("Failed to parse public key: {}", e))?;
        
        let enc = pk.to_encoded_point(false);

        let x_slice = enc.x().expect("x coordinate missing");
        let y_slice = enc.y().expect("y coordinate missing");
        let mut x_arr = [0u8; 32];
        x_arr.copy_from_slice(x_slice);   
        let mut y_arr = [0u8; 32];
        y_arr.copy_from_slice(y_slice);
    

        let x = bytes_to_u64_array_be(&x_arr);
        let y = bytes_to_u64_array_be(&y_arr);
        
        Ok(ECDSAPublicKey(AffinePoint {
            x: P256Base(x),
            y: P256Base(y),
            zero: false,
        }))
    }

    #[test]
    fn test_sha256_circuit() -> Result<(), Box<DynError>> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let msg = [132, 106, 83, 105, 103, 110, 97, 116, 117, 114, 101, 49, 67, 161, 1, 38, 64, 89, 11, 59, 216, 24, 89, 11, 54, 166, 103, 118, 101, 114, 115, 105, 111, 110, 99, 49, 46, 48, 111, 100, 105, 103, 101, 115, 116, 65, 108, 103, 111, 114, 105, 116, 104, 109, 103, 83, 72, 65, 45, 50, 53, 54, 108, 118, 97, 108, 117, 101, 68, 105, 103, 101, 115, 116, 115, 162, 113, 111, 114, 103, 46, 105, 115, 111, 46, 49, 56, 48, 49, 51, 46, 53, 46, 49, 184, 37, 26, 0, 29, 90, 114, 88, 32, 0, 23, 37, 162, 181, 131, 222, 171, 211, 23, 65, 85, 142, 70, 53, 49, 162, 57, 178, 226, 189, 22, 158, 8, 172, 30, 58, 214, 172, 211, 63, 92, 26, 5, 51, 186, 144, 88, 32, 79, 33, 61, 17, 144, 2, 164, 206, 42, 162, 44, 93, 104, 206, 187, 233, 138, 81, 28, 94, 26, 112, 124, 95, 199, 6, 228, 190, 121, 138, 155, 148, 26, 9, 70, 177, 129, 88, 32, 168, 151, 237, 146, 99, 229, 5, 234, 151, 165, 1, 85, 7, 180, 190, 160, 121, 72, 126, 111, 9, 196, 55, 179, 7, 87, 236, 61, 82, 169, 230, 107, 26, 11, 59, 27, 255, 88, 32, 117, 247, 169, 196, 28, 191, 167, 95, 196, 64, 220, 230, 155, 67, 148, 148, 142, 174, 117, 123, 207, 65, 89, 88, 95, 90, 254, 96, 69, 202, 92, 19, 26, 16, 141, 148, 203, 88, 32, 26, 213, 99, 181, 216, 243, 106, 124, 137, 60, 194, 4, 31, 76, 253, 171, 16, 53, 252, 140, 145, 145, 133, 209, 245, 110, 76, 27, 98, 246, 6, 129, 26, 18, 76, 19, 4, 88, 32, 235, 206, 216, 83, 13, 46, 4, 70, 126, 176, 2, 235, 220, 52, 180, 168, 237, 35, 186, 125, 201, 40, 202, 176, 90, 93, 198, 187, 100, 51, 155, 117, 26, 31, 37, 41, 180, 88, 32, 206, 9, 179, 23, 18, 221, 168, 15, 211, 52, 82, 53, 189, 24, 187, 138, 194, 198, 132, 84, 215, 212, 127, 9, 120, 226, 155, 252, 186, 6, 41, 152, 26, 32, 190, 247, 249, 88, 32, 184, 39, 8, 231, 34, 192, 73, 200, 187, 145, 248, 117, 32, 173, 67, 214, 76, 115, 136, 63, 230, 240, 14, 245, 97, 171, 199, 78, 189, 148, 227, 9, 26, 32, 245, 148, 173, 88, 32, 172, 204, 194, 244, 203, 52, 178, 19, 135, 138, 142, 165, 165, 27, 212, 249, 102, 29, 209, 42, 206, 152, 66, 103, 90, 4, 191, 58, 103, 167, 227, 102, 26, 36, 2, 101, 16, 88, 32, 212, 84, 117, 192, 25, 251, 162, 124, 233, 228, 85, 72, 205, 242, 231, 113, 55, 42, 63, 170, 157, 225, 38, 164, 180, 60, 42, 14, 93, 100, 128, 143, 26, 37, 19, 24, 221, 88, 32, 225, 171, 153, 134, 121, 65, 185, 166, 83, 200, 112, 35, 154, 119, 52, 131, 201, 198, 33, 228, 134, 225, 132, 123, 169, 7, 249, 51, 97, 191, 3, 164, 26, 39, 227, 109, 167, 88, 32, 174, 150, 58, 182, 132, 43, 25, 157, 167, 55, 130, 155, 11, 66, 127, 243, 162, 241, 64, 213, 185, 158, 236, 122, 236, 37, 157, 162, 73, 85, 67, 1, 26, 39, 246, 69, 67, 88, 32, 196, 91, 141, 230, 214, 186, 89, 204, 153, 136, 24, 135, 72, 36, 4, 11, 138, 245, 63, 118, 24, 119, 95, 42, 173, 177, 183, 143, 155, 160, 13, 129, 26, 42, 132, 127, 127, 88, 32, 251, 82, 151, 230, 221, 106, 220, 216, 186, 15, 22, 153, 253, 177, 69, 136, 79, 114, 244, 10, 79, 9, 183, 134, 145, 112, 16, 164, 70, 52, 50, 149, 26, 55, 198, 235, 212, 88, 32, 93, 191, 141, 69, 76, 113, 207, 38, 205, 160, 243, 220, 131, 12, 203, 140, 167, 33, 3, 124, 245, 25, 38, 207, 82, 17, 69, 138, 77, 60, 24, 97, 26, 60, 7, 70, 206, 88, 32, 50, 69, 63, 130, 245, 185, 21, 89, 253, 239, 134, 109, 44, 89, 100, 11, 69, 13, 125, 195, 23, 42, 122, 86, 50, 202, 227, 235, 225, 92, 123, 139, 26, 60, 59, 125, 23, 88, 32, 189, 69, 36, 135, 113, 16, 146, 125, 252, 88, 72, 22, 192, 213, 7, 173, 156, 3, 103, 152, 139, 1, 199, 199, 236, 213, 9, 1, 166, 147, 121, 208, 26, 64, 139, 72, 16, 88, 32, 191, 23, 215, 183, 15, 163, 46, 36, 212, 2, 69, 162, 188, 122, 56, 124, 135, 69, 156, 79, 0, 216, 198, 223, 90, 170, 59, 44, 38, 7, 30, 213, 26, 72, 141, 193, 46, 88, 32, 149, 235, 216, 215, 68, 204, 134, 76, 86, 60, 167, 72, 232, 226, 3, 223, 19, 229, 137, 19, 104, 105, 117, 18, 249, 243, 171, 61, 75, 160, 220, 33, 26, 80, 179, 160, 152, 88, 32, 22, 106, 42, 179, 74, 192, 12, 8, 222, 1, 134, 223, 19, 0, 134, 109, 145, 12, 38, 133, 206, 19, 120, 137, 247, 131, 238, 166, 38, 232, 152, 218, 26, 84, 2, 61, 60, 88, 32, 163, 235, 203, 202, 189, 191, 219, 33, 114, 74, 230, 18, 5, 56, 138, 6, 31, 79, 77, 160, 180, 6, 253, 213, 141, 244, 251, 143, 19, 203, 127, 42, 26, 88, 131, 199, 83, 88, 32, 211, 60, 87, 185, 164, 108, 175, 29, 145, 33, 190, 195, 39, 33, 86, 215, 89, 83, 33, 43, 144, 43, 98, 142, 197, 180, 89, 245, 55, 27, 159, 50, 26, 91, 17, 203, 23, 88, 32, 194, 27, 93, 207, 130, 141, 223, 251, 131, 1, 150, 81, 117, 223, 205, 238, 238, 145, 50, 67, 83, 56, 54, 73, 66, 239, 27, 122, 157, 243, 215, 141, 26, 98, 17, 110, 140, 88, 32, 140, 60, 196, 229, 113, 72, 101, 197, 5, 86, 207, 139, 46, 60, 25, 58, 42, 247, 55, 101, 83, 56, 171, 108, 160, 100, 30, 116, 156, 80, 127, 68, 26, 101, 13, 47, 218, 88, 32, 149, 142, 243, 3, 14, 58, 171, 158, 225, 23, 110, 213, 201, 131, 238, 219, 189, 36, 107, 179, 71, 138, 140, 129, 6, 68, 63, 109, 198, 247, 88, 145, 26, 102, 183, 189, 149, 88, 32, 77, 186, 200, 252, 159, 18, 48, 202, 90, 180, 246, 80, 50, 246, 2, 203, 98, 57, 24, 247, 246, 105, 248, 35, 242, 107, 97, 100, 24, 107, 82, 135, 26, 104, 72, 31, 153, 88, 32, 40, 137, 176, 125, 248, 196, 103, 229, 48, 118, 15, 46, 51, 41, 222, 89, 118, 81, 224, 254, 184, 36, 120, 59, 217, 219, 214, 200, 200, 134, 187, 173, 26, 104, 243, 40, 182, 88, 32, 83, 200, 172, 130, 180, 107, 35, 21, 252, 3, 185, 100, 89, 227, 32, 109, 206, 220, 97, 133, 236, 141, 199, 115, 134, 197, 23, 216, 176, 170, 221, 101, 26, 109, 131, 155, 196, 88, 32, 111, 110, 103, 60, 59, 210, 78, 128, 89, 9, 80, 221, 57, 175, 165, 32, 58, 131, 72, 222, 190, 48, 225, 149, 42, 233, 183, 71, 124, 44, 96, 157, 26, 110, 39, 161, 94, 88, 32, 122, 165, 97, 6, 40, 155, 139, 197, 45, 230, 240, 88, 74, 159, 37, 121, 164, 21, 45, 133, 192, 15, 86, 3, 148, 222, 113, 230, 161, 243, 136, 247, 26, 116, 214, 212, 97, 88, 32, 41, 64, 139, 151, 160, 171, 112, 67, 69, 142, 163, 249, 74, 200, 152, 33, 141, 188, 98, 144, 60, 244, 97, 31, 139, 7, 236, 109, 251, 209, 168, 233, 26, 117, 56, 194, 106, 88, 32, 145, 22, 121, 126, 152, 254, 56, 247, 12, 33, 54, 181, 130, 112, 221, 14, 29, 188, 7, 97, 231, 246, 71, 237, 43, 70, 61, 122, 118, 125, 224, 84, 26, 117, 176, 165, 136, 88, 32, 172, 253, 147, 205, 134, 219, 168, 156, 85, 29, 4, 74, 99, 196, 60, 153, 27, 197, 246, 142, 173, 188, 173, 129, 29, 199, 15, 209, 61, 80, 214, 249, 26, 122, 115, 88, 180, 88, 32, 120, 180, 131, 35, 206, 217, 212, 183, 42, 124, 233, 30, 221, 222, 214, 15, 56, 75, 11, 143, 199, 70, 235, 8, 161, 127, 251, 171, 42, 22, 165, 48, 26, 125, 66, 8, 38, 88, 32, 245, 115, 174, 229, 40, 175, 104, 165, 56, 127, 215, 139, 91, 14, 121, 104, 249, 159, 226, 7, 103, 82, 51, 166, 238, 86, 28, 226, 190, 133, 153, 49, 26, 126, 184, 21, 149, 88, 32, 21, 137, 175, 237, 34, 93, 254, 68, 140, 40, 0, 246, 94, 17, 224, 31, 182, 92, 158, 14, 212, 3, 62, 228, 185, 120, 102, 226, 253, 107, 234, 44, 26, 127, 211, 18, 34, 88, 32, 159, 27, 163, 39, 242, 219, 92, 132, 147, 43, 200, 138, 14, 151, 167, 248, 195, 198, 184, 71, 99, 162, 139, 26, 145, 118, 157, 223, 26, 170, 109, 104, 119, 111, 114, 103, 46, 105, 115, 111, 46, 49, 56, 48, 49, 51, 46, 53, 46, 49, 46, 97, 97, 109, 118, 97, 184, 28, 26, 1, 217, 132, 206, 88, 32, 205, 124, 69, 171, 211, 108, 76, 173, 200, 214, 182, 222, 39, 167, 226, 168, 23, 41, 114, 35, 236, 95, 202, 173, 199, 234, 76, 84, 35, 48, 58, 240, 26, 8, 255, 11, 195, 88, 32, 62, 191, 17, 238, 143, 108, 126, 7, 214, 152, 107, 146, 40, 207, 238, 1, 97, 202, 43, 229, 24, 35, 227, 3, 158, 221, 10, 152, 233, 87, 167, 47, 26, 10, 248, 212, 141, 88, 32, 172, 43, 175, 195, 57, 138, 245, 28, 177, 125, 39, 152, 153, 227, 90, 126, 108, 143, 169, 140, 238, 210, 177, 51, 253, 241, 34, 206, 64, 108, 91, 19, 26, 11, 223, 37, 249, 88, 32, 251, 111, 29, 129, 23, 135, 255, 253, 26, 109, 203, 19, 183, 231, 108, 248, 210, 97, 82, 7, 3, 219, 165, 145, 31, 83, 96, 30, 205, 82, 202, 32, 26, 13, 103, 170, 130, 88, 32, 152, 223, 43, 248, 47, 153, 240, 56, 128, 176, 118, 203, 235, 70, 7, 174, 123, 149, 166, 228, 167, 12, 65, 253, 143, 241, 237, 251, 93, 153, 224, 219, 26, 15, 46, 96, 115, 88, 32, 245, 107, 239, 71, 157, 65, 18, 213, 233, 166, 88, 242, 154, 98, 67, 148, 153, 94, 23, 8, 127, 4, 86, 221, 240, 236, 198, 250, 20, 175, 146, 185, 26, 22, 12, 92, 86, 88, 32, 69, 165, 231, 235, 43, 28, 100, 27, 168, 205, 146, 52, 254, 171, 11, 107, 3, 100, 80, 3, 75, 105, 12, 241, 95, 66, 148, 232, 207, 163, 96, 67, 26, 30, 60, 153, 139, 88, 32, 238, 152, 224, 55, 11, 22, 78, 208, 45, 15, 38, 162, 140, 186, 98, 42, 65, 73, 97, 82, 85, 115, 44, 135, 50, 77, 249, 227, 182, 143, 243, 148, 26, 39, 163, 205, 187, 88, 32, 195, 3, 138, 214, 14, 70, 62, 117, 94, 207, 95, 203, 221, 72, 204, 12, 174, 202, 107, 249, 194, 70, 45, 100, 24, 87, 239, 217, 189, 141, 19, 18, 26, 40, 5, 57, 184, 88, 32, 110, 167, 197, 32, 222, 164, 154, 54, 161, 28, 153, 131, 63, 236, 155, 149, 153, 155, 170, 9, 109, 57, 48, 62, 41, 131, 167, 219, 65, 8, 95, 205, 26, 43, 187, 39, 172, 88, 32, 37, 71, 227, 27, 232, 191, 254, 249, 26, 98, 76, 255, 183, 147, 110, 20, 219, 77, 208, 170, 47, 215, 68, 138, 130, 116, 108, 230, 219, 157, 115, 78, 26, 45, 3, 244, 3, 88, 32, 201, 49, 168, 66, 235, 108, 13, 230, 34, 141, 29, 142, 234, 247, 198, 255, 42, 42, 118, 199, 155, 188, 218, 5, 85, 212, 241, 106, 168, 160, 233, 24, 26, 51, 164, 43, 38, 88, 32, 80, 50, 96, 61, 8, 227, 179, 14, 204, 131, 186, 31, 66, 0, 245, 239, 220, 241, 145, 236, 177, 244, 138, 34, 242, 221, 52, 41, 186, 4, 189, 28, 26, 54, 237, 213, 90, 88, 32, 77, 157, 208, 219, 24, 133, 150, 123, 181, 59, 102, 215, 176, 165, 230, 145, 111, 144, 172, 41, 83, 195, 148, 123, 88, 116, 251, 61, 10, 105, 216, 9, 26, 56, 203, 42, 67, 88, 32, 230, 187, 113, 27, 121, 122, 126, 31, 71, 210, 174, 124, 110, 171, 42, 0, 177, 105, 120, 223, 28, 255, 184, 242, 227, 201, 42, 50, 188, 234, 214, 197, 26, 58, 230, 34, 31, 88, 32, 252, 59, 14, 92, 242, 245, 53, 163, 121, 34, 114, 195, 6, 78, 209, 40, 94, 211, 232, 218, 4, 117, 53, 218, 155, 254, 194, 43, 52, 223, 217, 30, 26, 77, 11, 202, 209, 88, 32, 5, 48, 99, 78, 125, 216, 185, 121, 78, 59, 147, 217, 187, 83, 101, 86, 190, 198, 227, 64, 136, 223, 139, 249, 17, 88, 47, 44, 73, 183, 10, 72, 26, 77, 28, 37, 189, 88, 32, 145, 254, 192, 168, 89, 203, 41, 82, 194, 12, 110, 0, 195, 219, 78, 178, 51, 123, 185, 17, 131, 56, 169, 78, 122, 81, 219, 117, 100, 224, 118, 166, 26, 78, 188, 33, 204, 88, 32, 111, 200, 190, 208, 27, 141, 77, 95, 148, 89, 212, 145, 75, 210, 66, 235, 87, 112, 50, 50, 140, 158, 126, 36, 86, 225, 34, 22, 211, 208, 67, 217, 26, 83, 126, 41, 225, 88, 32, 203, 35, 64, 159, 67, 85, 221, 255, 164, 241, 61, 162, 137, 179, 145, 81, 11, 18, 15, 67, 190, 188, 46, 142, 121, 120, 214, 25, 166, 95, 99, 182, 26, 85, 97, 151, 192, 88, 32, 83, 62, 160, 118, 35, 226, 229, 28, 194, 83, 83, 109, 127, 149, 48, 159, 22, 57, 42, 223, 214, 111, 43, 147, 252, 241, 65, 78, 69, 50, 85, 227, 26, 93, 29, 158, 115, 88, 32, 176, 76, 92, 214, 10, 181, 179, 194, 15, 83, 192, 166, 132, 181, 157, 240, 11, 169, 193, 145, 156, 240, 142, 190, 235, 175, 238, 232, 166, 24, 178, 248, 26, 112, 52, 183, 253, 88, 32, 136, 241, 71, 66, 180, 80, 168, 44, 148, 135, 113, 158, 55, 167, 48, 4, 215, 155, 30, 173, 184, 53, 58, 77, 44, 13, 242, 37, 0, 92, 10, 217, 26, 113, 49, 205, 160, 88, 32, 22, 227, 253, 244, 146, 108, 191, 68, 240, 184, 138, 179, 136, 3, 169, 42, 210, 235, 218, 98, 14, 209, 220, 65, 55, 37, 3, 141, 5, 53, 158, 135, 26, 115, 14, 74, 87, 88, 32, 225, 82, 215, 38, 25, 180, 50, 89, 157, 193, 251, 72, 100, 40, 79, 176, 225, 45, 76, 205, 126, 163, 86, 244, 67, 174, 219, 6, 188, 224, 58, 204, 26, 118, 245, 25, 197, 88, 32, 141, 10, 92, 157, 110, 227, 137, 6, 116, 204, 111, 248, 123, 78, 154, 1, 175, 198, 235, 94, 26, 37, 143, 65, 168, 237, 165, 94, 20, 96, 56, 255, 26, 121, 213, 188, 92, 88, 32, 100, 51, 157, 121, 59, 247, 130, 233, 125, 174, 146, 190, 9, 123, 81, 232, 225, 166, 232, 202, 127, 45, 95, 245, 185, 154, 63, 110, 185, 86, 93, 53, 26, 127, 125, 179, 36, 88, 32, 158, 117, 112, 157, 43, 11, 91, 15, 36, 201, 238, 106, 111, 66, 170, 96, 20, 59, 60, 10, 63, 197, 73, 20, 156, 105, 110, 114, 72, 125, 6, 123, 109, 100, 101, 118, 105, 99, 101, 75, 101, 121, 73, 110, 102, 111, 161, 105, 100, 101, 118, 105, 99, 101, 75, 101, 121, 164, 1, 2, 32, 1, 33, 88, 32, 89, 252, 92, 128, 6, 172, 82, 163, 148, 121, 193, 170, 186, 203, 189, 29, 86, 252, 185, 143, 238, 170, 24, 35, 52, 196, 91, 58, 118, 9, 2, 158, 34, 88, 32, 63, 80, 30, 94, 32, 131, 12, 112, 181, 162, 255, 58, 6, 144, 162, 46, 151, 130, 187, 44, 26, 118, 254, 121, 137, 82, 218, 236, 89, 158, 221, 77, 103, 100, 111, 99, 84, 121, 112, 101, 117, 111, 114, 103, 46, 105, 115, 111, 46, 49, 56, 48, 49, 51, 46, 53, 46, 49, 46, 109, 68, 76, 108, 118, 97, 108, 105, 100, 105, 116, 121, 73, 110, 102, 111, 163, 102, 115, 105, 103, 110, 101, 100, 192, 116, 50, 48, 50, 51, 45, 49, 49, 45, 48, 55, 84, 49, 53, 58, 52, 49, 58, 48, 54, 90, 105, 118, 97, 108, 105, 100, 70, 114, 111, 109, 192, 116, 50, 48, 50, 51, 45, 49, 49, 45, 48, 55, 84, 49, 53, 58, 52, 49, 58, 48, 54, 90, 106, 118, 97, 108, 105, 100, 85, 110, 116, 105, 108, 192, 116, 50, 48, 50, 51, 45, 49, 49, 45, 48, 55, 84, 49, 53, 58, 52, 49, 58, 48, 54, 90];
        let digest = [47, 138, 26, 108, 5, 180, 111, 106, 123, 186, 17, 106, 186, 192, 111, 10, 12, 214, 143, 213, 119, 124, 104, 151, 8, 130, 110, 237, 45, 84, 87, 192];
        let msg_len_in_bits = (msg.len() * 8) as u64;
    
        // Create SHA256 circuit using your make_circuits function
        let sha256_targets = make_circuits(&mut builder, msg_len_in_bits);
        
        // Create expected digest targets
        let expected_digest_targets: Vec<BoolTarget> = (0..256)
            .map(|_| builder.add_virtual_bool_target_safe())
            .collect();
        
        // Add constraints to ensure computed digest equals expected digest
        for i in 0..256 {
            builder.connect(
                sha256_targets.digest[i].target,
                expected_digest_targets[i].target
            );
        }
        
        // Build the circuit
        let data = builder.build::<C>();
        
        // Create witness
        let mut pw = PartialWitness::new();
        
        // Convert message bytes to bits and set as witness
        let msg_bits = array_to_bits(&msg);
        for (i, &bit) in msg_bits.iter().enumerate() {
            if i < sha256_targets.message.len() {
                pw.set_bool_target(sha256_targets.message[i], bit)?;
            }
        }
        
        // Convert expected digest bytes to bits and set as witness
        let expected_digest_bits = array_to_bits(&digest);
        for (i, &bit) in expected_digest_bits.iter().enumerate() {
            pw.set_bool_target(expected_digest_targets[i], bit)?;
        }
        
        // Generate proof
        let proof = data.prove(pw)?;
        
        // Verify proof
        data.verify(proof)?;
        
        Ok(())
    }

    #[test]
    fn test_mdl_pod_verify() -> Result<(), Box<DynError>> {
        // Load the MDL data
        let root: serde_cbor::Value = serde_cbor::from_reader(File::open("test_keys/mdl/decoded.bin")?)?;
        
        let issuer_auth = match &root {
            serde_cbor::Value::Map(map) => map
                .iter()
                .find(|(k, _)| matches!(k, serde_cbor::Value::Text(t) if t == "issuer_auth"))
                .and_then(|(_, v)| match v {
                    serde_cbor::Value::Array(arr) => Some(arr),
                    _ => None,
                })
                .context("issuer_auth missing / not an array")?,
            _ => return Err("Root is not a CBOR map".into()),
        };

        // Extract public key from certificate
        let pk = extract_pk_from_cert("test_keys/mdl/issuer-cert.pem")?;
        
        // Extract message and signature
        let (msg, signature) = extract_mdl_signature_data(&issuer_auth)?;

        // Create the MdlPod
        let params = Params {
            max_input_signed_pods: 0,
            ..Default::default()
        };

        let vds = vec![
            pod2::backends::plonky2::STANDARD_REC_MAIN_POD_CIRCUIT_DATA
                .verifier_only
                .clone(),
            pod2::backends::plonky2::emptypod::STANDARD_EMPTY_POD_DATA
                .1
                .verifier_only
                .clone(),
            STANDARD_MDL_POD_DATA.1.verifier_only.clone(),
        ];
        let vdset = VDSet::new(params.max_depth_mt_vds, &vds).unwrap();
        let vds_root = vdset.root();
        
        let mdl_pod = timed!(
            "MdlPod::new",
            MdlPod::new(&params, vds_root, msg, pk, signature)?
        );

        mdl_pod.verify()?;
        
        Ok(())
    }

    #[test]
    fn test_mdl_pod_with_mainpod() -> Result<(), Box<DynError>> {
        // Similar to test_mdl_pod_verify but also test MainPod integration
        // Load the MDL data
        let root: serde_cbor::Value = serde_cbor::from_reader(File::open("test_keys/mdl/decoded.bin")?)?;
        
        let issuer_auth = match &root {
            serde_cbor::Value::Map(map) => map
                .iter()
                .find(|(k, _)| matches!(k, serde_cbor::Value::Text(t) if t == "issuer_auth"))
                .and_then(|(_, v)| match v {
                    serde_cbor::Value::Array(arr) => Some(arr),
                    _ => None,
                })
                .context("issuer_auth missing / not an array")?,
            _ => return Err("Root is not a CBOR map".into()),
        };

        // Extract public key from certificate
        let pk = extract_pk_from_cert("test_keys/mdl/issuer-cert.pem")?;
        
        // Extract message and signature
        let (msg, signature) = extract_mdl_signature_data(&issuer_auth)?;

        // Create the MdlPod
        let params = Params {
            max_input_signed_pods: 0,
            ..Default::default()
        };


        let vds = vec![
            pod2::backends::plonky2::STANDARD_REC_MAIN_POD_CIRCUIT_DATA
                .verifier_only
                .clone(),
            pod2::backends::plonky2::emptypod::STANDARD_EMPTY_POD_DATA
                .1
                .verifier_only
                .clone(),
            STANDARD_MDL_POD_DATA.1.verifier_only.clone(),
        ];
        let vdset = VDSet::new(params.max_depth_mt_vds, &vds).unwrap();
        let vds_root = vdset.root();
        
        
        let mdl_pod = timed!(
            "MdlPod::new",
            MdlPod::new(&params, vds_root, msg.clone(), pk, signature)?
        );

        mdl_pod.verify()?;

        // Wrap in MainPod
        let main_mdl_pod = pod2::frontend::MainPod {
            pod: mdl_pod.clone(),
            public_statements: mdl_pod.pub_statements(),
            params: params.clone(),
        };

        // Generate a new MainPod
        let mut main_pod_builder = MainPodBuilder::new(&params, &vdset);
        main_pod_builder.add_main_pod(main_mdl_pod.clone());

        let digest = Sha256::digest(&msg);
        let digest_bytes: [u8; 32] = digest.into();
        let msg_scalar = P256Scalar(bytes_to_u64_array_be(&digest_bytes));

        // Add operation to verify the message
        let msg_limbs = p256_field_to_limbs(msg_scalar.0);
        let msg_hash = PoseidonHash::hash_no_pad(&msg_limbs);
        let msg_copy = main_pod_builder
            .pub_op(op!(
                new_entry,
                KEY_SIGNED_MSG,
                Value::from(RawValue(msg_hash.elements))
            ))
            .unwrap();
        main_pod_builder
            .pub_op(op!(eq, (&main_mdl_pod, KEY_SIGNED_MSG), msg_copy))?;

        // Perpetuate the pk
        main_pod_builder
            .pub_op(op!(copy, main_mdl_pod.public_statements[2].clone()))?;

        let mut prover = pod2::backends::plonky2::mock::mainpod::MockProver {};
        let pod = main_pod_builder.prove(&mut prover, &params)?;
        assert!(pod.pod.verify().is_ok());

        println!("Going to prove the main_pod");
        let mut prover = mainpod::Prover {};
        let main_pod = timed!(
            "main_pod_builder.prove",
            main_pod_builder.prove(&mut prover, &params)?
        );
        let pod = (main_pod.pod as Box<dyn Any>)
            .downcast::<mainpod::MainPod>()
            .unwrap();
        pod.verify()?;

        Ok(())
    }
}