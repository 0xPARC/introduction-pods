// mdlpod.rs
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
use plonky2_sha256::{
    circuit::make_circuits
};
use plonky2_ecdsa::{
    curve::{
        ecdsa::{ECDSAPublicKey, ECDSASignature},
        p256::P256,
    },
    gadgets::{
        biguint::WitnessBigUint,
        curve::CircuitBuilderCurve,
        ecdsa::{verify_p256_message_circuit, ECDSAPublicKeyTarget, ECDSASignatureTarget},
        nonnative::{CircuitBuilderNonNative, NonNativeTarget},
    },
};
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
        mainpod,
        mainpod::calculate_id,
    },
    measure_gates_begin, measure_gates_end,
    middleware::{
        self, AnchoredKey, DynError, EMPTY_HASH, F, Hash, KEY_TYPE, Key, NativePredicate, Params,
        Pod, PodId, RawValue, RecursivePod, SELF, Statement, ToFields, Value,
    },
    timed,
};
use crate::PodType;
use plonky2_ecdsa::field::p256_scalar::P256Scalar;
use sha2::{Digest, Sha256};
use serde_cbor;

const KEY_SIGNED_MSG: &str = "signed_msg";
const KEY_P256_PK: &str = "p256_pk";

static P256_VERIFY_DATA: LazyLock<(P256VerifyTarget, CircuitData<F, C, D>)> =
    LazyLock::new(|| build_p256_verify().expect("successful build"));

fn build_p256_verify() -> Result<(P256VerifyTarget, CircuitData<F, C, D>)> {
    let config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let p256_verify_target = P256VerifyTarget::add_targets(&mut builder)?;

    let data = timed!("P256Verify build", builder.build::<C>());
    Ok((p256_verify_target, data))
}

/// Note: this circuit requires the CircuitConfig's standard_ecc_config or
/// wide_ecc_config.
struct P256VerifyTarget {
    msg: NonNativeTarget<P256Scalar>,
    pk: ECDSAPublicKeyTarget<P256>,
    signature: ECDSASignatureTarget<P256>,
}

impl P256VerifyTarget {
    fn add_targets(builder: &mut CircuitBuilder<F, D>) -> Result<Self> {
        let measure = measure_gates_begin!(builder, "P256VerifyTarget");
        let msg = builder.add_virtual_nonnative_target::<P256Scalar>();
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
            msg,
            pk,
            signature: sig,
        })
    }

    fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        msg: P256Scalar,
        pk: ECDSAPublicKey<P256>,
        signature: ECDSASignature<P256>,
    ) -> Result<()> {
        pw.set_biguint_target(
            &self.msg.value,
            &biguint_from_array(std::array::from_fn(|i| msg.0[i])),
        )?;
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
    msg: P256Scalar,
    pk: ECDSAPublicKey<P256>,
    proof: Proof,
    vds_hash: Hash,
}

impl middleware::RecursivePod for MdlPod {
    fn verifier_data(&self) -> VerifierOnlyCircuitData<C, D> {
        let (_, circuit_data) = &*STANDARD_MDL_POD_DATA;
        circuit_data.verifier_data().verifier_only
    }
    fn proof(&self) -> Proof {
        self.proof.clone()
    }
    fn vds_root(&self) -> Hash {
        self.vds_hash
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
) -> Result<(P256Scalar, ECDSASignature<P256>), Box<DynError>> {
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
    let sig_bytes = serde_cbor::to_vec(&sig_structure)
        .map_err(|e| format!("Failed to serialize sig_structure: {}", e))?;

    // Hash the message
    let digest = Sha256::digest(&sig_bytes);
    let digest_bytes: [u8; 32] = digest.into();
    let msg = P256Scalar(bytes_to_u64_array_be(&digest_bytes));

    // Extract r and s from signature
    let r = P256Scalar(bytes_to_u64_array_be(&sig_r_s[..32].try_into().unwrap()));
    let s = P256Scalar(bytes_to_u64_array_be(&sig_r_s[32..].try_into().unwrap()));

    let signature = ECDSASignature { r, s };
    
    Ok((msg, signature))
}


impl MdlPod {
    fn _prove(
        params: &Params,
        vds_root: Hash,
        msg: P256Scalar,
        pk: ECDSAPublicKey<P256>,
        signature: ECDSASignature<P256>,
    ) -> Result<MdlPod> {
        // 1. prove the P256Verify circuit
        let (p256_verify_target, p256_circuit_data) = &*P256_VERIFY_DATA;
        let mut pw = PartialWitness::<F>::new();
        p256_verify_target.set_targets(&mut pw, msg, pk, signature)?;

        let p256_verify_proof = timed!(
            "prove the p256 signature verification (P256VerifyTarget)",
            p256_circuit_data.prove(pw)?
        );

        // sanity check
        p256_circuit_data
            .verifier_data()
            .verify(p256_verify_proof.clone())?;

        // 2. verify the p256_verify proof in a MdlPodVerifyTarget circuit
        let (mdl_pod_target, circuit_data) = &*STANDARD_MDL_POD_DATA;

        let statements = pub_self_statements(msg, pk)
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
            vds_hash: EMPTY_HASH,
        })
    }

    #[allow(clippy::new_ret_no_self)]
    pub fn new(
        params: &Params,
        vds_root: Hash,
        msg: P256Scalar,
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
        let statements = pub_self_statements(self.msg, self.pk)
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
        pub_self_statements(self.msg, self.pk)
    }

    fn serialized_proof(&self) -> String {
        let mut buffer = Vec::new();
        use plonky2::util::serialization::Write;
        buffer.write_proof(&self.proof).unwrap();
        BASE64_STANDARD.encode(buffer)
    }
}

fn type_statement() -> Statement {
    Statement::ValueOf(
        AnchoredKey::from((SELF, KEY_TYPE)),
        Value::from(PodType::MdlCurve),
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
        StatementTarget::new_native(builder, params, NativePredicate::ValueOf, &[ak_msg, value]);

    let pk_hash = builder.hash_n_to_hash_no_pad::<PoseidonHash>(pk.to_vec());
    let ak_key = builder.constant_value(Key::from(KEY_P256_PK).raw());
    let ak_pk = StatementArgTarget::anchored_key(builder, &ak_podid, &ak_key);
    let value = StatementArgTarget::literal(builder, &ValueTarget::from_slice(&pk_hash.elements));
    let st_pk =
        StatementTarget::new_native(builder, params, NativePredicate::ValueOf, &[ak_pk, value]);

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

    let st_msg = Statement::ValueOf(
        AnchoredKey::from((SELF, KEY_SIGNED_MSG)),
        Value::from(RawValue(msg_hash.elements)),
    );

    // hash the pk as in-circuit
    let pk_x_limbs = p256_field_to_limbs(pk.0.x.0);
    let pk_y_limbs = p256_field_to_limbs(pk.0.y.0);
    let pk_hash = PoseidonHash::hash_no_pad(&[pk_x_limbs, pk_y_limbs].concat());

    let st_pk = Statement::ValueOf(
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
    #[ignore]
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
        let vds_root = EMPTY_HASH;
        
        let mdl_pod = timed!(
            "MdlPod::new",
            MdlPod::new(&params, vds_root, msg, pk, signature)?
        );

        mdl_pod.verify()?;
        
        Ok(())
    }

    #[test]
    #[ignore]
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
        let vds_root = EMPTY_HASH;
        
        let mdl_pod = timed!(
            "MdlPod::new",
            MdlPod::new(&params, vds_root, msg, pk, signature)?
        );

        mdl_pod.verify()?;

        // Wrap in MainPod
        let main_mdl_pod = pod2::frontend::MainPod {
            pod: mdl_pod.clone(),
            public_statements: mdl_pod.pub_statements(),
            params: params.clone(),
        };

        // Generate a new MainPod
        let mut main_pod_builder = MainPodBuilder::new(&params);
        main_pod_builder.add_main_pod(main_mdl_pod.clone());

        // Add operation to verify the message
        let msg_limbs = p256_field_to_limbs(msg.0);
        let msg_hash = PoseidonHash::hash_no_pad(&msg_limbs);
        let msg_copy = main_pod_builder
            .pub_op(op!(
                new_entry,
                (KEY_SIGNED_MSG, Value::from(RawValue(msg_hash.elements)))
            ))?;
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