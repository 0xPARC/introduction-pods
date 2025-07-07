use std::{any::Any, cmp::Ordering, sync::LazyLock};

use anyhow::anyhow;
use itertools::Itertools;
use num::BigUint;
use plonky2::{
    field::types::Field,
    hash::{
        hash_types::{HashOut, HashOutTarget},
        poseidon::PoseidonHash,
    },
    iop::{
        target::{BoolTarget, Target},
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CircuitData, VerifierOnlyCircuitData},
        config::Hasher,
        proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget},
    },
};
use plonky2_rsa::gadgets::{
    biguint::{CircuitBuilderBigUint, WitnessBigUint},
    rsa::pow_65537,
};
use pod2::{
    backends::plonky2::{
        Error, Result,
        basetypes::{C, D, F, VDSet},
        circuits::{
            common::{
                CircuitBuilderPod, Flattenable, StatementArgTarget, StatementTarget, ValueTarget,
            },
            mainpod::CalculateIdGadget,
        },
        deserialize_proof,
        mainpod::{self, calculate_id, get_common_data},
        serialize_proof,
    },
    measure_gates_begin, measure_gates_end,
    middleware::{
        self, AnchoredKey, Hash, KEY_TYPE, Key, NativePredicate, Params, Pod, PodId, Proof,
        RawValue, RecursivePod, SELF, Statement, ToFields, Value,
    },
    timed,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256, Sha512};
use ssh_key::{
    Algorithm, HashAlg, Mpint, SshSig,
    public::{KeyData, RsaPublicKey},
};

use crate::{PodType, gadgets::bits_bytes::reversed_bits_to_bytes_be};

const RSA_BYTE_SIZE: usize = 512;

const KEY_SIGNED_MSG: &str = "signed_msg";
const KEY_RSA_PK: &str = "rsa_pk";

pub(super) const BITS: usize = 27;
pub type BigUintTarget = plonky2_rsa::gadgets::biguint::BigUintTarget<BITS>;

pub(super) const RSA_LIMBS: usize = 4096usize.div_ceil(BITS);

fn mpint_to_biguint(x: &Mpint) -> BigUint {
    BigUint::from_bytes_be(x.as_positive_bytes().unwrap())
}

/// Circuit that checks a given RSA signature.
#[derive(Clone, Debug)]
pub struct RSATargets {
    pub signature: BigUintTarget,
    pub modulus: BigUintTarget,
    pub padded_data: BigUintTarget,
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
    RSATargets {
        signature,
        modulus,
        padded_data,
    }
}

pub fn set_rsa_targets(
    pw: &mut PartialWitness<F>,
    targets: &RSATargets,
    sig: &SshSig,
    padded_data: &[u8],
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

static RSA_VERIFY_DATA: LazyLock<(RSATargets, CircuitData<F, C, D>)> =
    LazyLock::new(|| build_rsa_verify().expect("successful build"));

fn build_rsa_verify() -> Result<(RSATargets, CircuitData<F, C, D>)> {
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let rsa_pod_verify_target = build_rsa(&mut builder);

    // Register public inputs
    builder.register_public_inputs(&rsa_pod_verify_target.signature.limbs);
    builder.register_public_inputs(&rsa_pod_verify_target.modulus.limbs);
    builder.register_public_inputs(&rsa_pod_verify_target.padded_data.limbs);

    let data = timed!("RSAVerify build", builder.build::<C>());
    Ok((rsa_pod_verify_target, data))
}

/// Circuit that verifies a proof generated from the RSATargets circuit.
#[derive(Clone, Debug)]
struct RsaPodVerifyTarget {
    vd_root: HashOutTarget,
    id: HashOutTarget,
    proof: ProofWithPublicInputsTarget<D>,
}

struct RsaPodVerifyInput {
    vd_root: Hash,
    id: PodId,
    proof: ProofWithPublicInputs<F, C, D>,
}

impl RsaPodVerifyTarget {
    fn add_targets(builder: &mut CircuitBuilder<F, D>, params: &Params) -> Self {
        let measure = measure_gates_begin!(builder, "RsaPodVerifyTarget");

        // Verify proof of RSA verification
        let (_, circuit_data) = &*RSA_VERIFY_DATA;
        let verifier_data_targ = builder.constant_verifier_data(&circuit_data.verifier_only);
        let proof_targ = builder.add_virtual_proof_with_pis(&circuit_data.common);
        builder.verify_proof::<C>(&proof_targ, &verifier_data_targ, &circuit_data.common);

        // Extract message & public key
        let msg = BigUintTarget {
            limbs: proof_targ.public_inputs[2 * RSA_LIMBS..].to_vec(),
        };
        let modulus = BigUintTarget {
            limbs: proof_targ.public_inputs[RSA_LIMBS..2 * RSA_LIMBS].to_vec(),
        };

        // Form statements
        let msg_bits = biguint_to_bits_targets(builder, &msg, 8 * RSA_BYTE_SIZE);
        let msg_bytes = reversed_bits_to_bytes_be(builder, &msg_bits);
        let modulus_bits = biguint_to_bits_targets(builder, &modulus, 8 * RSA_BYTE_SIZE);
        let modulus_bytes = reversed_bits_to_bytes_be(builder, &modulus_bits);

        let statements = pub_self_statements_target(builder, params, &msg_bytes, &modulus_bytes);
        let id = CalculateIdGadget {
            params: params.clone(),
        }
        .eval(builder, &statements);

        // Register public inputs
        let vd_root = builder.add_virtual_hash();
        builder.register_public_inputs(&id.elements);
        builder.register_public_inputs(&vd_root.elements);

        measure_gates_end!(builder, measure);
        Self {
            vd_root,
            id,
            proof: proof_targ,
        }
    }

    fn set_targets(&self, pw: &mut PartialWitness<F>, input: &RsaPodVerifyInput) -> Result<()> {
        pw.set_proof_with_pis_target(&self.proof, &input.proof)?;
        pw.set_hash_target(self.id, HashOut::from_vec(input.id.0.0.to_vec()))?;
        pw.set_target_arr(&self.vd_root.elements, &input.vd_root.0)?;

        Ok(())
    }
}

#[derive(Serialize, Deserialize)]
struct Data {
    msg: Vec<u8>,
    pk: Vec<u8>,
    proof: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RsaPod {
    params: Params,
    id: PodId,
    msg: Vec<u8>,
    pk: Vec<u8>,
    proof: Proof,
    vd_set: VDSet,
}

impl RecursivePod for RsaPod {
    fn verifier_data(&self) -> VerifierOnlyCircuitData<C, D> {
        let (_, circuit_data) = &*STANDARD_RSA_POD_DATA;
        circuit_data.verifier_data().verifier_only
    }
    fn proof(&self) -> Proof {
        self.proof.clone()
    }
    fn vd_set(&self) -> &VDSet {
        &self.vd_set
    }
    fn deserialize_data(
        params: Params,
        data: serde_json::Value,
        vd_set: VDSet,
        id: PodId,
    ) -> Result<Box<dyn RecursivePod>> {
        let data: Data = serde_json::from_value(data)?;
        let common = get_common_data(&params)?;
        let proof = deserialize_proof(&common, &data.proof)?;
        Ok(Box::new(Self {
            params,
            id,
            msg: data.msg,
            pk: data.pk,
            proof,
            vd_set,
        }))
    }
}

static STANDARD_RSA_POD_DATA: LazyLock<(RsaPodVerifyTarget, CircuitData<F, C, D>)> =
    LazyLock::new(|| build().expect("successful build"));

fn build() -> Result<(RsaPodVerifyTarget, CircuitData<F, C, D>)> {
    let params = &*pod2::backends::plonky2::DEFAULT_PARAMS;

    // use pod2's recursion config as config for the introduction pod; which if
    // the zk feature enabled, will have the zk property enabled
    let rec_circuit_data = &*pod2::backends::plonky2::STANDARD_REC_MAIN_POD_CIRCUIT_DATA;
    let config = rec_circuit_data.common.config.clone();

    let mut builder = CircuitBuilder::<F, D>::new(config);
    let rsa_pod_verify_target = RsaPodVerifyTarget::add_targets(&mut builder, params);
    let rec_circuit_data = &*pod2::backends::plonky2::STANDARD_REC_MAIN_POD_CIRCUIT_DATA;
    pod2::backends::plonky2::recursion::pad_circuit(&mut builder, &rec_circuit_data.common);

    let data = timed!("RSAPod build", builder.build::<C>());
    assert_eq!(rec_circuit_data.common, data.common);
    Ok((rsa_pod_verify_target, data))
}

impl RsaPod {
    fn new(
        params: &Params,
        vd_set: &VDSet,
        raw_msg: &str,
        sig: &SshSig,
        namespace: &str,
    ) -> Result<RsaPod> {
        // Load signature into verification circuit
        let (rsa_verify_target, rsa_circuit_data) = &*RSA_VERIFY_DATA;
        let mut pw = PartialWitness::<F>::new();
        let encoded_padded_data = build_ssh_signed_data(namespace, raw_msg.as_bytes(), sig)?;

        let pk = match sig.public_key() {
            KeyData::Rsa(pk) => pk,
            _ => {
                return Err(Error::custom(String::from(
                    "signature does not carry an Rsa key",
                )));
            }
        };

        let pk_bytes =
            pk.n.as_positive_bytes()
                .expect("Public key was negative")
                .to_vec();
        if pk_bytes.len() != RSA_BYTE_SIZE {
            return Err(Error::custom(String::from(
                "Public key was not the correct size",
            )));
        }

        set_rsa_targets(&mut pw, rsa_verify_target, sig, &encoded_padded_data)?;

        let rsa_verify_proof = timed!(
            "prove the RSA signature verification (RSAVerifyTarget)",
            rsa_circuit_data.prove(pw)?
        );

        // Verify in wrapped circuit
        let (rsa_pod_target, circuit_data) = &*STANDARD_RSA_POD_DATA;

        let statements = pub_self_statements(&encoded_padded_data, &pk_bytes)
            .into_iter()
            .map(mainpod::Statement::from)
            .collect_vec();
        let id: PodId = PodId(calculate_id(&statements, params));

        // Set targets
        let input = RsaPodVerifyInput {
            vd_root: vd_set.root(),
            id,
            proof: rsa_verify_proof,
        };

        let mut pw = PartialWitness::<F>::new();
        rsa_pod_target.set_targets(&mut pw, &input)?;
        let proof_with_pis = timed!(
            "prove the ed25519-verification proof verification (Ed25519Pod proof)",
            circuit_data.prove(pw)?
        );

        #[cfg(test)] // sanity check
        {
            circuit_data
                .verifier_data()
                .verify(proof_with_pis.clone())?;
        }

        Ok(RsaPod {
            params: params.clone(),
            id,
            msg: encoded_padded_data,
            pk: pk_bytes,
            proof: proof_with_pis.proof,
            vd_set: vd_set.clone(),
        })
    }

    pub fn new_boxed(
        params: &Params,
        vd_set: &VDSet,
        raw_msg: &str,
        sig: &SshSig,
        namespace: &str,
    ) -> Result<Box<dyn RecursivePod>> {
        Ok(Self::new(params, vd_set, raw_msg, sig, namespace).map(Box::new)?)
    }
}

impl Pod for RsaPod {
    fn params(&self) -> &Params {
        &self.params
    }

    fn verify(&self) -> Result<()> {
        let statements = pub_self_statements(&self.msg, &self.pk)
            .into_iter()
            .map(mainpod::Statement::from)
            .collect_vec();
        let id: PodId = PodId(calculate_id(&statements, &self.params));
        if id != self.id {
            return Err(Error::id_not_equal(self.id, id));
        }

        let (_, circuit_data) = &*STANDARD_RSA_POD_DATA;

        let public_inputs = id
            .to_fields(&self.params)
            .iter()
            .chain(self.vd_set().root().0.iter()) // slot for the unused vds root
            .cloned()
            .collect_vec();

        circuit_data
            .verify(ProofWithPublicInputs {
                proof: self.proof.clone(),
                public_inputs,
            })
            .map_err(|e| Error::custom(format!("RSAPod proof verification failure: {:?}", e)))
    }

    fn id(&self) -> PodId {
        self.id
    }

    fn pub_self_statements(&self) -> Vec<middleware::Statement> {
        pub_self_statements(&self.msg, &self.pk)
    }

    fn pod_type(&self) -> (usize, &'static str) {
        (PodType::Rsa as usize, "RSA")
    }

    fn serialize_data(&self) -> serde_json::Value {
        serde_json::to_value(Data {
            proof: serialize_proof(&self.proof),
            msg: self.msg.clone(),
            pk: self.pk.clone(),
        })
        .expect("serialization to json")
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
    fn equals(&self, other: &dyn Pod) -> bool {
        if let Some(other) = other.as_any().downcast_ref::<RsaPod>() {
            self == other
        } else {
            false
        }
    }
}

fn type_statement() -> Statement {
    Statement::equal(
        AnchoredKey::from((SELF, KEY_TYPE)),
        Value::from(PodType::Rsa),
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

    // Hash the message
    let msg_hash = builder.hash_n_to_hash_no_pad::<PoseidonHash>(msg.to_vec());
    let ak_key = builder.constant_value(Key::from(KEY_SIGNED_MSG).raw());
    let ak_msg = StatementArgTarget::anchored_key(builder, &ak_podid, &ak_key);
    let value = StatementArgTarget::literal(builder, &ValueTarget::from_slice(&msg_hash.elements));
    let st_msg =
        StatementTarget::new_native(builder, params, NativePredicate::Equal, &[ak_msg, value]);

    // Hash the public key
    let pk_hash = builder.hash_n_to_hash_no_pad::<PoseidonHash>(pk.to_vec());
    let ak_key = builder.constant_value(Key::from(KEY_RSA_PK).raw());
    let ak_pk = StatementArgTarget::anchored_key(builder, &ak_podid, &ak_key);
    let value = StatementArgTarget::literal(builder, &ValueTarget::from_slice(&pk_hash.elements));
    let st_pk =
        StatementTarget::new_native(builder, params, NativePredicate::Equal, &[ak_pk, value]);

    vec![st_type, st_msg, st_pk]
}

fn pub_self_statements(msg: &[u8], pk: &[u8]) -> Vec<middleware::Statement> {
    let st_type = type_statement();

    // Hash the message
    let msg_fields: Vec<F> = msg.iter().map(|&b| F::from_canonical_u8(b)).collect();
    let msg_hash = PoseidonHash::hash_no_pad(&msg_fields);

    let st_msg = Statement::equal(
        AnchoredKey::from((SELF, KEY_SIGNED_MSG)),
        Value::from(RawValue(msg_hash.elements)),
    );

    // Hash the public key
    let pk_fields: Vec<F> = pk.iter().map(|&b| F::from_canonical_u8(b)).collect();
    let pk_hash = PoseidonHash::hash_no_pad(&pk_fields);

    let st_pk = Statement::equal(
        AnchoredKey::from((SELF, KEY_RSA_PK)),
        Value::from(RawValue(pk_hash.elements)),
    );

    vec![st_type, st_msg, st_pk]
}

fn biguint_to_bits_targets(
    builder: &mut CircuitBuilder<F, D>,
    biguint: &BigUintTarget,
    total_bits: usize,
) -> Vec<BoolTarget> {
    // Returns bits in little-endian order, i.e. least significant BIT first (this is NOT the same as little endian BYTE ordering)
    let false_target = builder._false();
    let mut bits: Vec<BoolTarget> = Vec::new();
    for limb in &biguint.limbs {
        bits.extend_from_slice(&builder.split_le(*limb, BITS));
    }

    match bits.len().cmp(&total_bits) {
        Ordering::Less => {
            bits.extend(vec![false_target; total_bits - bits.len()]);
        }
        Ordering::Equal => {}
        Ordering::Greater => {
            for bit in bits.iter().skip(total_bits) {
                let not_bit_i = builder.not(*bit);
                builder.assert_bool(not_bit_i);
            }
            bits = bits[..total_bits].to_vec();
        }
    }
    bits
}

/// Build SSH signed data format
pub fn build_ssh_signed_data(namespace: &str, raw_msg: &[u8], ssh_sig: &SshSig) -> Result<Vec<u8>> {
    // Use the SSH library's built-in method to create the data to sign
    let encoded_data = ssh_key::SshSig::signed_data(namespace, ssh_sig.hash_alg(), raw_msg)
        .expect("failed to build encoded SSH data");

    // Hash the data to sign and generate the digest info
    let (hashed_data, digest_info): (Vec<u8>, Vec<u8>) = match ssh_sig.algorithm() {
        Algorithm::Rsa {
            hash: Some(HashAlg::Sha256),
        } => (Sha256::digest(&encoded_data).to_vec(), vec![
            0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02,
            0x01, 0x05, 0x00, 0x04, 0x20,
        ]),
        Algorithm::Rsa {
            hash: Some(HashAlg::Sha512),
        } => (Sha512::digest(&encoded_data).to_vec(), vec![
            0x30, 0x51, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02,
            0x03, 0x05, 0x00, 0x04, 0x40,
        ]),
        _ => {
            return Err(Error::custom(String::from(
                "rsa-sha2-256 and rsa-sha2-256 only",
            )));
        }
    };

    let mut combined_data = digest_info;
    combined_data.extend_from_slice(&hashed_data);

    let comb_len = combined_data.len();

    if RSA_BYTE_SIZE < comb_len + 11 {
        return Err(Error::custom(String::from(
            "Internal encoding error. Encoded message overflows modulus.",
        )));
    }

    // Generate padding string PS
    let ps_len = RSA_BYTE_SIZE - comb_len - 3;
    let ps = vec![0xff; ps_len]; // PS consists of 0xff octets

    // Concatenate to form the encoded message EM
    // EM = 0x00 || 0x01 || PS || 0x00 || T
    let mut padded_data = Vec::with_capacity(RSA_BYTE_SIZE);
    padded_data.push(0x00); // Leading 0x00
    padded_data.push(0x01); // 0x01 byte
    padded_data.extend_from_slice(&ps); // Padding string PS (all 0xff)
    padded_data.push(0x00); // Separator 0x00
    padded_data.extend_from_slice(&combined_data); // DigestInfo T

    Ok(padded_data)
}

#[cfg(test)]
pub mod tests {
    use std::any::Any;

    use pod2::{self, middleware::VDSet};

    use super::*;

    fn get_test_rsa_pod() -> Result<(Box<dyn RecursivePod>, VDSet, Vec<u8>)> {
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
            STANDARD_RSA_POD_DATA.1.verifier_only.clone(),
        ];
        let vd_set = VDSet::new(params.max_depth_mt_vds, &vds).unwrap();

        // Use the sample data from plonky2_rsa
        let msg = "0xPARC\n";
        let namespace = "double-blind.xyz";
        let sig = SshSig::from_pem(include_bytes!("../test_keys/id_rsa_example.sig")).unwrap();

        let rsa_pod = timed!(
            "RsaPod::new",
            RsaPod::new_boxed(&params, &vd_set.clone(), msg, &sig, namespace).unwrap()
        );
        let encoded_padded_data = build_ssh_signed_data(namespace, msg.as_bytes(), &sig)?;
        Ok((rsa_pod, vd_set, encoded_padded_data))
    }

    #[test]
    fn test_rsa_pod_with_mainpod_verify() -> Result<()> {
        let (rsa_pod, vd_set, msg_encoded) = get_test_rsa_pod().unwrap();
        let params = rsa_pod.params().clone();

        // prepare the msg_hash as it will be checked in the 2nd iteration
        // MainPod in the pod operation
        let msg_fields: Vec<F> = msg_encoded
            .iter()
            .map(|&b| F::from_canonical_u8(b))
            .collect();
        let msg_hash = PoseidonHash::hash_no_pad(&msg_fields);

        crate::tests::test_introduction_pod_signature_flow(
            rsa_pod,
            params,
            vd_set,
            KEY_SIGNED_MSG,
            msg_hash,
        )?;

        Ok(())
    }

    #[test]
    fn test_ssh_rsa_encode() -> Result<()> {
        // Only tests a signature generated with Sha512 as the inner hash algorithm and rsa-sha2-512 as the signature method.
        let msg = "0xPARC\n";
        let namespace = "double-blind.xyz";
        let sig = SshSig::from_pem(include_bytes!("../test_keys/id_rsa_example.sig")).unwrap();
        let data = build_ssh_signed_data(namespace, msg.as_bytes(), &sig).unwrap();

        assert_eq!(data, vec![
            0, 1, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 0, 48, 81, 48, 13, 6, 9, 96, 134, 72, 1, 101, 3, 4, 2, 3, 5, 0, 4, 64, 181,
            197, 44, 214, 116, 75, 54, 39, 234, 42, 140, 208, 11, 206, 41, 35, 206, 205, 191, 120,
            173, 54, 59, 138, 2, 32, 227, 203, 41, 241, 18, 139, 161, 89, 68, 192, 135, 58, 241,
            130, 136, 20, 149, 230, 135, 249, 125, 234, 20, 202, 101, 48, 221, 110, 27, 245, 17,
            102, 82, 107, 69, 88, 89, 51
        ]);

        Ok(())
    }

    #[test]
    #[ignore] // this is for the GitHub CI, it takes too long and the CI would fail.
    fn test_serialization() -> Result<()> {
        let (rsa_pod, vd_set, _) = get_test_rsa_pod()?;

        rsa_pod.verify().unwrap();

        let rsa_pod = (rsa_pod as Box<dyn Any>).downcast::<RsaPod>().unwrap();
        let data = rsa_pod.serialize_data();
        let recovered_rsa_pod =
            RsaPod::deserialize_data(rsa_pod.params().clone(), data, vd_set, rsa_pod.id()).unwrap();
        let recovered_rsa_pod = (recovered_rsa_pod as Box<dyn Any>)
            .downcast::<RsaPod>()
            .unwrap();

        assert_eq!(recovered_rsa_pod, rsa_pod);

        Ok(())
    }
}
