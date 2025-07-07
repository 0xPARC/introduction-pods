//! Implements the MdlPod, a POD that proves that the given `pk` has signed
//! the `msg` with the ES256 signature scheme.
//!
//! This POD is build through two steps:
//! - first it generates a plonky2 proof of correct signature verification
//! - then, verifies the previous proof in a new plonky2 proof, using the
//!   `standard_recursion_config`, padded to match the `RecursiveCircuit<MainPod>`
//!   configuration.

mod parse;

use std::sync::LazyLock;

use anyhow::anyhow;
use itertools::Itertools;
use num::bigint::BigUint;
use plonky2::{
    field::types::Field,
    hash::{
        hash_types::{HashOut, HashOutTarget},
        hashing::hash_n_to_hash_no_pad,
        poseidon::{PoseidonHash, PoseidonPermutation},
    },
    iop::{
        target::Target,
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CircuitData, VerifierOnlyCircuitData},
        proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget},
    },
};
use plonky2_ecdsa::{
    curve::{
        ecdsa::{ECDSAPublicKey, ECDSASignature},
        p256::P256,
    },
    gadgets::{
        biguint::{BigUintTarget, WitnessBigUint},
        curve::CircuitBuilderCurve,
        ecdsa::{ECDSAPublicKeyTarget, ECDSASignatureTarget, verify_p256_message_circuit},
        nonnative::CircuitBuilderNonNative,
    },
};
use plonky2_sha256::circuit::{
    VariableLengthSha256Targets, fill_variable_length_circuits, make_variable_length_circuits,
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
        deserialize_proof,
        mainpod::{self, calculate_id, get_common_data},
        serialize_proof,
    },
    measure_gates_begin, measure_gates_end,
    middleware::{
        self, AnchoredKey, BackendError, F, Hash, KEY_TYPE, Key, NativePredicate, Params, Pod,
        PodId, RawValue, RecursivePod, SELF, Statement, ToFields, TypedValue, VALUE_SIZE, VDSet,
        Value,
    },
    timed,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{
    PodType,
    gadgets::{
        bits_bytes::bits_to_bytes_be,
        comparison::check_less_or_equal,
        search::{LookupTarget, merkle_root_rabin_karp_circuit, merkle_tree},
    },
    mdlpod::parse::{DataType, EntryTarget, MdlData, parse_data, sha_256_pad},
};

type MDLFieldData<'a> = &'a [(&'a str, DataType)];

const MDL_FIELDS: MDLFieldData<'static> = &[
    ("document_number", DataType::String),
    ("expiry_date", DataType::Date),
    ("family_name", DataType::String),
    ("given_name", DataType::String),
    ("resident_address", DataType::String),
    ("birth_date", DataType::Date),
    ("age_birth_year", DataType::Int),
    ("sex", DataType::Int),
    ("hair_colour", DataType::String),
    ("eye_colour", DataType::String),
    ("height", DataType::Int),
    ("weight", DataType::Int),
];

#[derive(Serialize, Deserialize)]
struct Data {
    mdl_dict: Vec<(String, Value)>,
    pk: ECDSAPublicKey<P256>,
    proof: String,
}

struct MdlItemTarget {
    entry: EntryTarget,
    lookup: LookupTarget,
    hash: VariableLengthSha256Targets,
}

// TODO: it turns out that the thing that is signed is not exactly the mso,
// but I haven't changed the variable names yet
struct MdlDocTarget {
    mso: Vec<Target>,
    mso_len: Target,
    entries: Vec<MdlItemTarget>,
}

fn connect_entry_and_hash(
    builder: &mut CircuitBuilder<F, D>,
    entry: &EntryTarget,
    hash: &VariableLengthSha256Targets,
) {
    let hash_msg_bytes = bits_to_bytes_be(builder, &hash.message);
    builder.connect_slice(&hash_msg_bytes, &entry.cbor[..]);
    let bytes_per_block = builder.constant(F::from_canonical_u32(64));
    let max_allowed_end = builder.mul(bytes_per_block, hash.msg_blocks.0);
    check_less_or_equal(
        builder,
        entry.data_end_offset,
        max_allowed_end,
        (hash.message.len().ilog2() - 2) as usize,
    );
}

fn mso_search_for_hash(
    builder: &mut CircuitBuilder<F, D>,
    hash: &VariableLengthSha256Targets,
) -> Vec<Target> {
    let mut out = Vec::with_capacity(34);
    // CBOR tag for a 32 byte string
    out.extend([0x58, 0x20].map(|x| builder.constant(F::from_canonical_u8(x))));
    let sha_bytes = bits_to_bytes_be(builder, &hash.digest);
    out.extend(sha_bytes);
    out
}

fn connect_mso_and_lookup(
    builder: &mut CircuitBuilder<F, D>,
    mso_len: Target,
    mso_merkle_root: HashOutTarget,
    lookup: &LookupTarget,
) {
    builder.connect_hashes(mso_merkle_root, lookup.root);
    let digest_index = builder.le_sum(lookup.index_bits.iter());
    let window_len = builder.constant(F::from_canonical_u32(34));
    let digest_end = builder.add(digest_index, window_len);
    check_less_or_equal(builder, digest_end, mso_len, SEARCH_TREE_DEPTH + 1);
}

fn connect_doc_and_hash(
    builder: &mut CircuitBuilder<F, D>,
    doc: &MdlDocTarget,
    hash: &VariableLengthSha256Targets,
) {
    let hash_bytes = bits_to_bytes_be(builder, &hash.message);
    builder.connect_slice(&doc.mso, &hash_bytes[..doc.mso.len()]);
    // 9 bytes of padding + 63 bytes for rounding up
    let len_addition = builder.constant(F::from_canonical_u32(72));
    let len_with_addition = builder.add(doc.mso_len, len_addition);
    // 1 block = 64 bytes = 2^6 bytes
    let (_, expected_blocks) = builder.split_low_high(len_with_addition, 6, SEARCH_TREE_DEPTH);
    builder.connect(hash.msg_blocks.0, expected_blocks);
}

const SEARCH_TREE_DEPTH: usize = 12;
const ENTRY_MAX_BYTES: usize = 128;
const ENTRY_MAX_BITS: usize = ENTRY_MAX_BYTES * 8;
const MSO_MAX_BLOCKS: usize = 48;
const MSO_MAX_BYTES_PADDED: usize = MSO_MAX_BLOCKS * 64;
const MSO_MAX_BITS_PADDED: usize = MSO_MAX_BYTES_PADDED * 8;
const MSO_MAX_BYTES_UNPADDED: usize = MSO_MAX_BYTES_PADDED - 9;

impl MdlDocTarget {
    fn add_targets(builder: &mut CircuitBuilder<F, D>, fields: MDLFieldData<'_>) -> Self {
        let measure = measure_gates_begin!(builder, "MdlDocTarget");
        let mso_len = builder.add_virtual_target();
        let mso = builder.add_virtual_targets(MSO_MAX_BYTES_UNPADDED);
        let merkle_root = merkle_root_rabin_karp_circuit(builder, &mso, SEARCH_TREE_DEPTH, 34);
        let mut entries = Vec::with_capacity(fields.len());
        for (key, data_type) in fields {
            let entry = EntryTarget::new(builder, key, *data_type);
            let hash =
                plonky2_sha256::circuit::make_variable_length_circuits(builder, ENTRY_MAX_BITS);
            let lookup = LookupTarget::new(builder, SEARCH_TREE_DEPTH, 34);
            connect_entry_and_hash(builder, &entry, &hash);
            let search_string = mso_search_for_hash(builder, &hash);
            builder.connect_slice(&lookup.data, &search_string);
            connect_mso_and_lookup(builder, mso_len, merkle_root, &lookup);
            builder.register_public_inputs(&entry.value.elements);
            entries.push(MdlItemTarget {
                entry,
                hash,
                lookup,
            });
        }
        measure_gates_end!(builder, measure);
        MdlDocTarget {
            mso,
            mso_len,
            entries,
        }
    }

    fn set_targets(&self, pw: &mut PartialWitness<F>, data: &MdlData) -> anyhow::Result<()> {
        let mut mso_padded = data.signed_message.clone();
        sha_256_pad(&mut mso_padded, MSO_MAX_BLOCKS)?;
        for (&ch_t, &ch) in self.mso.iter().zip(mso_padded.iter()) {
            pw.set_target(ch_t, F::from_canonical_u8(ch))?;
        }
        pw.set_target(
            self.mso_len,
            F::from_canonical_usize(data.signed_message.len()),
        )?;
        let tree = merkle_tree(&mso_padded[..self.mso.len()], SEARCH_TREE_DEPTH, 34);
        for entry_t in self.entries.iter() {
            let entry = data
                .data
                .get(&entry_t.entry.field_name)
                .ok_or_else(|| anyhow!("could not find entry for {}", &entry_t.entry.field_name))?;
            entry_t.entry.set_targets(pw, &entry.cbor)?;
            fill_variable_length_circuits::<_, 2>(
                pw,
                &entry.cbor,
                entry_t.hash.message.len(),
                &entry_t.hash,
            )?;
            let mut hasher = Sha256::new();
            hasher.update(&entry.cbor);
            let hash = hasher.finalize();
            let index = memchr::memmem::find(&data.signed_message, &hash)
                .ok_or_else(|| anyhow!("hash not found in mso"))?
                - 2;
            entry_t
                .lookup
                .set_targets_from_index(pw, &data.signed_message, index, &tree)?;
        }
        Ok(())
    }
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

/// Note: this circuit requires the CircuitConfig's standard_ecc_config or
/// wide_ecc_config.
struct P256VerifyTarget {
    sha256_targets: VariableLengthSha256Targets,
    pk: ECDSAPublicKeyTarget<P256>,
    signature: ECDSASignatureTarget<P256>,
}

impl P256VerifyTarget {
    fn add_targets(builder: &mut CircuitBuilder<F, D>, max_msg_len_bits: usize) -> Self {
        let measure = measure_gates_begin!(builder, "P256VerifyTarget");

        let sha256_targets = make_variable_length_circuits(builder, max_msg_len_bits);

        // Pre-compute constants outside the closure
        let zero = builder.zero();
        let one = builder.one();

        // Convert the 256-bit digest output to bytes
        let digest_bytes_targets: Vec<Target> = (0..32)
            .map(|i| {
                // Convert 8 bits to a byte
                let mut byte_val = zero;
                for j in 0..8 {
                    let bit_val = builder.select(sha256_targets.digest[i * 8 + j], one, zero);
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
            limbs: limbs.into_iter().map(U32Target).collect(),
        };

        // Create NonNativeTarget from limbs
        let msg = builder.biguint_to_nonnative(&msg_big_uint);
        let pk = ECDSAPublicKeyTarget(builder.add_virtual_affine_point_target::<P256>());
        let r = builder.add_virtual_nonnative_target();
        let s = builder.add_virtual_nonnative_target();
        let sig = ECDSASignatureTarget::<P256> { r, s };

        verify_p256_message_circuit(builder, msg.clone(), sig.clone(), pk.clone());

        // register pk as public input
        for l in pk.0.x.value.limbs.iter() {
            builder.register_public_input(l.0);
        }
        for l in pk.0.y.value.limbs.iter() {
            builder.register_public_input(l.0);
        }

        measure_gates_end!(builder, measure);
        P256VerifyTarget {
            sha256_targets,
            pk,
            signature: sig,
        }
    }

    fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        msg: Vec<u8>,
        pk: ECDSAPublicKey<P256>,
        signature: ECDSASignature<P256>,
    ) -> Result<()> {
        fill_variable_length_circuits::<_, 2>(
            pw,
            &msg,
            self.sha256_targets.message.len(),
            &self.sha256_targets,
        )?;
        pw.set_biguint_target(&self.pk.0.x.value, &biguint_from_array(pk.0.x.0))?;
        pw.set_biguint_target(&self.pk.0.y.value, &biguint_from_array(pk.0.y.0))?;
        pw.set_biguint_target(&self.signature.r.value, &biguint_from_array(signature.r.0))?;
        pw.set_biguint_target(&self.signature.s.value, &biguint_from_array(signature.s.0))?;

        Ok(())
    }
}

pub struct MdlVerifyTarget {
    doc: MdlDocTarget,
    sig: P256VerifyTarget,
}

impl MdlVerifyTarget {
    fn add_targets(builder: &mut CircuitBuilder<F, D>) -> Self {
        let sig = P256VerifyTarget::add_targets(builder, MSO_MAX_BITS_PADDED);
        let doc = MdlDocTarget::add_targets(builder, MDL_FIELDS);
        connect_doc_and_hash(builder, &doc, &sig.sha256_targets);
        Self { doc, sig }
    }

    fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        pk: &ECDSAPublicKey<P256>,
        mdl_data: &MdlData,
    ) -> anyhow::Result<()> {
        self.doc.set_targets(pw, mdl_data)?;
        self.sig
            .set_targets(pw, mdl_data.signed_message.clone(), *pk, mdl_data.signature)?;
        Ok(())
    }
}

static MDL_VERIFY_DATA: LazyLock<(MdlVerifyTarget, CircuitData<F, C, D>)> =
    LazyLock::new(build_mdl_verify);

fn build_mdl_verify() -> (MdlVerifyTarget, CircuitData<F, C, D>) {
    let config = CircuitConfig::wide_ecc_config();
    let mut builder = CircuitBuilder::new(config);
    let target = MdlVerifyTarget::add_targets(&mut builder);
    let data = timed!("MDLVerify build", builder.build());
    (target, data)
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MdlPod {
    params: Params,
    id: PodId,
    pk: ECDSAPublicKey<P256>,
    mdl_dict: Vec<(String, Value)>,
    proof: Proof,
    vd_set: VDSet,
}

#[derive(Clone, Debug)]
struct MdlPodVerifyTarget {
    vd_root: HashOutTarget,
    id: HashOutTarget,
    proof: ProofWithPublicInputsTarget<D>,
}

pub struct MdlPodVerifyInput {
    vd_root: Hash,
    id: PodId,
    proof: ProofWithPublicInputs<F, C, D>,
}

impl MdlPodVerifyTarget {
    fn add_targets(builder: &mut CircuitBuilder<F, D>, params: &Params) -> Result<Self> {
        let measure = measure_gates_begin!(builder, "MdlPodVerifyTarget");

        // Verify P256VerifyTarget's proof (with verifier_data hardcoded as constant)
        let (_, circuit_data) = &*MDL_VERIFY_DATA;
        let verifier_data_targ = builder.constant_verifier_data(&circuit_data.verifier_only);
        let proof_targ = builder.add_virtual_proof_with_pis(&circuit_data.common);
        builder.verify_proof::<C>(&proof_targ, &verifier_data_targ, &circuit_data.common);

        // calculate id
        let statements = pub_self_statements_target(builder, params, &proof_targ.public_inputs);
        let id = CalculateIdGadget {
            params: params.clone(),
        }
        .eval(builder, &statements);

        // register the public inputs
        let vd_root = builder.add_virtual_hash();
        builder.register_public_inputs(&id.elements);
        builder.register_public_inputs(&vd_root.elements);

        measure_gates_end!(builder, measure);
        Ok(MdlPodVerifyTarget {
            vd_root,
            id,
            proof: proof_targ,
        })
    }

    fn set_targets(&self, pw: &mut PartialWitness<F>, input: &MdlPodVerifyInput) -> Result<()> {
        pw.set_proof_with_pis_target(&self.proof, &input.proof)?;
        pw.set_hash_target(self.id, HashOut::from_vec(input.id.0.0.to_vec()))?;
        pw.set_target_arr(&self.vd_root.elements, &input.vd_root.0)?;

        Ok(())
    }
}

impl RecursivePod for MdlPod {
    fn verifier_data(&self) -> VerifierOnlyCircuitData<C, D> {
        let (_, circuit_data) = &*STANDARD_MDL_POD_DATA;
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
    ) -> Result<Box<dyn RecursivePod>, BackendError> {
        let data: Data = serde_json::from_value(data)?;
        let common = get_common_data(&params)?;
        let proof = deserialize_proof(&common, &data.proof)?;
        Ok(Box::new(Self {
            params,
            id,
            mdl_dict: data.mdl_dict,
            pk: data.pk,
            proof,
            vd_set,
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

impl MdlPod {
    fn _prove(
        params: &Params,
        vd_set: &VDSet,
        pk: ECDSAPublicKey<P256>,
        mdl_data: &MdlData,
    ) -> Result<MdlPod> {
        let (mdl_verify_target, mdl_circuit_data) = &*MDL_VERIFY_DATA;
        let mut pw = PartialWitness::<F>::new();
        mdl_verify_target.set_targets(&mut pw, &pk, mdl_data)?;

        let mdl_verify_proof = timed!("Proof of MDL contents", mdl_circuit_data.prove(pw)?);

        // sanity check
        mdl_circuit_data
            .verifier_data()
            .verify(mdl_verify_proof.clone())?;

        // 2. verify the p256_verify proof in a MdlPodVerifyTarget circuit
        let (mdl_pod_target, circuit_data) = &*STANDARD_MDL_POD_DATA;

        let mdl_dict: Vec<_> = MDL_FIELDS
            .iter()
            .map(|(key, _)| -> anyhow::Result<_> {
                let key_owned = key.to_string();
                let typed_value = mdl_data
                    .data
                    .get(*key)
                    .ok_or_else(|| anyhow!("missing field {}", key))?
                    .value
                    .clone();
                let value = Value::new(typed_value);
                Ok((key_owned, value))
            })
            .collect::<Result<_, _>>()?;
        let statements = pub_self_statements(&pk, &mdl_dict)
            .into_iter()
            .map(mainpod::Statement::from)
            .collect_vec();
        let id: PodId = PodId(calculate_id(&statements, params));

        // set targets
        let input = MdlPodVerifyInput {
            vd_root: vd_set.root(),
            id,
            proof: mdl_verify_proof,
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
            pk,
            mdl_dict,
            proof: proof_with_pis.proof,
            vd_set: vd_set.clone(),
        })
    }

    #[allow(clippy::new_ret_no_self)]
    pub fn new(
        params: &Params,
        vd_set: &VDSet,
        pk: ECDSAPublicKey<P256>,
        mdl_data: &[u8],
    ) -> Result<Box<dyn RecursivePod>, BackendError> {
        let mdl_data_parsed = parse_data(mdl_data)?;
        Ok(Self::_prove(params, vd_set, pk, &mdl_data_parsed).map(Box::new)?)
    }

    fn _verify(&self) -> Result<()> {
        let statements = pub_self_statements(&self.pk, &self.mdl_dict)
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
            .chain(self.vd_set().root().0.iter())
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
    fn verify(&self) -> Result<(), BackendError> {
        self._verify()
    }

    fn id(&self) -> PodId {
        self.id
    }

    fn pub_self_statements(&self) -> Vec<middleware::Statement> {
        pub_self_statements(&self.pk, &self.mdl_dict)
    }

    fn pod_type(&self) -> (usize, &'static str) {
        (PodType::Mdl as usize, "Mdl")
    }

    fn serialize_data(&self) -> serde_json::Value {
        serde_json::to_value(Data {
            mdl_dict: self.mdl_dict.clone(),
            pk: self.pk,
            proof: serialize_proof(&self.proof),
        })
        .expect("serialization to json")
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self as &dyn std::any::Any
    }

    fn equals(&self, other: &dyn Pod) -> bool {
        if let Some(o) = (other as &dyn std::any::Any).downcast_ref::<MdlPod>() {
            self == o
        } else {
            false
        }
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
    public_inputs: &[Target],
) -> Vec<StatementTarget> {
    let st_type = StatementTarget::from_flattened(
        params,
        &builder.constants(&type_statement().to_fields(params)),
    );

    let mut statements = vec![st_type];
    let self_id = builder.constant_value(RawValue::from(SELF.0));
    let ak_for = |b: &mut CircuitBuilder<F, D>, s: &str| {
        let key = b.constant_value(Key::from(s).raw());
        StatementArgTarget::anchored_key(b, &self_id, &key)
    };
    let ak = ak_for(builder, "pk_hash");
    let hash = builder.hash_n_to_hash_no_pad::<PoseidonHash>(public_inputs[..16].to_vec());
    let value = StatementArgTarget::literal(builder, &ValueTarget::from_slice(&hash.elements));
    let st = StatementTarget::new_native(builder, params, NativePredicate::Equal, &[ak, value]);
    statements.push(st);
    for (chunk, (name, _)) in public_inputs[16..]
        .chunks(VALUE_SIZE)
        .zip_eq(MDL_FIELDS.iter())
    {
        let ak = ak_for(builder, name);
        let value = StatementArgTarget::literal(builder, &ValueTarget::from_slice(chunk));
        let st = StatementTarget::new_native(builder, params, NativePredicate::Equal, &[ak, value]);
        statements.push(st);
    }

    statements
}

fn pk_statement(pk: &ECDSAPublicKey<P256>) -> middleware::Statement {
    let data_array: Vec<_> =
        pk.0.x
            .0
            .into_iter()
            .chain(pk.0.y.0)
            .flat_map(|x| [x as u32, (x >> 32) as u32].map(F::from_canonical_u32))
            .collect();
    let value = Value::from(TypedValue::Raw(RawValue(
        hash_n_to_hash_no_pad::<_, PoseidonPermutation<_>>(&data_array).elements,
    )));
    Statement::equal(AnchoredKey::from((SELF, "pk_hash")), value)
}

fn mdl_statements(data: &[(String, Value)]) -> impl Iterator<Item = middleware::Statement> {
    data.iter()
        .map(|(k, v)| Statement::equal(AnchoredKey::from((SELF, k)), v.clone()))
}

// compatible with the same method in-circuit (pub_self_statements_target)
fn pub_self_statements(
    pk: &ECDSAPublicKey<P256>,
    mdl_dict: &[(String, Value)],
) -> Vec<middleware::Statement> {
    [type_statement(), pk_statement(pk)]
        .into_iter()
        .chain(mdl_statements(mdl_dict))
        .collect()
}

#[cfg(test)]
pub mod tests {

    use p256::{PublicKey, elliptic_curve::sec1::ToEncodedPoint};
    use plonky2_ecdsa::{
        curve::{
            curve_types::AffinePoint,
            ecdsa::{ECDSAPublicKey, verify_message},
            p256::P256,
        },
        field::p256_base::P256Base,
    };
    use pod2::{self, middleware::VDSet};

    use super::*;
    use crate::mdlpod::parse::{scalar_from_bytes, test::cbor_parsed};

    fn public_key_from_bytes(bytes: &[u8]) -> anyhow::Result<ECDSAPublicKey<P256>> {
        let (_, pem) = x509_parser::pem::parse_x509_pem(bytes)
            .map_err(|e| anyhow!("Failed to parse PEM: {:?}", e))?;
        let (_, cert) = x509_parser::parse_x509_certificate(&pem.contents)
            .map_err(|e| anyhow!("Failed to parse certificate: {:?}", e))?;
        let pk_sec1 = cert.public_key().subject_public_key.data.as_ref();

        // Parse SEC1 encoded public key
        let pk = PublicKey::from_sec1_bytes(pk_sec1)
            .map_err(|e| anyhow!("Failed to parse public key: {}", e))?;

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

    fn extract_pk_from_cert(cert_path: &str) -> anyhow::Result<ECDSAPublicKey<P256>> {
        let pem_data = std::fs::read(cert_path)?;
        public_key_from_bytes(&pem_data)
    }

    #[test]
    fn test_verify_mdl_no_sig() -> anyhow::Result<()> {
        let mdl_data = cbor_parsed()?;
        let mut builder = CircuitBuilder::new(CircuitConfig::standard_recursion_config());
        let doc = MdlDocTarget::add_targets(&mut builder, MDL_FIELDS);
        let data = builder.build::<C>();
        let mut pw = PartialWitness::new();
        doc.set_targets(&mut pw, &mdl_data)?;
        let mut mso_padded = mdl_data.signed_message.clone();
        sha_256_pad(&mut mso_padded, MSO_MAX_BLOCKS)?;
        for (&ch_t, ch) in doc.mso.iter().zip(mso_padded) {
            pw.set_target(ch_t, F::from_canonical_u8(ch))?;
        }
        pw.set_target(
            doc.mso_len,
            F::from_canonical_usize(mdl_data.signed_message.len()),
        )?;
        let proof = data.prove(pw)?;
        data.verify(proof)
    }

    fn verify_mdl_signature(mdl_data: &MdlData, pk: &ECDSAPublicKey<P256>) -> bool {
        let digest = Sha256::digest(&mdl_data.signed_message);
        let ecdsa_msg = scalar_from_bytes(&digest);
        verify_message(ecdsa_msg, mdl_data.signature, *pk)
    }

    #[test]
    #[ignore]
    fn test_verify_mdl_with_sig() -> anyhow::Result<()> {
        let mdl_data = cbor_parsed()?;
        let pk = public_key_from_bytes(include_bytes!("../test_keys/mdl/issuer-cert.pem"))?;
        if !verify_mdl_signature(&mdl_data, &pk) {
            anyhow::bail!("Invalid signature form message");
        }
        let (target, data) = &*MDL_VERIFY_DATA;
        let mut pw = PartialWitness::new();
        target.set_targets(&mut pw, &pk, &mdl_data)?;
        let proof = data.prove(pw)?;
        data.verify(proof)
    }

    fn get_test_mdl_pod() -> anyhow::Result<(Box<dyn RecursivePod>, Params, VDSet)> {
        // Load the MDL data
        let mdl_doc = include_bytes!("../test_keys/mdl/response.cbor");

        // Extract public key from certificate
        let pk = extract_pk_from_cert("test_keys/mdl/issuer-cert.pem")?;

        // Create the MdlPod
        let params = Params {
            max_input_signed_pods: 0,
            max_public_statements: 14,
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
        let vd_set = VDSet::new(params.max_depth_mt_vds, &vds).unwrap();

        let mdl_pod = timed!("MdlPod::new", MdlPod::new(&params, &vd_set, pk, mdl_doc)?);

        mdl_pod.verify()?;

        Ok((mdl_pod, params, vd_set))
    }

    #[test]
    #[ignore]
    fn test_mdl_pod() -> anyhow::Result<()> {
        get_test_mdl_pod().map(|_| ())
    }

    #[test]
    #[ignore]
    fn test_mdl_pod_serialization() -> anyhow::Result<()> {
        let (pod, params, vd_set) = get_test_mdl_pod()?;
        let data = pod.serialize_data();
        let recovered_pod = MdlPod::deserialize_data(params, data, vd_set, pod.id())?;
        assert!(pod.equals(recovered_pod.as_ref()));
        Ok(())
    }
}
