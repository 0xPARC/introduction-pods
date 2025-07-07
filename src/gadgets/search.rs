//! Gadgets for proving that a particular substring occurs in a string.
//!
//! The implementation uses the Rabin-Karp algorithm with a Merkle tree, as
//! suggested in the paper https://arxiv.org/abs/2505.13964v1.
//!
//! The search uses a rolling hash function, which is not collision resistant.  In the
//! MDL pod, we rely on the fact that the message can't easily be modified
//! because it is signed, and the substrings can't easily be modified because
//! they are hashes.

use num::traits::Euclid;
use plonky2::{
    field::{goldilocks_field::GoldilocksField, types::Field},
    hash::{
        hash_types::HashOutTarget, merkle_proofs::MerkleProofTarget, merkle_tree::MerkleTree,
        poseidon::PoseidonHash,
    },
    iop::{
        target::{BoolTarget, Target},
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::circuit_builder::CircuitBuilder,
};

use crate::gadgets::bits_bytes::set_bits_target_le;

pub type F = GoldilocksField;
pub const D: usize = 2;

fn assert_len_ok(msg_len: usize, window_len: usize, n_merkle_leaves: usize) {
    assert!(msg_len >= window_len);
    assert!(msg_len + 1 - window_len <= n_merkle_leaves);
}

pub fn merkle_leaves_rabin_karp_circuit(
    builder: &mut CircuitBuilder<F, D>,
    msg: &[Target],
    merkle_tree_depth: usize,
    window_len: usize,
) -> Vec<HashOutTarget> {
    let n_merkle_leaves = 1 << merkle_tree_depth;
    assert_len_ok(msg.len(), window_len, n_merkle_leaves);
    let mut merkle_leaves = Vec::with_capacity(n_merkle_leaves);
    let mut hash = [builder.zero(); 4];
    let factor = GoldilocksField::from_canonical_u64(0x100);
    let factor_t = builder.constant(GoldilocksField::from_canonical_u64(0x100));
    let (max_exp, sub_pos) = (window_len - 1).div_rem_euclid(&4);
    let factor_max_power = -factor.exp_u64(max_exp as u64);
    let factor_max_power_t = builder.constant(factor_max_power);
    for (pos, &ch) in msg.iter().enumerate() {
        if pos >= window_len {
            hash[sub_pos] =
                builder.mul_add(factor_max_power_t, msg[pos - window_len], hash[sub_pos]);
        }
        let tmp = builder.mul_add(factor_t, hash[3], ch);
        hash = [tmp, hash[0], hash[1], hash[2]];
        if pos >= window_len - 1 {
            merkle_leaves.push(HashOutTarget { elements: hash });
        }
    }
    merkle_leaves.resize(n_merkle_leaves, *merkle_leaves.last().unwrap());
    merkle_leaves
}

pub fn merkle_root_circuit(
    builder: &mut CircuitBuilder<F, D>,
    leaves: &[HashOutTarget],
) -> HashOutTarget {
    assert!(!leaves.is_empty());
    if leaves.len() == 1 {
        leaves[0]
    } else {
        let split_pos = leaves.len() / 2;
        let left = merkle_root_circuit(builder, &leaves[..split_pos]);
        let right = merkle_root_circuit(builder, &leaves[split_pos..]);
        let mut hashes = Vec::with_capacity(8);
        hashes.extend_from_slice(&left.elements);
        hashes.extend_from_slice(&right.elements);
        builder.hash_n_to_hash_no_pad::<PoseidonHash>(hashes)
    }
}

pub fn merkle_root_rabin_karp_circuit(
    builder: &mut CircuitBuilder<F, D>,
    msg: &[Target],
    merkle_tree_depth: usize,
    window_len: usize,
) -> HashOutTarget {
    let leaves = merkle_leaves_rabin_karp_circuit(builder, msg, merkle_tree_depth, window_len);
    merkle_root_circuit(builder, &leaves)
}

pub fn merkle_tree(
    msg: &[u8],
    merkle_tree_depth: usize,
    window_len: usize,
) -> MerkleTree<F, PoseidonHash> {
    let n_merkle_leaves = 1 << merkle_tree_depth;
    assert_len_ok(msg.len(), window_len, n_merkle_leaves);
    let mut leaves = Vec::with_capacity(n_merkle_leaves);
    let mut hash = [GoldilocksField::ZERO; 4];
    let factor = GoldilocksField::from_canonical_u64(0x100);
    let (max_exp, sub_pos) = (window_len - 1).div_rem_euclid(&4);
    let factor_max_power = -factor.exp_u64(max_exp as u64);
    for (pos, &ch) in msg.iter().enumerate() {
        if pos >= window_len {
            hash[sub_pos] +=
                factor_max_power * GoldilocksField::from_canonical_u8(msg[pos - window_len]);
        }
        let tmp = factor * hash[3] + GoldilocksField::from_canonical_u8(ch);
        hash = [tmp, hash[0], hash[1], hash[2]];
        if pos >= window_len - 1 {
            leaves.push(hash.to_vec())
        }
    }
    leaves.resize(n_merkle_leaves, leaves.last().unwrap().clone());
    MerkleTree::new(leaves, 0)
}

pub fn window_hash_circuit(builder: &mut CircuitBuilder<F, D>, window: &[Target]) -> HashOutTarget {
    merkle_root_rabin_karp_circuit(builder, window, 0, window.len())
}

pub struct LookupTarget {
    pub data: Vec<Target>,
    pub index_bits: Vec<BoolTarget>,
    pub proof: MerkleProofTarget,
    pub root: HashOutTarget,
}

impl LookupTarget {
    pub fn new(
        builder: &mut CircuitBuilder<F, D>,
        merkle_tree_depth: usize,
        window_len: usize,
    ) -> Self {
        let data = builder.add_virtual_targets(window_len);
        let hash = window_hash_circuit(builder, &data);
        let index_bits: Vec<_> = (0..merkle_tree_depth)
            .map(|_| builder.add_virtual_bool_target_safe())
            .collect();
        let proof = MerkleProofTarget {
            siblings: builder.add_virtual_hashes(merkle_tree_depth),
        };
        let root = builder.add_virtual_hash();
        builder.verify_merkle_proof::<PoseidonHash>(
            hash.elements.to_vec(),
            &index_bits,
            root,
            &proof,
        );
        LookupTarget {
            data,
            index_bits,
            proof,
            root,
        }
    }

    pub fn set_targets_from_index(
        &self,
        pw: &mut PartialWitness<F>,
        msg: &[u8],
        index: usize,
        tree: &MerkleTree<F, PoseidonHash>,
    ) -> anyhow::Result<()> {
        for (&ch_t, &ch) in self.data.iter().zip(msg.iter().skip(index)) {
            pw.set_target(ch_t, GoldilocksField::from_canonical_u8(ch))?;
        }
        let proof = tree.prove(index);
        for (&s_t, &s) in self.proof.siblings.iter().zip(proof.siblings.iter()) {
            pw.set_hash_target(s_t, s)?;
        }
        set_bits_target_le(pw, &self.index_bits, index as u64)
    }
}

#[cfg(test)]
mod test {
    use plonky2::{
        field::{goldilocks_field::GoldilocksField, types::Field},
        iop::witness::{PartialWitness, WitnessWrite},
        plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig},
    };
    use rand::{Rng, RngCore, rngs::OsRng};

    use super::{LookupTarget, merkle_tree};
    use crate::gadgets::search::merkle_root_rabin_karp_circuit;

    type C = plonky2::plonk::config::PoseidonGoldilocksConfig;
    pub const MERKLE_TREE_DEPTH: usize = 12;
    pub const DOC_LENGTH: usize = 3072;

    #[test]
    fn test_merkle_root() -> anyhow::Result<()> {
        let window_len = 34;
        let mut msg = [0u8; DOC_LENGTH];
        OsRng.fill_bytes(&mut msg);
        let tree = merkle_tree(&msg, MERKLE_TREE_DEPTH, window_len);
        let merkle_root = tree.cap.0[0];
        let mut builder = CircuitBuilder::new(CircuitConfig::standard_recursion_config());
        let msg_t = builder.add_virtual_targets(DOC_LENGTH);
        let merkle_root_t =
            merkle_root_rabin_karp_circuit(&mut builder, &msg_t, MERKLE_TREE_DEPTH, window_len);
        let mut pw = PartialWitness::new();
        for (&ch, &ch_t) in msg.iter().zip(msg_t.iter()) {
            pw.set_target(ch_t, GoldilocksField::from_canonical_u8(ch))?;
        }
        pw.set_hash_target(merkle_root_t, merkle_root)?;
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof)
    }

    #[test]
    fn test_find() -> anyhow::Result<()> {
        for window_len in 32..36 {
            let mut msg = [0u8; DOC_LENGTH];
            OsRng.fill_bytes(&mut msg);
            let tree = merkle_tree(&msg, MERKLE_TREE_DEPTH, window_len);
            let merkle_root = tree.cap.0[0];
            let mut builder = CircuitBuilder::new(CircuitConfig::standard_recursion_config());
            let msg_t = builder.add_virtual_targets(DOC_LENGTH);
            let merkle_root_t =
                merkle_root_rabin_karp_circuit(&mut builder, &msg_t, MERKLE_TREE_DEPTH, window_len);
            let lookups: Vec<_> = (0..10)
                .map(|_| LookupTarget::new(&mut builder, MERKLE_TREE_DEPTH, window_len))
                .collect();
            for l in lookups.iter() {
                builder.connect_hashes(l.root, merkle_root_t);
            }
            let mut pw = PartialWitness::new();
            for (&ch, &ch_t) in msg.iter().zip(msg_t.iter()) {
                pw.set_target(ch_t, GoldilocksField::from_canonical_u8(ch))?;
            }
            pw.set_hash_target(merkle_root_t, merkle_root)?;
            for l in lookups.iter() {
                let idx = OsRng.gen_range(0..(DOC_LENGTH - window_len + 1));
                l.set_targets_from_index(&mut pw, &msg, idx, &tree)?;
            }
            let data = builder.build::<C>();
            let proof = data.prove(pw)?;
            data.verify(proof)?;
        }
        Ok(())
    }
}
