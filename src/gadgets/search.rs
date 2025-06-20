//! Gadgets for proving that a particular substring occurs in a string.
//!
//! The implementation is based on the paper https://arxiv.org/abs/2505.13964v1.
//!
//! The search uses a hash function that is not collision resistant.  In the
//! MDL pod, we rely on the fact that the message can't easily be modified
//! because it is signed, and the substrings can't easily be modified because
//! they are hashes.

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
    plonk::{circuit_builder::CircuitBuilder, config::PoseidonGoldilocksConfig},
};

pub type F = GoldilocksField;
pub const D: usize = 2;
pub type C = PoseidonGoldilocksConfig;

pub const fn doc_len(merkle_tree_depth: usize, window_len: usize) -> usize {
    (1 << merkle_tree_depth) + window_len - 1
}

pub fn merkle_root_circuit(
    builder: &mut CircuitBuilder<F, D>,
    msg: &[Target],
    merkle_tree_depth: usize,
    window_len: usize,
) -> HashOutTarget {
    let n_merkle_leaves = 1 << merkle_tree_depth;
    let doc_len = n_merkle_leaves + window_len - 1;
    assert!(msg.len() == doc_len);
    let mut merkle_tree = vec![builder.constant_hash(Default::default()); 2 * n_merkle_leaves - 1];
    let mut hash = [builder.zero(); 4];
    let factor = builder.constant(GoldilocksField::from_canonical_u64(0x100));
    // - factor ^ (HASH_LEN / 4)
    let factor_max_power =
        builder.constant(GoldilocksField::from_canonical_u64(0xfffffffe00000002));
    let merkle_offset = n_merkle_leaves - window_len;
    for (pos, &ch) in msg.iter().enumerate() {
        let mut tmp3 = builder.mul(factor, hash[3]);
        tmp3 = builder.add(tmp3, ch);
        let mut tmp1 = hash[1];
        if pos >= window_len {
            let to_add = builder.mul(factor_max_power, msg[pos - window_len]);
            tmp1 = builder.add(tmp1, to_add);
        }
        hash = [tmp3, hash[0], tmp1, hash[2]];
        if pos >= window_len - 1 {
            merkle_tree[pos + merkle_offset] = HashOutTarget { elements: hash };
        }
    }
    for pos in (0..n_merkle_leaves - 1).rev() {
        let mut to_hash = Vec::with_capacity(8);
        to_hash.extend_from_slice(&merkle_tree[2 * pos + 1].elements);
        to_hash.extend_from_slice(&merkle_tree[2 * pos + 2].elements);
        merkle_tree[pos] = builder.hash_n_to_hash_no_pad::<PoseidonHash>(to_hash);
    }
    merkle_tree[0]
}

pub fn merkle_tree(
    msg: &[u8],
    merkle_tree_depth: usize,
    window_len: usize,
) -> MerkleTree<F, PoseidonHash> {
    let n_merkle_leaves = 1 << merkle_tree_depth;
    let doc_len = n_merkle_leaves + window_len - 1;
    assert!(msg.len() == doc_len);
    let mut leaves = Vec::with_capacity(n_merkle_leaves);
    let mut hash = [GoldilocksField::ZERO; 4];
    let factor = GoldilocksField::from_canonical_u64(0x100);
    let factor_max_power = GoldilocksField::from_canonical_u64(0xfffffffe00000002);
    for (pos, &ch) in msg.iter().enumerate() {
        let tmp3 = factor * hash[3] + GoldilocksField::from_canonical_u8(ch);
        let mut tmp1 = hash[1];
        if pos >= window_len {
            tmp1 += factor_max_power * GoldilocksField::from_canonical_u8(msg[pos - window_len]);
        }
        hash = [tmp3, hash[0], tmp1, hash[2]];
        if pos >= window_len - 1 {
            leaves.push(hash.to_vec())
        }
    }
    MerkleTree::new(leaves, 0)
}

pub fn window_hash_circuit(builder: &mut CircuitBuilder<F, D>, window: &[Target]) -> HashOutTarget {
    let mut hash = [builder.zero(); 4];
    let factor = builder.constant(GoldilocksField::from_canonical_u64(0x100));
    for &ch in window.iter() {
        let mut tmp3 = builder.mul(factor, hash[3]);
        tmp3 = builder.add(tmp3, ch);
        hash = [tmp3, hash[0], hash[1], hash[2]];
    }
    HashOutTarget { elements: hash }
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

    pub fn set_targets_from_substring(
        &self,
        pw: &mut PartialWitness<F>,
        msg: &[u8],
        substring: &[u8],
        tree: &MerkleTree<F, PoseidonHash>,
    ) -> anyhow::Result<()> {
        let index = memchr::memmem::find(msg, substring)
            .ok_or_else(|| anyhow::anyhow!("Substring not found"))?;
        self.set_targets_from_index(pw, msg, index, tree)
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
        for (n, &t) in self.index_bits.iter().enumerate() {
            pw.set_bool_target(t, (index >> n) & 1 != 0)?;
        }
        Ok(())
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

    use super::{C, LookupTarget, merkle_root_circuit, merkle_tree};

    pub const MERKLE_TREE_DEPTH: usize = 12;
    pub const MERKLE_LEAVES: usize = 1 << MERKLE_TREE_DEPTH;
    pub const WINDOW_LEN: usize = 34;
    pub const DOC_LENGTH: usize = MERKLE_LEAVES + WINDOW_LEN - 1;

    #[test]
    fn test_merkle_root() -> anyhow::Result<()> {
        let mut msg = [0u8; DOC_LENGTH];
        OsRng.fill_bytes(&mut msg);
        let tree = merkle_tree(&msg, MERKLE_TREE_DEPTH, WINDOW_LEN);
        let merkle_root = tree.cap.0[0];
        let mut builder = CircuitBuilder::new(CircuitConfig::standard_recursion_config());
        let msg_t = builder.add_virtual_targets(DOC_LENGTH);
        let merkle_root_t =
            merkle_root_circuit(&mut builder, &msg_t, MERKLE_TREE_DEPTH, WINDOW_LEN);
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
        let mut msg = [0u8; DOC_LENGTH];
        OsRng.fill_bytes(&mut msg);
        let tree = merkle_tree(&msg, MERKLE_TREE_DEPTH, WINDOW_LEN);
        let merkle_root = tree.cap.0[0];
        let mut builder = CircuitBuilder::new(CircuitConfig::standard_recursion_config());
        let msg_t = builder.add_virtual_targets(DOC_LENGTH);
        let merkle_root_t =
            merkle_root_circuit(&mut builder, &msg_t, MERKLE_TREE_DEPTH, WINDOW_LEN);
        let lookups: Vec<_> = (0..40)
            .map(|_| LookupTarget::new(&mut builder, MERKLE_TREE_DEPTH, WINDOW_LEN))
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
            let idx = OsRng.gen_range(0..MERKLE_LEAVES);
            l.set_targets_from_substring(&mut pw, &msg, &msg[idx..idx + WINDOW_LEN], &tree)?;
        }
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof)
    }
}
