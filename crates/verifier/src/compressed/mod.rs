pub mod types;

use alloc::borrow::Borrow;
use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::string::String;

use itertools::Itertools;
use p3_baby_bear::BabyBear;
use p3_field::AbstractField;
use p3_field::PrimeField32;
use p3_symmetric::CryptographicHasher;
use serde::{Deserialize, Serialize};
use sp1_core_machine::{reduce::SP1ReduceProof, SP1_CIRCUIT_VERSION};
use sp1_primitives::io::SP1PublicValues;
use sp1_recursion_circuit::hash::FieldHasher;
use sp1_recursion_core::{
    air::{RecursionPublicValues, NUM_PV_ELMS_TO_HASH},
    machine::RecursionAir,
};
use sp1_stark::{air::PublicValues, Word};
use sp1_stark::{
    baby_bear_poseidon2::BabyBearPoseidon2, InnerHash, MachineProof, MachineVerificationError,
    StarkGenericConfig, StarkMachine, DIGEST_SIZE,
};

pub use crate::compressed::types::*;

pub type CoreSC = BabyBearPoseidon2;

pub type InnerSC = BabyBearPoseidon2;

type CompressAir<F> = RecursionAir<F, COMPRESS_DEGREE>;
const COMPRESS_DEGREE: usize = 3;

struct CpuProver<SC: StarkGenericConfig, A> {
    machine: StarkMachine<SC, A>,
}

pub struct CompressVerifier {
    compress_prover: CpuProver<InnerSC, CompressAir<<InnerSC as StarkGenericConfig>::Val>>,
    allowed_vk_map: BTreeMap<<InnerSC as FieldHasher<BabyBear>>::Digest, usize>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SP1CompressedBundle {
    pub proof: SP1ReduceProof<InnerSC>,
    pub public_values: SP1PublicValues,
    pub sp1_version: String,
}

impl CompressVerifier {
    pub fn new() -> Self {
        let machine = CompressAir::compress_machine(InnerSC::default());
        let allowed_vk_map: BTreeMap<[BabyBear; DIGEST_SIZE], usize> =
            bincode::deserialize(include_bytes!("../../../prover/vk_map.bin")).unwrap();
        Self { compress_prover: CpuProver { machine }, allowed_vk_map }
    }

    pub fn verify_compressed(
        &self,
        bundle: &SP1CompressedBundle,
        vk: &SP1VerifyingKey,
    ) -> Result<(), MachineVerificationError<CoreSC>> {
        if bundle.sp1_version != SP1_CIRCUIT_VERSION {
            return Err(MachineVerificationError::EmptyProof);
        }

        let proof = &bundle.proof;

        let public_values: &PublicValues<Word<_>, _> =
            proof.proof.public_values.as_slice().borrow();

        // Get the committed value digest bytes.
        let committed_value_digest_bytes = public_values
            .committed_value_digest
            .iter()
            .flat_map(|w| w.0.iter().map(|x| x.as_canonical_u32() as u8))
            .collect_vec();

        // Make sure the committed value digest matches the public values hash.
        for (a, b) in committed_value_digest_bytes.iter().zip_eq(bundle.public_values.hash()) {
            if *a != b {
                return Err(MachineVerificationError::InvalidPublicValues(
                    "committed value digest doesn't match the public values hash",
                ));
            }
        }

        let SP1ReduceProof { vk: compress_vk, proof } = proof;
        let mut challenger = self.compress_prover.machine.config().challenger();
        let machine_proof = MachineProof { shard_proofs: vec![proof.clone()] };
        self.compress_prover.machine.verify(compress_vk, &machine_proof, &mut challenger)?;

        // Validate public values
        let public_values: &RecursionPublicValues<_> = proof.public_values.as_slice().borrow();
        assert_recursion_public_values_valid(self.compress_prover.machine.config(), public_values);

        if !self.allowed_vk_map.contains_key(&compress_vk.hash_babybear()) {
            return Err(MachineVerificationError::InvalidVerificationKey);
        }

        // `is_complete` should be 1. In the reduce program, this ensures that the proof is fully
        // reduced.
        if public_values.is_complete != BabyBear::one() {
            return Err(MachineVerificationError::InvalidPublicValues("is_complete is not 1"));
        }

        // Verify that the proof is for the sp1 vkey we are expecting.
        let vkey_hash = vk.hash_babybear();
        if public_values.sp1_vk_digest != vkey_hash {
            return Err(MachineVerificationError::InvalidPublicValues("sp1 vk hash mismatch"));
        }

        Ok(())
    }
}

fn recursion_public_values_digest(
    config: &InnerSC,
    public_values: &RecursionPublicValues<BabyBear>,
) -> [BabyBear; 8] {
    let hash = InnerHash::new(config.perm.clone());
    let pv_array = public_values.as_array();
    hash.hash_slice(&pv_array[0..NUM_PV_ELMS_TO_HASH])
}

fn assert_recursion_public_values_valid(
    config: &InnerSC,
    public_values: &RecursionPublicValues<BabyBear>,
) {
    let expected_digest = recursion_public_values_digest(config, public_values);
    for (value, expected) in public_values.digest.iter().copied().zip_eq(expected_digest) {
        assert_eq!(value, expected);
    }
}
