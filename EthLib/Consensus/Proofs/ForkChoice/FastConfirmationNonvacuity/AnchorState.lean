module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Body
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Certificates
-- These equations expose SSZ's mutual recursion to the certificate evaluator.
import all EthLib.Serialization.Ssz.Merkle.Merkleize
import all EthLib.Serialization.Ssz.Codec.Root
import all EthLib.Serialization.Ssz.Codec.Serialize

/-! Kernel certificate for the five-validator witness's concrete genesis state.

This state root is nonzero; a confirming execution needs further certificates. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.FiveValidatorWitness

open Base Serialization.Ssz
open scoped NonvacuityCertificates

attribute [local cbv_eval] hashTreeRootAtM.eq_def depthFor.eq_def SszType.hashTreeRoot_eq
  zeroSubtree_eq layoutChunksAtM.eq_def serialize.eq_def serializeSequence.eq_def
  serializeStruct.eq_def serializeEach.eq_def serializeEachFrom.eq_def serializeFields.eq_def
  serializeFieldsFrom.eq_def

/-- The root certified below for the five-validator state with the certified body root. -/
def stateRoot : Root := ⟨#[0, 37, 86, 15, 195, 37, 68, 199, 169, 148, 187, 41, 148, 247, 69, 176,
  140, 110, 165, 78, 4, 31, 167, 109, 249, 126, 200, 58, 172, 5, 30, 84], by decide⟩

-- These normal forms avoid carrying the state constructor through every reduction step.

-- The two reflexivity proofs below check them against the existing typed SSZ definitions.
private def stateValue (root : Root) : Value :=
  let zero := Value.bytes (Array.replicate 32 0)
  let checkpoint := Value.seq [.uint 0, zero]
  let validatorValue (balance : Nat) := Value.seq
    [.bytes (Array.replicate 48 0), zero, .uint balance, .bool false, .uint 0, .uint 0,
      .uint 18446744073709551615, .uint 18446744073709551615]
  .seq [.uint 0, zero, .uint 0,
    .seq [.bytes #[0, 0, 0, 1], .bytes #[0, 0, 0, 1], .uint 0],
    .seq [.uint 0, .uint 0, zero, zero, .bytes root.toArray],
    .seq (List.replicate 8 zero), .seq (List.replicate 8 zero), .seq [],
    .seq [zero, .uint 0, zero], .seq [], .uint 0,
    .seq ([200, 200, 200, 100, 200].map validatorValue),
    .seq ([200, 200, 200, 100, 200].map Value.uint),
    .seq (List.replicate 8 zero), .seq (List.replicate 8 (.uint 0)), .seq [], .seq [],
    .bits #[false, false, false, false], checkpoint, checkpoint, checkpoint]

private def stateDesc : Desc :=
  let uint := Desc.uint 8
  let root := Desc.byteVector 32
  let checkpoint := Desc.container ["epoch", "root"] [uint, root]
  let eth1 := Desc.container ["deposit_root", "deposit_count", "block_hash"] [root, uint, root]
  let pending := Desc.container ["aggregation_bits", "data", "inclusion_delay", "proposer_index"]
    [.bitList 2048,
      .container ["slot", "index", "beacon_block_root", "source", "target"]
        [uint, uint, root, checkpoint, checkpoint], uint, uint]
  .container
    ["genesis_time", "genesis_validators_root", "slot", "fork", "latest_block_header",
      "block_roots", "state_roots", "historical_roots", "eth1_data", "eth1_data_votes",
      "eth1_deposit_index", "validators", "balances", "randao_mixes", "slashings",
      "previous_epoch_attestations", "current_epoch_attestations", "justification_bits",
      "previous_justified_checkpoint", "current_justified_checkpoint", "finalized_checkpoint"]
    [uint, root, uint,
      .container ["previous_version", "current_version", "epoch"]
        [.byteVector 4, .byteVector 4, uint],
      .container ["slot", "proposer_index", "parent_root", "state_root", "body_root"]
        [uint, uint, root, root, root],
      .vector root 8, .vector root 8, .list root 16777216, eth1, .list eth1 16, uint,
      .list (.container ["pubkey", "withdrawal_credentials", "effective_balance", "slashed",
        "activation_eligibility_epoch", "activation_epoch", "exit_epoch", "withdrawable_epoch"]
        [.byteVector 48, root, uint, .bool, uint, uint, uint, uint]) 8,
      .list uint 8, .vector root 8, .vector uint 8, .list pending 512, .list pending 512,
      .bitVector 4, checkpoint, checkpoint, checkpoint]

set_option maxRecDepth 10000 in
private theorem state_value (root : Root) : SszType.toValue (state root) = stateValue root := by
  rfl

set_option maxRecDepth 10000 in
private theorem state_desc : SszType.desc (BeaconState preset .phase0) = stateDesc := by rfl

set_option Elab.async false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
set_option cbv.maxSteps 10000000 in
/-- The actual initial state has the displayed root, with no hash assumption. -/
theorem state_root : SszType.hashTreeRoot (state bodyRoot) = .ok stateRoot := by
  let : NeZero preset.BYTES_PER_LOGS_BLOOM.toNat := ⟨by decide⟩
  let : NeZero preset.SYNC_COMMITTEE_SIZE.toNat := ⟨by decide⟩
  let : NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat := ⟨by decide⟩
  let : NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat := ⟨by decide⟩
  let : NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat := ⟨by decide⟩
  let : NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat := ⟨by decide⟩
  let : NeZero ((preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat) :=
    ⟨by decide⟩
  let : NeZero preset.PTC_SIZE.toNat := ⟨by decide⟩
  let : NeZero (2 * preset.SLOTS_PER_EPOCH.toNat) := ⟨by decide⟩
  let : NeZero ((preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat) :=
    ⟨by decide⟩
  let : NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat := ⟨by decide⟩
  rw [SszType.hashTreeRoot_eq, state_value, state_desc]
  cbv

/-- The anchor's state root is nonzero because its second byte is 37. -/
theorem stateRoot_ne_zero : stateRoot ≠ Vector.replicate 32 0 := by decide

end EthLib.Consensus.Models.Network.FiveValidatorWitness
