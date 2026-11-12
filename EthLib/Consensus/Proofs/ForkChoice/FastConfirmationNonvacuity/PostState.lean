module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.FirstBlock
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Certificates
-- Reuse the checked state descriptor without exposing it as a witness API.
import all EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.AnchorState
-- These equations expose SSZ's mutual recursion to the certificate evaluator.
import all EthLib.Serialization.Ssz.Merkle.Merkleize
import all EthLib.Serialization.Ssz.Codec.Root
import all EthLib.Serialization.Ssz.Codec.Serialize

/-! Kernel certificate for the state after the witness's slot-one block. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.FiveValidatorWitness

open Base Serialization.Ssz
open scoped NonvacuityCertificates

attribute [local cbv_eval] hashTreeRootAtM.eq_def depthFor.eq_def SszType.hashTreeRoot_eq
  zeroSubtree_eq layoutChunksAtM.eq_def serialize.eq_def serializeSequence.eq_def
  serializeStruct.eq_def serializeEach.eq_def serializeEachFrom.eq_def serializeFields.eq_def
  serializeFieldsFrom.eq_def

/-- The post-state root, certified by `post_root`. -/
def postRoot : Root := ⟨#[45, 83, 186, 136, 34, 222, 78, 249, 102, 21, 11, 157, 143, 11, 68, 204,
  241, 162, 23, 220, 223, 203, 150, 107, 3, 70, 5, 23, 3, 92, 110, 109], by decide⟩

-- A compact normal form avoids repeatedly reducing the nested state updates.
private def postValue : Value :=
  let zero := Value.bytes (Array.replicate 32 0)
  let checkpoint := Value.seq [.uint 0, zero]
  let eth1 := Value.seq [zero, .uint 0, zero]
  let validatorValue (balance : Nat) := Value.seq
    [.bytes (Array.replicate 48 0), zero, .uint balance, .bool false, .uint 0, .uint 0,
      .uint 18446744073709551615, .uint 18446744073709551615]
  .seq [.uint 0, zero, .uint 1,
    .seq [.bytes #[0, 0, 0, 1], .bytes #[0, 0, 0, 1], .uint 0],
    .seq [.uint 1, .uint 0, .bytes anchorRoot.toArray, zero, .bytes bodyRoot.toArray],
    .seq (.bytes anchorRoot.toArray :: List.replicate 7 zero),
    .seq (.bytes stateRoot.toArray :: List.replicate 7 zero), .seq [],
    eth1, .seq [eth1], .uint 0,
    .seq ([200, 200, 200, 100, 200].map validatorValue),
    .seq ([200, 200, 200, 100, 200].map Value.uint),
    .seq (.bytes revealMix.toArray :: List.replicate 7 zero),
    .seq (List.replicate 8 (.uint 0)), .seq [], .seq [],
    .bits #[false, false, false, false], checkpoint, checkpoint, checkpoint]

set_option maxRecDepth 10000 in
private theorem post_value : SszType.toValue postState = postValue := by rfl

set_option Elab.async false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
set_option cbv.maxSteps 10000000 in
/-- The state actually produced by the first block has the displayed root. -/
theorem post_root : SszType.hashTreeRoot postState = .ok postRoot := by
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
  rw [SszType.hashTreeRoot_eq, post_value, state_desc]
  cbv

/-- The post-state root is nonzero, as required for a held block's state. -/
theorem postRoot_ne_zero : postRoot ≠ Vector.replicate 32 0 := by decide

end EthLib.Consensus.Models.Network.FiveValidatorWitness
