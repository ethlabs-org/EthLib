module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.AnchorState
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Certificates
-- These equations expose SSZ's mutual recursion to the certificate evaluator.
import all EthLib.Serialization.Ssz.Merkle.Merkleize
import all EthLib.Serialization.Ssz.Codec.Root
import all EthLib.Serialization.Ssz.Codec.Serialize

/-! Kernel certificates for the five-validator witness's concrete genesis anchor.

These facts establish initialization and nonzero roots, not a confirming execution. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.FiveValidatorWitness

open Base Serialization.Ssz
open scoped NonvacuityCertificates

attribute [local cbv_eval] hashTreeRootAtM.eq_def depthFor.eq_def SszType.hashTreeRoot_eq
  zeroSubtree_eq layoutChunksAtM.eq_def serialize.eq_def serializeSequence.eq_def
  serializeStruct.eq_def serializeEach.eq_def serializeEachFrom.eq_def serializeFields.eq_def
  serializeFieldsFrom.eq_def

/-- The root of the genesis block, with the certified state root. -/
def anchorRoot : Root := ⟨#[55, 33, 215, 25, 110, 21, 184, 68, 214, 44, 44, 231, 191, 73,
  184, 207, 124, 7, 161, 74, 206, 139, 115, 214, 204, 138, 1, 138, 62, 9, 235, 207], by decide⟩

set_option Elab.async false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
set_option cbv.maxSteps 1000000 in
/-- Replacing the body by its certified root leaves only the header to hash. -/
theorem anchor_root : SszType.hashTreeRoot (anchorBlock stateRoot) = .ok anchorRoot := by
  rw [← BeaconBlock.hashTreeRoot_header (block := anchorBlock stateRoot) body_root,
    SszType.hashTreeRoot_eq]
  cbv

/-- The anchor root differs from its zero parent root. -/
theorem anchorRoot_ne_zero : anchorRoot ≠ Vector.replicate 32 0 := by decide

/-- The initialized store, written out so later state certificates need not recompute its hashes. -/
def anchor : Store preset .phase0 where
  timeMs := 0
  genesisTimeMs := 0
  justifiedCheckpoint := ⟨0, anchorRoot⟩
  finalizedCheckpoint := ⟨0, anchorRoot⟩
  unrealizedJustifiedCheckpoint := ⟨0, anchorRoot⟩
  unrealizedFinalizedCheckpoint := ⟨0, anchorRoot⟩
  proposerBoostRoot := Vector.replicate 32 0
  equivocatingIndices := []
  blocks := Std.TreeMap.empty.insert anchorRoot (anchorBlock stateRoot)
  blockStates := Std.TreeMap.empty.insert anchorRoot (state bodyRoot)
  blockTimeliness := ∅
  ptcTimeliness := fun _ => Std.TreeMap.empty.insert anchorRoot true
  checkpointStates := Std.TreeMap.empty.insert ⟨0, anchorRoot⟩ (state bodyRoot)
  latestMessages := ∅
  unrealizedJustifications := Std.TreeMap.empty.insert anchorRoot ⟨0, anchorRoot⟩
  payloads := fun _ => ∅
  payloadTimelinessVote := fun _ =>
    Std.TreeMap.empty.insert anchorRoot (Vector.replicate _ none)
  payloadDataAvailabilityVote := fun _ =>
    Std.TreeMap.empty.insert anchorRoot (Vector.replicate _ none)
  inclusionLists := fun _ => .empty
  payloadInclusionListSatisfaction := fun _ => ∅

/-- Initialization accepts the actual body, state and block roots without a hash hypothesis. -/
theorem initialized :
    getForkchoiceStore config (state bodyRoot) (anchorBlock stateRoot) = .ok anchor := by
  simp only [getForkchoiceStore, state_root, anchor_root, Except.mapError, bind, Except.bind]
  have sameRoot : (anchorBlock stateRoot).stateRoot = stateRoot := rfl
  simp only [sameRoot, ne_eq, not_true_eq_false, ↓reduceIte]
  rfl

end EthLib.Consensus.Models.Network.FiveValidatorWitness
