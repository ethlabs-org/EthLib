module

public import EthLib.Consensus.Proofs.ForkChoice.HonestCheckpoints
import EthLib.Consensus.Proofs.ForkChoice.BlockRuns

/-!
# Checkpoint-block lookup in honest stores

Before Gloas, descending parent slots make the ancestor walk terminate.

If its requested slot is at or above the anchor, the walk finds a checkpoint block.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J}

private theorem exists_getAncestor_of_reachable {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (aligned : anchorBlock.slot ≤ anchorState.slot)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    (preGloas : fork < .glamsterdam) {root : Root} {block : BeaconBlock preset fork}
    (known : store.blocks[root]? = some block) {slot : Slot}
    (above : anchorBlock.slot ≤ slot) :
    ∃ ancestor, store.getAncestor ⟨root, .pending⟩ slot = .ok ancestor := by
  by_cases below : block.slot ≤ slot
  · exact ⟨_, Store.getAncestor_of_le known below⟩
  · have different : block ≠ anchorBlock := by
      rintro rfl
      exact below above
    obtain ⟨_, _, _, produced⟩ := reachable.blockStatesFromParents known
    obtain ⟨_, _, _, _, _, -, parentState, _⟩ := produced different
    obtain ⟨parent, parentKnown⟩ := reachable.known_of_blockState parentState
    have lower := reachable.parentsBelow aligned unknown root block parent known parentKnown
    -- Strictly descending slots make this recursive walk finite.
    obtain ⟨ancestor, walked⟩ := exists_getAncestor_of_reachable reachable aligned unknown preGloas
      parentKnown above
    refine ⟨ancestor, ?_⟩
    rw [Store.getAncestor_step known below parentKnown lower,
      Store.parentPayloadStatus_of_lt preGloas]
    exact walked
termination_by block.slot.toNat
decreasing_by exact UInt64.lt_iff_toNat_lt.mp lower

/-- An honest store reads the checkpoint block of a held block at an epoch after the anchor's slot.

The walk stops at the first slot of the epoch, at or above the anchor. -/
theorem Execution.exists_getCheckpointBlock_of_held {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (preGloas : fork < .glamsterdam) {limit : ℕ}
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit)
    {root : Root} {block : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some block)
    {epoch : Epoch} {first : Slot} (firstOk : computeStartSlotAtEpoch preset epoch = .ok first)
    (above : anchorBlock.slot ≤ first) :
    ∃ checkpointRoot, ((e.world k).state w).getCheckpointBlock root epoch = .ok checkpointRoot := by
  have reachable := e.reachable
    (fun v member => (start v member).symm ▸ Store.Reachable.anchor anchored) k w honest
  have aligned : anchorBlock.slot ≤ anchorState.slot := anchorSlot ▸ UInt64.le_refl _
  obtain ⟨ancestor, walked⟩ := exists_getAncestor_of_reachable reachable aligned
    (anchorParent w honest k bounded) preGloas known above
  exact ⟨ancestor.root, by
    simp [Store.getCheckpointBlock, firstOk, walked, Except.mapError,
      bind, Except.bind, pure, Except.pure]⟩

end EthLib.Consensus.Models.Network
