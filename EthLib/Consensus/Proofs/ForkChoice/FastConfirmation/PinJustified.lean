module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.CheckpointConsistency

/-!
# The pin's finalized block is on the justified chain of an honest store

The pin of a fast-confirmation call reads the finalized block of the call's target state.

A counting state on another branch must pass through that block.

This file shows that, from the two checkpoint facts of the honest stores, with no new assumption.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}

/-- The finalized checkpoint of the call's target state is on the justified chain of another store.

The caller's store holds the target block's state, and its head leads to that block.

The head reads the store's finalized block, since it is a viable leaf, or the justified block.

So the target block reads that finalized block, and it reads the target state's finalized block.

The other store's justified chain reads the caller's finalized block, as the finality fact gives.

The two stores agree on their blocks, so the earlier read passes to the other store. -/
private theorem pin_finRead {A B : Store preset fork}
    (reachedA : Store.Reachable config anchorState anchorBlock A)
    (reachedB : Store.Reachable config anchorState anchorBlock B)
    (preGloas : fork < .glamsterdam) (sound : Invariant anchorState)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (params : DirectSafety.Parameters preset) (nonzero : HeldStateRootsNonzero A)
    (unknownParent : A.blocks[anchorBlock.parentRoot]? = none)
    (same : ∀ (r : Root) (b c : BeaconBlock preset fork),
      A.blocks[r]? = some b → B.blocks[r]? = some c → b = c)
    (chain : A.getCheckpointBlock A.justifiedCheckpoint.root A.finalizedCheckpoint.epoch =
      .ok A.finalizedCheckpoint.root)
    (finality : A.finalizedCheckpoint.epoch ≤ B.justifiedCheckpoint.epoch →
      B.getCheckpointBlock B.justifiedCheckpoint.root A.finalizedCheckpoint.epoch =
        .ok A.finalizedCheckpoint.root)
    {head : ForkChoiceNode} (headOk : A.getHead config = .ok head)
    {epoch : Epoch} {target : Checkpoint}
    (epochOk : A.getCurrentStoreEpoch config = .ok epoch)
    (targetOk : A.getCurrentTarget config head.root = .ok target)
    {anc : BeaconState preset fork} (ancOk : A.blockStates[target.root]? = some anc)
    (later : getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch)
    (finalizedLe : A.finalizedCheckpoint.epoch ≤ epoch)
    (justifiedLe : A.finalizedCheckpoint.epoch ≤ B.justifiedCheckpoint.epoch) :
    B.getCheckpointBlock B.justifiedCheckpoint.root anc.finalizedCheckpoint.epoch =
      .ok anc.finalizedCheckpoint.root := by
  obtain ⟨epoch', block, epochOk', targetRead, rfl⟩ := Store.getCurrentTarget_eq_ok_iff.mp targetOk
  obtain rfl : epoch' = epoch := Except.ok.inj (epochOk'.symm.trans epochOk)
  have ancLe : anc.finalizedCheckpoint.epoch ≤ A.finalizedCheckpoint.epoch :=
    ((reachedA.ordered_finalized sound).2) ancOk
  -- The head reads the finalized block, as a viable leaf or as the justified block.
  have headRead : A.getCheckpointBlock head.root A.finalizedCheckpoint.epoch =
      .ok A.finalizedCheckpoint.root := by
    rcases Store.getHead_viable headOk with viable | ⟨-, same⟩
    · exact reachedA.isViableLeaf_finalized (UInt64.le_of_eq anchorSlot) unknownParent viable
    · rw [congrArg ForkChoiceNode.root same]
      exact chain
  -- The target block reads it too, and so it reads the finalized block of the target state.
  have targetFinalized : A.getCheckpointBlock block A.finalizedCheckpoint.epoch =
      .ok A.finalizedCheckpoint.root :=
    (Store.getCheckpointBlock_trans preGloas targetRead finalizedLe) ▸ headRead
  -- The block of the target state reads the finalized block of that state.
  obtain ⟨-, -, -, ancReads⟩ :=
    Store.Reachable.finalizedState_of_blockState reachedA sound anchorSlot params nonzero ancOk
  have ancRead := ancReads later
  have middle : A.getCheckpointBlock A.finalizedCheckpoint.root anc.finalizedCheckpoint.epoch =
      .ok anc.finalizedCheckpoint.root := by
    rw [← Store.getCheckpointBlock_trans preGloas targetFinalized ancLe]
    exact ancRead
  -- The other store's justified chain reads the caller's finalized block, which it holds.
  have justifiedRead := finality justifiedLe
  obtain ⟨-, finalizedBlock, -, finalizedHeld, -, -⟩ :=
    Store.isAncestor_of_getCheckpointBlock preGloas justifiedRead
  obtain ⟨boundary, checkpointBlock, boundaryOk, checkpointHeld, checkpointLe, -⟩ :=
    Store.isAncestor_of_getCheckpointBlock preGloas ancRead
  have aboveAnchor : anchorBlock.slot ≤ boundary :=
    UInt64.le_trans (reachedA.anchorSlot_le (UInt64.le_of_eq anchorSlot) checkpointHeld)
      checkpointLe
  have received := Store.getCheckpointBlock_of_same_blocks reachedB same boundaryOk aboveAnchor
    ⟨finalizedBlock, finalizedHeld⟩ middle
  rw [Store.getCheckpointBlock_trans preGloas justifiedRead ancLe]
  exact received

end EthLib.Consensus.Models.Network
