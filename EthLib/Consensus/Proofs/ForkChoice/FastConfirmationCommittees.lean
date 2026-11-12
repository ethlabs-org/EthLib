module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSupport
import EthLib.Consensus.Proofs.ForkChoice.BlockStates

/-!
# Statements: the committees of a vote for a sibling are those of the head

This file states two facts that the walk of the fast confirmation rule needs.

The rule is that of [arXiv 2405.00549v4][fcr].

The proofs are placeholders.

Both statements are proof obligations, not assumptions.

A store caps the weight of a sibling of a confirmed block by the committees of its head.

The slots of those committees run from the parent of the block to the current one, both excluded.

A vote counted for a sibling was checked against the committees of its target state.

The target is of an epoch from that of the parent to the current one.

For the current epoch and the one before, `CommitteesFollow.common` relates the two committees.

The epoch two before the current one is at most the epoch of the parent.

There the target is the checkpoint of the chain of the head, so the head reached it by a run.

The first statement gives the committees of that run.

The second statement joins the cases.

[fcr]: https://arxiv.org/abs/2405.00549v4
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- A checkpoint on the chain of a head keeps its committees in the state of the head.

The checkpoint is cached in an honest store, and the head is a block of that store.

The checkpoint is the checkpoint block of the head at its epoch, after the anchor.

The head is at the start of that epoch or later.

The epoch read is at most the lookahead after the checkpoint, and its activity is fixed there.

The state of the head has not yet overwritten the RANDAO mix that the seed of the epoch reads.

The proof reconstructs the cached state with `Store.Reachable.blockState_history_run`.

That run starts at the checkpoint state, so `RunKept.committeesKept` applies. -/
theorem Execution.committeesKept_of_head_checkpoint {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ}
    (nonzero : ∀ (r : Root) (b : BeaconBlock preset fork),
      ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    {head : Root} {headState targetState : BeaconState preset fork} {target : Checkpoint}
    {boundary : Slot} {epoch : Epoch}
    (headFound : ((e.world k).state w).blockStates[head]? = some headState)
    (cached : ((e.world k).state w).checkpointStates[target]? = some targetState)
    (onChain : ((e.world k).state w).getCheckpointBlock head target.epoch = .ok target.root)
    (boundaryOk : computeStartSlotAtEpoch preset target.epoch = .ok boundary)
    (afterAnchor : anchorState.slot ≤ boundary) (reached : boundary ≤ headState.slot)
    (above : target.epoch ≤ epoch)
    (final : epoch.toNat ≤ target.epoch.toNat + preset.MIN_SEED_LOOKAHEAD.toNat)
    (fixed : epoch ≤ activityFixedEpoch targetState)
    (inRing : (getCurrentEpoch headState).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
      epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) :
    CommitteesKept epoch targetState headState ∧
      getCommitteeCountPerSlot headState epoch = getCommitteeCountPerSlot targetState epoch := by
  sorry

variable [DecidablePred (· ∈ J)]

/-- A validator counted for a child of a parent is an active member of the window of the head.

The store is that of an honest validator, up to date, and its parents are below its blocks.

The head of the store descends from the parent.

The current epoch is at most two epochs after the epoch of the parent.

The window is the committees of the head over the slots between the parent and the current slot.

The validator is active and not slashed in the justified state, and its vote counts for the child.

Then it is an active member of the window in that state.

The vote is of a slot of the window, by the facts of `VoteOrigin`.

For a target of the current epoch or the one before, `CommitteesFollow.common` gives the committee.

For a target two epochs before, the target is on the chain of the head.

`Execution.committeesKept_of_head_checkpoint` gives the committee there.

The preset bounds are sufficient for this argument; they are not claimed to be necessary. -/
theorem Execution.mem_activeMembers_of_sibling_vote {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) (preGloas : fork < .glamsterdam)
    (lookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat ∧ 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat ∧
      preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (committees : CommitteesFollow e)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ}
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (lower : ((e.world k).state w).ParentsBelow)
    (nonzero : ∀ (r : Root) (b : BeaconBlock preset fork),
      ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    {head : ForkChoiceNode} {state : BeaconState preset fork}
    {block parentBlock childBlock : BeaconBlock preset fork} {root : Root}
    {current last first : Slot} {epoch : Epoch} {window : Std.TreeSet ValidatorIndex}
    (headOk : ((e.world k).state w).getHead config = .ok head)
    (stateOk : ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint =
      .ok state)
    (blockOk : ((e.world k).state w).block root = .ok block)
    (parentOk : ((e.world k).state w).block block.parentRoot = .ok parentBlock)
    (currentOk : ((e.world k).state w).getCurrentSlot config = .ok current)
    (epochOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch)
    (age : epoch.toNat ≤ (computeEpochAtSlot preset parentBlock.slot).toNat + 2)
    (firstOk : addChecked parentBlock.slot 1 = .ok first)
    (lastOk : subChecked current 1 = .ok last)
    (windowOk : ((e.world k).state w).getCommitteesBetweenSlots head.root first last = .ok window)
    (headAbove : ((e.world k).state w).isAncestor head ⟨block.parentRoot, .pending⟩ = .ok true)
    {c : ForkChoiceNode} {v : ValidatorIndex}
    (childKnown : ((e.world k).state w).blocks[c.root]? = some childBlock)
    (child : childBlock.parentRoot = block.parentRoot)
    (counted : ((e.world k).state w).voteCountsFor c v = true)
    (active : v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset) :
    v ∈ Store.activeMembers state window := by
  sorry

end EthLib.Consensus.Models.Network
