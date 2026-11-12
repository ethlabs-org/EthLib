module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSupport
import EthLib.Consensus.Proofs.ForkChoice.BlockStates
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationResets

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

/-- The ancestor walk reconstructs a boundary state without reading the history ring. -/
private theorem checkpoint_run_of_walk {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (transitions : ∀ (root : Root) (block : BeaconBlock preset fork)
      (state : BeaconState preset fork), store.blocks[root]? = some block →
      store.blockStates[root]? = some state → block ≠ anchorBlock →
      ∃ parent signed, signed.message = block ∧
        store.blockStates[block.parentRoot]? = some parent ∧
        stateTransition config checks sources.engine parent signed true = .ok state)
    {boundary : Slot} (anchorBelow : anchorBlock.slot ≤ boundary)
    (stateBelow : anchorState.slot ≤ boundary)
    {node ancestor : ForkChoiceNode} {state : BeaconState preset fork}
    (held : store.blockStates[node.root]? = some state)
    (walk : store.getAncestor node boundary = .ok ancestor)
    (reached : boundary ≤ state.slot) :
    ∃ base middle, store.blockStates[ancestor.root]? = some base ∧
      lookaheadState config checks base boundary = .ok middle ∧
      middle.slot = boundary ∧ RunKept middle state := by
  obtain ⟨block, found⟩ := reachable.known_of_blockState held
  by_cases low : block.slot ≤ boundary
  · rw [Store.getAncestor_of_le found low] at walk
    cases walk
    have atBoundary : state.slot = boundary := by
      by_cases same : block = anchorBlock
      · obtain ⟨post, stored, initial, _⟩ := reachable.blockStatesFromParents found
        rw [held, Option.some.injEq] at stored
        subst post
        exact UInt64.le_antisymm ((initial same) ▸ stateBelow) reached
      · exact UInt64.le_antisymm ((reachable.blockState_header found held same).1 ▸ low) reached
    refine ⟨state, state, held, ?_, atBoundary, RunKept.refl _⟩
    simp [lookaheadState, atBoundary, pure, Except.pure]
  · have other : block ≠ anchorBlock := fun same => low (same ▸ anchorBelow)
    obtain ⟨parentState, signed, message, parentHeld, transition⟩ :=
      transitions node.root block state found held other
    obtain ⟨advanced, slots, _, _, processed, _⟩ := stateTransition_ok transition
    have slotEq := (reachable.blockState_header found held other).1
    -- The successful walk supplies the parent's strict slot decrease, including at the anchor.
    rw [Store.getAncestor] at walk
    split at walk
    · simp_all
    rename_i b same
    rw [found, Option.some.injEq] at same
    subst b
    simp only [low, ↓reduceIte] at walk
    split at walk
    · simp [throw, throwThe, MonadExceptOf.throw] at walk
    · rename_i parent parentFound
      split at walk
      · rename_i parentLower
        by_cases before : boundary ≤ parentState.slot
        · obtain ⟨base, middle, baseHeld, made, middleSlot, run⟩ :=
            checkpoint_run_of_walk reachable transitions anchorBelow stateBelow parentHeld walk before
          exact ⟨base, middle, baseHeld, made, middleSlot,
            run.trans (runKept_stateTransition transition)⟩
        · have parentLe : parent.slot ≤ boundary := by
            by_cases same : parent = anchorBlock
            · exact same ▸ anchorBelow
            · rw [← (reachable.blockState_header parentFound parentHeld same).1]
              exact UInt64.le_of_lt (UInt64.not_le.mp before)
          rw [Store.getAncestor_of_le parentFound parentLe] at walk
          cases walk
          obtain ⟨middle, made, middleSlot, run⟩ := lookaheadState_of_processSlots slots
            (UInt64.le_of_lt (UInt64.not_le.mp before))
            (message ▸ UInt64.not_le.mp low)
          exact ⟨parentState, middle, parentHeld, made, middleSlot,
            run.trans (runKept_processBlock processed)⟩
      · simp [throw, throwThe, MonadExceptOf.throw] at walk
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transition
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

set_option linter.unusedVariables false in
/-- A checkpoint on the chain of a head keeps its committees in the state of the head.

The checkpoint is cached in an honest store, and the head is a block of that store.

The checkpoint is the checkpoint block of the head at its epoch, after the anchor.

The head is at the start of that epoch or later.

The epoch read is at most the lookahead after the checkpoint, and its activity is fixed there.

The state of the head has not yet overwritten the RANDAO mix that the seed of the epoch reads.

The proof reconstructs the cached state along the ancestor walk, without a history-ring read.

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
  -- The ancestor walk needs neither a nonzero state root nor a lower bound on the epoch read.
  clear nonzero above
  have reachable := e.reachable
    (fun w hw => (start w hw).symm ▸ Store.Reachable.anchor anchored) k w receiver
  obtain ⟨base, slot, baseHeld, slotOk, made⟩ :=
    e.checkpointStates_fixedChecks anchored (start w receiver) cached
  have slotEq := Except.ok.inj (slotOk.symm.trans boundaryOk)
  subst slot
  unfold Store.getCheckpointBlock at onChain
  simp only [boundaryOk, Except.mapError, bind, Except.bind] at onChain
  cases walk : ((e.world k).state w).getAncestor ⟨head, .pending⟩ boundary with
  | error err => simp [walk] at onChain
  | ok ancestor =>
    simp only [walk, pure, Except.pure, Except.ok.injEq] at onChain
    obtain ⟨targetBlock, targetHeld, targetBelow⟩ := Store.getAncestor_le walk
    -- Even a malformed anchor must lie below a successful checkpoint walk.
    obtain ⟨anchorRoot, anchorHash, anchorHeld⟩ := reachable.anchor_known
    obtain ⟨_, anchorHash', _, _, _, anchorFinal, _⟩ := getForkchoiceStore_anchor anchored
    have rootEq := Except.ok.inj (anchorHash.symm.trans anchorHash')
    have anchorKnown : ((e.world k).state w).blocks[anchor.finalizedCheckpoint.root]? =
        some anchorBlock := by simpa [anchorFinal, ← rootEq] using anchorHeld
    obtain ⟨targetBlock', targetHeld', anchorLe⟩ := Store.slot_le_of_isAncestor anchorKnown
      (e.isAncestor_anchor_of_known anchored start receiver targetHeld)
    rw [targetHeld, Option.some.injEq] at targetHeld'
    subst targetBlock'
    obtain ⟨base', middle, baseHeld', made', middleSlot, run⟩ := checkpoint_run_of_walk reachable
      (fun r b s found stored other =>
        e.exists_transition_of_nonanchor_block anchored receiver (start w receiver)
          found stored other)
      (UInt64.le_trans anchorLe targetBelow) afterAnchor headFound walk reached
    rw [onChain, baseHeld, Option.some.injEq] at baseHeld'
    subst base'
    have middleEq := Except.ok.inj (made'.symm.trans made)
    subst middle
    by_cases positive : 0 < preset.SLOTS_PER_EPOCH
    · have atEpoch : getCurrentEpoch targetState = target.epoch := by
        simpa [getCurrentEpoch, middleSlot] using
          computeEpochAtSlot_computeStartSlotAtEpoch positive boundaryOk
      refine ⟨run.committeesKept (atEpoch ▸ final) fixed inRing, ?_⟩
      unfold getCommitteeCountPerSlot
      rw [run.active.getActiveValidatorIndices_eq fixed]
    · have zero : preset.SLOTS_PER_EPOCH = 0 := by
        have := UInt64.not_lt.mp positive
        exact UInt64.le_antisymm this UInt64.zero_le
      constructor
      · intro duty index atEpoch
        have epochZero : epoch = 0 := by simpa [computeEpochAtSlot, zero] using atEpoch.symm
        exact run.committeesKept (by rw [epochZero]; exact Nat.zero_le _) fixed inRing
          duty index atEpoch
      · simp [getCommitteeCountPerSlot, committeeCountOf, zero]

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
