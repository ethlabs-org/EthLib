module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSupport
import EthLib.Consensus.Proofs.ForkChoice.BlockStates
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationResets

/-!
# Proofs: the committees of a vote for a sibling are those of the head

This file proves two facts that the walk of the fast confirmation rule needs.

The rule is that of [arXiv 2405.00549v4][fcr].

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

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
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
  have forward := e.forwardReachable
    (fun w hw => (start w hw) ▸ Store.ForwardReachable.anchor anchored) k w receiver
  have reachable := forward.reachable
  have parentHeld := Store.block_ok_iff.mp parentOk
  obtain ⟨headBlock, headHeld, parentHeadLe⟩ := Store.slot_le_of_isAncestor parentHeld headAbove
  obtain ⟨headState, headStateHeld, _⟩ := reachable.blockStatesFromParents headHeld
  have headStateOk := Store.blockState_ok_iff.mpr headStateHeld
  obtain ⟨message, supported, latest, _, supportedOk, descends⟩ :=
    Store.exists_of_voteCountsFor _ counted
  obtain ⟨attestation, rfl, origin⟩ := forward.votesHaveOrigins latest
  obtain ⟨votedBlock, votedHeld, votedLe⟩ := origin.voted
  have supportedEq : supported = ⟨attestation.data.beaconBlockRoot, .pending⟩ := by
    have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le.mpr preGloas
    simpa [Store.getSupportedNode, notGloas, LatestMessage.ofAttestation, pure, Except.pure] using
      supportedOk.symm
  subst supported
  obtain ⟨same, sameHeld, childLe⟩ := Store.slot_le_of_isAncestor childKnown descends
  rw [votedHeld, Option.some.injEq] at sameHeld
  subst same
  have parentChildLt := lower c.root childBlock parentBlock childKnown (child ▸ parentHeld)
  have parentVoteLt := UInt64.lt_of_lt_of_le parentChildLt (UInt64.le_trans childLe votedLe)
  obtain ⟨readSlot, readOk, past⟩ := origin.past
  rw [currentOk, Except.ok.injEq] at readOk
  subst readSlot
  have low : first ≤ attestation.data.slot := by
    have := (addChecked_ok_iff.mp firstOk).2
    have := UInt64.lt_iff_toNat_lt.mp parentVoteLt
    rw [UInt64.le_iff_toNat_le]
    simp only [UInt64.toNat_one] at *
    omega
  have high : attestation.data.slot ≤ last := by
    have := (subChecked_ok_iff.mp lastOk).2
    have := UInt64.lt_iff_toNat_lt.mp past
    rw [UInt64.le_iff_toNat_le]
    simp only [UInt64.toNat_one] at *
    omega
  have epochEq : epoch = computeEpochAtSlot preset current := by
    simpa [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure] using
      epochOk.symm
  have monotone {a b : Slot} (le : a ≤ b) :
      (computeEpochAtSlot preset a).toNat ≤ (computeEpochAtSlot preset b).toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp le)
  have targetPast : attestation.data.target.epoch.toNat ≤ epoch.toNat := by
    rw [origin.targetEpoch, epochEq]
    exact monotone (UInt64.le_of_lt past)
  obtain ⟨targetState, index, committee, cached, below, committeeOk, member⟩ :=
    origin.exists_mem_committee
  have kept : CommitteesKept attestation.data.target.epoch targetState headState ∧
      getCommitteeCountPerSlot headState attestation.data.target.epoch =
        getCommitteeCountPerSlot targetState attestation.data.target.epoch := by
    by_cases recent : epoch.toNat ≤ attestation.data.target.epoch.toNat + 1
    -- Both runs keep the same seed and active registry for the two recent target epochs.
    · obtain ⟨common, headRun, targetRun, final, fixed, headRing, targetRing⟩ :=
        committees.common w receiver k head headState epoch v attestation targetState
          headOk headStateOk epochOk targetPast recent origin cached
      have headKept := headRun.committeesKept final fixed headRing
      have targetKept := targetRun.committeesKept final fixed targetRing
      refine ⟨fun slot index same => (headKept slot index same).trans
        (targetKept slot index same).symm, ?_⟩
      unfold getCommitteeCountPerSlot
      rw [headRun.active.getActiveValidatorIndices_eq fixed,
        targetRun.active.getActiveValidatorIndices_eq fixed]
    -- An older target must be exactly the parent's epoch, so both chains share its checkpoint.
    · have targetEq : attestation.data.target.epoch = computeEpochAtSlot preset parentBlock.slot := by
        have := monotone (UInt64.le_of_lt parentVoteLt)
        rw [← origin.targetEpoch] at this
        apply UInt64.toNat_inj.mp
        omega
      let boundary := parentBlock.slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH
      have boundaryOk := computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) parentBlock.slot
      have targetBoundary : computeStartSlotAtEpoch preset attestation.data.target.epoch =
          .ok boundary := targetEq ▸ boundaryOk
      have boundaryLe : boundary ≤ parentBlock.slot := by
        have := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
        have := Nat.div_mul_le_self parentBlock.slot.toNat preset.SLOTS_PER_EPOCH.toNat
        dsimp [boundary]
        rw [UInt64.le_iff_toNat_le]
        simp only [computeEpochAtSlot, UInt64.toNat_div] at *
        omega
      have childCheckpoint : ((e.world k).state w).getCheckpointBlock c.root
          attestation.data.target.epoch =
          ((e.world k).state w).getCheckpointBlock block.parentRoot attestation.data.target.epoch := by
        simp only [Store.getCheckpointBlock, targetBoundary, Except.mapError, bind, Except.bind]
        rw [Store.getAncestor_of_gt (node := ⟨c.root, .pending⟩) preGloas childKnown
          (UInt64.not_le.mpr (UInt64.lt_of_le_of_lt boundaryLe parentChildLt))
          (child ▸ parentHeld) parentChildLt, child]
      have onVoted := Store.getAncestor_of_isAncestor_of_lt preGloas childKnown descends
      have votedCheckpoint : ((e.world k).state w).getCheckpointBlock
          attestation.data.beaconBlockRoot attestation.data.target.epoch =
          ((e.world k).state w).getCheckpointBlock c.root attestation.data.target.epoch := by
        simp only [Store.getCheckpointBlock, targetBoundary, Except.mapError, bind, Except.bind]
        rw [Store.getAncestor_trans (UInt64.le_trans boundaryLe
          (UInt64.le_of_lt parentChildLt)) onVoted]
        have pending := Store.getAncestor_pending_of_lt preGloas rfl onVoted
        have cEq : c = ⟨c.root, .pending⟩ := by cases c; simp_all
        rw [cEq]
      have parentCheckpoint := origin.targetRoot
      rw [votedCheckpoint, childCheckpoint] at parentCheckpoint
      have onChain := Store.getCheckpointBlock_of_isAncestor preGloas parentHeld headAbove
        targetBoundary boundaryLe parentCheckpoint
      obtain ⟨parentState, parentStateHeld, _⟩ := reachable.blockStatesFromParents parentHeld
      have parentStateSlot : parentState.slot = parentBlock.slot := by
        by_cases same : parentBlock = anchorBlock
        · obtain ⟨post, held, initial, _⟩ := reachable.blockStatesFromParents parentHeld
          rw [parentStateHeld, Option.some.injEq] at held
          subst post
          rw [initial same, same, anchorSlot]
        · exact (reachable.blockState_header parentHeld parentStateHeld same).1
      have anchorParentLe := reachable.anchorSlot_le_blockState parentStateHeld
      rw [parentStateSlot, ← anchorSlot] at anchorParentLe
      have positive : 0 < preset.SLOTS_PER_EPOCH := by
        by_contra absent
        have zero := UInt64.le_antisymm (UInt64.not_lt.mp absent) UInt64.zero_le
        simp [computeEpochAtSlot, zero] at targetEq epochEq
        simp [targetEq, epochEq] at recent
      have anchorStart := computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) anchorBlock.slot
      have aligned : anchorBlock.slot = anchorBlock.slot / preset.SLOTS_PER_EPOCH *
          preset.SLOTS_PER_EPOCH := by
        unfold isStartSlotAtEpoch computeSlotsSinceEpochStart at anchorBoundary
        rw [anchorStart] at anchorBoundary
        simp only [Except.mapError, bind, Except.bind, pure, Except.pure,
          Except.ok.injEq, decide_eq_true_eq] at anchorBoundary
        have zero := congrArg UInt64.toNat anchorBoundary
        simp only [UInt64.toNat_sub, UInt64.toNat_zero] at zero
        have eq := (computeStartSlotAtEpoch_ok_iff.mp anchorStart).2
        have le := Nat.div_mul_le_self anchorBlock.slot.toNat preset.SLOTS_PER_EPOCH.toNat
        have upper := anchorBlock.slot.toNat_lt
        have lower := (anchorBlock.slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH).toNat_lt
        simp only [computeEpochAtSlot, UInt64.toNat_div] at eq
        apply UInt64.toNat_inj.mp
        omega
      have afterAnchor : anchorState.slot ≤ boundary := by
        rw [← anchorSlot, aligned, UInt64.le_iff_toNat_le]
        have le := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat
          (monotone anchorParentLe)
        have eq := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
        have anchorEq := (computeStartSlotAtEpoch_ok_iff.mp anchorStart).2
        simp only [computeEpochAtSlot, UInt64.toNat_div] at le eq anchorEq
        dsimp [boundary]
        omega
      have headSlotLe := reachable.blockState_slot_le (UInt64.le_of_eq anchorSlot) headHeld headStateHeld
      have reached := UInt64.le_trans boundaryLe (UInt64.le_trans parentHeadLe headSlotLe)
      obtain ⟨base, targetSlot, baseHeld, targetSlotOk, made⟩ :=
        e.checkpointStates_fixedChecks anchored (start w receiver) cached
      have targetSlotEq := Except.ok.inj (targetSlotOk.symm.trans targetBoundary)
      subst targetSlot
      have targetLower : boundary ≤ targetState.slot := by
        unfold lookaheadState at made
        split at made
        · exact UInt64.le_of_eq (processSlots_slot (mapError_ok_iff.mp made)).2.symm
        · cases Except.ok.inj made
          exact UInt64.not_lt.mp ‹¬ targetState.slot < boundary›
      have targetEpochLe : attestation.data.target.epoch ≤ getCurrentEpoch targetState := by
        have := monotone targetLower
        rw [computeEpochAtSlot_computeStartSlotAtEpoch positive targetBoundary] at this
        exact UInt64.le_iff_toNat_le.mpr this
      obtain ⟨now, nowOk, _, statesLe⟩ := forward.slots_le_current
        (Store.slotDuration_pos currentOk) (UInt64.le_of_eq anchorSlot)
      rw [currentOk, Except.ok.injEq] at nowOk
      subst now
      have headEpochLe := monotone (statesLe _ _ headStateHeld)
      rw [← epochEq] at headEpochLe
      apply e.committeesKept_of_head_checkpoint anchored start receiver nonzero headStateHeld
        cached onChain targetBoundary afterAnchor reached (UInt64.le_refl _) (by omega)
      · exact UInt64.le_trans targetEpochLe (getCurrentEpoch_le_activityFixedEpoch _)
      · change (computeEpochAtSlot preset headState.slot).toNat + _ + 1 < _
        have targetNat := congrArg UInt64.toNat targetEq
        omega
  have inside := Store.mem_getCommitteesBetweenSlots windowOk low high headStateOk
    (by rw [← origin.targetEpoch] at below ⊢; exact kept.2 ▸ below)
    ((kept.1 _ _ origin.targetEpoch.symm).trans committeeOk) member
  have supporter : v ∈ ((e.world k).state w).supportersOf state c := by
    simp only [Store.supportersOf, List.mem_toFinset, List.mem_map, List.mem_filter] at *
    obtain ⟨entry, entryMem, eq⟩ := active
    exact ⟨entry, ⟨entryMem, eq ▸ counted⟩, eq⟩
  have activeAt := Store.isActiveAt_of_mem_supportersOf
    (BeaconState.registryWithinLimit_of_lt preGloas state) supporter
  simp only [Store.activeMembers, Finset.mem_filter, List.mem_toFinset, Std.TreeSet.mem_toList]
  exact ⟨inside, activeAt⟩

end EthLib.Consensus.Models.Network
