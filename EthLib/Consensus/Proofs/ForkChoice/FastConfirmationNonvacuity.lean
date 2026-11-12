module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSafety

/-!
# Compatibility of the fast-confirmation premises at the anchor

These results test the premises of the safety statement for Theorem 1 of [the paper][fcr].

The anchor store and the anchor state can name different justified checkpoints.

`OneJustifiedPerEpoch` identifies them when their positive epochs agree within its horizon.

If that identifies the anchor root with its parent, the `anchorParent` premise fails.

At genesis, the raw state's checkpoint need not be justified in the store.

[fcr]: https://arxiv.org/html/2405.00549v4#S4
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- Uniqueness compares a positive-epoch state checkpoint with the store's checkpoint. -/
theorem Execution.anchor_currentJustified_eq_of_oneJustifiedPerEpoch
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J)
    {horizon : Epoch} (unique : OneJustifiedPerEpoch e horizon)
    (sameEpoch : anchorState.currentJustifiedCheckpoint.epoch = getCurrentEpoch anchorState)
    (positive : 0 < anchorState.currentJustifiedCheckpoint.epoch)
    (within : getCurrentEpoch anchorState ≤ horizon) :
    anchorState.currentJustifiedCheckpoint = anchor.justifiedCheckpoint := by
  obtain ⟨root, _, _, stored, justified, _⟩ := getForkchoiceStore_anchor anchored
  have atStart : (e.world 0).state u = anchor := start u caller
  -- Both alternatives of Justified are present in the initial world.
  have stateJustified : anchor.Justified anchorState.currentJustifiedCheckpoint :=
    .inr (.inr ⟨positive, .inl ⟨root, anchorState, stored, rfl⟩⟩)
  have storeJustified : anchor.Justified anchor.justifiedCheckpoint := .inl rfl
  exact unique u caller u caller 0 0 _ _ (atStart ▸ stateJustified)
    (atStart ▸ storeJustified) (by simpa [justified] using sameEpoch)
    (sameEpoch ▸ within)

/-- A same-epoch anchor checkpoint cannot name the anchor's excluded parent. -/
theorem Execution.false_of_anchor_checkpoint_parent
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J)
    {horizon : Epoch} (unique : OneJustifiedPerEpoch e horizon)
    (sameEpoch : anchorState.currentJustifiedCheckpoint.epoch = getCurrentEpoch anchorState)
    (positive : 0 < anchorState.currentJustifiedCheckpoint.epoch)
    (within : getCurrentEpoch anchorState ≤ horizon)
    (parent : anchorState.currentJustifiedCheckpoint.root = anchorBlock.parentRoot)
    {limit : ℕ} (started : e.startTime ≤ limit)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none) : False := by
  obtain ⟨root, _, held, _, justified, _⟩ := getForkchoiceStore_anchor anchored
  have same := e.anchor_currentJustified_eq_of_oneJustifiedPerEpoch anchored start caller
    unique sameEpoch positive within
  have rootEq : anchorBlock.parentRoot = root := by
    simpa [parent, justified] using congrArg Checkpoint.root same
  -- The excluded parent is the anchor itself, which the initial store holds.
  have missing := anchorParent u caller 0 started
  change (e.start u).blocks[anchorBlock.parentRoot]? = none at missing
  rw [start u caller, rootEq, held] at missing
  contradiction

/-- A raw genesis checkpoint naming the excluded parent is not justified in the store.

This covers an anchor whose parent and state's current justified root are both zero.

No assertion about the value or injectivity of a hash is needed. -/
theorem Execution.not_justified_of_genesis_anchor_checkpoint_parent
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J)
    {horizon : Epoch} (unique : OneJustifiedPerEpoch e horizon)
    (sound : Invariant anchorState) (epochZero : getCurrentEpoch anchorState = 0)
    (parent : anchorState.currentJustifiedCheckpoint.root = anchorBlock.parentRoot)
    {limit : ℕ} (started : e.startTime ≤ limit)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none) :
    ¬ anchor.Justified anchorState.currentJustifiedCheckpoint := by
  intro rawJustified
  have settled := sound.settled
  have sameEpoch : anchorState.currentJustifiedCheckpoint.epoch = getCurrentEpoch anchorState := by
    apply UInt64.toNat_inj.mp
    simpa [JustifiedSettled, getPreviousEpoch, epochZero, Uint64.saturatingSub,
      UInt64.le_iff_toNat_le] using settled
  obtain ⟨root, _, held, _, justified, _⟩ := getForkchoiceStore_anchor anchored
  have atStart : (e.world 0).state u = anchor := start u caller
  have storeJustified : anchor.Justified anchor.justifiedCheckpoint := .inl rfl
  have same := unique u caller u caller 0 0
    anchorState.currentJustifiedCheckpoint anchor.justifiedCheckpoint (atStart ▸ rawJustified)
    (atStart ▸ storeJustified)
    (by simpa [justified] using sameEpoch) (by simp [sameEpoch, epochZero])
  have rootEq : anchorBlock.parentRoot = root := by
    simpa [parent, justified] using congrArg Checkpoint.root same
  -- The excluded parent would be the anchor itself.
  have missing := anchorParent u caller 0 started
  change (e.start u).blocks[anchorBlock.parentRoot]? = none at missing
  rw [start u caller, rootEq, held] at missing
  contradiction

/-- A store built from an anchor cannot read a shuffling dependency before that anchor.

The block handler reads this dependency even when the proposer boost is zero. -/
theorem _root_.EthLib.Consensus.Store.Reachable.getShufflingDependentRoot_ne_ok_of_lt_anchor
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {epoch : Epoch} {slot : Slot}
    (dependent : computeShufflingDependentSlot preset epoch = .ok slot)
    (before : slot < anchorBlock.slot) (root result : Root) :
    store.getShufflingDependentRoot root epoch ≠ .ok result := by
  intro read
  simp only [Store.getShufflingDependentRoot, Base.bind_ok_iff, Base.mapError_ok_iff,
    pure, Except.pure, Except.ok.injEq] at read
  obtain ⟨dependentSlot, slotOk, ancestor, walk, _⟩ := read
  rw [dependent, Except.ok.injEq] at slotOk
  subst dependentSlot
  obtain ⟨block, known, below⟩ := Store.getAncestor_le walk
  have above := reachable.anchorSlot_le_block known
  rw [UInt64.le_iff_toNat_le] at above below
  rw [UInt64.lt_iff_toNat_lt] at before
  omega

/-- The common-state premise bounds a vote's target by the epoch of the head state.

An old head cannot supply this premise for an arbitrarily recent cached vote target. -/
theorem CommitteesFollow.targetEpoch_le_headEpoch_add_lookahead
    (committees : CommitteesFollow e) {w : ValidatorIndex} (honest : w ∈ J)
    {k : ℕ} {head : ForkChoiceNode} {headState : BeaconState preset fork}
    {current : Epoch} {v : ValidatorIndex} {attestation : Attestation preset fork}
    {targetState : BeaconState preset fork}
    (headOk : ((e.world k).state w).getHead config = .ok head)
    (headStateOk : ((e.world k).state w).blockState head.root = .ok headState)
    (currentOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok current)
    (targetPast : attestation.data.target.epoch.toNat ≤ current.toNat)
    (recent : current.toNat ≤ attestation.data.target.epoch.toNat + 1)
    (origin : ((e.world k).state w).VoteOrigin config v attestation)
    (targetOk : ((e.world k).state w).checkpointStates[attestation.data.target]? =
      some targetState) :
    attestation.data.target.epoch.toNat ≤
      (getCurrentEpoch headState).toNat + preset.MIN_SEED_LOOKAHEAD.toNat := by
  obtain ⟨common, headRun, _, targetBound, _⟩ :=
    committees.common w honest k head headState current v attestation targetState
      headOk headStateOk currentOk targetPast recent origin targetOk
  -- A common state is no later than the head state that follows it.
  have headLater := UInt64.le_iff_toNat_le.mp headRun.later
  omega

end EthLib.Consensus.Models.Network
