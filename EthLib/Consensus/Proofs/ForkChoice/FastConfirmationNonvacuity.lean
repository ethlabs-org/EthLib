module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSafety

/-!
# Compatibility of the fast-confirmation premises at the anchor

These results test the premises of the safety statement for Theorem 1 of [the paper][fcr].

The anchor store and the anchor state can name different justified checkpoints.

`OneJustifiedPerEpoch` identifies them when their epochs agree and lie within its horizon.

If that identifies the anchor root with its parent, the `anchorParent` premise fails.

This excludes those anchors, not executions with an anchor at a later epoch.

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

/-- Uniqueness also compares the checkpoint inside the anchor state with the store's checkpoint. -/
theorem Execution.anchor_currentJustified_eq_of_oneJustifiedPerEpoch
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J)
    {horizon : Epoch} (unique : OneJustifiedPerEpoch e horizon)
    (sameEpoch : anchorState.currentJustifiedCheckpoint.epoch = getCurrentEpoch anchorState)
    (within : getCurrentEpoch anchorState ≤ horizon) :
    anchorState.currentJustifiedCheckpoint = anchor.justifiedCheckpoint := by
  obtain ⟨root, _, _, stored, justified, _⟩ := getForkchoiceStore_anchor anchored
  have atStart : (e.world 0).state u = anchor := start u caller
  -- Both alternatives of Justified are present in the initial world.
  have stateJustified : anchor.Justified anchorState.currentJustifiedCheckpoint :=
    .inr (.inr (.inl ⟨root, anchorState, stored, rfl⟩))
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
    (within : getCurrentEpoch anchorState ≤ horizon)
    (parent : anchorState.currentJustifiedCheckpoint.root = anchorBlock.parentRoot)
    {limit : ℕ} (started : e.startTime ≤ limit)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none) : False := by
  obtain ⟨root, _, held, _, justified, _⟩ := getForkchoiceStore_anchor anchored
  have same := e.anchor_currentJustified_eq_of_oneJustifiedPerEpoch anchored start caller
    unique sameEpoch within
  have rootEq : anchorBlock.parentRoot = root := by
    simpa [parent, justified] using congrArg Checkpoint.root same
  -- The excluded parent is the anchor itself, which the initial store holds.
  have missing := anchorParent u caller 0 started
  change (e.start u).blocks[anchorBlock.parentRoot]? = none at missing
  rw [start u caller, rootEq, held] at missing
  contradiction

/-- At epoch zero, the state invariant supplies the equal-epoch condition.

This covers an anchor whose parent and state's current justified root are both zero.

No assertion about the value or injectivity of a hash is needed. -/
theorem Execution.false_of_genesis_anchor_checkpoint_parent
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J)
    {horizon : Epoch} (unique : OneJustifiedPerEpoch e horizon)
    (sound : Invariant anchorState) (epochZero : getCurrentEpoch anchorState = 0)
    (parent : anchorState.currentJustifiedCheckpoint.root = anchorBlock.parentRoot)
    {limit : ℕ} (started : e.startTime ≤ limit)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none) : False := by
  have settled := sound.settled
  have sameEpoch : anchorState.currentJustifiedCheckpoint.epoch = getCurrentEpoch anchorState := by
    apply UInt64.toNat_inj.mp
    simpa [JustifiedSettled, getPreviousEpoch, epochZero, Uint64.saturatingSub,
      UInt64.le_iff_toNat_le] using settled
  exact e.false_of_anchor_checkpoint_parent anchored start caller unique sameEpoch
    (by simp [epochZero]) parent started anchorParent

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

end EthLib.Consensus.Models.Network
