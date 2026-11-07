module

public import EthLib.Consensus.Proofs.Transition.Provenance.Ancestry
public import EthLib.Consensus.Proofs.Transition.Provenance.Voters

/-!
# Proofs: a counted vote names the source and the target of its weighing call

A weighing call justifies a checkpoint of the previous or current epoch.

Its supermajority link runs from a source checkpoint to that target.

The source is the justified checkpoint of the target's epoch: the current justified checkpoint
while that epoch runs, and the previous justified one in the epoch after it.

An attestation is checked against the same rule when a block includes it.

So a counted vote names the call's target, and the call's source.

Two facts of chains make that work.

- Within one epoch the justified checkpoints stay: only the end of an epoch writes them.
- The end of an epoch makes the current justified checkpoint the previous one.

The second fails at the end of epoch 1, which weighs nothing.

So for a target in epoch 1 the source agrees only when the chain's two justified checkpoints did.

From a genesis state both are the genesis checkpoint, so they agree.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- Along a chain the epoch never decreases. -/
theorem Reaches.epoch_le {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) :
    (getCurrentEpoch start.state).toNat ≤ (getCurrentEpoch after.state).toNat := by
  rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
  exact Nat.div_le_div_right chain.slot_le

/-- A slot step that closes its epoch moves the epoch on by one. -/
theorem epoch_of_closes {next : BeaconState preset fork}
    (slot : next.slot.toNat = state.slot.toNat + 1) (closes : ClosesEpoch preset state) :
    (getCurrentEpoch next).toNat = (getCurrentEpoch state).toNat + 1 := by
  have fits : state.slot.toNat + 1 < 2 ^ 64 := slot ▸ UInt64.toNat_lt next.slot
  rw [closesEpoch_iff fits] at closes
  rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, slot, Nat.succ_div]
  simp [closes]

/-- A slot step that does not close its epoch keeps the epoch. -/
theorem epoch_of_open {next : BeaconState preset fork}
    (slot : next.slot.toNat = state.slot.toNat + 1) (notClosing : ¬ClosesEpoch preset state) :
    getCurrentEpoch next = getCurrentEpoch state := by
  have same := flagsEpoch_of_open slot notClosing true
  simpa [flagsEpoch] using same

/-- Within one epoch of a chain, the justified checkpoints stay. -/
theorem Reaches.justified_of_same_epoch {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after)
    (same : getCurrentEpoch after.state = getCurrentEpoch start.state) :
    after.state.previousJustifiedCheckpoint = start.state.previousJustifiedCheckpoint ∧
      after.state.currentJustifiedCheckpoint = start.state.currentJustifiedCheckpoint := by
  obtain ⟨run⟩ := chain
  induction run with
  | nil => exact ⟨rfl, rfl⟩
  | @snoc middle last run step more =>
    have middleLe := Reaches.epoch_le (config := config) (checks := checks) ⟨run⟩
    have lastLe := (Reaches.refl (config := config) (checks := checks) middle).step step
    have stepLe := lastLe.epoch_le
    have middleSame : getCurrentEpoch middle.state = getCurrentEpoch start.state := by
      apply UInt64.toNat_inj.mp
      rw [← same] at middleLe ⊢
      omega
    obtain ⟨previous, current⟩ := more middleSame
    rw [← previous, ← current]
    cases step with
    | @slot fork state next notDue computed =>
      obtain ⟨_, _, stepSlot, -, -, -, closing⟩ := advanceSlot_history computed
      split at closing
      · next closes =>
        exfalso
        have := epoch_of_closes stepSlot closes
        simp only at same middleSame this
        rw [middleSame, ← same] at this
        omega
      · exact ⟨closing.2.1, closing.2.2.1⟩
    | upgrade due computed =>
      have same := upgradeNext_history computed
      simp only [BeaconState.history, Prod.mk.injEq] at same
      exact ⟨same.2.2.2.2.2.1, same.2.2.2.2.2.2.1⟩
    | block engine signed validateResult notDue computed =>
      have frame := frame_processBlock (applySignedBlock_ok computed).2.1
      exact ⟨frame.previousJustified, frame.currentJustified⟩

/-- Across the end of an epoch that weighs, the current justified checkpoint becomes the previous
one.

The epoch must be at least two, since the first two epochs weigh nothing. -/
theorem Reaches.previousJustified_of_next_epoch {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after)
    (next : (getCurrentEpoch after.state).toNat = (getCurrentEpoch start.state).toNat + 1)
    (weighs : GENESIS_EPOCH + 1 < getCurrentEpoch start.state) :
    after.state.previousJustifiedCheckpoint = start.state.currentJustifiedCheckpoint := by
  obtain ⟨run⟩ := chain
  induction run with
  | nil => omega
  | @snoc middle last run step more =>
    have middleChain : Reaches config checks start middle := ⟨run⟩
    have middleLe := middleChain.epoch_le
    have stepLe := ((Reaches.refl (config := config) (checks := checks) middle).step step).epoch_le
    by_cases moved : (getCurrentEpoch middle.state).toNat = (getCurrentEpoch start.state).toNat + 1
    · -- The epoch had already moved on: this step stays in it and keeps the checkpoints.
      have stays : getCurrentEpoch last.state = getCurrentEpoch middle.state :=
        UInt64.toNat_inj.mp (by omega)
      rw [← more moved]
      exact (((Reaches.refl _).step step).justified_of_same_epoch stays).1
    · -- This step ends the epoch of the start, so it weighs.
      have startEpoch : getCurrentEpoch middle.state = getCurrentEpoch start.state :=
        UInt64.toNat_inj.mp (by omega)
      have kept := middleChain.justified_of_same_epoch startEpoch
      cases step with
      | @slot fork state nextState notDue computed =>
        obtain ⟨cached, cachedOk, stepSlot, -, -, -, closing⟩ := advanceSlot_history computed
        split at closing
        · obtain ⟨weighed, weighedOk, -, previousSame, -, -⟩ := closing
          simp only at kept startEpoch ⊢
          rw [previousSame, ← kept.2]
          have cachedSame : cached.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∧
              getCurrentEpoch cached = getCurrentEpoch state := by
            obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
            exact ⟨rfl, rfl⟩
          rcases processJustificationAndFinalization_weighs weighedOk with ⟨early, _⟩ |
            ⟨_, _, _, _, _, _, _, _, _, _, _, weighs'⟩
          · rw [cachedSame.2, startEpoch] at early
            exact absurd early (UInt64.not_le.mpr weighs)
          · rw [(weighJustificationAndFinalization_checkpoints weighs').1, cachedSame.1]
        · next notClosing =>
          have := epoch_of_open stepSlot notClosing
          simp only at this next startEpoch
          rw [this, startEpoch] at next
          omega
      | @upgrade _ post due computed =>
        have same := upgradeNext_history computed
        simp only [BeaconState.history, Prod.mk.injEq] at same
        have : getCurrentEpoch post.val.state = getCurrentEpoch middle.state := by
          simp only [getCurrentEpoch, same.1]
        rw [this, startEpoch] at next
        omega
      | @block fork engine signed validateResult state post notDue computed =>
        have postSlot := processBlock_slot (applySignedBlock_ok computed).2.1
        have : getCurrentEpoch post = getCurrentEpoch state := by
          simp only [getCurrentEpoch, postSlot]
        simp only at next startEpoch
        rw [this, startEpoch] at next
        omega

end EthLib.Consensus
