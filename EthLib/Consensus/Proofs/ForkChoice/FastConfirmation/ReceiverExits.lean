module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalStatements
public import EthLib.Consensus.Proofs.Transition.Committees

/-!
# The exits that a near receiver's window can see

A fast confirmation reads its stake from a checkpoint state, the source.

A receiver near the call reads the committees of an epoch at most three epochs after the source.

The stake that leaves the active set by then must fit `exitReserve` of the source.

Every exit is placed at `current + 1 + MAX_SEED_LOOKAHEAD` or later, from the epoch where it starts.

So activity up to `current + MAX_SEED_LOOKAHEAD` is fixed at each state, as `ActiveKept` states.

With a lookahead of at least three epochs, every such exit was already scheduled at the source.
-/

@[expose] public section

namespace EthLib.Consensus

/-- The seed lookahead covers three epochs, so activity three epochs ahead of a state is fixed.

The near window of a fast confirmation reaches three epochs after its source.

Mainnet and minimal both use a lookahead of four epochs. -/
structure Preset.ExitWindowFixed (preset : Preset) : Prop where
  lookahead : 3 ≤ preset.MAX_SEED_LOOKAHEAD.toNat

/-- The mainnet preset fixes activity three epochs ahead. -/
theorem Preset.exitWindowFixed_mainnet : Preset.mainnet.ExitWindowFixed := by
  constructor; decide

/-- The minimal preset fixes activity three epochs ahead. -/
theorem Preset.exitWindowFixed_minimal : Preset.minimal.ExitWindowFixed := by
  constructor; decide

end EthLib.Consensus

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork}

/-- Stake active at the source and inactive at a near epoch of a later state fits the reserve.

The later state keeps the source's activity up to its fixed epoch, as every run does.

The epoch is from the source's epoch to three epochs after it.

A validator active at the source and inactive at that epoch was active there in the source too.

So its exit was already set by that epoch, which `exitReserve` counts. -/
theorem exitStake_le_exitReserve (config : Config) {post : Fork}
    {source : BeaconState preset fork} {later : BeaconState preset post}
    (preGloas : fork < .glamsterdam) (fixedWindow : preset.ExitWindowFixed)
    (kept : ActiveKept (activityFixedEpoch source) source later)
    {epoch : Epoch} (low : getCurrentEpoch source ≤ epoch)
    (high : epoch.toNat ≤ (getCurrentEpoch source).toNat + 3) :
    stake (fun v => balanceAt source v.toNat)
        {v ∈ activeVoters source | isActiveAt later epoch v.toNat = false} ≤
      exitReserve config source := by
  apply stake_mono
  intro v member
  rw [Finset.mem_filter] at member ⊢
  obtain ⟨active, absent⟩ := member
  refine ⟨active, ?_⟩
  -- The epoch is within the source's fixed epoch, so the later state reads the source's activity.
  have fixed : epoch ≤ activityFixedEpoch source := by
    rw [UInt64.le_iff_toNat_le, activityFixedEpoch_toNat]
    have := epoch.toNat_lt
    have := fixedWindow.lookahead
    omega
  rw [kept epoch fixed] at absent
  unfold activeVoters at active
  rw [List.mem_toFinset, mem_getActiveValidatorIndices (source.validators.bound preGloas)] at active
  obtain ⟨validator, found, current⟩ := active
  simp only [isActiveAt, found, Option.map_some, Option.getD_some] at absent
  simp only [found, Option.any_some, decide_eq_true_eq]
  -- Active at the source's epoch and not at the later one: activation is early, so exit is due.
  simp only [isActiveValidator, Bool.and_eq_true, Bool.and_eq_false_iff, decide_eq_true_eq,
    decide_eq_false_iff_not, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at current absent
  rw [UInt64.le_iff_toNat_le] at low
  omega

/-- A head state that keeps the source's fixed activity omits at most the reserve per near epoch.

Each full epoch of the window must lie between the source's epoch and three epochs after it.

The committees of a full epoch hold every validator active in it at the head state.

So an omitted source validator is inactive at that epoch, and `exitStake_le_exitReserve` applies. -/
theorem windowExitBound_of_activeKept (config : Config) (store : Store preset fork)
    (source : BeaconState preset fork) (head : Root) (first last : Slot)
    {headState : BeaconState preset fork} (preGloas : fork < .glamsterdam)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) (fixedWindow : preset.ExitWindowFixed)
    (headOk : store.blockState head = .ok headState)
    (kept : ActiveKept (activityFixedEpoch source) source headState)
    (near : ∀ (epoch : Epoch) (epochStart next epochEnd : Slot),
      computeStartSlotAtEpoch preset epoch = .ok epochStart →
      addChecked epochStart preset.SLOTS_PER_EPOCH = .ok next →
      subChecked next 1 = .ok epochEnd → first ≤ epochStart → epochEnd ≤ last →
      getCurrentEpoch source ≤ epoch ∧ epoch.toNat ≤ (getCurrentEpoch source).toNat + 3) :
    WindowExitBound (config := config) store source head first last := by
  intro epoch epochStart next epochEnd members startOk nextOk endOk firstLe lastLe membersOk
  obtain ⟨low, high⟩ := near epoch epochStart next epochEnd startOk nextOk endOk firstLe lastLe
  refine Nat.le_trans (stake_mono ?_)
    (exitStake_le_exitReserve config preGloas fixedWindow kept low high)
  intro v member
  simp only [Finset.mem_filter] at member ⊢
  refine ⟨member.1, ?_⟩
  cases active : isActiveAt headState epoch v.toNat
  · rfl
  · -- The window's slots cover the whole epoch, so its committees hold the active validator.
    have startNat := (computeStartSlotAtEpoch_ok_iff.mp startOk).2
    have nextNat := (addChecked_ok_iff.mp nextOk).2
    have endNat := (subChecked_ok_iff.mp endOk)
    simp only [UInt64.toNat_one] at endNat
    exact absurd (Store.mem_getCommitteesBetweenSlots_of_active (store := store) preGloas positive
      membersOk headOk (by omega) (by rw [Nat.succ_mul]; omega)
      (mem_getActiveValidatorIndices_of_isActiveAt active)) member.2

end EthLib.Consensus.Models.Network
