module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Heads
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Duties

/-! The five implementation-level bounds at the witness's confirming call.

The call has zero weight shift and zero balance-drift margin.

Its two remaining honest duties have 400 Gwei, exceeding the 264 Gwei the rule requires.

The late-margin field is vacuous because no complete epoch fits between the call and the limit. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.EightValidatorWitness.Trace
open Base Base.Uint64

/-- The confirming call reads slot three. -/
theorem call_slot : (running 3000 4).getCurrentSlot config = .ok 3 := by
  simp [Store.getCurrentSlot, show (running 3000 4).genesisTimeMs = 0 from rfl,
    show (running 3000 4).timeMs = 3000 from rfl, computeSlotAtTimeMs, subChecked, divChecked,
    show config.SLOT_DURATION_MS = 1000 from rfl, bind, Except.bind, Except.mapError]

/-- The confirming call remains in epoch zero. -/
theorem call_epoch : (running 3000 4).getCurrentStoreEpoch config = .ok 0 := by
  rw [Store.getCurrentStoreEpoch, call_slot]
  rfl

/-- The call's head is the slot-one child. -/
theorem call_head : (running 3000 4).getHead config = .ok ⟨blockRoot, .pending⟩ :=
  running_head 3000 4 (by decide) call_epoch (.inl rfl)

/-- No epoch processing is needed to pull up the call's head state. -/
theorem call_pulled : (running 3000 4).getPulledUpHeadState config blockRoot = .ok postState := by
  simp only [Store.getPulledUpHeadState, call_epoch]
  have stored : (running 3000 4).blockState blockRoot = .ok postState := by
    simp [Store.blockState, running, admitted, pure, Except.pure]
  rw [stored]
  rfl

/-- Validators whose duties have ended at the call. -/
def pastMembers : Std.TreeSet ValidatorIndex :=
  (((((((∅ : Std.TreeSet ValidatorIndex).insert 0).insert 1).insert 2).insert 3).insert 4).insert 5)

/-- The epoch's first three slots assign exactly validators zero to five. -/
theorem call_past_members :
    (running 3000 4).getCommitteesBetweenSlots blockRoot 0 2 = .ok pastMembers := by
  have zero : (running 3000 4).getSlotCommittee blockRoot 0 =
      .ok (((∅ : Std.TreeSet ValidatorIndex).insert 0).insert 1) := by
    have stored : (running 3000 4).blockState blockRoot = .ok postState := by
      simp [Store.blockState, running, admitted, pure, Except.pure]
    simp only [Store.getSlotCommittee, stored, bind, Except.bind,
      show getCommitteeCountPerSlot postState (computeEpochAtSlot preset 0) = 1 from rfl,
      show List.range (1 : UInt64).toNat = [0] from rfl, List.foldlM_cons, List.foldlM_nil,
      show (0 : Nat).toUInt64 = 0 from rfl, post_committees.1, Except.mapError]
    rfl
  simp only [Store.getCommitteesBetweenSlots, show addChecked 2 1 = .ok 3 from rfl,
    Except.mapError, bind, Except.bind,
    show List.range ((3 : UInt64).toNat - (0 : UInt64).toNat) = [0, 1, 2] from rfl,
    List.foldlM_cons, List.foldlM_nil,
    show (0 : Slot) + (0 : Nat).toUInt64 = 0 from rfl,
    show (0 : Slot) + (1 : Nat).toUInt64 = 1 from rfl,
    show (0 : Slot) + (2 : Nat).toUInt64 = 2 from rfl,
    zero, (running_committees 3000 4).1, (running_committees 3000 4).2]
  rfl

/-- The three past duties account for 1200 of the 1600 Gwei. -/
theorem call_past_weight :
    (running 3000 4).computeCommitteeWeightBetweenSlots blockRoot postState 0 2 = .ok 1200 := by
  suffices read : (running 3000 4).computeCommitteeWeightAndMembers blockRoot postState 0 2 =
      .ok (1200, some pastMembers) by
    rw [Store.computeCommitteeWeightBetweenSlots, read]
    rfl
  have total : getTotalBalance postState [0, 1, 2, 3, 4, 5] = .ok 1200 := by
    rw [getTotalBalance_ok_iff]
    simp only [List.forall_mem_cons, sumMarked_eq_sum, getElem?_markIndices]
    decide
  have active : ([(0 : ValidatorIndex), 1, 2, 3, 4, 5].filterM fun index => do
      pure (isActiveValidator (← validatorAt postState index) 0)) =
      (.ok [0, 1, 2, 3, 4, 5] : Except ForkChoiceError _) := by
    have passes : ∀ index ∈ [(0 : ValidatorIndex), 1, 2, 3, 4, 5],
        (do pure (isActiveValidator (← validatorAt postState index) 0)) =
          (.ok true : Except ForkChoiceError Bool) := by
      intro index member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    obtain ⟨out, filtered⟩ := filterM_exists_ok (fun index member => ⟨true, passes index member⟩)
    have contains : [(0 : ValidatorIndex), 1, 2, 3, 4, 5] ⊆ out := fun index member =>
      mem_filterM_ok_of_test filtered member (passes index member)
    have same := (sublist_of_filterM_ok filtered).eq_of_length_le
      ((show [(0 : ValidatorIndex), 1, 2, 3, 4, 5].Nodup by decide).length_le_of_subset contains)
    simpa only [same] using filtered
  simp only [Store.computeCommitteeWeightAndMembers,
    show ¬ (0 : Slot) > 2 by decide, ↓reduceIte,
    show isFullValidatorSetCovered preset 0 2 = .ok false from rfl,
    call_past_members, bind, Except.bind]
  change (do
    let members ← ([(0 : ValidatorIndex), 1, 2, 3, 4, 5].filterM fun index => do
      pure (isActiveValidator (← validatorAt postState index) 0))
    pure (← (getTotalBalance postState members).mapError ForkChoiceError.accessor,
      some pastMembers)) = .ok (1200, some pastMembers)
  rw [active]
  simp only [bind, Except.bind, total, Except.mapError]
  rfl

/-- Honest validators six and seven supply the required share of the remaining 400 Gwei. -/
theorem remaining_margin :
    3 * ((1600 - 1200) / 100 * (100 - config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat)) ≤
      3 * stake (fun v => balanceAt postState v.toNat)
        {v ∈ ((unslashedActiveBalances postState).map (·.1)).toFinset |
          v ∉ pastMembers ∧ v ∈ honest} := by
  change 792 ≤ 1200
  decide

set_option maxRecDepth 10000 in
/-- The singleton call history starts at the anchor and returns the certified child. -/
theorem only_call {i n : Nat} {fcr after : FastConfirmationStore}
    (call : CallAt execution 0 [112] (getFastConfirmationStore anchor) i n fcr after) :
    i = 0 ∧ n = 112 ∧ fcr = getFastConfirmationStore anchor ∧ after = confirmed := by
  obtain ⟨index, prior, called⟩ := call
  cases i with
  | succ i => simp at index
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at index
    subst n
    simp only [List.take_zero, List.map_nil, List.foldlM_nil, pure, Except.pure,
      Except.ok.injEq] at prior
    subst fcr
    rw [call_store, running_call, Except.ok.injEq] at called
    exact ⟨rfl, rfl, rfl, called.symm⟩

set_option maxRecDepth 10000 in
/-- All five rule bounds hold together at the genuinely advancing call. -/
theorem rule_bounds : RuleBounds execution 0 [112] (getFastConfirmationStore anchor) 0 0 4000 where
  walked := by
    intro i n fcr after head slot start balanceSource chain later call headOk slotOk _ _ _
      sourceOk _ confirmedMembers
    obtain ⟨rfl, rfl, rfl, rfl⟩ := only_call call
    rw [call_store] at headOk slotOk sourceOk confirmedMembers ⊢
    rw [call_head, Except.ok.injEq] at headOk
    rw [call_slot, Except.ok.injEq] at slotOk
    subst head slot
    have source := local_checkpoint (code := .running 3000 4) sourceOk
    subst balanceSource
    rw [confirms_by_walk.1]
    refine ⟨fun last bounded _ => weights bounded, ?_, ?_, ?_, ?_⟩
    · intro member inside block parent firstSlot lastSlot beforeBlock participants maximum score
        support discount adversary blockOk parentOk firstOk lastOk _ _ maximumOk scoreOk
        supportOk discountOk adversaryOk
      obtain ⟨otherSupport, threshold, otherOk, thresholdOk, exceeds⟩ :=
        Store.isOneConfirmed_eq_ok_true_iff.mp (confirmedMembers member inside)
      rw [supportOk, Except.ok.injEq] at otherOk
      subst otherSupport
      have lower := Store.computeSafetyThreshold_bound call_slot blockOk parentOk scoreOk
        firstOk lastOk maximumOk discountOk adversaryOk thresholdOk
      have strict := UInt64.lt_iff_toNat_lt.mp exceeds
      omega
    · intro s epochStart lastSlot participants _ pulled _ _ read
      rw [call_pulled, Except.ok.injEq] at pulled
      subst s
      change ByzantineStakeAtMost (fun v => balanceAt (state bodyRoot) v.toNat)
        (Store.activeMembers (state bodyRoot) participants) honest 34 100
      exact range_byzantine (code := .running 3000 4) read
    · intro s epochStart lastSlot participants total soFar _ pulled startOk lastOk read totalOk
        weightOk
      rw [call_pulled, Except.ok.injEq] at pulled
      subst s
      have es : epochStart = 0 := (Except.ok.inj ((show
        computeStartSlotAtEpoch preset (computeEpochAtSlot preset 3) = .ok 0 from rfl).symm.trans
          startOk)).symm
      have ls : lastSlot = 2 :=
        (Except.ok.inj ((show subChecked 3 1 = .ok 2 from rfl).symm.trans lastOk)).symm
      subst epochStart lastSlot
      rw [call_past_members, Except.ok.injEq] at read
      subst participants
      have totalRead : getTotalActiveBalance postState = .ok 1600 := total_balance
      rw [totalRead, Except.ok.injEq] at totalOk
      rw [call_past_weight, Except.ok.injEq] at weightOk
      subst total soFar
      exact remaining_margin
    · intro w _ k s full bounded _ _ _
      exact False.elim (no_complete_epoch bounded full)

end EthLib.Consensus.Models.Network.EightValidatorWitness.Trace
