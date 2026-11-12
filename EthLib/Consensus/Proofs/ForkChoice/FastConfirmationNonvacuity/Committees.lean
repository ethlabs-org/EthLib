module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Facts
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Shuffling

/-! Committee reserve bound and unchanged weight margins for the short execution.

Every successful range of ordered slots holds both validators of its first slot.

So it has at least 400 Gwei of stake, and no Byzantine stake.

The exit reserve of the anchor is one maximum balance, 200 Gwei, since the churn limit is one.

So `100 B + 50 reserve = 10000` is at most `34 w`, which is at least 13600, on every such range.

This supplies Assumption 2 of arXiv 2405.00549v4, with the reserve, at all queried slots. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.EightValidatorWitness.Trace
open Base Base.Uint64

/-- A successful slot read returns exactly the seats of the fixed zero-round assignment. -/
theorem slot_members {code : Local} {root : Root} {slot : Slot}
    {members : Std.TreeSet ValidatorIndex}
    (read : code.store.getSlotCommittee root slot = .ok members) :
    ∀ v, v ∈ members ↔ v ∈ seats slot := by
  simp only [Store.getSlotCommittee, bind_ok_iff] at read
  obtain ⟨s, stateOk, read⟩ := read
  have registry : s.validators = (state bodyRoot).validators := by
    rcases local_block_state (Store.blockState_ok_iff.mp stateOk) with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  have count : getCommitteeCountPerSlot s (computeEpochAtSlot preset slot) = 1 := by
    unfold getCommitteeCountPerSlot getActiveValidatorIndices
    rw [registry]
    exact slot_committee_count bodyRoot slot
  rw [count] at read
  simp only [show List.range (1 : UInt64).toNat = [0] from rfl,
    List.foldlM_cons, List.foldlM_nil, bind_pure] at read
  change (do
    let committee ← (getBeaconCommittee s slot 0).mapError ForkChoiceError.accessor
    pure (committee.foldl (fun (set : Std.TreeSet ValidatorIndex) v => set.insert v) ∅)) =
      .ok members at read
  simp only [bind_ok_iff, mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at read
  obtain ⟨committee, committeeOk, rfl⟩ := read
  rw [committee_at_slot registry committeeOk]
  intro v
  unfold seats
  have flip (a : ValidatorIndex) : Ordering.eq = compare a v ↔ v = a := by
    rw [eq_comm, Std.LawfulEqCmp.compare_eq_iff_eq, eq_comm]
  simp [eq_comm, or_comm]
  simp only [flip]

/-- A range member has a duty in an included slot, and every such duty is a member. -/
theorem range_members {code : Local} {root : Root} {first last : Slot}
    {members : Std.TreeSet ValidatorIndex}
    (read : code.store.getCommitteesBetweenSlots root first last = .ok members)
    (v : ValidatorIndex) :
    v ∈ members ↔ ∃ slot, first ≤ slot ∧ slot ≤ last ∧ v ∈ seats slot := by
  simp only [Store.getCommitteesBetweenSlots, bind_ok_iff, mapError_ok_iff] at read
  obtain ⟨afterLast, afterOk, read⟩ := read
  have afterNat := (addChecked_ok_iff.mp afterOk).2
  simp only [UInt64.toNat_one] at afterNat
  constructor
  · intro member
    rcases (mem_foldlM_committees_iff read).mp member with empty |
      ⟨i, inside, committee, ok, present⟩
    · exact False.elim (Std.TreeSet.not_mem_emptyc empty)
    · have offset := List.mem_range.mp inside
      have bound := afterLast.toNat_lt
      have iBound : i < 2 ^ 64 := by omega
      have iNat : i.toUInt64.toNat = i := by
        simp [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' iBound]
      have slotNat : (first + i.toUInt64).toNat = first.toNat + i := by
        rw [UInt64.toNat_add, iNat, Nat.mod_eq_of_lt (by omega)]
      refine ⟨first + i.toUInt64, ?_, ?_, (slot_members ok v).mp present⟩
      · rw [UInt64.le_iff_toNat_le, slotNat]; omega
      · rw [UInt64.le_iff_toNat_le, slotNat]; omega
  · rintro ⟨slot, low, high, present⟩
    have lowNat := UInt64.le_iff_toNat_le.mp low
    have highNat := UInt64.le_iff_toNat_le.mp high
    have inside : slot.toNat - first.toNat ∈ List.range (afterLast.toNat - first.toNat) :=
      List.mem_range.mpr (by omega)
    have back : first + (slot.toNat - first.toNat).toUInt64 = slot := by
      rw [← UInt64.toNat_sub_of_le _ _ low, Nat.toUInt64_eq,
        UInt64.ofNat_toNat, UInt64.add_comm, UInt64.sub_add_cancel]
    obtain ⟨committee, ok⟩ := foldlM_forall_of_ok
      (fun _ _ _ step => (bind_ok_iff.mp step).imp fun _ read => read.1) _ _ _ read _ inside
    exact (mem_foldlM_committees_iff read).mpr (.inr ⟨_, inside, committee, ok,
      (slot_members ok v).mpr (by rw [back]; exact present)⟩)

/-- Every position of the registry is a validator of 200 Gwei. -/
theorem registered_validator {v : ValidatorIndex} (registered : v < 8) :
    (state bodyRoot).validators.data[v.toNat]? = some (validator 200) := by
  rcases registered_cases registered with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The anchor's churn limit is one validator, so its exit reserve is one maximum balance. -/
theorem exit_reserve_state (root : Root) : exitReserve config (state root) = 200 := by
  change exitReserve config (state default) = 200
  decide

/-- The committee bound of Assumption 2 holds on every successful range, ordered or not. -/
theorem range_byzantine {code : Local} {root : Root} {first last : Slot}
    {members : Std.TreeSet ValidatorIndex}
    (read : code.store.getCommitteesBetweenSlots root first last = .ok members) :
    ByzantineStakeAtMost (fun v => balanceAt (state bodyRoot) v.toNat)
      (Store.activeMembers (state bodyRoot) members) honest 34 100 := by
  apply committee_byzantine
  intro v inside
  obtain ⟨member, _⟩ := Store.mem_activeMembers.mp inside
  obtain ⟨slot, _, _, seat⟩ := (range_members read v).mp member
  exact (seats_pair slot).2.2 v seat

/-- Every range of ordered slots holds the 400 Gwei of its first slot and no Byzantine stake. -/
theorem range_reserve {code : Local} {root : Root} {first last : Slot}
    {members : Std.TreeSet ValidatorIndex} (ordered : first ≤ last)
    (read : code.store.getCommitteesBetweenSlots root first last = .ok members) :
    100 * stake (fun v => balanceAt (state bodyRoot) v.toNat)
        {v ∈ Store.activeMembers (state bodyRoot) members | v ∉ honest} +
      50 * exitReserve config (state bodyRoot) ≤
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat *
        stake (fun v => balanceAt (state bodyRoot) v.toNat)
          (Store.activeMembers (state bodyRoot) members) := by
  have registered : ∀ v ∈ Store.activeMembers (state bodyRoot) members, v ∈ honest := by
    intro v inside
    obtain ⟨member, _⟩ := Store.mem_activeMembers.mp inside
    obtain ⟨slot, _, _, seat⟩ := (range_members read v).mp member
    exact (seats_pair slot).2.2 v seat
  have none : {v ∈ Store.activeMembers (state bodyRoot) members | v ∉ honest} = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v member
    obtain ⟨inside, dishonest⟩ := Finset.mem_filter.mp member
    exact dishonest (registered v inside)
  -- The two validators of the first slot are active members of the range.
  have pair : stake (fun v => balanceAt (state bodyRoot) v.toNat)
      {2 * (first % 4), 2 * (first % 4) + 1} ≤
      stake (fun v => balanceAt (state bodyRoot) v.toNat)
        (Store.activeMembers (state bodyRoot) members) := by
    apply stake_mono
    intro v inside
    simp only [Finset.mem_insert, Finset.mem_singleton] at inside
    have seat : v ∈ seats first := by
      rcases inside with rfl | rfl
      · exact (seats_pair first).1
      · exact (seats_pair first).2.1
    have member : v ∈ members := (range_members read v).mpr ⟨first, UInt64.le_refl _, ordered, seat⟩
    exact Store.mem_activeMembers.mpr ⟨member, validator 200,
      registered_validator ((seats_pair first).2.2 v seat), rfl⟩
  have value : stake (fun v => balanceAt (state bodyRoot) v.toNat)
      {2 * (first % 4), 2 * (first % 4) + 1} = 400 := by
    have rem : (first % 4).toNat < 4 := by
      rw [UInt64.toNat_mod]
      exact Nat.mod_lt _ (by decide)
    have cases : first % 4 = 0 ∨ first % 4 = 1 ∨ first % 4 = 2 ∨ first % 4 = 3 := by
      simp only [← UInt64.toNat_inj]
      change (first % 4).toNat = 0 ∨ (first % 4).toNat = 1 ∨
        (first % 4).toNat = 2 ∨ (first % 4).toNat = 3
      omega
    rcases cases with eq | eq | eq | eq <;> rw [eq] <;> decide
  rw [none, stake_empty, exit_reserve_state, show config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat = 34
    from rfl]
  omega

/-- The configured proposer boost contributes no stake. -/
theorem proposer_score : computeProposerScore config (state bodyRoot) = .ok 0 := by
  have total : getTotalBalance (state bodyRoot) [0, 1, 2, 3, 4, 5, 6, 7] = .ok 1600 :=
    total_balance
  have balances : unslashedActiveBalances (state bodyRoot) =
      [(0, 200), (1, 200), (2, 200), (3, 200), (4, 200), (5, 200), (6, 200), (7, 200)] := rfl
  simp only [computeProposerScore, calculateCommitteeFraction, balances, List.map_cons,
    List.map_nil, total, Except.mapError, bind, Except.bind]
  rfl

/-- Every receiver uses the same balances, so the adverse weight shift is zero. -/
theorem weights {last : Nat} (bounded : last ≤ 4000) :
    WeightBounds execution (state bodyRoot) 3000 last 0 where
  reads := by
    intro w _ k head s current firstSlot lastSlot maximum _ byLimit _ _ _ checkpoint read
    obtain ⟨code, eq⟩ := store_code (byLimit.trans bounded) w
    rw [eq] at checkpoint
    rw [local_checkpoint checkpoint] at read
    exact ⟨maximum, 0, read, proposer_score⟩
  margin := by
    intro w _ k head s score sourceScore firstSlot lastSlot maximum sourceMaximum _ byLimit
      _ checkpoint receiverScore originalScore receiver original p q _ _
    obtain ⟨code, eq⟩ := store_code (byLimit.trans bounded) w
    rw [eq] at checkpoint
    rw [local_checkpoint checkpoint] at receiverScore receiver ⊢
    rw [receiverScore, Except.ok.injEq] at originalScore
    rw [receiver, Except.ok.injEq] at original
    subst sourceScore sourceMaximum
    exact Nat.le_refl _
  sourceReserve := by
    intro w _ k head firstSlot lastSlot members time ordered read
    obtain ⟨code, eq⟩ := store_code (n := k) (by omega) w
    rw [eq] at read
    exact range_reserve ordered read
  byzantine := by
    intro w _ k head s firstSlot lastSlot members _ byLimit checkpoint read
    obtain ⟨code, eq⟩ := store_code (byLimit.trans bounded) w
    rw [eq] at checkpoint read
    rw [local_checkpoint checkpoint]
    exact range_byzantine read
  dishonest := by
    intro w _ k byLimit v inside
    obtain ⟨code, eq⟩ := store_code (byLimit.trans bounded) w
    rw [eq] at inside
    cases code <;> change v ∈ ([] : List ValidatorIndex) at inside <;> contradiction

/-- Store clocks reach at most the first boundary of epoch one before the limit. -/
theorem current_slot_le_four {n : Nat} {v : ValidatorIndex} {slot : Slot}
    (bounded : (execution.world n).time ≤ 4000)
    (clock : ((execution.world n).state v).getCurrentSlot config = .ok slot) : slot ≤ 4 := by
  have bounds := execution.clock_bounds v n
  have genesis : ((execution.world n).state v).genesisTimeMs = 0 := bounds.1
  have upper : ((execution.world n).state v).timeMs.toNat ≤ (execution.world n).time := by
    simpa only [show (execution.start v).timeMs.toNat = 0 from rfl, Nat.zero_max] using bounds.2.2
  unfold Store.getCurrentSlot at clock
  rw [genesis, mapError_ok_iff] at clock
  exact computeSlotAtTimeMs_mono (show ((execution.world n).state v).timeMs ≤ 4000 from
    UInt64.le_iff_toNat_le.mpr (upper.trans bounded)) clock
    (show computeSlotAtTimeMs config 0 4000 = .ok 4 from rfl)

/-- The finite assignment covers exactly the first epoch's committee seats. -/
theorem seats_assignment {slot : Slot} (past : slot < 4) (v : ValidatorIndex) :
    v ∈ seats slot ↔ ∃ index, assignment.committee v slot = some index := by
  have slots : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by
    have nat := UInt64.lt_iff_toNat_lt.mp past
    simp only [← UInt64.toNat_inj]
    change slot.toNat = 0 ∨ slot.toNat = 1 ∨ slot.toNat = 2 ∨ slot.toNat = 3
    change slot.toNat < 4 at nat
    omega
  by_cases registered : v < 8
  · rcases registered_cases registered with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases slots with rfl | rfl | rfl | rfl <;>
      simp [seats, assignment]
  · have distinct :
        ¬ v = 0 ∧ ¬ v = 1 ∧ ¬ v = 2 ∧ ¬ v = 3 ∧ ¬ v = 4 ∧ ¬ v = 5 ∧ ¬ v = 6 ∧ ¬ v = 7 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact registered (by decide)
    rcases slots with rfl | rfl | rfl | rfl <;> simp [seats, assignment, registered, distinct]

/-- Every past range read by an honest store agrees with the execution's duty assignment. -/
theorem committees_assigned : ∀ w ∈ honest, ∀ k, (execution.world k).time ≤ 4000 →
    ∀ head current first last members,
      ((execution.world k).state w).getHead config = .ok head →
      ((execution.world k).state w).getCurrentSlot config = .ok current → last < current →
      ((execution.world k).state w).getCommitteesBetweenSlots head.root first last = .ok members →
      ∀ v ∈ honest, v ∈ members ↔ ∃ slot index,
        first ≤ slot ∧ slot ≤ last ∧ assignment.committee v slot = some index := by
  intro w _ k bounded head current first last members _ clock past read v _
  have below := current_slot_le_four bounded clock
  obtain ⟨code, eq⟩ := store_code bounded w
  rw [eq] at read
  rw [range_members read]
  constructor
  · rintro ⟨slot, low, high, member⟩
    obtain ⟨index, assigned⟩ := (seats_assignment
      (UInt64.lt_of_le_of_lt high (UInt64.lt_of_lt_of_le past below)) v).mp member
    exact ⟨slot, index, low, high, assigned⟩
  · rintro ⟨slot, index, low, high, assigned⟩
    exact ⟨slot, low, high, (seats_assignment
      (UInt64.lt_of_le_of_lt high (UInt64.lt_of_lt_of_le past below)) v).mpr ⟨index, assigned⟩⟩

/-- The initial state is a common retained source for the head and every cached target. -/
theorem committees_follow : CommitteesFollow execution 4000 where
  assigned := by
    intro w own k bounded head current first last members headOk clock past _ read
    exact committees_assigned w own k bounded head current first last members headOk clock past read
  common := by
    intro w _ k bounded head headState current v attestation targetState _ headOk _ _ _ _ cached
    obtain ⟨code, eq⟩ := store_code bounded w
    rw [eq] at headOk cached
    have target : attestation.data.target = ⟨0, anchorRoot⟩ ∧ targetState = state bodyRoot := by
      cases code <;>
        simp only [Local.store, running, admitted, ticked, anchor, Std.TreeMap.getElem?_insert]
          at cached <;>
        split at cached <;> simp_all [Checkpoint.compare, Ordering.then_eq_eq,
          Std.LawfulEqCmp.compare_eq_iff_eq]
    rw [target.2]
    refine ⟨state bodyRoot, ?_, RunKept.refl _, ?_, ?_, ?_, ?_⟩
    · rcases local_block_state (Store.blockState_ok_iff.mp headOk) with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact RunKept.refl _
      · exact runKept_stateTransition first_transition
    · rw [target.1]; decide
    · rw [target.1]; decide
    · rcases local_block_state (Store.blockState_ok_iff.mp headOk) with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
        rw [target.1] <;> decide
    · rw [target.1]; decide

end EthLib.Consensus.Models.Network.EightValidatorWitness.Trace
