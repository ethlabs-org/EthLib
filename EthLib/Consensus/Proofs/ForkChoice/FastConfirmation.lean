module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.FilterM
public import EthLib.Base.Proofs.MapM
public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.ForkChoice.FastConfirmation
public import EthLib.Consensus.Proofs.ForkChoice.Store
public import EthLib.Consensus.Proofs.Accessors

/-!
# Proofs: the fast confirmation rule

An empty range of slots weighs nothing, and so does a sum over no items.

The adversary has no weight in an empty range.

A sum is the sum of its weights, so at most the sum of bounds on them.

A range of slots that ends later has every member of the committees of a shorter one.

A member of the committees of the slots between two slots shows that the first is earlier.

A range that covers a whole epoch weighs the whole active balance.

At each slot the tracked heads move on by one: the current head becomes the previous one.

The update keeps the confirmed block.

A restart keeps the old confirmed block or takes the one confirmed before the restart.

From Gloas the payload status of the head does not change which blocks are in its chain.

The fast confirmation of a slot records the head of the store, at every fork.

The safe execution block is the payload of the confirmed block, and from Gloas its bid's parent.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Fork}

/-- A sum over no items is zero. -/
theorem sumGwei_nil {α : Type} {weight : α → Except ForkChoiceError Gwei} :
    sumGwei [] weight = .ok 0 := by
  simp [sumGwei, bind, Except.bind, pure, Except.pure]

/-- A sum that the store computes is the sum of its weights. -/
theorem toNat_eq_of_sumGwei {α : Type} {items : List α}
    {weight : α → Except ForkChoiceError Gwei} {value : α → Nat} {total : Gwei}
    (summed : sumGwei items weight = .ok total)
    (each : ∀ item ∈ items, ∀ computed, weight item = .ok computed →
      computed.toNat = value item) :
    total.toNat = (items.map value).sum := by
  -- The fold adds each weight to the running sum.
  have fold : ∀ (rest : List α) (start sum : Nat),
      (∀ item ∈ rest, ∀ computed, weight item = .ok computed → computed.toNat = value item) →
      rest.foldlM (fun sum item => return sum + (← weight item).toNat) start = .ok sum →
      sum = start + (rest.map value).sum := by
    intro rest
    induction rest with
    | nil =>
      intro start sum _ folded
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at folded
      simp [folded]
    | cons first rest ih =>
      intro start sum each folded
      simp only [List.foldlM_cons, bind_ok_iff, pure, Except.pure] at folded
      obtain ⟨next, ⟨computed, computedOk, nextOk⟩, folded⟩ := folded
      simp only [Except.ok.injEq] at nextOk
      subst nextOk
      have head := each first List.mem_cons_self computed computedOk
      have tail := ih _ _ (fun item member => each item (List.mem_cons_of_mem first member))
        folded
      simp only [List.map_cons, List.sum_cons]
      omega
  simp only [sumGwei, bind_ok_iff] at summed
  obtain ⟨sum, sumOk, summed⟩ := summed
  have exact := fold items 0 sum each sumOk
  split at summed
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at summed
  · rename_i small
    simp only [pure, Except.pure, Except.ok.injEq] at summed
    subst summed
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    omega

/-- A sum that the store computes is at most the sum of bounds on its weights. -/
theorem toNat_le_of_sumGwei {α : Type} {items : List α}
    {weight : α → Except ForkChoiceError Gwei} {bound : α → Nat} {total : Gwei}
    (summed : sumGwei items weight = .ok total)
    (each : ∀ item ∈ items, ∀ value, weight item = .ok value → value.toNat ≤ bound item) :
    total.toNat ≤ (items.map bound).sum := by
  let value : α → Nat := fun item => match weight item with
    | .ok computed => computed.toNat
    | .error _ => 0
  rw [toNat_eq_of_sumGwei (value := value) summed fun item _ computed computedOk => by
    simp only [value, computedOk]]
  clear summed
  induction items with
  | nil => simp
  | cons first rest ih =>
    simp only [List.map_cons, List.sum_cons]
    refine Nat.add_le_add ?_ (ih fun item member => each item (List.mem_cons_of_mem _ member))
    · cases computed : weight first with
      | error _ => simp only [value, computed, Nat.zero_le]
      | ok computed' =>
        simpa only [value, computed] using each first List.mem_cons_self computed' computed

/-- The validator at an index is the one that the registry holds there. -/
theorem validatorAt_ok_iff {state : BeaconState preset fork} {index : ValidatorIndex}
    {validator : Validator} :
    validatorAt state index = .ok validator ↔
      state.validators.data[index.toNat]? = some validator := by
  unfold validatorAt
  split <;> simp_all [throw, throwThe, MonadExceptOf.throw, pure, Except.pure]

/-- The members of a set with a list folded in: those of the set and of the list. -/
private theorem mem_list_foldl_insert {v : ValidatorIndex} :
    ∀ {members : List ValidatorIndex} {start : Std.TreeSet ValidatorIndex},
      v ∈ members.foldl (·.insert ·) start ↔ v ∈ start ∨ v ∈ members
  | [], start => by simp
  | first :: rest, start => by
    simp only [List.foldl_cons, mem_list_foldl_insert, Std.TreeSet.mem_insert, List.mem_cons,
      Std.LawfulEqCmp.compare_eq_iff_eq]
    constructor
    · rintro ((rfl | inside) | later)
      · exact .inr (.inl rfl)
      · exact .inl inside
      · exact .inr (.inr later)
    · rintro (inside | rfl | later)
      · exact .inl (.inr inside)
      · exact .inl (.inl rfl)
      · exact .inr later

/-- The members of a set with a committee folded in: those of the set and of the committee. -/
private theorem mem_foldl_insert {committee participants : Std.TreeSet ValidatorIndex}
    {v : ValidatorIndex} :
    v ∈ committee.foldl (·.insert ·) participants ↔ v ∈ participants ∨ v ∈ committee := by
  rw [Std.TreeSet.foldl_eq_foldl_toList, mem_list_foldl_insert, Std.TreeSet.mem_toList]

/-- The members of a set with an array folded in: those of the set and of the array. -/
private theorem mem_array_foldl_insert {committee : Array ValidatorIndex}
    {participants : Std.TreeSet ValidatorIndex} {v : ValidatorIndex} :
    v ∈ committee.foldl (·.insert ·) participants ↔ v ∈ participants ∨ v ∈ committee := by
  rw [← Array.foldl_toList, mem_list_foldl_insert, Array.mem_toList_iff]

/-- The members of a fold that adds what it reads: those it starts with, and those it reads.

Adding a read value must give the members of the set and of the value. -/
private theorem mem_foldlM_add_iff {α β : Type} [Membership ValidatorIndex β]
    {read : α → Except ForkChoiceError β}
    {add : Std.TreeSet ValidatorIndex → β → Std.TreeSet ValidatorIndex} {v : ValidatorIndex}
    (adds : ∀ participants committee,
      v ∈ add participants committee ↔ v ∈ participants ∨ v ∈ committee) :
    ∀ {items : List α} {start out : Std.TreeSet ValidatorIndex},
      items.foldlM (fun (participants : Std.TreeSet ValidatorIndex) item => do
          let committee ← read item
          return add participants committee) start =
        (.ok out : Except ForkChoiceError _) →
      (v ∈ out ↔
        v ∈ start ∨ ∃ item ∈ items, ∃ committee, read item = .ok committee ∧ v ∈ committee)
  | [], start, out, folded => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at folded
    subst folded
    simp
  | first :: rest, start, out, folded => by
    simp only [List.foldlM_cons, bind_ok_iff, pure, Except.pure] at folded
    obtain ⟨next, ⟨committee, readOk, nextOk⟩, folded⟩ := folded
    simp only [Except.ok.injEq] at nextOk
    subst nextOk
    rw [mem_foldlM_add_iff adds folded, adds]
    constructor
    · rintro ((inside | inCommittee) | ⟨item, member, other, otherOk, inOther⟩)
      · exact .inl inside
      · exact .inr ⟨first, List.mem_cons_self, committee, readOk, inCommittee⟩
      · exact .inr ⟨item, List.mem_cons_of_mem first member, other, otherOk, inOther⟩
    · rintro (inside | ⟨item, member, other, otherOk, inOther⟩)
      · exact .inl (.inl inside)
      · rcases List.mem_cons.mp member with rfl | later
        · rw [readOk, Except.ok.injEq] at otherOk
          subst otherOk
          exact .inl (.inr inOther)
        · exact .inr ⟨item, later, other, otherOk, inOther⟩

/-- The members of a fold of committees: those it starts with, and those of a committee it reads.
-/
theorem mem_foldlM_committees_iff {α : Type}
    {read : α → Except ForkChoiceError (Std.TreeSet ValidatorIndex)} {v : ValidatorIndex} :
    ∀ {items : List α} {start out : Std.TreeSet ValidatorIndex},
      items.foldlM (fun (participants : Std.TreeSet ValidatorIndex) item => do
          let committee ← read item
          return committee.foldl (·.insert ·) participants) start =
        (.ok out : Except ForkChoiceError _) →
      (v ∈ out ↔
        v ∈ start ∨ ∃ item ∈ items, ∃ committee, read item = .ok committee ∧ v ∈ committee) :=
  mem_foldlM_add_iff fun _ _ => mem_foldl_insert

namespace Store

variable {config : Config} {store : Store preset fork}

/-- A range that starts after it ends weighs nothing. -/
theorem computeCommitteeWeightBetweenSlots_of_gt {head : Root}
    {balanceSource : BeaconState preset fork} {startSlot endSlot : Slot}
    (empty : endSlot < startSlot) :
    store.computeCommitteeWeightBetweenSlots head balanceSource startSlot endSlot = .ok 0 := by
  simp [computeCommitteeWeightBetweenSlots, computeCommitteeWeightAndMembers, empty, bind,
    Except.bind, pure, Except.pure]

/-- A range that covers a whole epoch weighs the total active balance of the source. -/
theorem computeCommitteeWeightBetweenSlots_of_covered {head : Root}
    {balanceSource : BeaconState preset fork} {startSlot endSlot : Slot}
    (covered : isFullValidatorSetCovered preset startSlot endSlot = .ok true) :
    store.computeCommitteeWeightBetweenSlots head balanceSource startSlot endSlot =
      (getTotalActiveBalance balanceSource).mapError .accessor := by
  -- A covered range ends in a later epoch than its first slot, so it is not empty.
  have ordered : startSlot ≤ endSlot := by
    have steps := covered
    simp only [isFullValidatorSetCovered, bind_ok_iff, mapError_ok_iff] at steps
    obtain ⟨afterFirst, first, lastOfFirst, last, afterEnd, after, later⟩ := steps
    have one : (1 : UInt64).toNat = 1 := rfl
    rw [Uint64.addChecked_ok_iff] at first after
    rw [Uint64.subChecked_ok_iff] at last
    rw [one] at last after
    have later : (lastOfFirst / preset.SLOTS_PER_EPOCH).toNat <
        (afterEnd / preset.SLOTS_PER_EPOCH).toNat := by
      simpa [pure, Except.pure, computeEpochAtSlot, UInt64.lt_iff_toNat_lt] using later
    rw [UInt64.toNat_div, UInt64.toNat_div] at later
    have below : lastOfFirst.toNat < afterEnd.toNat :=
      Nat.lt_of_not_ge fun ge => absurd later (Nat.not_lt.mpr (Nat.div_le_div_right ge))
    have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by
      rcases Nat.eq_zero_or_pos preset.SLOTS_PER_EPOCH.toNat with zero | positive
      · simp [zero] at later
      · exact positive
    rw [UInt64.le_iff_toNat_le]
    omega
  have notGt : ¬ endSlot < startSlot := UInt64.not_lt.mpr ordered
  simp only [computeCommitteeWeightBetweenSlots, computeCommitteeWeightAndMembers, notGt,
    covered, ↓reduceIte]
  cases (getTotalActiveBalance balanceSource) <;> rfl

/-- A range of slots that starts after it ends has no members of its committees. -/
theorem getCommitteesBetweenSlots_of_gt {head : Root} {startSlot endSlot : Slot}
    (empty : endSlot < startSlot) :
    store.getCommitteesBetweenSlots head startSlot endSlot = .ok ∅ := by
  have below : endSlot.toNat + 1 < 2 ^ 64 := by
    have := UInt64.lt_iff_toNat_lt.mp empty
    have := startSlot.toNat_lt
    omega
  have afterEndOk : Uint64.addChecked endSlot 1 = .ok (endSlot + 1) := by
    rw [Uint64.addChecked_ok_iff]
    refine ⟨by simpa using below, ?_⟩
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by simpa using below)]
  have zero : (endSlot + 1).toNat - startSlot.toNat = 0 := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by simpa using below)]
    have := UInt64.lt_iff_toNat_lt.mp empty
    simp only [UInt64.toNat_one]
    omega
  simp only [getCommitteesBetweenSlots, afterEndOk, Except.mapError, bind, Except.bind, zero,
    List.range_zero, List.foldlM_nil, pure, Except.pure]

/-- A slot is before another when the committees of the slots between them have a member.

The range starts at the slot after the first and ends at the slot before the second.

This is the empty-slot range of arXiv 2405.00549v4, Definition 5. -/
theorem lt_of_mem_getCommitteesBetweenSlots {head : Root} {low high firstSlot lastSlot : Slot}
    {participants : Std.TreeSet ValidatorIndex} {v : ValidatorIndex}
    (firstOk : Uint64.addChecked low 1 = .ok firstSlot)
    (lastOk : Uint64.subChecked high 1 = .ok lastSlot)
    (participantsOk : store.getCommitteesBetweenSlots head firstSlot lastSlot = .ok participants)
    (member : v ∈ participants) : low < high := by
  refine UInt64.not_le.mp fun notLower => ?_
  have empty : lastSlot < firstSlot := by
    rw [Uint64.subChecked_ok_iff] at lastOk
    rw [Uint64.addChecked_ok_iff] at firstOk
    rw [UInt64.le_iff_toNat_le] at notLower
    rw [UInt64.lt_iff_toNat_lt]
    simp only [UInt64.toNat_one] at firstOk lastOk
    omega
  rw [getCommitteesBetweenSlots_of_gt empty, Except.ok.injEq] at participantsOk
  exact absurd (participantsOk ▸ member) Std.TreeSet.not_mem_emptyc

/-- The members that come with a committee weight are those of the committees of its range. -/
theorem getCommitteesBetweenSlots_of_computeCommitteeWeightAndMembers {head : Root}
    {balanceSource : BeaconState preset fork} {startSlot endSlot : Slot} {weight : Gwei}
    {participants : Std.TreeSet ValidatorIndex}
    (computed : store.computeCommitteeWeightAndMembers head balanceSource startSlot endSlot =
      .ok (weight, some participants)) :
    store.getCommitteesBetweenSlots head startSlot endSlot = .ok participants := by
  simp only [computeCommitteeWeightAndMembers] at computed
  split at computed
  · simp [pure, Except.pure] at computed
  · rw [bind_ok_iff] at computed
    obtain ⟨covered, -, computed⟩ := computed
    cases covered
    · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok_iff, mapError_ok_iff] at computed
      obtain ⟨found, foundOk, _, -, _, -, final⟩ := computed
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at final
      exact final.2 ▸ foundOk
    · simp only [↓reduceIte, bind_ok_iff, mapError_ok_iff] at computed
      obtain ⟨_, -, final⟩ := computed
      simp [pure, Except.pure] at final

/-- A member of the committees of a range is a member of those of a range that ends later.

Both ranges start at one slot. -/
theorem mem_getCommitteesBetweenSlots_of_le {head : Root} {startSlot shortEnd endSlot : Slot}
    {short long : Std.TreeSet ValidatorIndex}
    (shortOk : store.getCommitteesBetweenSlots head startSlot shortEnd = .ok short)
    (longOk : store.getCommitteesBetweenSlots head startSlot endSlot = .ok long)
    (le : shortEnd ≤ endSlot) {v : ValidatorIndex} (member : v ∈ short) : v ∈ long := by
  simp only [getCommitteesBetweenSlots, bind_ok_iff, mapError_ok_iff] at shortOk longOk
  obtain ⟨afterShort, afterShortOk, shortOk⟩ := shortOk
  obtain ⟨afterEnd, afterEndOk, longOk⟩ := longOk
  rw [Uint64.addChecked_ok_iff] at afterShortOk afterEndOk
  rw [UInt64.le_iff_toNat_le] at le
  have one : (1 : UInt64).toNat = 1 := rfl
  rw [one] at afterShortOk afterEndOk
  rcases (mem_foldlM_committees_iff shortOk).mp member with none | ⟨offset, inRange, rest⟩
  · simp at none
  refine (mem_foldlM_committees_iff longOk).mpr (.inr ⟨offset, ?_, rest⟩)
  rw [List.mem_range] at inRange ⊢
  omega

/-- A member of a committee of a slot, in the state of the head, is one that the rule reads for it.

The index of the committee must be below the count of committees per slot of the epoch of the slot.
-/
theorem mem_getSlotCommittee {head : Root} {slot : Slot} {headState : BeaconState preset fork}
    {index : CommitteeIndex} {committee : Array ValidatorIndex}
    {members : Std.TreeSet ValidatorIndex} {validator : ValidatorIndex}
    (computed : store.getSlotCommittee head slot = .ok members)
    (stateOk : store.blockState head = .ok headState)
    (below : index < getCommitteeCountPerSlot headState (computeEpochAtSlot preset slot))
    (committeeOk : getBeaconCommittee headState slot index = .ok committee)
    (member : validator ∈ committee) :
    validator ∈ members := by
  simp only [getSlotCommittee, stateOk, bind, Except.bind] at computed
  have back : index.toNat.toUInt64 = index := UInt64.ofNat_toNat
  refine (mem_foldlM_add_iff (fun _ _ => mem_array_foldl_insert) computed).mpr
    (.inr ⟨index.toNat, ?_, committee, ?_, member⟩)
  · exact List.mem_range.mpr (UInt64.lt_iff_toNat_lt.mp below)
  · rw [back, committeeOk]
    rfl

/-- A member of a committee of a slot of a range, in the state of the head, is one the rule reads.

The index of the committee must be below the count of committees per slot of the epoch of the slot.
-/
theorem mem_getCommitteesBetweenSlots {head : Root} {startSlot endSlot slot : Slot}
    {participants : Std.TreeSet ValidatorIndex} {headState : BeaconState preset fork}
    {index : CommitteeIndex} {committee : Array ValidatorIndex} {validator : ValidatorIndex}
    (computed : store.getCommitteesBetweenSlots head startSlot endSlot = .ok participants)
    (low : startSlot ≤ slot) (high : slot ≤ endSlot)
    (stateOk : store.blockState head = .ok headState)
    (below : index < getCommitteeCountPerSlot headState (computeEpochAtSlot preset slot))
    (committeeOk : getBeaconCommittee headState slot index = .ok committee)
    (member : validator ∈ committee) :
    validator ∈ participants := by
  simp only [getCommitteesBetweenSlots, bind_ok_iff, mapError_ok_iff] at computed
  obtain ⟨afterEnd, afterEndOk, folded⟩ := computed
  rw [Uint64.addChecked_ok_iff, UInt64.toNat_one] at afterEndOk
  rw [UInt64.le_iff_toNat_le] at low high
  -- The slot is the start moved on by its offset, which lies in the range.
  have inRange : slot.toNat - startSlot.toNat ∈ List.range (afterEnd.toNat - startSlot.toNat) :=
    List.mem_range.mpr (by omega)
  have back : startSlot + (slot.toNat - startSlot.toNat).toUInt64 = slot := by
    rw [← UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr low), Nat.toUInt64_eq,
      UInt64.ofNat_toNat, UInt64.add_comm, UInt64.sub_add_cancel]
  obtain ⟨members, membersOk⟩ := foldlM_forall_of_ok
    (fun _ _ _ stepOk => (bind_ok_iff.mp stepOk).imp fun _ read => read.1) _ _ _ folded _
    inRange
  rw [back] at membersOk
  have inMembers := mem_getSlotCommittee membersOk stateOk below committeeOk member
  refine (mem_foldlM_committees_iff folded).mpr (.inr ⟨_, inRange, members, ?_, inMembers⟩)
  rw [back, membersOk]

/-- The adversary of a range reads the committee weight, its share, then the equivocators.

That holds for every input, errors included, so reading the members once changes nothing. -/
theorem computeAdversarialWeight_eq_spec {config : Config} {head : Root}
    {balanceSource : BeaconState preset fork} {startSlot endSlot : Slot} :
    store.computeAdversarialWeight config head balanceSource startSlot endSlot = (do
      let w ← store.computeCommitteeWeightBetweenSlots head balanceSource startSlot endSlot
      let s ← (Uint64.mulChecked (w / 100) config.CONFIRMATION_BYZANTINE_THRESHOLD).mapError .arith
      let e ← store.getEquivocationScore head balanceSource startSlot endSlot
      return Uint64.saturatingSub s e) := by
  unfold computeAdversarialWeight computeCommitteeWeightBetweenSlots
  rcases pair : store.computeCommitteeWeightAndMembers head balanceSource startSlot endSlot with
    _ | ⟨w, _ | m⟩
  · rfl
  · simp only [bind, Except.bind, pure, Except.pure, getEquivocationScore]
    split <;> try rfl
    split <;> rfl
  · have := getCommitteesBetweenSlots_of_computeCommitteeWeightAndMembers pair
    simp [bind, Except.bind, pure, Except.pure, getEquivocationScore, this]

/-- A range of slots that starts after it ends has no adversarial weight.

This serves the case of arXiv 2405.00549v4, Definition 5, with no empty slot. -/
theorem computeAdversarialWeight_of_gt {config : Config} {head : Root}
    {balanceSource : BeaconState preset fork} {startSlot endSlot : Slot}
    (empty : endSlot < startSlot) :
    store.computeAdversarialWeight config head balanceSource startSlot endSlot = .ok 0 := by
  have noMember : (∅ : Std.TreeSet ValidatorIndex).toList = [] := rfl
  have noShare : Uint64.mulChecked (0 / 100) config.CONFIRMATION_BYZANTINE_THRESHOLD = .ok 0 := by
    rw [Uint64.mulChecked_ok_iff]
    simp
  have noScore : store.getEquivocationScoreOf balanceSource ∅ = .ok 0 := by
    unfold getEquivocationScoreOf
    rw [noMember]
    obtain ⟨out, filtered⟩ := filterM_exists_ok
      (test := fun v : ValidatorIndex => do
        return isActiveValidator (← validatorAt balanceSource v) (getCurrentEpoch balanceSource))
      (list := []) (by simp)
    have emptyOut := List.eq_nil_of_sublist_nil (sublist_of_filterM_ok filtered)
    simp only [List.filter_nil]
    rw [filtered, emptyOut]
    simp only [bind, Except.bind, sumGwei_nil]
  rw [computeAdversarialWeight_eq_spec, computeCommitteeWeightBetweenSlots_of_gt empty]
  simp only [getEquivocationScore, getCommitteesBetweenSlots_of_gt empty, noShare, noScore, bind,
    Except.bind, pure, Except.pure, Except.mapError]
  rfl

/-- At each slot the tracked heads move on: the current head becomes the previous one. -/
theorem updateFastConfirmationVariables_heads {fcr after : FastConfirmationStore} {head : Root}
    (updated : store.updateFastConfirmationVariables config fcr head = .ok after) :
    (after.previousSlotHead, after.currentSlotHead) = (fcr.currentSlotHead, head) := by
  unfold updateFastConfirmationVariables at updated
  simp only [bind_ok_iff] at updated
  obtain ⟨_, -, _, -, _, -, updated⟩ := updated
  split at updated <;> simp only [bind_ok_iff] at updated <;>
    obtain ⟨_, -, updated⟩ := updated <;> split at updated <;>
    (simp only [pure, Except.pure, Except.ok.injEq] at updated; subst updated; rfl)

/-- The update of the tracked variables leaves the confirmed block as it was. -/
theorem updateFastConfirmationVariables_confirmedRoot {fcr after : FastConfirmationStore}
    {head : Root}
    (updated : store.updateFastConfirmationVariables config fcr head = .ok after) :
    after.confirmedRoot = fcr.confirmedRoot := by
  unfold updateFastConfirmationVariables at updated
  simp only [bind_ok_iff] at updated
  obtain ⟨_, -, _, -, _, -, updated⟩ := updated
  split at updated <;> simp only [bind_ok_iff] at updated <;>
    obtain ⟨_, -, updated⟩ := updated <;> split at updated <;>
    (simp only [pure, Except.pure, Except.ok.injEq] at updated; subst updated; rfl)

/-- A restart keeps the old confirmed block, or takes the block confirmed before the restart. -/
theorem getRestartResilientConfirmedRoot_eq_or {fcr : FastConfirmationStore}
    {head rootBeforeRestart root : Root}
    (restarted : store.getRestartResilientConfirmedRoot config fcr head rootBeforeRestart =
      .ok root) :
    root = fcr.confirmedRoot ∨ root = rootBeforeRestart := by
  unfold getRestartResilientConfirmedRoot at restarted
  simp only [bind_ok_iff] at restarted
  obtain ⟨_, -, _, -, restarted⟩ := restarted
  split at restarted
  · simp only [pure, Except.pure, Except.ok.injEq] at restarted
    exact Or.inl restarted.symm
  · simp only [bind_ok_iff] at restarted
    obtain ⟨_, -, restarted⟩ := restarted
    split at restarted
    · simp only [pure, Except.pure, Except.ok.injEq] at restarted
      exact Or.inl restarted.symm
    · simp only [bind_ok_iff] at restarted
      obtain ⟨_, -, restarted⟩ := restarted
      split at restarted
      · simp only [pure, Except.pure, Except.ok.injEq] at restarted
        exact Or.inl restarted.symm
      · simp only [pure, Except.pure, Except.ok.injEq] at restarted
        exact Or.inr restarted.symm

/-- From Gloas the payload status of the head does not change whether a block is in its chain.

So a head given by its root, as a pending node, answers as the head that the fork choice finds. -/
theorem isAncestor_head_pending (gloas : .glamsterdam ≤ fork) (head : ForkChoiceNode)
    (root : Root) :
    store.isAncestor head ⟨root, .pending⟩ =
      store.isAncestor ⟨head.root, .pending⟩ ⟨root, .pending⟩ := by
  rw [isAncestor_pending gloas, isAncestor_pending gloas]
  simp only [bind, Except.bind]
  split
  · rfl
  · rename_i ancestorBlock _
    have same := getAncestor_root (store := store) head .pending ancestorBlock.slot
    revert same
    cases store.getAncestor head ancestorBlock.slot <;>
      cases store.getAncestor ⟨head.root, .pending⟩ ancestorBlock.slot <;>
      simp_all [Functor.map, Except.map, pure, Except.pure]

/-- The fast confirmation of a slot records the head of the store as the head of the slot.

The head of the slot before becomes the previous head. -/
theorem onFastConfirmation_heads {fcr after : FastConfirmationStore}
    (confirmed : store.onFastConfirmation config fcr = .ok after) :
    ∃ head, store.getHead config = .ok head ∧
      (after.previousSlotHead, after.currentSlotHead) = (fcr.currentSlotHead, head.root) := by
  unfold onFastConfirmation at confirmed
  simp only [bind_ok_iff] at confirmed
  obtain ⟨head, found, updated, update, root, -, confirmed⟩ := confirmed
  simp only [pure, Except.pure, Except.ok.injEq] at confirmed
  subst confirmed
  exact ⟨head, found, updateFastConfirmationVariables_heads (after := updated) update⟩

/-- Before Gloas the execution block of a block of the store is its payload. -/
theorem executionBlockHashAt_of_lt {root : Root} {bellatrix : .bellatrix ≤ fork}
    (before : fork < .glamsterdam) :
    store.executionBlockHashAt root bellatrix =
      (fun block => (block.body.executionPayload ⟨bellatrix, before⟩).blockHash) <$>
        store.block root := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le.mpr before
  simp only [executionBlockHashAt, notGloas, ↓reduceDIte, bind, Except.bind, pure,
    Except.pure, Functor.map, Except.map]

/-- From Gloas the execution block of a block of the store is the parent payload of its bid. -/
theorem executionBlockHashAt_of_gloas {root : Root} {bellatrix : .bellatrix ≤ fork}
    (gloas : .glamsterdam ≤ fork) :
    store.executionBlockHashAt root bellatrix =
      (fun block => (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) <$>
        store.block root := by
  simp only [executionBlockHashAt, gloas, ↓reduceDIte, bind, Except.bind, pure,
    Except.pure, Functor.map, Except.map]

/-- Before Gloas the safe execution block is the payload of the confirmed block. -/
theorem getSafeExecutionBlockHash_of_lt {fcr : FastConfirmationStore}
    {bellatrix : .bellatrix ≤ fork} (before : fork < .glamsterdam) :
    store.getSafeExecutionBlockHash fcr bellatrix =
      (fun block => (block.body.executionPayload ⟨bellatrix, before⟩).blockHash) <$>
        store.block fcr.confirmedRoot :=
  store.executionBlockHashAt_of_lt before

/-- From Gloas the safe execution block is the parent payload of the bid of the confirmed block. -/
theorem getSafeExecutionBlockHash_of_gloas {fcr : FastConfirmationStore}
    {bellatrix : .bellatrix ≤ fork} (gloas : .glamsterdam ≤ fork) :
    store.getSafeExecutionBlockHash fcr bellatrix =
      (fun block => (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) <$>
        store.block fcr.confirmedRoot :=
  store.executionBlockHashAt_of_gloas gloas

/-- Before Gloas the finalized execution block is the payload of the finalized block. -/
theorem getFinalizedExecutionBlockHash_of_lt {bellatrix : .bellatrix ≤ fork}
    (before : fork < .glamsterdam) :
    store.getFinalizedExecutionBlockHash bellatrix =
      (fun block => (block.body.executionPayload ⟨bellatrix, before⟩).blockHash) <$>
        store.block store.finalizedCheckpoint.root :=
  store.executionBlockHashAt_of_lt before

/-- From Gloas the finalized execution block is the parent payload of the finalized bid. -/
theorem getFinalizedExecutionBlockHash_of_gloas {bellatrix : .bellatrix ≤ fork}
    (gloas : .glamsterdam ≤ fork) :
    store.getFinalizedExecutionBlockHash bellatrix =
      (fun block => (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) <$>
        store.block store.finalizedCheckpoint.root :=
  store.executionBlockHashAt_of_gloas gloas

/-- A committee that has a value is cut from indices whose number times its end fits in 64 bits. -/
private theorem fits_of_computeCommittee {indices : Array ValidatorIndex} {seed : Bytes32}
    {index count : UInt64} {committee : Array ValidatorIndex}
    (computed : computeCommittee preset indices seed index count = .ok committee) :
    indices.size * (index.toNat + 1) < 2 ^ 64 := by
  cases shuffle : computeShuffledPermutation preset (UInt64.ofNat indices.size) seed with
  | error err =>
    simp [computeCommittee, shuffle, bind, Except.bind] at computed
  | ok shuffled =>
    simp only [computeCommittee, shuffle, bind, Except.bind, shuffledCommittee] at computed
    split at computed
    · simp [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at computed
    · split at computed
      · rename_i ok
        exact ok.2
      · simp [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at computed

open Uint64 in
/-- A validator active in an epoch is a member of the committees of its whole range of slots.

The range is that of a whole epoch, and the committees are read in the state of the head. -/
theorem mem_getCommitteesBetweenSlots_of_isActiveAt {head : Root}
    {headState : BeaconState preset fork} {epoch : Epoch} {epochStart next epochEnd : Slot}
    {members : Std.TreeSet ValidatorIndex}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (startOk : computeStartSlotAtEpoch preset epoch = .ok epochStart)
    (nextOk : addChecked epochStart preset.SLOTS_PER_EPOCH = .ok next)
    (endOk : subChecked next 1 = .ok epochEnd)
    (stateOk : store.blockState head = .ok headState)
    (computed : store.getCommitteesBetweenSlots head epochStart epochEnd = .ok members)
    {v : ValidatorIndex} (active : isActiveAt headState epoch v.toNat = true) : v ∈ members := by
  classical
  have lengthLt := UInt64.toNat_lt preset.SLOTS_PER_EPOCH
  obtain ⟨startFits, startNat⟩ := computeStartSlotAtEpoch_ok_iff.mp startOk
  obtain ⟨nextFits, nextNat⟩ := addChecked_ok_iff.mp nextOk
  obtain ⟨oneLe, endNat⟩ := subChecked_ok_iff.mp endOk
  simp only [UInt64.toNat_one] at oneLe endNat
  have endEpoch : computeEpochAtSlot preset epochEnd = epoch := by
    apply UInt64.toNat_inj.mp
    rw [computeEpochAtSlot, UInt64.toNat_div, endNat, nextNat, startNat]
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [Nat.succ_mul]
      omega
  simp only [getCommitteesBetweenSlots, bind_ok_iff, mapError_ok_iff] at computed
  obtain ⟨afterEnd, afterEndOk, folded⟩ := computed
  obtain ⟨afterEndFits, afterEndNat⟩ := addChecked_ok_iff.mp afterEndOk
  simp only [UInt64.toNat_one] at afterEndFits afterEndNat
  -- The last slot of the epoch has a committee that the rule reads.
  have inRange : preset.SLOTS_PER_EPOCH.toNat - 1 ∈
      List.range (afterEnd.toNat - epochStart.toNat) :=
    List.mem_range.mpr (by omega)
  obtain ⟨lastMembers, lastOk⟩ := foldlM_forall_of_ok
    (fun _ _ _ stepOk => (bind_ok_iff.mp stepOk).imp fun _ read => read.1) _ _ _ folded _
    inRange
  have back : epochStart + (preset.SLOTS_PER_EPOCH.toNat - 1).toUInt64 = epochEnd := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega : preset.SLOTS_PER_EPOCH.toNat - 1 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega)]
    omega
  rw [back] at lastOk
  simp only [getSlotCommittee, stateOk, bind, Except.bind, endEpoch] at lastOk
  have perPos := UInt64.le_iff_toNat_le.mp (one_le_getCommitteeCountPerSlot headState epoch)
  simp only [UInt64.toNat_one] at perPos
  have perLt := UInt64.toNat_lt (getCommitteeCountPerSlot headState epoch)
  obtain ⟨lastCommittee, lastCommitteeOk⟩ := foldlM_forall_of_ok
    (P := fun index => ∃ committee,
      getBeaconCommittee headState epochEnd index.toUInt64 = .ok committee)
    (fun _ _ _ stepOk => by
      obtain ⟨committee, read, -⟩ := bind_ok_iff.mp stepOk
      exact ⟨committee, mapError_ok_iff.mp read⟩) _ _ _ lastOk
    ((getCommitteeCountPerSlot headState epoch).toNat - 1) (List.mem_range.mpr (by omega))
  obtain ⟨seed, position, count, seedOk, positionNat, countNat, committeeOk⟩ :=
    getBeaconCommittee_ok lastCommitteeOk
  obtain ⟨activeList, shuffled, shuffleOk⟩ :=
    attesterShuffle_ok_of_getBeaconCommittee lastCommitteeOk
  rw [endEpoch] at seedOk positionNat countNat committeeOk shuffleOk
  have indicesFit := getActiveValidatorIndicesChecked_of_attesterShuffle shuffleOk
  have fits := fits_of_computeCommittee committeeOk
  have indexNat : ((getCommitteeCountPerSlot headState epoch).toNat - 1).toUInt64.toNat =
      (getCommitteeCountPerSlot headState epoch).toNat - 1 := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have endMod : (epochEnd % preset.SLOTS_PER_EPOCH).toNat = preset.SLOTS_PER_EPOCH.toNat - 1 := by
    rw [UInt64.toNat_mod, endNat, nextNat, startNat]
    have : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat - 1 =
        (preset.SLOTS_PER_EPOCH.toNat - 1) + preset.SLOTS_PER_EPOCH.toNat * epoch.toNat := by
      rw [Nat.mul_comm]
      omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [positionNat, endMod, indexNat] at fits
  have equal : (preset.SLOTS_PER_EPOCH.toNat - 1) *
      (getCommitteeCountPerSlot headState epoch).toNat +
      ((getCommitteeCountPerSlot headState epoch).toNat - 1) + 1 =
      (getCommitteeCountPerSlot headState epoch).toNat * preset.SLOTS_PER_EPOCH.toNat := by
    obtain ⟨l, hl⟩ : ∃ l, preset.SLOTS_PER_EPOCH.toNat = l + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
      positive).symm⟩
    obtain ⟨c, hc⟩ : ∃ c, (getCommitteeCountPerSlot headState epoch).toNat = c + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
    rw [hl, hc]
    simp only [Nat.add_sub_cancel]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    rw [Nat.mul_comm c l]
    omega
  rw [equal] at fits
  simp only [List.size_toArray] at fits
  have sizeFits : (getActiveValidatorIndices headState epoch).toArray.size < 2 ^ 64 := by
    simpa only [List.size_toArray] using
      Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) positive)) fits
  have small : (getActiveValidatorIndices headState epoch).length ≤ 2 ^ 40 := by
    simpa using le_of_computeCommittee sizeFits committeeOk
  obtain ⟨slot, index, committee, slotEpoch, indexLt, slotCommitteeOk, mem⟩ :=
    exists_mem_getBeaconCommittee indicesFit seedOk (by
      intro zero
      have := congrArg UInt64.toNat zero
      simp only [UInt64.toNat_zero] at this
      omega) (by rw [Nat.succ_mul]; omega) small fits
    (mem_getActiveValidatorIndices_of_isActiveAt active)
  have slotNat := congrArg UInt64.toNat slotEpoch
  rw [computeEpochAtSlot, UInt64.toNat_div] at slotNat
  have divided := Nat.div_add_mod slot.toNat preset.SLOTS_PER_EPOCH.toNat
  have remainder := Nat.mod_lt slot.toNat positive
  rw [slotNat] at divided
  rw [Nat.mul_comm] at divided
  exact mem_getCommitteesBetweenSlots (by
    simp only [getCommitteesBetweenSlots, bind_ok_iff, mapError_ok_iff]
    exact ⟨afterEnd, afterEndOk, folded⟩) (UInt64.le_iff_toNat_le.mpr (by omega))
    (UInt64.le_iff_toNat_le.mpr (by omega)) stateOk (slotEpoch ▸ indexLt) slotCommitteeOk mem

end Store

end EthLib.Consensus
