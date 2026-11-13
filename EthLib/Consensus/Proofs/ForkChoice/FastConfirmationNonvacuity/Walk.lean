module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Stores

/-! Four received votes make the candidate store's walk confirm its slot-1 child.

These are store computations, not yet a certificate of a network execution. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.EightValidatorWitness

open Base Serialization.Ssz

set_option maxRecDepth 10000 in
/-- Processing the child leaves the epoch-zero committee assignment unchanged. -/
theorem post_committees :
    getBeaconCommittee postState 0 0 = .ok #[0, 1] ∧
    getBeaconCommittee postState 1 0 = .ok #[2, 3] ∧
    getBeaconCommittee postState 2 0 = .ok #[4, 5] ∧
    getBeaconCommittee postState 3 0 = .ok #[6, 7] := by
  change getBeaconCommittee (state bodyRoot) 0 0 = .ok #[0, 1] ∧
    getBeaconCommittee (state bodyRoot) 1 0 = .ok #[2, 3] ∧
    getBeaconCommittee (state bodyRoot) 2 0 = .ok #[4, 5] ∧
    getBeaconCommittee (state bodyRoot) 3 0 = .ok #[6, 7]
  exact committees bodyRoot

set_option maxRecDepth 10000 in
/-- Slots 1 and 2 each assign two honest validators in every candidate store. -/
theorem running_committees (time : UInt64) (count : Nat) :
    (running time count).getSlotCommittee blockRoot 1 =
      .ok (((∅ : Std.TreeSet ValidatorIndex).insert 2).insert 3) ∧
    (running time count).getSlotCommittee blockRoot 2 =
      .ok (((∅ : Std.TreeSet ValidatorIndex).insert 4).insert 5) := by
  have stored : (running time count).blockState blockRoot = .ok postState := by
    simp [Store.blockState, running, admitted, pure, Except.pure]
  have one : getCommitteeCountPerSlot postState 0 = 1 := rfl
  simp only [Store.getSlotCommittee, stored, bind, Except.bind,
    show computeEpochAtSlot preset 1 = 0 from rfl,
    show computeEpochAtSlot preset 2 = 0 from rfl, one]
  change (do let committee ← (getBeaconCommittee postState 1 0).mapError ForkChoiceError.accessor
             pure (committee.foldl Std.TreeSet.insert (∅ : Std.TreeSet ValidatorIndex))) =
      .ok (((∅ : Std.TreeSet ValidatorIndex).insert 2).insert 3) ∧
    (do let committee ← (getBeaconCommittee postState 2 0).mapError ForkChoiceError.accessor
        pure (committee.foldl Std.TreeSet.insert (∅ : Std.TreeSet ValidatorIndex))) =
      .ok (((∅ : Std.TreeSet ValidatorIndex).insert 4).insert 5)
  rw [post_committees.2.1, post_committees.2.2.1]
  exact ⟨rfl, rfl⟩

set_option maxRecDepth 10000 in
/-- The interval before slot 3 contains exactly validators 2, 3, 4 and 5. -/
theorem running_committee_range (time : UInt64) (count : Nat) :
    (running time count).getCommitteesBetweenSlots blockRoot 1 2 =
      .ok (((((∅ : Std.TreeSet ValidatorIndex).insert 2).insert 3).insert 4).insert 5) := by
  have afterEnd : Uint64.addChecked 2 1 = .ok 3 := rfl
  simp only [Store.getCommitteesBetweenSlots, afterEnd, Except.mapError, bind, Except.bind,
    show List.range ((3 : Slot).toNat - (1 : Slot).toNat) = [0, 1] from rfl,
    List.foldlM_cons, List.foldlM_nil,
    show (1 : Slot) + (0 : Nat).toUInt64 = 1 from rfl,
    show (1 : Slot) + (1 : Nat).toUInt64 = 2 from rfl,
    (running_committees time count).1, (running_committees time count).2]
  rfl

set_option maxRecDepth 10000 in
/-- The four assigned validators contribute 800 Gwei of active effective balance. -/
theorem running_committee_weight (time : UInt64) (count : Nat) :
    (running time count).computeCommitteeWeightAndMembers blockRoot (state bodyRoot) 1 2 =
      .ok (800, some (((((∅ : Std.TreeSet ValidatorIndex).insert 2).insert 3).insert 4).insert
        5)) := by
  have total : getTotalBalance (state bodyRoot) [2, 3, 4, 5] = .ok 800 := by
    rw [getTotalBalance_ok_iff]
    simp only [List.forall_mem_cons, sumMarked_eq_sum, getElem?_markIndices]
    decide
  simp only [Store.computeCommitteeWeightAndMembers,
    show ¬ (1 : Slot) > 2 by decide, ↓reduceIte,
    show isFullValidatorSetCovered preset 1 2 = .ok false from rfl,
    running_committee_range, bind, Except.bind]
  change (do
    let active ← [(2 : ValidatorIndex), 3, 4, 5].filterM fun index => do
      pure (isActiveValidator (← validatorAt (state bodyRoot) index) 0)
    pure (← (getTotalBalance (state bodyRoot) active).mapError _,
      some (((((∅ : Std.TreeSet ValidatorIndex).insert 2).insert 3).insert 4).insert 5))) = _
  have active : ([(2 : ValidatorIndex), 3, 4, 5].filterM fun index => do
      pure (isActiveValidator (← validatorAt (state bodyRoot) index) 0)) =
      (.ok [2, 3, 4, 5] : Except ForkChoiceError _) := by
    have passes : ∀ index ∈ [(2 : ValidatorIndex), 3, 4, 5],
        (do pure (isActiveValidator (← validatorAt (state bodyRoot) index) 0)) =
          (.ok true : Except ForkChoiceError Bool) := by
      intro index member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> rfl
    obtain ⟨out, filtered⟩ := filterM_exists_ok (fun index member =>
      ⟨true, passes index member⟩)
    have contains : [(2 : ValidatorIndex), 3, 4, 5] ⊆ out := fun index member =>
      mem_filterM_ok_of_test filtered member (passes index member)
    have eq := (sublist_of_filterM_ok filtered).eq_of_length_le
      ((show [(2 : ValidatorIndex), 3, 4, 5].Nodup by decide).length_le_of_subset contains)
    simpa only [eq] using filtered
  rw [active]
  simp only [bind, Except.bind, total]
  rfl

set_option maxRecDepth 10000 in
/-- Half the committee weight plus its 34-percent adversarial bound is 672 Gwei. -/
theorem running_threshold (count : Nat) :
    (running 3000 count).computeSafetyThreshold config blockRoot blockRoot (state bodyRoot) =
      .ok 672 := by
  have child : (running 3000 count).block blockRoot = .ok signedBlock.message := by
    simp [Store.block, running_child, pure, Except.pure]
  have parent : (running 3000 count).block anchorRoot = .ok (anchorBlock stateRoot) := by
    simp [Store.block, running_anchor, pure, Except.pure]
  have slot : (running 3000 count).getCurrentSlot config = .ok 3 := by
    change (computeSlotAtTimeMs config 0 3000).mapError ForkChoiceError.arith = .ok 3
    have clock : computeSlotAtTimeMs config 0 3000 = .ok 3 := by
      simp [computeSlotAtTimeMs, Uint64.subChecked, Uint64.divChecked, config,
        bind, Except.bind]
    rw [clock]
    rfl
  have total : getTotalBalance (state bodyRoot) [0, 1, 2, 3, 4, 5, 6, 7] = .ok 1600 := by
    rw [getTotalBalance_ok_iff]
    simp only [List.forall_mem_cons, sumMarked_eq_sum, getElem?_markIndices]
    decide
  have balances : unslashedActiveBalances (state bodyRoot) =
      [(0, 200), (1, 200), (2, 200), (3, 200), (4, 200), (5, 200), (6, 200), (7, 200)] := rfl
  have proposer : computeProposerScore config (state bodyRoot) = .ok 0 := by
    simp only [computeProposerScore, calculateCommitteeFraction, balances, List.map_cons,
      List.map_nil, total, Except.mapError, bind, Except.bind]
    rfl
  have equiv : (running 3000 count).getEquivocationScoreOf (state bodyRoot)
      (((((∅ : Std.TreeSet ValidatorIndex).insert 2).insert 3).insert 4).insert 5) = .ok 0 := by
    change (do
      let active ← ([] : List ValidatorIndex).filterM fun index => do
        pure (isActiveValidator (← validatorAt (state bodyRoot) index) 0)
      sumGwei active fun index => do pure (← validatorAt (state bodyRoot) index).effectiveBalance)
        = .ok 0
    rw [filterM_nil]
    rfl
  have committee : (running 3000 count).computeCommitteeWeightBetweenSlots blockRoot
      (state bodyRoot) 1 2 = .ok 800 := by
    rw [Store.computeCommitteeWeightBetweenSlots, running_committee_weight]
    rfl
  have adversary : (running 3000 count).computeAdversarialWeight config blockRoot
      (state bodyRoot) 1 2 = .ok 272 := by
    rw [Store.computeAdversarialWeight, running_committee_weight]
    change (do let score ← (running 3000 count).getEquivocationScoreOf (state bodyRoot)
                 (((((∅ : Std.TreeSet ValidatorIndex).insert 2).insert 3).insert 4).insert 5)
               pure (Uint64.saturatingSub 272 score)) = .ok 272
    rw [equiv]
    rfl
  have discount : (running 3000 count).computeEmptySlotSupportDiscount config blockRoot
      (state bodyRoot) blockRoot = .ok 0 := by
    simp only [Store.computeEmptySlotSupportDiscount, child, bind, Except.bind,
      show signedBlock.message.parentRoot = anchorRoot from rfl, parent]
    rfl
  have adversary' : (running 3000 count).getAdversarialWeight config blockRoot
      (state bodyRoot) blockRoot = .ok 272 := by
    simp only [Store.getAdversarialWeight, slot, child, Store.getBlockEpoch,
      show signedBlock.message.parentRoot = anchorRoot from rfl, parent, bind, Except.bind,
      pure, Except.pure]
    exact adversary
  simp only [Store.computeSafetyThreshold, slot, child, bind, Except.bind,
    show signedBlock.message.parentRoot = anchorRoot from rfl, parent, proposer]
  change (do
    let maximum ← (running 3000 count).computeCommitteeWeightBetweenSlots blockRoot
      (state bodyRoot) 1 2
    let discount ← (running 3000 count).computeEmptySlotSupportDiscount config blockRoot
      (state bodyRoot) blockRoot
    let adversary ← (running 3000 count).getAdversarialWeight config blockRoot
      (state bodyRoot) blockRoot
    if discount > maximum then throw (ForkChoiceError.supportDiscountAboveMaximum blockRoot)
    let withBoost ← (Uint64.addChecked maximum 0).mapError ForkChoiceError.arith
    let doubled ← (Uint64.mulChecked 2 adversary).mapError ForkChoiceError.arith
    let bound ← (Uint64.addChecked withBoost doubled).mapError ForkChoiceError.arith
    pure ((bound - discount) / 2)) = .ok 672
  rw [committee, discount, adversary']
  rfl

set_option maxRecDepth 10000 in
/-- The four received votes exceed the child's safety threshold. -/
theorem running_one_confirmed :
    (running 3000 4).isOneConfirmed config blockRoot (state bodyRoot)
      ((running 3000 4).tallyVotes (state bodyRoot)) blockRoot = .ok true := by
  have target : (running 3000 4).checkpointState (running 3000 4).justifiedCheckpoint =
      .ok (state bodyRoot) := by
    simp [Store.checkpointState, running, admitted, ticked, anchor, pure, Except.pure]
  have score := running_weight 3000 4 (by decide)
  simp only [Store.getWeight, show ¬ Fork.glamsterdam ≤ Fork.phase0 by decide,
    ↓reduceIte, ↓reduceDIte, Store.justifiedTally, target, bind, Except.bind,
    pure, Except.pure,
    show (running 3000 4).proposerBoostRoot = Vector.replicate 32 0 from rfl,
    ne_eq, not_true_eq_false, decide_false, Bool.not_false] at score
  have scored : (running 3000 4).scoreFromTally ((running 3000 4).tallyVotes (state bodyRoot))
      ⟨blockRoot, .pending⟩ = .ok 800 := by
    cases result : (running 3000 4).scoreFromTally
      ((running 3000 4).tallyVotes (state bodyRoot)) ⟨blockRoot, .pending⟩ <;>
      simp_all
  rw [Store.isOneConfirmed, scored]
  simp only [bind, Except.bind, running_threshold]
  rfl

set_option maxRecDepth 10000 in
/-- The current-epoch walk advances from the anchor to its distinct child.

Only the observed justified checkpoint matters for this walk in epoch zero. -/
theorem running_walk (fcr : FastConfirmationStore)
    (source : fcr.currentEpochObservedJustifiedCheckpoint = ⟨0, anchorRoot⟩) :
    (running 3000 4).findLatestConfirmedDescendant config fcr blockRoot anchorRoot =
      .ok blockRoot := by
  have child : (running 3000 4).block blockRoot = .ok signedBlock.message := by
    simp [Store.block, running_child, pure, Except.pure]
  have parent : (running 3000 4).block anchorRoot = .ok (anchorBlock stateRoot) := by
    simp [Store.block, running_anchor, pure, Except.pure]
  have slot : (running 3000 4).getCurrentSlot config = .ok 3 := by
    change (computeSlotAtTimeMs config 0 3000).mapError ForkChoiceError.arith = .ok 3
    simp [computeSlotAtTimeMs, Uint64.subChecked, Uint64.divChecked, config,
      bind, Except.bind, Except.mapError]
  have epoch : (running 3000 4).getCurrentStoreEpoch config = .ok 0 := by
    rw [Store.getCurrentStoreEpoch, slot]
    rfl
  have epochChild : (running 3000 4).getBlockEpoch blockRoot = .ok 0 := by
    rw [Store.getBlockEpoch, child]
    rfl
  have epochParent : (running 3000 4).getBlockEpoch anchorRoot = .ok 0 := by
    rw [Store.getBlockEpoch, parent]
    rfl
  have ancestorRoots : (running 3000 4).getAncestorRoots blockRoot anchorRoot =
      .ok [blockRoot] := by
    rw [Store.getAncestorRoots, running_child]
    simp only [parent, bind, Except.bind]
    rfl
  have unrealized : (running 3000 4).unrealizedJustification blockRoot =
      .ok postState.currentJustifiedCheckpoint := by
    simp [Store.unrealizedJustification, running, admitted, pure, Except.pure]
  have checkpoint : (running 3000 4).checkpointState ⟨0, anchorRoot⟩ =
      .ok (state bodyRoot) := by
    simp [Store.checkpointState, running, admitted, ticked, anchor, pure, Except.pure]
  simp only [Store.findLatestConfirmedDescendant, epoch, slot, epochParent, source,
    bind, Except.bind, checkpoint]
  simp only [show isStartSlotAtEpoch preset 3 = .ok false from rfl,
    show Uint64.addChecked 0 1 = .ok 1 from rfl, Except.mapError,
    ↓reduceIte, pure, Except.pure, Bool.false_eq_true]
  simp only [unrealized,
    show postState.currentJustifiedCheckpoint.epoch = 0 from rfl,
    show Uint64.addChecked 0 1 = .ok 1 from rfl,
    show (0 : Epoch) ≤ 1 by decide, decide_true, ↓reduceIte, ancestorRoots]
  simp [epochChild, epochParent, running_one_confirmed, Except.map,
    bind, Except.bind, pure, Except.pure]

end EthLib.Consensus.Models.Network.EightValidatorWitness
