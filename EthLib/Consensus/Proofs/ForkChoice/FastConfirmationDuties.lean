module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationCheckpoints
import EthLib.Consensus.Proofs.HonestAggregation
import EthLib.Consensus.Proofs.ForkChoice.HonestHeads

/-!
# Signing the counted target before the next epoch

Safety of the epoch origin makes each remaining honest duty vote for the caller's target.

The rollover committee read supplies the duties of validators active in the caller's state.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Fork}

namespace Models.Network

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J} [DecidablePred (· ∈ J)]

/-- A successful range read supplies each committee in that range. -/
private theorem coverage_committee_exists_of_range {store : Store preset fork}
    {head : Root} {first last slot : Slot} {members : Std.TreeSet ValidatorIndex}
    {state : BeaconState preset fork} {index : CommitteeIndex}
    (read : store.getCommitteesBetweenSlots head first last = .ok members)
    (low : first ≤ slot) (high : slot ≤ last)
    (stateOk : store.blockState head = .ok state)
    (below : index < getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)) :
    ∃ committee, getBeaconCommittee state slot index = .ok committee := by
  simp only [Store.getCommitteesBetweenSlots, bind_ok_iff, mapError_ok_iff] at read
  obtain ⟨afterEnd, afterOk, folded⟩ := read
  have afterNat := (addChecked_ok_iff.mp afterOk).2
  have lowNat := UInt64.le_iff_toNat_le.mp low
  have highNat := UInt64.le_iff_toNat_le.mp high
  have inRange : slot.toNat - first.toNat ∈ List.range (afterEnd.toNat - first.toNat) := by
    simp only [List.mem_range, UInt64.toNat_one] at *
    omega
  obtain ⟨slotMembers, slotOk⟩ := foldlM_forall_of_ok
    (fun _ _ _ stepOk => (bind_ok_iff.mp stepOk).imp fun _ read => read.1)
    _ _ _ folded _ inRange
  have back : first + (slot.toNat - first.toNat).toUInt64 = slot := by
    rw [← UInt64.toNat_sub_of_le _ _ low, Nat.toUInt64_eq, UInt64.ofNat_toNat,
      UInt64.add_comm, UInt64.sub_add_cancel]
  rw [back] at slotOk
  simp only [Store.getSlotCommittee, stateOk, bind, Except.bind] at slotOk
  obtain ⟨committee, committeeOk⟩ := foldlM_forall_of_ok
    (fun _ _ _ stepOk => (bind_ok_iff.mp stepOk).imp fun _ read => read.1)
    _ _ _ slotOk _ (List.mem_range.mpr (UInt64.lt_iff_toNat_lt.mp below))
  rw [Nat.toUInt64_eq, UInt64.ofNat_toNat] at committeeOk
  exact ⟨committee, mapError_ok_iff.mp committeeOk⟩

/-- A successful shuffle bounds the active registry used by a committee. -/
private theorem coverage_active_small_of_committee
    {state : BeaconState preset fork} {slot : Slot} {index : CommitteeIndex}
    {committee : Array ValidatorIndex}
    (read : getBeaconCommittee state slot index = .ok committee) :
    (getActiveValidatorIndices state (computeEpochAtSlot preset slot)).length ≤ 2 ^ 40 := by
  obtain ⟨active, shuffled, shuffle⟩ := attesterShuffle_ok_of_getBeaconCommittee read
  simp only [attesterShuffle, bind_ok_iff, liftArith, mapError_ok_iff,
    pure, Except.pure, Except.ok.injEq] at shuffle
  obtain ⟨seed, seedOk, indices, indicesOk, count, countOk, permutation,
    permutationOk, pair⟩ := shuffle
  have same := getActiveValidatorIndicesChecked_ok indicesOk
  subst indices
  have small := (computeShuffledPermutation_ok permutationOk).1
  have countNat := (ofNatChecked_ok_iff.mp countOk).2
  simpa only [countNat, List.size_toArray] using small

/-- Successful committee slicing bounds its final registry-position product. -/
private theorem coverage_product_lt_of_committee
    {state : BeaconState preset fork} {slot : Slot} {index : CommitteeIndex}
    {committee : Array ValidatorIndex}
    (read : getBeaconCommittee state slot index = .ok committee) :
    (getActiveValidatorIndices state (computeEpochAtSlot preset slot)).length *
      ((slot % preset.SLOTS_PER_EPOCH).toNat *
        (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat +
        index.toNat + 1) < 2 ^ 64 := by
  obtain ⟨seed, position, count, _, positionNat, _, computed⟩ := getBeaconCommittee_ok read
  simp only [computeCommittee, bind_ok_iff] at computed
  obtain ⟨shuffled, _, computed⟩ := computed
  unfold shuffledCommittee at computed
  split at computed
  · rename_i fits
    simpa only [List.size_toArray, positionNat] using fits.2
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at computed
    split at computed <;> cases computed

/-- A complete epoch range contains every validator active in its state. -/
private theorem coverage_mem_range_of_active {store : Store preset fork}
    {head : Root} {epoch next : Epoch} {first boundary last : Slot}
    {members : Std.TreeSet ValidatorIndex} {state : BeaconState preset fork}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (nextOk : addChecked epoch 1 = .ok next)
    (firstOk : computeStartSlotAtEpoch preset epoch = .ok first)
    (boundaryOk : computeStartSlotAtEpoch preset next = .ok boundary)
    (lastOk : subChecked boundary 1 = .ok last)
    (read : store.getCommitteesBetweenSlots head first last = .ok members)
    (stateOk : store.blockState head = .ok state)
    {v : ValidatorIndex} (active : v ∈ getActiveValidatorIndices state epoch) :
    v ∈ members := by
  have firstNat := (computeStartSlotAtEpoch_ok_iff.mp firstOk).2
  have boundaryNat := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  have lastNat := (subChecked_ok_iff.mp lastOk).2
  simp only [UInt64.toNat_one] at nextNat lastNat
  rw [nextNat, Nat.add_mul, Nat.one_mul] at boundaryNat
  have low : first ≤ last := UInt64.le_iff_toNat_le.mpr (by omega)
  have lastEpoch : computeEpochAtSlot preset last = epoch := by
    apply UInt64.toNat_inj.mp
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_eq_of_lt_le (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega)
  have lastMod : (last % preset.SLOTS_PER_EPOCH).toNat + 1 =
      preset.SLOTS_PER_EPOCH.toNat := by
    have divided := congrArg UInt64.toNat lastEpoch
    simp only [computeEpochAtSlot, UInt64.toNat_div] at divided
    have decomposed := Nat.div_add_mod last.toNat preset.SLOTS_PER_EPOCH.toNat
    rw [divided] at decomposed
    rw [Nat.mul_comm] at decomposed
    rw [UInt64.toNat_mod]
    omega
  let per := getCommitteeCountPerSlot state epoch
  have perPos : 0 < per.toNat := UInt64.le_iff_toNat_le.mp
    (one_le_getCommitteeCountPerSlot state epoch)
  let index := per - 1
  have indexNat : index.toNat + 1 = per.toNat := by
    dsimp only [index]
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
      simp only [UInt64.toNat_one]
      omega))]
    simp only [UInt64.toNat_one]
    omega
  have indexLt : index < per := UInt64.lt_iff_toNat_lt.mpr
    (Nat.lt_of_lt_of_eq (Nat.lt_succ_self index.toNat) indexNat)
  obtain ⟨committee, committeeOk⟩ := coverage_committee_exists_of_range read low
    (UInt64.le_refl _) stateOk (index := index) (by rw [lastEpoch]; exact indexLt)
  have small := coverage_active_small_of_committee committeeOk
  rw [lastEpoch] at small
  have product := coverage_product_lt_of_committee committeeOk
  rw [lastEpoch] at product
  have position : (last % preset.SLOTS_PER_EPOCH).toNat * per.toNat + index.toNat + 1 =
      per.toNat * preset.SLOTS_PER_EPOCH.toNat := by
    calc
      _ = (last % preset.SLOTS_PER_EPOCH).toNat * per.toNat + per.toNat := by omega
      _ = ((last % preset.SLOTS_PER_EPOCH).toNat + 1) * per.toNat := by
        rw [Nat.add_mul, Nat.one_mul]
      _ = _ := by rw [lastMod, Nat.mul_comm]
  change (getActiveValidatorIndices state epoch).length *
    ((last % preset.SLOTS_PER_EPOCH).toNat * per.toNat + index.toNat + 1) < 2 ^ 64 at product
  rw [position] at product
  obtain ⟨a, shuffled, shuffle⟩ := attesterShuffle_ok_of_getBeaconCommittee committeeOk
  rw [lastEpoch] at shuffle
  have indicesOk := getActiveValidatorIndicesChecked_of_attesterShuffle shuffle
  obtain ⟨seed, seedOk, _, _⟩ := attesterShuffle_ok shuffle
  have slotsFit : (epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 64 := by
    have bound := boundary.toNat_lt
    rw [Nat.add_mul, Nat.one_mul]
    omega
  obtain ⟨slot, i, c, epochOk, below, cOk, member⟩ := exists_mem_getBeaconCommittee indicesOk
    seedOk (by intro zero; simp only [zero, UInt64.toNat_zero, Nat.lt_irrefl] at positive)
    slotsFit small product active
  have lower : first ≤ slot := UInt64.le_iff_toNat_le.mpr (by
    have bound := Nat.div_mul_le_self slot.toNat preset.SLOTS_PER_EPOCH.toNat
    have eq := congrArg UInt64.toNat epochOk
    simp only [computeEpochAtSlot, UInt64.toNat_div] at eq
    rw [eq] at bound
    omega)
  have upper : slot ≤ last := UInt64.le_iff_toNat_le.mpr (by
    have bound := Nat.lt_mul_div_succ slot.toNat positive
    have eq := congrArg UInt64.toNat epochOk
    simp only [computeEpochAtSlot, UInt64.toNat_div] at eq
    rw [eq, Nat.mul_comm, Nat.add_mul, Nat.one_mul] at bound
    omega)
  exact Store.mem_getCommitteesBetweenSlots read lower upper stateOk (epochOk ▸ below) cOk member

/-- A matching slot-start read bounds the genesis offset by one slot duration. -/
private theorem coverage_genesis_offset_of_slot_start {genesis actual : UInt64}
    {slot : Slot} {begin : UInt64}
    (slots : 0 < config.SLOT_DURATION_MS)
    (beginOk : computeTimeAtSlotMs config genesis slot = .ok begin)
    (slotOk : computeSlotAtTimeMs config actual begin = .ok slot) :
    actual.toNat ≤ genesis.toNat ∧
      genesis.toNat < actual.toNat + config.SLOT_DURATION_MS.toNat := by
  simp only [computeTimeAtSlotMs, bind_ok_iff] at beginOk
  obtain ⟨offset, offsetOk, summed⟩ := beginOk
  have offsetNat := (mulChecked_ok_iff.mp offsetOk).2
  have beginNat := (addChecked_ok_iff.mp summed).2
  simp only [computeSlotAtTimeMs, bind_ok_iff] at slotOk
  obtain ⟨elapsed, elapsedOk, divided⟩ := slotOk
  have elapsedNat := (subChecked_ok_iff.mp elapsedOk).2
  have elapsedBound := (subChecked_ok_iff.mp elapsedOk).1
  have quotient := (divChecked_ok_iff.mp divided).2
  have positive := UInt64.lt_iff_toNat_lt.mp slots
  have lower := Nat.div_mul_le_self elapsed.toNat config.SLOT_DURATION_MS.toNat
  have upper := Nat.lt_mul_div_succ elapsed.toNat positive
  rw [← quotient] at lower upper
  rw [Nat.mul_comm, Nat.add_mul, Nat.one_mul] at upper
  omega

/-- The same sub-slot genesis offset preserves the slot read at every external boundary. -/
private theorem coverage_slot_at_start_of_genesis_offset {genesis actual : UInt64}
    {slot : Slot} {begin : UInt64}
    (slots : 0 < config.SLOT_DURATION_MS)
    (beginOk : computeTimeAtSlotMs config genesis slot = .ok begin)
    (offset : actual.toNat ≤ genesis.toNat ∧
      genesis.toNat < actual.toNat + config.SLOT_DURATION_MS.toNat) :
    computeSlotAtTimeMs config actual begin = .ok slot := by
  have parsed := beginOk
  simp only [computeTimeAtSlotMs, bind_ok_iff] at parsed
  obtain ⟨distance, distanceOk, summed⟩ := parsed
  have distanceNat := (mulChecked_ok_iff.mp distanceOk).2
  have beginNat := (addChecked_ok_iff.mp summed).2
  have low : actual ≤ begin := UInt64.le_iff_toNat_le.mpr (by omega)
  have elapsedNat : (begin - actual).toNat = begin.toNat - actual.toNat :=
    UInt64.toNat_sub_of_le _ _ low
  have quotient : (begin - actual).toNat / config.SLOT_DURATION_MS.toNat = slot.toNat := by
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [Nat.add_mul, Nat.one_mul]
      omega
  unfold computeSlotAtTimeMs
  rw [subChecked_ok_iff.mpr ⟨low, elapsedNat⟩]
  simp only [bind, Except.bind]
  exact divChecked_ok_iff.mpr ⟨by intro zero; simp [zero] at slots, quotient.symm⟩

/-- The state path along an actual ancestor walk consists of kept transitions. -/
theorem coverage_runKept_of_ancestor {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {checks : SignatureChecks} {engine : ExecutionEngine preset fork}
    (transitions : ∀ (root : Root) (block : BeaconBlock preset fork)
      (state : BeaconState preset fork), store.blocks[root]? = some block →
      store.blockStates[root]? = some state → block ≠ anchorBlock →
      ∃ parent signed, signed.message = block ∧
        store.blockStates[block.parentRoot]? = some parent ∧
        stateTransition config checks engine parent signed true = .ok state)
    {node ancestor : ForkChoiceNode} {slot : Slot}
    {state ancestorState : BeaconState preset fork}
    (anchorBelow : anchorBlock.slot ≤ slot)
    (ancestorHeld : store.blockStates[ancestor.root]? = some ancestorState)
    (held : store.blockStates[node.root]? = some state)
    (walk : store.getAncestor node slot = .ok ancestor) :
    RunKept ancestorState state := by
  obtain ⟨block, found⟩ := reachable.known_of_blockState held
  by_cases low : block.slot ≤ slot
  · rw [Store.getAncestor_of_le found low] at walk
    cases walk
    rw [held, Option.some.injEq] at ancestorHeld
    subst ancestorState
    exact RunKept.refl _
  · have other : block ≠ anchorBlock := fun same => low (same ▸ anchorBelow)
    obtain ⟨parentState, signed, message, parentHeld, transition⟩ :=
      transitions node.root block state found held other
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
      · exact (coverage_runKept_of_ancestor reachable transitions anchorBelow ancestorHeld
          parentHeld walk).trans (runKept_stateTransition transition)
      · simp [throw, throwThe, MonadExceptOf.throw] at walk
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transition
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

omit [DecidablePred (· ∈ J)] in
/-- Descendants of a common epoch origin agree on that epoch's active validators. -/
theorem coverage_activity_eq_of_common_ancestor {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (preGloas : fork < .glamsterdam) {limit : ℕ} (oneBlock : OneBlockPerRoot e limit)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : ℕ}
    (nBound : (e.world n).time ≤ limit) (kBound : (e.world k).time ≤ limit)
    {origin : Root} {originBlock otherOrigin : BeaconBlock preset fork}
    (originKnown : ((e.world n).state u).blocks[origin]? = some originBlock)
    (otherKnown : ((e.world k).state w).blocks[origin]? = some otherOrigin)
    {countHead otherHead : Root} {countState otherState : BeaconState preset fork}
    (countRead : ((e.world n).state u).getPulledUpHeadState config countHead = .ok countState)
    (otherRead : ((e.world k).state w).blockState otherHead = .ok otherState)
    (countDescends : ((e.world n).state u).isAncestor ⟨countHead, .pending⟩
      ⟨origin, .pending⟩ = .ok true)
    (otherDescends : ((e.world k).state w).isAncestor ⟨otherHead, .pending⟩
      ⟨origin, .pending⟩ = .ok true) :
    getActiveValidatorIndices countState (computeEpochAtSlot preset originBlock.slot) =
      getActiveValidatorIndices otherState (computeEpochAtSlot preset originBlock.slot) := by
  have forward (v : ValidatorIndex) (honest : v ∈ J) (i : ℕ) :
      Store.ForwardReachable config anchorState anchorBlock ((e.world i).state v) :=
    e.forwardReachable (fun a ha => (anchored a ha) ▸ .anchor anchorStore) i v honest
  have reached := (forward u caller n).reachable
  have reachedOther := (forward w receiver k).reachable
  have blocksSame := oneBlock u caller w receiver n k nBound kBound
  have sameOrigin := blocksSame origin originBlock otherOrigin originKnown otherKnown
  subst otherOrigin
  obtain ⟨common, commonHeld, anchorCommon, _⟩ := reached.blockStatesFromParents originKnown
  obtain ⟨commonOther, commonOtherHeld, _, _⟩ :=
    reachedOther.blockStatesFromParents otherKnown
  have same := e.blockStates_eq anchorStore caller receiver (anchored u caller)
    (anchored w receiver) blocksSame commonHeld commonOtherHeld
  subst commonOther
  have originSlot : common.slot = originBlock.slot := by
    by_cases same : originBlock = anchorBlock
    · rw [anchorCommon same, same, anchorSlot]
    · exact (reached.blockState_header originKnown commonHeld same).1
  have originEpoch : getCurrentEpoch common = computeEpochAtSlot preset originBlock.slot := by
    rw [getCurrentEpoch, originSlot]
  have fixed : computeEpochAtSlot preset originBlock.slot ≤ activityFixedEpoch common := by
    rw [← originEpoch]
    exact getCurrentEpoch_le_activityFixedEpoch common
  have count := countRead
  simp only [Store.getPulledUpHeadState, bind_ok_iff] at count
  obtain ⟨raw, rawOk, epoch, epochOk, rest⟩ := count
  have run := coverage_runKept_of_ancestor reached
    (fun _ _ _ held stored other =>
      e.exists_transition_of_nonanchor_block anchorStore caller (anchored u caller)
        held stored other)
    (reached.anchorSlot_le_block originKnown) commonHeld
    (Store.blockState_ok_iff.mp rawOk)
    (Store.getAncestor_of_isAncestor_of_lt preGloas originKnown countDescends)
  have pulled : RunKept raw countState := by
    split at rest
    · obtain ⟨first, _, processed⟩ := bind_ok_iff.mp rest
      exact runKept_processSlots (mapError_ok_iff.mp processed)
    · cases Except.ok.inj rest
      exact RunKept.refl _
  have otherRun := coverage_runKept_of_ancestor reachedOther
    (fun _ _ _ held stored other =>
      e.exists_transition_of_nonanchor_block anchorStore receiver (anchored w receiver)
        held stored other)
    (reachedOther.anchorSlot_le_block otherKnown) commonOtherHeld
    (Store.blockState_ok_iff.mp otherRead)
    (Store.getAncestor_of_isAncestor_of_lt preGloas otherKnown otherDescends)
  exact ((run.trans pulled).active.getActiveValidatorIndices_eq fixed).trans
    (otherRun.active.getActiveValidatorIndices_eq fixed).symm

omit [DecidablePred (· ∈ J)] in
/-- The actual rollover range assigns a duty to every originally active honest validator. -/
private theorem coverage_exists_duty_of_active_at_rollover {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (preGloas : fork < .glamsterdam) {limit : ℕ} (oneBlock : OneBlockPerRoot e limit)
    (committees : CommitteesFollow e limit)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : ℕ}
    (nBound : (e.world n).time ≤ limit) (kBound : (e.world k).time ≤ limit)
    {origin : Root} {originBlock otherOrigin : BeaconBlock preset fork}
    (originKnown : ((e.world n).state u).blocks[origin]? = some originBlock)
    (otherKnown : ((e.world k).state w).blocks[origin]? = some otherOrigin)
    {epoch next : Epoch} {first boundary last : Slot}
    (originEpoch : computeEpochAtSlot preset originBlock.slot = epoch)
    (nextOk : addChecked epoch 1 = .ok next)
    (firstOk : computeStartSlotAtEpoch preset epoch = .ok first)
    (boundaryOk : computeStartSlotAtEpoch preset next = .ok boundary)
    (lastOk : subChecked boundary 1 = .ok last)
    {countHead : Root} {otherHead : ForkChoiceNode}
    {countState otherState : BeaconState preset fork} {members : Std.TreeSet ValidatorIndex}
    (countRead : ((e.world n).state u).getPulledUpHeadState config countHead = .ok countState)
    (otherRead : ((e.world k).state w).blockState otherHead.root = .ok otherState)
    (countDescends : ((e.world n).state u).isAncestor ⟨countHead, .pending⟩
      ⟨origin, .pending⟩ = .ok true)
    (otherDescends : ((e.world k).state w).isAncestor ⟨otherHead.root, .pending⟩
      ⟨origin, .pending⟩ = .ok true)
    (headOk : ((e.world k).state w).getHead config = .ok otherHead)
    (slotOk : ((e.world k).state w).getCurrentSlot config = .ok boundary)
    (read : ((e.world k).state w).getCommitteesBetweenSlots otherHead.root first last = .ok members)
    {v : ValidatorIndex} (honest : v ∈ J)
    (active : v ∈ getActiveValidatorIndices countState epoch) :
    ∃ slot index, first ≤ slot ∧ slot ≤ last ∧ assignment.committee v slot = some index := by
  have forward : Store.ForwardReachable config anchorState anchorBlock ((e.world k).state w) :=
    e.forwardReachable (fun a ha => (anchored a ha) ▸ .anchor anchorStore) k w receiver
  have same := coverage_activity_eq_of_common_ancestor anchorStore anchored anchorSlot preGloas
    oneBlock caller receiver nBound kBound originKnown otherKnown countRead otherRead countDescends
    otherDescends
  rw [originEpoch] at same
  rw [same] at active
  have member := coverage_mem_range_of_active positive nextOk firstOk boundaryOk lastOk
    read otherRead active
  have lastNat := (subChecked_ok_iff.mp lastOk).2
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  have epochBoundary := computeEpochAtSlot_computeStartSlotAtEpoch
    (UInt64.lt_iff_toNat_lt.mpr positive) boundaryOk
  have epochFirst := computeEpochAtSlot_computeStartSlotAtEpoch
    (UInt64.lt_iff_toNat_lt.mpr positive) firstOk
  have past : last < boundary := UInt64.lt_iff_toNat_lt.mpr (by
    have bound := (subChecked_ok_iff.mp lastOk).1
    simp only [UInt64.toNat_one] at lastNat bound
    omega)
  apply (committees.assigned w receiver k kBound otherHead boundary first last members headOk
    slotOk past ?_ read v honest).mp member
  intro state found
  obtain ⟨current, currentOk, states⟩ :=
    forward.blockState_slots_le_current (Store.slotDuration_pos slotOk)
  have same := Except.ok.inj (currentOk.symm.trans slotOk)
  subst current
  have le := UInt64.le_iff_toNat_le.mp (states _ _ (Store.blockState_ok_iff.mp found))
  have epochLe := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat) le
  change (getCurrentEpoch state).toNat ≤ (computeEpochAtSlot preset boundary).toNat at epochLe
  rw [epochBoundary] at epochLe
  rw [epochFirst]
  simp only [UInt64.toNat_one] at nextNat
  omega

/-- Prompt and head totality supply successful reads at the actual rollover event. -/
private theorem coverage_exists_rollover_reads {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (slots : 0 < config.SLOT_DURATION_MS) (long : 1 < preset.SLOTS_PER_EPOCH)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (preGloas : fork < .glamsterdam) (boost : config.PROPOSER_SCORE_BOOST.toNat ≤ 100)
    {limit : ℕ} {horizon : Epoch}
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).Counts config state →
      getCurrentEpoch state ≤ horizon →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (supply : ∀ w ∈ J, ∀ k (checkpoint : Checkpoint) (state : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).checkpointState checkpoint = .ok state →
      ActiveStakeAtMost stakeCapGwei state)
    (prompt : Prompt e limit) (follows : HeadFollowsSupport e limit)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} {reference boundary : Slot}
    {referenceBegin begin : UInt64}
    (referenceSlot : ((e.world n).state u).getCurrentSlot config = .ok reference)
    (referenceOk : computeTimeAtSlotMs config genesisTimeMs reference = .ok referenceBegin)
    (referenceTime : (e.world n).time = referenceBegin.toNat)
    (referenceReady : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    (beginOk : computeTimeAtSlotMs config genesisTimeMs boundary = .ok begin)
    (started : e.startTime ≤ begin.toNat) (bounded : begin.toNat ≤ limit) :
    ∃ k head state, (e.world k).time = begin.toNat ∧
      UpToDate config checks sources (e.world k).time ((e.world k).view u)
        ((e.world k).state u) ∧
      ((e.world k).state u).getHead config = .ok head ∧
      ((e.world k).state u).getCurrentSlot config = .ok boundary ∧
      ((e.world k).state u).blockState head.root = .ok state ∧
      ∀ first last, last < boundary → ∃ participants,
        ((e.world k).state u).getCommitteesBetweenSlots head.root first last =
          .ok participants := by
  obtain ⟨k, atTime, ready⟩ := (prompt u caller boundary begin beginOk started bounded).1
  have kBound : (e.world k).time ≤ limit := atTime ▸ bounded
  obtain ⟨head, headOk⟩ := e.exists_getHead anchorStore sound anchored anchorSlot anchorAtBoundary
    slots long window preGloas boost nonzero anchorParent inHorizon large supply caller kBound
  have forward : Store.ForwardReachable config anchorState anchorBlock ((e.world k).state u) :=
    e.forwardReachable (fun a ha => (anchored a ha) ▸ .anchor anchorStore) k u caller
  have common : ((e.world k).state u).genesisTimeMs = ((e.world n).state u).genesisTimeMs := by
    rw [(e.clock_bounds u k).1, (e.clock_bounds u n).1]
  have referenceClock : ((e.world n).state u).timeMs = referenceBegin :=
    UInt64.toNat_inj.mp (referenceReady.1.trans referenceTime)
  have offset := coverage_genesis_offset_of_slot_start slots referenceOk
    (by simpa only [Store.getCurrentSlot, referenceClock] using mapError_ok_iff.mp referenceSlot)
  have clock : ((e.world k).state u).timeMs = begin :=
    UInt64.toNat_inj.mp (ready.1.trans atTime)
  have slotOk : ((e.world k).state u).getCurrentSlot config = .ok boundary := by
    unfold Store.getCurrentSlot
    rw [common, clock]
    exact mapError_ok_iff.mpr (coverage_slot_at_start_of_genesis_offset slots beginOk offset)
  obtain ⟨nodes, _, treeOk, _⟩ := Store.getHead_leaf headOk
  obtain ⟨justifiedBlock, justifiedOk⟩ := Store.filterNodeTree_known treeOk
  obtain ⟨block, blockOk, _⟩ := Store.slot_le_of_isAncestor justifiedOk
    (Store.isAncestor_getHead headOk)
  obtain ⟨state, stateOk, _, _⟩ := forward.reachable.blockStatesFromParents blockOk
  obtain ⟨_, current, _, _, _, currentOk, _, _, ranges⟩ :=
    follows.reads u caller k kBound head ready headOk
  rw [slotOk, Except.ok.injEq] at currentOk
  subst current
  exact ⟨k, head, state, atTime, ready, headOk, slotOk, Store.blockState_ok_iff.mpr stateOk,
    ranges⟩

/-- A successful pulled-up state read has the store's current epoch. -/
theorem coverage_pulled_epoch_of_current_epoch {store : Store preset fork}
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    {head : Root} {state : BeaconState preset fork} {epoch : Epoch}
    (epochOk : store.getCurrentStoreEpoch config = .ok epoch)
    (stateOk : store.getPulledUpHeadState config head = .ok state) :
    getCurrentEpoch state = epoch := by
  have parsed := stateOk
  simp only [Store.getPulledUpHeadState, epochOk, bind_ok_iff] at parsed
  obtain ⟨raw, rawOk, readEpoch, readEpochOk, parsed⟩ := parsed
  cases Except.ok.inj readEpochOk
  split at parsed
  · obtain ⟨first, firstOk, processed⟩ := bind_ok_iff.mp parsed
    rw [getCurrentEpoch, (processSlots_slot (mapError_ok_iff.mp processed)).2]
    exact computeEpochAtSlot_computeStartSlotAtEpoch
      (UInt64.lt_iff_toNat_lt.mpr positive) (mapError_ok_iff.mp firstOk)
  · rename_i notOld
    have stateEq : raw = state := Except.ok.inj parsed
    subst state
    have epochRead := epochOk
    simp only [Store.getCurrentStoreEpoch, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at epochRead
    obtain ⟨current, currentOk, epochEq⟩ := epochRead
    obtain ⟨now, nowOk, states⟩ :=
      forward.blockState_slots_le_current (Store.slotDuration_pos currentOk)
    have same := Except.ok.inj (nowOk.symm.trans currentOk)
    subst now
    have rawLe := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
      (UInt64.le_iff_toNat_le.mp (states _ _ (Store.blockState_ok_iff.mp rawOk)))
    change (getCurrentEpoch raw).toNat ≤ (computeEpochAtSlot preset current).toNat at rawLe
    rw [epochEq] at rawLe
    apply UInt64.le_antisymm (UInt64.le_iff_toNat_le.mpr rawLe)
    exact UInt64.not_lt.mp notOld

omit [DecidablePred (· ∈ J)] in
/-- Prefix safety supplies the actual duties of the originally counted active validators. -/
private theorem coverage_duties_of_safe_rollover {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (preGloas : fork < .glamsterdam) {limit : ℕ} (oneBlock : OneBlockPerRoot e limit)
    (committees : CommitteesFollow e limit)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {u : ValidatorIndex} (caller : u ∈ J) {n k : ℕ}
    (nBound : (e.world n).time ≤ limit) (kBound : (e.world k).time ≤ limit)
    {origin : Root} {originBlock : BeaconBlock preset fork}
    (originKnown : ((e.world n).state u).blocks[origin]? = some originBlock)
    {epoch next : Epoch} {first boundary last : Slot}
    (originEpoch : computeEpochAtSlot preset originBlock.slot = epoch)
    (nextOk : addChecked epoch 1 = .ok next)
    (firstOk : computeStartSlotAtEpoch preset epoch = .ok first)
    (boundaryOk : computeStartSlotAtEpoch preset next = .ok boundary)
    (lastOk : subChecked boundary 1 = .ok last)
    {head : Root} {otherHead : ForkChoiceNode} {state otherState : BeaconState preset fork}
    (countRead : ((e.world n).state u).getPulledUpHeadState config head = .ok state)
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (countDescends : ((e.world n).state u).isAncestor ⟨head, .pending⟩
      ⟨origin, .pending⟩ = .ok true)
    (ready : UpToDate config checks sources (e.world k).time ((e.world k).view u)
      ((e.world k).state u))
    (headOk : ((e.world k).state u).getHead config = .ok otherHead)
    (slotOk : ((e.world k).state u).getCurrentSlot config = .ok boundary)
    (otherRead : ((e.world k).state u).blockState otherHead.root = .ok otherState)
    (reads : ∀ first last, last < boundary → ∃ participants,
      ((e.world k).state u).getCommitteesBetweenSlots otherHead.root first last = .ok participants)
    (safe : SafeAt e (e.world k).time origin) :
    ∀ v ∈ activeVoters state, v ∈ J → ∃ slot index,
      first ≤ slot ∧ slot < boundary ∧ computeEpochAtSlot preset slot = epoch ∧
      assignment.committee v slot = some index := by
  have descends := safe u caller k otherHead rfl ready headOk
  have originRead := descends
  unfold Store.isAncestor at originRead
  obtain ⟨otherOrigin, otherKnown, _⟩ := bind_ok_iff.mp originRead
  have otherKnown := Store.block_ok_iff.mp otherKnown
  have pending := Store.getHead_pending preGloas headOk
  have nodeEq : otherHead = ⟨otherHead.root, .pending⟩ := by
    cases otherHead
    simp_all
  have forward : Store.ForwardReachable config anchorState anchorBlock ((e.world n).state u) :=
    e.forwardReachable (fun a ha => (anchored a ha) ▸ .anchor anchorStore) n u caller
  have stateEpoch := coverage_pulled_epoch_of_current_epoch forward positive epochOk countRead
  have lastNat := (subChecked_ok_iff.mp lastOk).2
  have lastPos := (subChecked_ok_iff.mp lastOk).1
  have before : last < boundary := UInt64.lt_iff_toNat_lt.mpr (by
    simp only [UInt64.toNat_one] at lastNat lastPos
    omega)
  obtain ⟨participants, participantsOk⟩ := reads first last before
  intro v active honest
  have activeAt : v ∈ getActiveValidatorIndices state epoch := by
    simpa only [activeVoters, stateEpoch, List.mem_toFinset] using active
  obtain ⟨slot, index, low, high, duty⟩ := coverage_exists_duty_of_active_at_rollover anchorStore
    anchored anchorSlot positive preGloas oneBlock committees retained caller caller nBound kBound
    originKnown otherKnown originEpoch nextOk firstOk boundaryOk lastOk countRead otherRead
    countDescends (by rw [← nodeEq]; exact descends) headOk slotOk participantsOk honest activeAt
  have epochAt : computeEpochAtSlot preset slot = epoch := by
    apply UInt64.toNat_inj.mp
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    apply Nat.div_eq_of_lt_le
    · exact (computeStartSlotAtEpoch_ok_iff.mp firstOk).2 ▸
        UInt64.le_iff_toNat_le.mp low
    · have nextNat := (addChecked_ok_iff.mp nextOk).2
      have boundaryNat := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
      simp only [UInt64.toNat_one] at nextNat
      rw [nextNat] at boundaryNat
      have bound := UInt64.lt_iff_toNat_lt.mp (UInt64.lt_of_le_of_lt high before)
      omega
  exact ⟨slot, index, low, UInt64.lt_of_le_of_lt high before, epochAt, duty⟩

/-- Reading a checkpoint through a descendant gives the same checkpoint at the ancestor. -/
private theorem coverage_checkpoint_read_of_descendant {store : Store preset fork}
    {node : ForkChoiceNode} {root checkpoint : Root} {block : BeaconBlock preset fork}
    {epoch : Epoch} {boundary : Slot}
    (preGloas : fork < .glamsterdam) (known : store.blocks[root]? = some block)
    (descends : store.isAncestor node ⟨root, .pending⟩ = .ok true)
    (boundaryOk : computeStartSlotAtEpoch preset epoch = .ok boundary)
    (earlier : boundary ≤ block.slot)
    (read : store.getCheckpointBlock node.root epoch = .ok checkpoint) :
    store.getCheckpointBlock root epoch = .ok checkpoint := by
  have walk := Store.getAncestor_of_isAncestor_of_lt preGloas known descends
  have through := Store.getAncestor_trans earlier walk
  have rootWalk := Store.getAncestor_root (store := store) node .pending boundary
  simp only [Store.getCheckpointBlock, boundaryOk, Except.mapError, bind, Except.bind] at read ⊢
  change ((fun x => x.root) <$> store.getAncestor ⟨node.root, .pending⟩ boundary) =
    .ok checkpoint at read
  change ((fun x => x.root) <$> store.getAncestor ⟨root, .pending⟩ boundary) = .ok checkpoint
  rw [← rootWalk, through] at read
  exact read

omit [DecidablePred (· ∈ J)] in
/-- An actual honest vote identifies the common store genesis time. -/
private theorem coverage_genesis_eq_of_vote {anchor : Store preset fork}
    (start : ∀ u ∈ J, e.start u = anchor) {v : ValidatorIndex} (honest : v ∈ J)
    {slot : Slot} {index : CommitteeIndex} {time n : ℕ}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot index time n attestation indexed) :
    anchor.genesisTimeMs = genesisTimeMs := by
  have common := (e.clock_bounds v n).1
  rw [start v honest] at common
  exact common.symm.trans vote.genesis

private theorem coverage_anchor_le_boundary {blockSlot boundary : Slot} {epoch : Epoch}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (anchorBound : anchorBlock.slot ≤ blockSlot)
    (blockEpoch : computeEpochAtSlot preset blockSlot = epoch)
    (boundaryOk : computeStartSlotAtEpoch preset epoch = .ok boundary) :
    anchorBlock.slot ≤ boundary := by
  have rounded : anchorBlock.slot / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH =
      anchorBlock.slot := by
    have roundedOk := computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) anchorBlock.slot
    have lower := (computeStartSlotAtEpoch_le_lt (UInt64.lt_iff_toNat_lt.mpr positive) roundedOk).1
    unfold isStartSlotAtEpoch computeSlotsSinceEpochStart at anchorAtBoundary
    rw [roundedOk] at anchorAtBoundary
    simp only [Except.mapError, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq, decide_eq_true_eq] at anchorAtBoundary
    have zero := congrArg UInt64.toNat anchorAtBoundary
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr lower)] at zero
    simp only [UInt64.toNat_zero] at zero
    exact UInt64.toNat_inj.mp (by omega)
  have mono := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat
    (Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
      (UInt64.le_iff_toNat_le.mp anchorBound))
  have a := (computeStartSlotAtEpoch_ok_iff.mp
    (computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) anchorBlock.slot)).2
  have b := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
  rw [rounded] at a
  rw [← blockEpoch, computeEpochAtSlot, UInt64.toNat_div] at b
  simp only [computeEpochAtSlot, UInt64.toNat_div] at a
  exact UInt64.le_iff_toNat_le.mpr (by omega)

omit [DecidablePred (· ∈ J)] in
/-- An honest vote for a safe chain has the target read by the original caller. -/
private theorem coverage_target_eq_of_safe_vote {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ u ∈ J, e.start u = anchor) {limit : ℕ} (oneBlock : OneBlockPerRoot e limit)
    (preGloas : fork < .glamsterdam) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    {u v : ValidatorIndex} (caller : u ∈ J) (honest : v ∈ J) {n k : ℕ}
    (nBound : (e.world n).time ≤ limit) (kBound : (e.world k).time ≤ limit)
    {target : Checkpoint} {countHead origin : Root} {originBlock : BeaconBlock preset fork}
    (originHeld : ((e.world n).state u).blocks[origin]? = some originBlock)
    (originEpoch : computeEpochAtSlot preset originBlock.slot = target.epoch)
    (countDescends : ((e.world n).state u).isAncestor ⟨countHead, .pending⟩
      ⟨origin, .pending⟩ = .ok true)
    (countRead : ((e.world n).state u).getCheckpointBlock countHead target.epoch = .ok target.root)
    {slot : Slot} {index : CommitteeIndex} {deadline first last : ℕ}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot index deadline k attestation indexed)
    (due : IsAttestationDeadline fork config genesisTimeMs slot deadline) {dueMs : UInt64}
    (dueOk : getAttestationDueMs config fork = .ok dueMs) (inSlot : dueMs < config.SLOT_DURATION_MS)
    (slotEpoch : computeEpochAtSlot preset slot = target.epoch)
    (afterFirst : first ≤ deadline) (before : deadline < last)
    (safe : ∀ t, first ≤ t → t < last → SafeAt e t origin)
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state v).blocks[root]? = some block →
        block.stateRoot ≠ Vector.replicate 32 0) :
    attestation.data.target = target := by
  obtain ⟨_, dataEpoch, _⟩ := vote.data_head anchored (UInt64.le_of_eq anchorSlot)
    start honest due dueOk inSlot
  have epochEq := dataEpoch.trans slotEpoch
  obtain ⟨head, _, headOk, _, dataRoot, _, supports⟩ :=
    vote.head_supports_of_safe anchored (UInt64.le_of_eq anchorSlot) start honest due dueOk
      inSlot afterFirst before safe
  have originKnown : ∃ block, ((e.world k).state v).blocks[origin]? = some block := by
    unfold Store.isAncestor at supports
    obtain ⟨block, found, _⟩ := bind_ok_iff.mp supports
    exact ⟨block, Store.block_ok_iff.mp found⟩
  obtain ⟨otherOrigin, otherHeld⟩ := originKnown
  have blocksSame := oneBlock u caller v honest n k nBound kBound
  have same := blocksSame origin originBlock otherOrigin originHeld otherHeld
  subst otherOrigin
  let boundary := target.epoch * preset.SLOTS_PER_EPOCH
  have boundaryOk : computeStartSlotAtEpoch preset target.epoch = .ok boundary := by
    dsimp only [boundary]
    rw [← originEpoch]
    exact computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) originBlock.slot
  have lower : boundary ≤ originBlock.slot := UInt64.le_iff_toNat_le.mpr (by
    have eq := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
    rw [← originEpoch, computeEpochAtSlot, UInt64.toNat_div] at eq
    rw [eq]
    exact Nat.div_mul_le_self _ _)
  have originRead := coverage_checkpoint_read_of_descendant preGloas originHeld countDescends
    boundaryOk lower countRead
  have reached : Store.Reachable config anchorState anchorBlock ((e.world k).state v) :=
    e.reachable (fun a ha => (start a ha) ▸ .anchor anchored) k v honest
  have anchorBound :=
    (e.reachable (fun a ha => (start a ha) ▸ Store.Reachable.anchor anchored)
      n u caller).anchorSlot_le_block originHeld
  have aboveAnchor := coverage_anchor_le_boundary positive anchorAtBoundary anchorBound
    originEpoch boundaryOk
  have transferred := Store.getCheckpointBlock_of_same_blocks reached blocksSame boundaryOk
    aboveAnchor ⟨originBlock, otherHeld⟩ originRead
  have pending := Store.getHead_pending preGloas headOk
  have headEq : head = ⟨attestation.data.beaconBlockRoot, .pending⟩ := by
    cases head
    simp_all
  have votedRead := coverage_checkpoint_read_of_descendant preGloas otherHeld
    (headEq ▸ supports) (epochEq.symm ▸ boundaryOk) lower
    (vote.data_target anchored anchorSlot anchorAtBoundary start honest nonzero)
  rw [epochEq, transferred, Except.ok.injEq] at votedRead
  exact congrArg₂ Checkpoint.mk epochEq votedRead.symm

omit [DecidablePred (· ∈ J)] in
/-- The send event of an honest vote supplies the signed-target evidence. -/
private theorem coverage_signsTarget_of_vote {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {v : ValidatorIndex} (honest : v ∈ J)
    {slot : Slot} {index : CommitteeIndex} {deadline n last : ℕ}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot index deadline n attestation indexed)
    (before : deadline ≤ last) {target : Checkpoint}
    (sameTarget : attestation.data.target = target) :
    SignsTarget e v target last := by
  have reached : Store.Reachable config anchorState anchorBlock ((e.world n).state v) :=
    e.reachable (fun a ha => (start a ha) ▸ .anchor anchored) n v honest
  have member : v ∈ indexed.attestingIndices.data := by
    have member : v ∈ indexed.attestingIndices.data.toList := by rw [vote.alone]; simp
    simpa only [Array.mem_toList_iff] using member
  obtain ⟨_, targetState, _, _, indexedOk, _⟩ := vote.reads
  have dataSame : indexed.data = attestation.data := by
    obtain ⟨indices, indicesOk, _⟩ := getAttestingIndices_of_getIndexedAttestation indexedOk
    obtain ⟨indexed', made, _, dataSame, _⟩ :=
      getIndexedAttestation_of_getAttestingIndices indicesOk
    have same := Except.ok.inj (indexedOk.symm.trans made)
    exact same ▸ dataSame
  refine ⟨n + 1, ?_, .attestation attestation, ?_, attestation.data, ?_, sameTarget⟩
  · simpa only [e.world_succ, vote.sends, World.apply] using vote.atTime.trans_le before
  · simp only [e.world_succ, vote.sends, World.apply, Set.mem_insert_iff, true_or]
  · exact ⟨_, indexed, reached, vote.reads, member, dataSame.symm⟩

omit [DecidablePred (· ∈ J)] in
/-- An unseen duty produces a signature before the next epoch's boundary. -/
private theorem coverage_signsTarget_of_unseen_duty {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (preGloas : fork < .glamsterdam) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    {limit : ℕ} (oneBlock : OneBlockPerRoot e limit)
    (committees : CommitteesFollow e limit)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 1 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {Δ : ℕ} (votes : Votes e.startTime limit e) (fits : DelayFits fork config genesisTimeMs Δ)
    {u v : ValidatorIndex} (caller : u ∈ J) (honest : v ∈ J) {n : ℕ}
    (bounded : (e.world n).time ≤ limit)
    {head : ForkChoiceNode} {current first last boundary dutySlot : Slot}
    {begin endTime : UInt64} {participants : Std.TreeSet ValidatorIndex} {index : CommitteeIndex}
    {target : Checkpoint} {origin : Root} {originBlock : BeaconBlock preset fork}
    (originHeld : ((e.world n).state u).blocks[origin]? = some originBlock)
    (originEpoch : computeEpochAtSlot preset originBlock.slot = target.epoch)
    (descends : ((e.world n).state u).isAncestor ⟨head.root, .pending⟩
      ⟨origin, .pending⟩ = .ok true)
    (targetRead : ((e.world n).state u).getCheckpointBlock head.root target.epoch = .ok target.root)
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (currentOk : ((e.world n).state u).getCurrentSlot config = .ok current)
    (firstOk : computeStartSlotAtEpoch preset (computeEpochAtSlot preset current) = .ok first)
    (lastOk : subChecked current 1 = .ok last)
    (prefixOk : ((e.world n).state u).getCommitteesBetweenSlots head.root first last =
      .ok participants)
    (unseen : v ∉ participants) (dutyFirst : first ≤ dutySlot) (dutyEnd : dutySlot < boundary)
    (dutyEpoch : computeEpochAtSlot preset dutySlot = target.epoch)
    (duty : assignment.committee v dutySlot = some index)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs current = .ok begin)
    (atSlot : (e.world n).time = begin.toNat)
    (endOk : computeTimeAtSlotMs config genesisTimeMs boundary = .ok endTime)
    (endBound : endTime.toNat ≤ limit)
    (safe : ∀ t, (e.world n).time ≤ t → t < endTime.toNat → SafeAt e t origin)
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ∀ (root : Root) (block : BeaconBlock preset fork),
        ((e.world k).state w).blocks[root]? = some block →
          block.stateRoot ≠ Vector.replicate 32 0) :
    SignsTarget e v target (endTime.toNat - 1) ∧ anchor.genesisTimeMs = genesisTimeMs := by
  have forward : Store.ForwardReachable config anchorState anchorBlock ((e.world n).state u) :=
    e.forwardReachable (fun a ha => (anchored a ha) ▸ .anchor anchorStore) n u caller
  have lastNat := (subChecked_ok_iff.mp lastOk).2
  have lastBound := (subChecked_ok_iff.mp lastOk).1
  have past : last < current := UInt64.lt_iff_toNat_lt.mpr (by
    simp only [UInt64.toNat_one] at lastNat lastBound
    omega)
  have currentLe : current ≤ dutySlot := by
    apply UInt64.le_iff_toNat_le.mpr
    by_contra notLe
    have dutyLast : dutySlot ≤ last := UInt64.le_iff_toNat_le.mpr (by
      simp only [UInt64.toNat_one] at lastNat lastBound
      omega)
    exact unseen ((committees.assigned_current_epoch retained caller bounded forward headOk
      currentOk firstOk past prefixOk v honest).mpr ⟨dutySlot, index, dutyFirst, dutyLast, duty⟩)
  obtain ⟨next, start, following, deadline, k, attestation, indexed, nextOk, startOk,
      followingOk, due, afterFirst, beforeNext, followingBound, vote⟩ :=
    e.exists_voteAt_of_duty_interval votes fits beginOk endOk
      (show e.startTime ≤ (e.world n).time from e.monotone_time (Nat.zero_le n))
      (by omega) endBound honest currentLe dutyEnd duty
  have beforeEnd : deadline < endTime.toNat := by
    have before := fits.deadline_lt_later_slot dutyEnd endOk due
    omega
  have voteBound : (e.world k).time ≤ limit := by rw [vote.atTime]; omega
  obtain ⟨dueMs, dueOk⟩ := fits.1
  have dueLt := fits.due_lt_slot nextOk startOk followingOk dueOk
  have targetEq := coverage_target_eq_of_safe_vote anchorStore anchorSlot anchorAtBoundary
    anchored oneBlock preGloas positive caller honest bounded voteBound originHeld originEpoch
    descends targetRead vote due dueOk dueLt dutyEpoch afterFirst (by omega) safe
    (nonzero v honest k voteBound)
  exact ⟨coverage_signsTarget_of_vote anchorStore anchored honest vote (by omega) targetEq,
    coverage_genesis_eq_of_vote anchored honest vote⟩

/-- Every counted honest validator signs the target strictly before the next epoch. -/
theorem Execution.signsTarget_by_boundary
    {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (long : 1 < preset.SLOTS_PER_EPOCH)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (preGloas : fork < .glamsterdam) (boost : config.PROPOSER_SCORE_BOOST.toNat ≤ 100)
    {limit : ℕ} {horizon : Epoch}
    (oneBlock : OneBlockPerRoot e limit) (prompt : Prompt e limit)
    (committees : CommitteesFollow e limit) (follows : HeadFollowsSupport e limit)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {Δ : ℕ} (votes : Votes e.startTime limit e) (fits : DelayFits fork config genesisTimeMs Δ)
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit → ∀ (r : Root) (b : BeaconBlock preset fork),
      ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork), (e.world k).time ≤ limit →
      ((e.world k).state w).Counts config state → getCurrentEpoch state ≤ horizon →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (supply : ∀ w ∈ J, ∀ k (checkpoint : Checkpoint) (state : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).checkpointState checkpoint = .ok state →
      ActiveStakeAtMost stakeCapGwei state)
    {u : ValidatorIndex} (caller : u ∈ J) {q : ℕ}
    (upToDate : UpToDate config checks sources (e.world q).time ((e.world q).view u)
      ((e.world q).state u))
    {head : ForkChoiceNode} (headOk : ((e.world q).state u).getHead config = .ok head)
    {state : BeaconState preset fork}
    (stateOk : ((e.world q).state u).getPulledUpHeadState config head.root = .ok state)
    {target : Checkpoint}
    (targetOk : ((e.world q).state u).getCurrentTarget config head.root = .ok target)
    (epochOk : ((e.world q).state u).getCurrentStoreEpoch config = .ok target.epoch)
    {current first last : Slot} {callBegin : UInt64}
    (currentOk : ((e.world q).state u).getCurrentSlot config = .ok current)
    (callBeginOk : computeTimeAtSlotMs config genesisTimeMs current = .ok callBegin)
    (atSlot : (e.world q).time = callBegin.toNat)
    (firstOk : computeStartSlotAtEpoch preset target.epoch = .ok first)
    (lastOk : subChecked current 1 = .ok last)
    {participants : Std.TreeSet ValidatorIndex}
    (participantsOk : ((e.world q).state u).getCommitteesBetweenSlots head.root first last =
      .ok participants)
    {origin : Root} {originBlock : BeaconBlock preset fork}
    (originHeld : ((e.world q).state u).blocks[origin]? = some originBlock)
    (originEpoch : computeEpochAtSlot preset originBlock.slot = target.epoch)
    (descends : ((e.world q).state u).isAncestor ⟨head.root, .pending⟩ ⟨origin, .pending⟩ =
      .ok true)
    {nextEpoch : Epoch} {boundary : Slot} {begin : UInt64}
    (nextOk : addChecked target.epoch 1 = .ok nextEpoch)
    (boundaryOk : computeStartSlotAtEpoch preset nextEpoch = .ok boundary)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs boundary = .ok begin)
    (bounded : begin.toNat ≤ limit)
    (originSafe : ∀ t, (e.world q).time ≤ t → t ≤ begin.toNat → SafeAt e t origin)
    {voters : Finset ValidatorIndex}
    (members : ∀ v ∈ voters, v ∈ J ∧ v ∈ activeVoters state ∧
      (SignsTarget e v target (e.world q).time ∨ v ∉ participants)) :
    ∀ v ∈ voters, SignsTarget e v target (begin.toNat - 1) := by
  have slotEpoch : computeEpochAtSlot preset current = target.epoch := by
    simpa only [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure,
      Except.pure, Except.ok.injEq] using epochOk
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  have boundaryNat := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
  simp only [UInt64.toNat_one] at nextNat
  have currentBefore : current < boundary := UInt64.lt_iff_toNat_lt.mpr (by
    have bound := Nat.lt_mul_div_succ current.toNat positive
    have epochNat := congrArg UInt64.toNat slotEpoch
    simp only [computeEpochAtSlot, UInt64.toNat_div] at epochNat
    rw [epochNat, Nat.mul_comm, ← nextNat, ← boundaryNat] at bound
    exact bound)
  have callBefore : (e.world q).time < begin.toNat := by
    obtain ⟨offset, offsetOk, summed⟩ := bind_ok_iff.mp callBeginOk
    obtain ⟨otherOffset, otherOffsetOk, otherSummed⟩ := bind_ok_iff.mp beginOk
    have a := (mulChecked_ok_iff.mp offsetOk).2
    have b := (addChecked_ok_iff.mp summed).2
    have c := (mulChecked_ok_iff.mp otherOffsetOk).2
    have d := (addChecked_ok_iff.mp otherSummed).2
    have strict := Nat.mul_lt_mul_of_pos_right
      (UInt64.lt_iff_toNat_lt.mp currentBefore) (UInt64.lt_iff_toNat_lt.mp slots)
    rw [atSlot]
    omega
  have qBound : (e.world q).time ≤ limit := callBefore.le.trans bounded
  obtain ⟨r, rolloverHead, rolloverState, atRollover, rolloverReady, rolloverHeadOk,
      rolloverSlot, rolloverStateOk, ranges⟩ :=
    coverage_exists_rollover_reads anchorStore sound anchored anchorSlot anchorAtBoundary
      slots long window preGloas boost nonzero anchorParent inHorizon large supply prompt follows
      caller currentOk callBeginOk atSlot upToDate beginOk
      ((e.monotone_time (Nat.zero_le q)).trans callBefore.le) bounded
  have rolloverBound : (e.world r).time ≤ limit := atRollover ▸ bounded
  have boundaryPositive : 1 ≤ boundary := UInt64.le_iff_toNat_le.mpr (by
    have productPositive := Nat.mul_pos (show 0 < nextEpoch.toNat by omega) positive
    simp only [UInt64.toNat_one]
    omega)
  have lastEpochOk : subChecked boundary 1 = .ok (boundary - 1) :=
    subChecked_ok_iff.mpr ⟨boundaryPositive, UInt64.toNat_sub_of_le _ _ boundaryPositive⟩
  -- Safety at the rollover identifies the same epoch origin on the actual head.
  have duties := coverage_duties_of_safe_rollover anchorStore anchored anchorSlot positive
    preGloas oneBlock committees retained caller qBound rolloverBound originHeld originEpoch
    nextOk firstOk boundaryOk lastEpochOk stateOk epochOk descends rolloverReady rolloverHeadOk
    rolloverSlot rolloverStateOk ranges
    (originSafe (e.world r).time (by omega) (by omega))
  have targetRead : ((e.world q).state u).getCheckpointBlock head.root target.epoch =
      .ok target.root := by
    have parsed := targetOk
    simp only [Store.getCurrentTarget, Store.getCheckpointForBlock, epochOk,
      bind_ok_iff] at parsed
    obtain ⟨epoch, sameEpoch, root, read, sameTarget⟩ := parsed
    cases Except.ok.inj sameEpoch
    have rootEq := congrArg Checkpoint.root (Except.ok.inj sameTarget)
    exact rootEq ▸ read
  intro v member
  rcases (members v member).2.2 with signed | unseen
  · obtain ⟨k, before, rest⟩ := signed
    exact ⟨k, by omega, rest⟩
  · obtain ⟨slot, index, low, high, epoch, duty⟩ :=
      duties v (members v member).2.1 (members v member).1
    exact (coverage_signsTarget_of_unseen_duty anchorStore anchorSlot anchorAtBoundary
      anchored preGloas positive oneBlock committees (by omega) votes fits caller
      (members v member).1 qBound originHeld originEpoch descends targetRead headOk currentOk
      (slotEpoch.symm ▸ firstOk) lastOk participantsOk unseen low high epoch duty callBeginOk
      atSlot beginOk bounded (fun t afterCall beforeEnd => originSafe t afterCall beforeEnd.le)
      nonzero).1

end Models.Network

end EthLib.Consensus
