module

public import EthLib.Consensus.Proofs.DirectSafety.ChurnBounds
public import EthLib.Consensus.Proofs.Transition.Requests

-- Reuse the operation-level activity and effective-balance preservation proofs.
import all EthLib.Consensus.Proofs.Transition.ActiveKept
import all EthLib.Consensus.Proofs.Transition.BalanceDrift

/-!
# Departure queue accounting

A queue call records its assigned epoch as well as the balance that it spends.

Partial withdrawals spend exit capacity without assigning a validator's exit.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base

/-- One successful balance-queue call, including the queue before and after it. -/
structure DepartureQueueCall where
  earliest : Epoch
  available : Gwei
  first : Epoch
  rate : Gwei
  amount : Gwei
  epoch : Epoch
  left : Gwei
  computed : churnQueue earliest first rate available amount = .ok (epoch, left)

/-- The capacity still usable through a fixed last epoch. -/
def departureQueuePotential (high cap : Nat) (epoch : Epoch) (left : Gwei) : Nat :=
  if epoch.toNat ≤ high then left.toNat + (high - epoch.toNat) * cap else 0

/-- A call cannot move the open queue epoch backwards. -/
theorem DepartureQueueCall.epoch_mono (call : DepartureQueueCall) :
    call.earliest.toNat ≤ call.epoch.toNat := by
  have placed := UInt64.le_iff_toNat_le.mp (churnQueue_spend call.computed).1
  rw [Base.Uint64.toNat_max] at placed
  omega

/-- Spending beyond the horizon counts nothing and leaves no usable capacity inside it. -/
theorem DepartureQueueCall.window_spend (call : DepartureQueueCall) (high cap : Nat)
    (rateBound : call.rate.toNat ≤ cap) :
    (if call.epoch.toNat ≤ high then call.amount.toNat else 0) +
      departureQueuePotential high cap call.epoch call.left ≤
        departureQueuePotential high cap call.earliest call.available := by
  have ordered := call.epoch_mono
  by_cases inside : call.epoch.toNat ≤ high
  · have before : call.earliest.toNat ≤ high := by omega
    obtain ⟨_, spent⟩ := churnQueue_window_le cap [(call.first, call.rate, call.amount)]
      call.earliest call.available call.epoch call.left
      (by intro c member; simpa using List.mem_singleton.mp member ▸ rateBound)
      (by simpa using call.computed)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at spent
    simp only [departureQueuePotential, inside, before, ↓reduceIte]
    have distance : high - call.earliest.toNat =
        (call.epoch.toNat - call.earliest.toNat) + (high - call.epoch.toNat) := by omega
    rw [distance, Nat.add_mul]
    omega
  · simp only [departureQueuePotential, inside, ↓reduceIte, Nat.zero_add]
    exact Nat.zero_le _

/-- A concrete sequence uses each call's output queue as the next call's input queue. -/
inductive DepartureQueueTrace : Epoch → Gwei → List DepartureQueueCall → Epoch → Gwei → Prop
  | nil (epoch : Epoch) (left : Gwei) : DepartureQueueTrace epoch left [] epoch left
  | cons (call : DepartureQueueCall) {rest : List DepartureQueueCall} {epoch : Epoch}
      {left : Gwei} (tail : DepartureQueueTrace call.epoch call.left rest epoch left) :
      DepartureQueueTrace call.earliest call.available (call :: rest) epoch left

/-- Filtering calls by completion epoch preserves the queue budget through that epoch. -/
theorem DepartureQueueTrace.window_le {earliest epoch : Epoch} {available left : Gwei}
    {calls : List DepartureQueueCall}
    (trace : DepartureQueueTrace earliest available calls epoch left) (high cap : Nat)
    (rates : ∀ call ∈ calls, call.rate.toNat ≤ cap) :
    ((calls.filter fun call => call.epoch.toNat ≤ high).map fun call => call.amount.toNat).sum +
      departureQueuePotential high cap epoch left ≤
        departureQueuePotential high cap earliest available := by
  induction trace with
  | nil => simp
  | cons call tail ih =>
    have step := call.window_spend high cap (rates call (by simp))
    have rest := ih (fun c member => rates c (List.mem_cons_of_mem _ member))
    by_cases inside : call.epoch.toNat ≤ high
    · simp only [List.filter_cons, decide_eq_true inside, ↓reduceIte,
        List.map_cons, List.sum_cons]
      rw [ite_eq_left inside] at step
      omega
    · simp only [List.filter_cons, decide_eq_false inside, Bool.false_eq_true, ↓reduceIte]
      rw [ite_eq_right inside] at step
      omega

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- An exit scheduling operation supplies a call with exactly its input and output queues. -/
theorem exitQueueCall_of_computed {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {amount : Gwei} {epoch : Epoch}
    (ok : computeExitEpochAndUpdateChurn config s electra amount = .ok (t, epoch)) :
    ∃ call : DepartureQueueCall,
      call.earliest = s.earliestExitEpoch electra ∧
      call.available = s.exitBalanceToConsume electra ∧
      call.amount = amount ∧ call.epoch = epoch ∧
      call.left = t.exitBalanceToConsume electra ∧
      exitChurnLimit config s = .ok call.rate := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, liftArith,
    mapError_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ok
  obtain ⟨first, _, rate, rateOk, ⟨placed, left⟩, queued, rfl, rfl⟩ := ok
  exact ⟨⟨_, _, first, rate, amount, placed, left, queued⟩,
    rfl, rfl, rfl, rfl, rfl, rateOk⟩

/-- A consolidation scheduling operation supplies its exact balance-queue call. -/
theorem consolidationQueueCall_of_computed {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {amount : Gwei} {epoch : Epoch}
    (ok : computeConsolidationEpochAndUpdateChurn config s electra amount = .ok (t, epoch)) :
    ∃ call : DepartureQueueCall,
      call.earliest = s.earliestConsolidationEpoch electra ∧
      call.available = s.consolidationBalanceToConsume electra ∧
      call.amount = amount ∧ call.epoch = epoch ∧
      call.left = t.consolidationBalanceToConsume electra ∧
      getConsolidationChurnLimit config s = .ok call.rate := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, liftArith,
    mapError_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ok
  obtain ⟨first, _, rate, rateOk, ⟨placed, left⟩, queued, rfl, rfl⟩ := ok
  exact ⟨⟨_, _, first, rate, amount, placed, left, queued⟩,
    rfl, rfl, rfl, rfl, rfl, rateOk⟩

/-- An initiated exit spends its old effective balance and retains the assigned queue epoch. -/
theorem initiateExit_call {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex}
    (ok : initiateValidatorExit config s index = .ok t) :
    t = s ∨ ∃ (v : Validator) (call : DepartureQueueCall),
      getValidator s index = .ok v ∧ v.exitEpoch = FAR_FUTURE_EPOCH ∧
      call.amount = v.effectiveBalance ∧
      call.earliest = s.earliestExitEpoch electra ∧
      call.available = s.exitBalanceToConsume electra ∧
      call.epoch = t.earliestExitEpoch electra ∧
      call.left = t.exitBalanceToConsume electra ∧
      exitChurnLimit config s = .ok call.rate ∧
      ∃ next, getValidator t index = .ok next ∧ next.exitEpoch = call.epoch := by
  obtain ⟨v, found, unchanged | ⟨far, queued, epoch, withdrawable, scheduled, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · exact .inl unchanged.2
  · have called : computeExitEpochAndUpdateChurn config s electra v.effectiveBalance =
        .ok (queued, epoch) := by simpa only [exitQueue, electra, ↓reduceDIte] using scheduled
    obtain ⟨call, earliest, available, amount, placed, left, rate⟩ :=
      exitQueueCall_of_computed electra called
    have queuedEpoch := (computeExitEpochAndUpdateChurn_earliest called).1
    have read := getValidator_setValidator_self set
    obtain ⟨inside, rfl⟩ := setValidator_ok set
    exact .inr ⟨v, call, found, far, amount, earliest, available,
      placed.trans queuedEpoch.symm, left, rate, _, read, placed.symm⟩

/-- Initiating an exit leaves every other registry entry unchanged. -/
theorem initiateExit_other {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index other : ValidatorIndex}
    (ok : initiateValidatorExit config s index = .ok t) (different : other ≠ index) :
    getValidator t other = getValidator s other := by
  obtain ⟨v, _, unchanged | ⟨_, queued, epoch, _, scheduled, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]
  · have called : computeExitEpochAndUpdateChurn config s electra v.effectiveBalance =
        .ok (queued, epoch) := by simpa only [exitQueue, electra, ↓reduceDIte] using scheduled
    rw [getValidator_setValidator_of_ne set different]
    exact getValidator_of_validators_eq (computeExitEpochAndUpdateChurn_earliest called).2.1 _

/-- A newly assigned exit identifies the unique registry entry charged by its call. -/
theorem initiateExit_charge {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index other : ValidatorIndex} {old next : Validator}
    (ok : initiateValidatorExit config s index = .ok t)
    (before : getValidator s other = .ok old) (after : getValidator t other = .ok next)
    (unset : old.exitEpoch = FAR_FUTURE_EPOCH) (assigned : next.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    other = index ∧ ∃ call : DepartureQueueCall,
      call.amount = old.effectiveBalance ∧ call.epoch = next.exitEpoch ∧
      call.earliest = s.earliestExitEpoch electra ∧
      call.available = s.exitBalanceToConsume electra ∧
      call.epoch = t.earliestExitEpoch electra ∧
      call.left = t.exitBalanceToConsume electra ∧
      exitChurnLimit config s = .ok call.rate := by
  have differentStates : t ≠ s := by
    intro same
    subst t
    have equal := Except.ok.inj (before.symm.trans after)
    exact assigned (equal ▸ unset)
  have sameIndex : other = index := by
    by_contra different
    have unchanged := initiateExit_other electra ok different
    have equal := Except.ok.inj (before.symm.trans (unchanged ▸ after))
    exact assigned (equal ▸ unset)
  subst other
  obtain same | ⟨v, call, found, _, amount, earliest, available, placed, left, rate,
    later, read, epoch⟩ := initiateExit_call electra ok
  · exact False.elim (differentStates same)
  · have oldSame := Except.ok.inj (found.symm.trans before)
    have nextSame := Except.ok.inj (read.symm.trans after)
    subst v later
    exact ⟨rfl, call, amount, epoch.symm, earliest, available, placed, left, rate⟩

/-- Partial withdrawals may spend exit capacity while leaving every validator unchanged. -/
theorem partialWithdrawal_call {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex} {v : Validator} {amount owed : Gwei}
    (ok : requestPartialWithdrawal config s electra index v amount owed = .ok t) :
    t.validators = s.validators ∧
      (t = s ∨ ∃ call : DepartureQueueCall,
        call.earliest = s.earliestExitEpoch electra ∧
        call.available = s.exitBalanceToConsume electra ∧
        call.epoch = t.earliestExitEpoch electra ∧
        call.left = t.exitBalanceToConsume electra ∧
        exitChurnLimit config s = .ok call.rate) := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨balance, _, kept, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨⟨queued, epoch⟩, called, _, _, _, _, rfl⟩ := ok
    obtain ⟨call, earliest, available, _, placed, left, rate⟩ :=
      exitQueueCall_of_computed electra called
    obtain ⟨queuedEpoch, registry, _⟩ := computeExitEpochAndUpdateChurn_earliest called
    exact ⟨registry, .inr ⟨call, earliest, available, placed.trans queuedEpoch.symm,
      left, rate⟩⟩
  · cases ok
    exact ⟨rfl, .inl rfl⟩

/-- Scheduling a consolidation spends the source balance before changing its exit epoch. -/
theorem queueConsolidation_call {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    ∃ call : DepartureQueueCall,
      call.amount = source.effectiveBalance ∧
      call.earliest = s.earliestConsolidationEpoch electra ∧
      call.available = s.consolidationBalanceToConsume electra ∧
      call.epoch = t.earliestConsolidationEpoch electra ∧
      call.left = t.consolidationBalanceToConsume electra ∧
      getConsolidationChurnLimit config s = .ok call.rate ∧
      ∃ next, getValidator t sourceIndex = .ok next ∧ next.exitEpoch = call.epoch := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨⟨queued, epoch⟩, called, withdrawable, _, changed, set, pending, _, rfl⟩ := ok
  obtain ⟨call, earliest, available, amount, placed, left, rate⟩ :=
    consolidationQueueCall_of_computed electra called
  have queuedEpoch := (computeConsolidationEpochAndUpdateChurn_earliest called).1
  have read := getValidator_setValidator_self set
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  exact ⟨call, amount, earliest, available, placed.trans queuedEpoch.symm, left,
    rate, _, read, placed.symm⟩

/-- Consolidation scheduling leaves registry entries other than its source unchanged. -/
theorem queueConsolidation_other {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {sourceIndex targetIndex other : ValidatorIndex}
    {source : Validator}
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t)
    (different : other ≠ sourceIndex) : getValidator t other = getValidator s other := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨⟨queued, epoch⟩, called, withdrawable, _, changed, set, pending, _, rfl⟩ := ok
  change getValidator changed other = getValidator s other
  rw [getValidator_setValidator_of_ne set different]
  exact getValidator_of_validators_eq
    (computeConsolidationEpochAndUpdateChurn_earliest called).2.1 _

/-- A consolidation charge comes from its unique source and uses that source's old balance. -/
theorem queueConsolidation_charge {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {sourceIndex targetIndex other : ValidatorIndex}
    {source old next : Validator}
    (sourceFound : getValidator s sourceIndex = .ok source)
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t)
    (before : getValidator s other = .ok old) (after : getValidator t other = .ok next)
    (unset : old.exitEpoch = FAR_FUTURE_EPOCH) (assigned : next.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    other = sourceIndex ∧ ∃ call : DepartureQueueCall,
      call.amount = old.effectiveBalance ∧ call.epoch = next.exitEpoch ∧
      call.earliest = s.earliestConsolidationEpoch electra ∧
      call.available = s.consolidationBalanceToConsume electra ∧
      call.epoch = t.earliestConsolidationEpoch electra ∧
      call.left = t.consolidationBalanceToConsume electra ∧
      getConsolidationChurnLimit config s = .ok call.rate := by
  have sameIndex : other = sourceIndex := by
    by_contra different
    have unchanged := queueConsolidation_other electra ok different
    have equal := Except.ok.inj (before.symm.trans (unchanged ▸ after))
    exact assigned (equal ▸ unset)
  subst other
  have sourceSame := Except.ok.inj (sourceFound.symm.trans before)
  subst source
  obtain ⟨call, amount, earliest, available, placed, left, rate, later, read, epoch⟩ :=
    queueConsolidation_call electra ok
  have nextSame := Except.ok.inj (read.symm.trans after)
  subst later
  exact ⟨rfl, call, amount, epoch.symm, earliest, available, placed, left, rate⟩

/-- The two departure queues, excluding pending transfers and withdrawals. -/
def departureQueues {fork : Fork} (electra : .pectra ≤ fork)
    (s : BeaconState preset fork) : Epoch × Gwei × Epoch × Gwei :=
  (s.earliestExitEpoch electra, s.exitBalanceToConsume electra,
    s.earliestConsolidationEpoch electra, s.consolidationBalanceToConsume electra)

private theorem departureQueues_increase {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex} {amount : Gwei}
    (ok : increaseBalance s index amount = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  obtain ⟨_, set⟩ := increaseBalance_ok ok
  obtain ⟨_, rfl⟩ := setBalance_ok set
  rfl

private theorem departureQueues_decrease {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex} {amount : Gwei}
    (ok : decreaseBalance s index amount = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  obtain ⟨_, set⟩ := decreaseBalance_ok ok
  obtain ⟨_, rfl⟩ := setBalance_ok set
  rfl

private theorem allDeltas_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {deltas : Array Gwei × Array Gwei}
    (ok : applyAllDeltas s deltas = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  refine foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra s)
    ?_ rfl ok
  intro a index b kept stepped
  simp only [applyDeltas, liftAccessor_ok, bind_ok_iff] at stepped
  obtain ⟨_, _, raised, increase, decrease⟩ := stepped
  exact (departureQueues_decrease electra decrease).trans
    ((departureQueues_increase electra increase).trans kept)

/-- Epoch rewards and penalties preserve departure capacity and queue epochs. -/
theorem rewards_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork)
    (ok : processRewardsAndPenalties config s = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  unfold processRewardsAndPenalties at ok
  split at ok
  · cases ok; rfl
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, folded⟩ := ok
  refine foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra s)
    ?_ rfl folded
  intro a deltas b kept stepped
  exact (allDeltas_departureQueues electra stepped).trans kept

/-- Epoch slashing penalties debit balances without spending departure capacity. -/
theorem slashingPenalties_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (ok : processSlashings s = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  simp only [processSlashings, electra, ↓reduceIte, bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, folded⟩ := ok
  refine foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra s)
    ?_ rfl folded
  intro a index b kept stepped
  unfold applySlashingPenaltyElectra at stepped
  simp only [bind_ok_iff] at stepped
  obtain ⟨_, _, stepped⟩ := stepped
  split at stepped
  · simp only [bind_ok_iff] at stepped
    obtain ⟨_, _, stepped⟩ := stepped
    split at stepped
    · simp only [bind_ok_iff] at stepped
      obtain ⟨_, _, _, _, decreased⟩ := stepped
      exact (departureQueues_decrease electra (liftAccessor_ok.mp decreased)).trans kept
    · cases stepped; exact kept
  · cases stepped; exact kept

private theorem addValidator_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {key : Cryptography.Bls.BLSPubkey}
    {credentials : Bytes32} {amount : Gwei}
    (ok : addValidatorToRegistry s key credentials amount = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  simp only [addValidatorToRegistry, altair, ↓reduceDIte,
    addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := ok
  rfl

private theorem pendingDeposit_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {deposit : PendingDeposit}
    (ok : applyPendingDeposit config checks s deposit = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  unfold applyPendingDeposit at ok
  split at ok
  · split at ok
    · cases ok; rfl
    simp only [bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · exact addValidator_departureQueues electra ok
    · cases ok; rfl
  · simp only [liftAccessor_ok, bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact departureQueues_increase electra ok

private theorem passPendingDeposits_departureQueues {fork : Fork}
    (electra : .pectra ≤ fork) {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {s : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available s processed count postponed
        deposits = .ok pass → departureQueues electra pass.1.state = departureQueues electra s
  | [], _, _, _, _, _, ok => by cases ok; rfl
  | deposit :: rest, s, processed, count, postponed, pass, ok => by
    unfold passPendingDeposits at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    split at ok
    · cases ok; rfl
    split at ok
    · cases ok
    split at ok
    · split at ok
      · cases ok
      rename_i credited
      split at ok
      · cases ok
      cases ok
      exact (passPendingDeposits_departureQueues electra (deposits := rest) ‹_›).trans
        (pendingDeposit_departureQueues electra credited)
    split at ok
    · split at ok
      · cases ok
      cases ok
      exact passPendingDeposits_departureQueues electra (deposits := rest) ‹_›
    split at ok
    · cases ok
    split at ok
    · cases ok; rfl
    split at ok
    · cases ok
    rename_i credited
    split at ok
    · cases ok
    cases ok
    exact (passPendingDeposits_departureQueues electra (deposits := rest) ‹_›).trans
      (pendingDeposit_departureQueues electra credited)

/-- Crediting pending deposits preserves both departure queues. -/
theorem pendingDeposits_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork)
    (ok : processPendingDeposits config checks s electra = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  unfold processPendingDeposits at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals exact passPendingDeposits_departureQueues electra ‹_›

private theorem applyWithdrawals_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) {withdrawals : Array Withdrawal}
    (ok : applyWithdrawals s withdrawals = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  unfold applyWithdrawals at ok
  rw [← Array.foldlM_toList] at ok
  refine foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra s)
    ?_ rfl ok
  intro a withdrawal b kept stepped
  simp only [applyWithdrawal, notGloas, false_and, ↓reduceDIte] at stepped
  exact (departureQueues_decrease electra stepped).trans kept

private theorem withdrawalIndex_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {withdrawals : Array Withdrawal}
    (ok : updateNextWithdrawalIndex s withdrawals = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  unfold updateNextWithdrawalIndex at ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, rfl⟩ := ok
    rfl
  · cases ok; rfl

private theorem withdrawalValidatorIndex_departureQueues {fork : Fork}
    {s t : BeaconState preset fork} (electra : .pectra ≤ fork)
    {capella : .shapella ≤ fork} {withdrawals : Array Withdrawal}
    (ok : updateNextWithdrawalValidatorIndex s capella withdrawals = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  simp only [updateNextWithdrawalValidatorIndex, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · cases ok
  · cases ok; rfl

/-- Paying withdrawals removes balances and pending entries without resetting churn. -/
theorem withdrawals_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {capella : .shapella ≤ fork} {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (ok : processWithdrawals s capella payload = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [processWithdrawals, notGloas, ↓reduceDIte, bind_ok_iff, ensure_ok_iff,
    liftAccessor_ok] at ok
  obtain ⟨expected, _, _, _, applied⟩ := ok
  simp only [applyExpectedWithdrawals, notGloas, electra, ↓reduceDIte, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq, exists_eq_left'] at applied
  obtain ⟨withdrawn, paid, indexed, moved, swept⟩ := applied
  have last := withdrawalValidatorIndex_departureQueues electra swept
  exact last.trans ((withdrawalIndex_departureQueues electra moved).trans
    (applyWithdrawals_departureQueues electra early paid))

/-- A slashing changes the departure queues only in its initial exit scheduling call. -/
theorem slashValidator_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config s index whistleblower = .ok t) :
    ∃ exited, initiateValidatorExit config s index = .ok exited ∧
      departureQueues electra t = departureQueues electra exited := by
  obtain ⟨exited, _, _, _, _, _, _, _, _, _, _, _, exitedOk, _, _, markedOk, _, _, _,
    lowered, _, _, raised, final, done⟩ := slashValidator_ok ok
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [notGloas, ↓reduceDIte] at done
  subst done
  refine ⟨exited, exitedOk, ?_⟩
  rw [departureQueues_increase electra final, departureQueues_increase electra raised,
    departureQueues_decrease electra lowered]
  obtain ⟨_, rfl⟩ := setValidator_ok markedOk
  rfl

private theorem passPendingConsolidations_departureQueues {fork : Fork}
    (electra : .pectra ≤ fork) {epoch : Epoch} :
    ∀ {items : List PendingConsolidation} {s : BeaconState preset fork} {result},
      passPendingConsolidations epoch s items = .ok result →
      departureQueues electra result.1 = departureQueues electra s
  | [], _, _, ok => by cases ok; rfl
  | item :: rest, s, result, ok => by
    unfold passPendingConsolidations at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    split at ok
    · cases ok
    split at ok
    · split at ok
      · cases ok
      rename_i recur
      cases ok
      exact (passPendingConsolidations_departureQueues electra recur :)
    split at ok
    · cases ok; rfl
    split at ok
    · cases ok
    split at ok
    · cases ok
    rename_i lowered loweredOk
    split at ok
    · cases ok
    rename_i raised raisedOk
    split at ok
    · cases ok
    rename_i recur
    cases ok
    exact (passPendingConsolidations_departureQueues electra recur).trans
      ((departureQueues_increase electra (liftAccessor_ok.mp raisedOk)).trans
        (departureQueues_decrease electra (liftAccessor_ok.mp loweredOk)))

private theorem queueExcess_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex}
    (ok : queueExcessActiveBalance s electra index = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := setBalance_ok set
    rfl
  · cases ok; rfl

/-- Switching credentials cannot reset departure capacity. -/
theorem switchToCompounding_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex}
    (ok : switchToCompoundingValidator s electra index = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, _, _, set, queued⟩ := ok
  rw [queueExcess_departureQueues electra queued]
  obtain ⟨_, rfl⟩ := setValidator_ok set
  rfl

/-- Effective-balance changes happen after scheduling and leave its queue fields unchanged. -/
theorem effectiveBalances_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (ok : processEffectiveBalanceUpdates s = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  refine foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra s)
    ?_ rfl ok
  intro before index after kept updated
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at updated
  obtain ⟨_, _, _, _, _, _, set⟩ := updated
  obtain ⟨_, rfl⟩ := setValidatorAt_ok set
  exact kept

private theorem preActivation_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex}
    (ok : queuePreActivation s electra index = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, setBalance, _, setValidator, rfl⟩ := ok
  obtain ⟨_, rfl⟩ := setValidator_ok setValidator
  obtain ⟨_, rfl⟩ := setBalance_ok setBalance
  rfl

private theorem compoundingExcess_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : Nat}
    (ok : queueCompoundingExcess s electra index = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  unfold queueCompoundingExcess at ok
  split at ok
  · split at ok
    · exact queueExcess_departureQueues electra (liftAccessor_ok.mp ok)
    · cases ok; rfl
  · cases ok; rfl

/-- Electra initializes its queues once; subsequent upgrade folds preserve all four fields. -/
theorem electra_departure_initialization {s : BeaconState preset .dencun}
    {t : BeaconState preset .pectra} (ok : upgradeToElectra config s = .ok t) :
    ∃ first exitEpoch exitRate consolidationRate,
      computeActivationExitEpoch preset (getCurrentEpoch s) = .ok first ∧
      Uint64.addChecked (s.validators.data.foldl (init := first) fun latest validator =>
        if validator.exitEpoch = FAR_FUTURE_EPOCH then latest else max latest validator.exitEpoch)
        1 = .ok exitEpoch ∧
      departureQueues (by decide) t = (exitEpoch, exitRate, first, consolidationRate) := by
  simp only [upgradeToElectra, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff] at ok
  obtain ⟨first, firstOk, exitEpoch, exitOk, exitRate, _, consolidationRate, _, middle,
    queued, compounded⟩ := ok
  have one := foldlM_ok_invariant
    (fun u => departureQueues (by decide) u = (exitEpoch, exitRate, first, consolidationRate))
    (fun a i b kept step => (preActivation_departureQueues (by decide) step).trans kept)
    rfl queued
  have two := foldlM_ok_invariant
    (fun u => departureQueues (by decide) u = (exitEpoch, exitRate, first, consolidationRate))
    (fun a i b kept step => (compoundingExcess_departureQueues (by decide) step).trans kept)
    one compounded
  exact ⟨first, exitEpoch, exitRate, consolidationRate, firstOk, exitOk, two⟩

/-- Both initialized departure queues open strictly after the crossing epoch. -/
theorem electra_departure_epochs {s : BeaconState preset .dencun}
    {t : BeaconState preset .pectra} (ok : upgradeToElectra config s = .ok t) :
    (getCurrentEpoch s).toNat < (t.earliestExitEpoch (by decide)).toNat ∧
    (getCurrentEpoch s).toNat < (t.earliestConsolidationEpoch (by decide)).toNat := by
  obtain ⟨first, exitEpoch, exitRate, consolidationRate, firstOk, exitOk, queues⟩ :=
    electra_departure_initialization ok
  have firstEq := (computeActivationExitEpoch_ok_iff.mp firstOk).2
  have latest : ∀ (vs : List Validator) (start : Epoch),
      start.toNat ≤ (vs.foldl (fun latest validator =>
        if validator.exitEpoch = FAR_FUTURE_EPOCH then latest else max latest validator.exitEpoch)
        start).toNat := by
    intro vs
    induction vs with
    | nil => intro start; exact Nat.le_refl _
    | cons v rest ih =>
      intro start
      have restLe := ih (if v.exitEpoch = FAR_FUTURE_EPOCH then start
        else max start v.exitEpoch)
      simp only [List.foldl_cons]
      apply Nat.le_trans _ restLe
      split
      · exact Nat.le_refl _
      · rw [Uint64.toNat_max]; exact Nat.le_max_left _ _
  have bound := latest s.validators.data.toList first
  rw [Array.foldl_toList] at bound
  have exitEq := (Uint64.addChecked_ok_iff.mp exitOk).2
  have exitField := congrArg Prod.fst queues
  have consolidationField := congrArg (fun q => q.2.2.1) queues
  change t.earliestExitEpoch (by decide) = exitEpoch at exitField
  change t.earliestConsolidationEpoch (by decide) = first at consolidationField
  rw [exitField, consolidationField]
  simp only [UInt64.reduceToNat] at exitEq
  have firstBefore : (getCurrentEpoch s).toNat < first.toNat := by omega
  refine ⟨firstBefore.trans_le ?_, firstBefore⟩
  rw [exitEq]
  exact bound.trans (Nat.le_add_right _ _)

/-- Processing pending transfers never replenishes either departure queue. -/
theorem processPendingConsolidations_departureQueues {fork : Fork}
    {s t : BeaconState preset fork} (electra : .pectra ≤ fork)
    (ok : processPendingConsolidations s electra = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  simp only [processPendingConsolidations, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨epoch, _, ⟨passed, read⟩, processed, rfl⟩ := ok
  exact passPendingConsolidations_departureQueues electra processed

/-- The epoch's pending-balance stage preserves both departure queues. -/
theorem pendingBalances_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork)
    (ok : processPendingBalances config checks s = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  simp only [processPendingBalances, electra, ↓reduceDIte, bind_ok_iff] at ok
  obtain ⟨middle, deposited, consolidated⟩ := ok
  exact (processPendingConsolidations_departureQueues electra consolidated).trans
    (pendingDeposits_departureQueues electra deposited)

private theorem justification_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork)
    (ok : processJustificationAndFinalization s = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok ok
  · rfl
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    rw [← rest]
    rfl

private theorem inactivity_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {altair : .altair ≤ fork}
    (ok : processInactivityUpdates config s altair = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  unfold processInactivityUpdates at ok
  split at ok
  · cases ok; rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    rfl

/-- A registry update either preserves both queues or executes an ejection's exit call. -/
theorem registryEntry_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {activation : Epoch} {index : Nat}
    (ok : updateRegistryEntryElectra config activation s index = .ok t) :
    departureQueues electra t = departureQueues electra s ∨
      ∃ validatorIndex, initiateValidatorExit config s validatorIndex = .ok t := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨validator, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨epoch, _, set⟩ := ok
    obtain ⟨_, rfl⟩ := setValidatorAt_ok set
    exact .inl rfl
  · split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨validatorIndex, _, exited⟩ := ok
      exact .inr ⟨validatorIndex, exited⟩
    · split at ok
      · obtain ⟨_, rfl⟩ := setValidatorAt_ok (liftAccessor_ok.mp ok)
        exact .inl rfl
      · cases ok
        exact .inl rfl

/-- Before Gloas every successful exit rate is bounded by the configured shared cap. -/
theorem exitChurnLimit_le_cap {fork : Fork} {s : BeaconState preset fork} {rate : Gwei}
    (early : fork < .glamsterdam) (ok : exitChurnLimit config s = .ok rate) :
    rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [exitChurnLimit, notGloas, ↓reduceIte, getActivationExitChurnLimit,
    bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨whole, _, rfl⟩ := ok
  exact UInt64.le_iff_toNat_le.mp Std.min_le_left

/-- Withdrawal requests either do nothing, initiate an exit, or spend partial-withdrawal churn. -/
theorem withdrawalRequest_cases {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) :
    t = s ∨ (∃ index, initiateValidatorExit config s index = .ok t) ∨
      ∃ index v owed,
        requestPartialWithdrawal config s electra index v request.amount owed = .ok t := by
  unfold processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact .inl rfl)
    | (cases ok)
    | exact .inr (.inl ⟨_, liftAccessor_ok.mp ok⟩)
    | exact .inr (.inr ⟨_, _, _, ok⟩)

/-- Starting an exit produces either no call or one call linked to the resulting queue. -/
theorem initiateExit_trace {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) {index : ValidatorIndex}
    (ok : initiateValidatorExit config s index = .ok t) :
    ∃ calls, DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
      calls (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      ∀ call ∈ calls, call.rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat := by
  obtain same | ⟨v, call, _, _, _, earliest, available, placed, left, rate, _⟩ :=
    initiateExit_call electra ok
  · subst t
    exact ⟨[], .nil _ _, by simp⟩
  · refine ⟨[call], ?_, ?_⟩
    · rw [← earliest, ← available, ← placed, ← left]
      exact .cons call (.nil _ _)
    · intro c member
      obtain rfl := List.mem_singleton.mp member
      exact exitChurnLimit_le_cap early rate

/-- Consecutive queue traces compose without adding capacity at their shared state. -/
theorem DepartureQueueTrace.append {a b c : Epoch} {x y z : Gwei}
    {first second : List DepartureQueueCall}
    (one : DepartureQueueTrace a x first b y) (two : DepartureQueueTrace b y second c z) :
    DepartureQueueTrace a x (first ++ second) c z := by
  induction one with
  | nil => exact two
  | cons call tail ih => exact .cons call (ih two)

/-- The Electra registry pass supplies a concrete exit-call trace with bounded rates. -/
theorem registryEntries_exitTrace {fork : Fork} (electra : .pectra ≤ fork)
    (early : fork < .glamsterdam) {activation : Epoch} {s t : BeaconState preset fork}
    {indices : List Nat}
    (ok : indices.foldlM (updateRegistryEntryElectra config activation) s = .ok t) :
    ∃ calls, DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
      calls (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      ∀ call ∈ calls, call.rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat := by
  induction indices generalizing s with
  | nil => cases ok; exact ⟨[], .nil _ _, by simp⟩
  | cons index rest ih =>
    obtain ⟨middle, stepped, remaining⟩ := bind_ok_iff.mp ok
    obtain ⟨later, tail, laterRates⟩ := ih remaining
    rcases registryEntry_departureQueues electra stepped with kept | ⟨i, exited⟩
    · have epoch := congrArg Prod.fst kept
      have left := congrArg (fun q => q.2.1) kept
      change middle.earliestExitEpoch electra = s.earliestExitEpoch electra at epoch
      change middle.exitBalanceToConsume electra = s.exitBalanceToConsume electra at left
      rw [epoch, left] at tail
      exact ⟨later, tail, laterRates⟩
    · obtain ⟨here, head, hereRates⟩ := initiateExit_trace electra early exited
      refine ⟨here ++ later, head.append tail, ?_⟩
      intro call member
      rcases List.mem_append.mp member with member | member
      · exact hereRates call member
      · exact laterRates call member

/-- An Electra epoch spends departure capacity only in the registry's exit calls. -/
theorem epoch_exitTrace {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (ok : processEpoch config checks s = .ok t) :
    ∃ calls, DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
      calls (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      ∀ call ∈ calls, call.rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  have capella : .shapella ≤ fork := Nat.le_trans (by decide) electra
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  have before : fork < .hegota := Nat.lt_trans early (by decide)
  simp only [processEpoch, altair, ↓reduceDIte, processEpochAltair, before, notGloas,
    capella, bind_ok_iff, pure, Except.pure, Except.ok.injEq, exists_eq_left'] at ok
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk,
    balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted, rootedOk,
    synced, syncedOk, looked⟩ := ok
  have head : departureQueues electra rewarded = departureQueues electra s :=
    (rewards_departureQueues electra rewardedOk).trans
      ((inactivity_departureQueues electra scoredOk).trans
        (justification_departureQueues electra justifiedOk))
  have resetFrame : departureQueues electra reset = departureQueues electra slashed := by
    unfold processEth1DataReset at resetOk
    simp only [bind, Except.bind, pure, Except.pure] at resetOk
    repeat' (split at resetOk <;> try cases resetOk)
    all_goals rfl
  have rootedFrame : departureQueues electra rooted = departureQueues electra mixed := by
    unfold processHistoricalSummariesUpdate at rootedOk
    simp only [bind, Except.bind, pure, Except.pure] at rootedOk
    repeat' (split at rootedOk <;> try cases rootedOk)
    all_goals rfl
  have syncedFrame : departureQueues electra synced = departureQueues electra rooted := by
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals rfl
  have lookedFrame : departureQueues electra t = departureQueues electra synced := by
    obtain ⟨_, looked, rfl⟩ := looked
    split at looked
    · simp only [liftAccessor_ok, processProposerLookahead, bind_ok_iff,
        pure, Except.pure, Except.ok.injEq] at looked
      obtain ⟨_, _, _, _, rfl⟩ := looked
      rfl
    · cases looked; rfl
  have tail : departureQueues electra t = departureQueues electra registered := by
    rw [lookedFrame, syncedFrame, rootedFrame]
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    change departureQueues electra balanced = departureQueues electra registered
    rw [effectiveBalances_departureQueues electra balancedOk,
      pendingBalances_departureQueues electra pendingOk, resetFrame,
      slashingPenalties_departureQueues electra slashedOk]
  simp only [processRegistryUpdates, electra, ↓reduceIte, bind_ok_iff] at registeredOk
  obtain ⟨_, _, entries⟩ := registeredOk
  obtain ⟨calls, trace, rates⟩ := registryEntries_exitTrace electra early entries
  have firstEpoch := congrArg Prod.fst head
  have firstBalance := congrArg (fun q => q.2.1) head
  have lastEpoch := congrArg Prod.fst tail
  have lastBalance := congrArg (fun q => q.2.1) tail
  change rewarded.earliestExitEpoch electra = s.earliestExitEpoch electra at firstEpoch
  change rewarded.exitBalanceToConsume electra = s.exitBalanceToConsume electra at firstBalance
  change t.earliestExitEpoch electra = registered.earliestExitEpoch electra at lastEpoch
  change t.exitBalanceToConsume electra = registered.exitBalanceToConsume electra at lastBalance
  rw [firstEpoch, firstBalance] at trace
  rw [lastEpoch, lastBalance]
  exact ⟨calls, trace, rates⟩

/-- Both full and partial withdrawal requests give linked, rate-bounded exit calls. -/
theorem withdrawalRequest_exitTrace {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) :
    ∃ calls, DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
      calls (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      ∀ call ∈ calls, call.rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat := by
  rcases withdrawalRequest_cases ok with same | ⟨index, exited⟩ | ⟨index, v, owed, withdrawn⟩
  · subst t; exact ⟨[], .nil _ _, by simp⟩
  · exact initiateExit_trace electra early exited
  · obtain ⟨_, same | ⟨call, earliest, available, placed, left, rate⟩⟩ :=
      partialWithdrawal_call electra withdrawn
    · subst t; exact ⟨[], .nil _ _, by simp⟩
    · refine ⟨[call], ?_, ?_⟩
      · rw [← earliest, ← available, ← placed, ← left]
        exact .cons call (.nil _ _)
      · intro c member
        obtain rfl := List.mem_singleton.mp member
        exact exitChurnLimit_le_cap early rate

/-- The validator-count churn is bounded by the registry size, not just active entries. -/
theorem validatorChurnLimit_le_cohortCap {fork : Fork} (s : BeaconState preset fork)
    (bound : Nat) (bounded : s.validators.data.size ≤ bound) :
    (getValidatorChurnLimit config s).toNat ≤ cohortCap config bound := by
  have active : (getActiveValidatorIndices s (getCurrentEpoch s)).length ≤
      s.validators.data.size := by
    exact (List.length_filterMap_le _ _).trans (by simp)
  have converted : (getActiveValidatorIndices s (getCurrentEpoch s)).length.toUInt64.toNat ≤
      bound := (Nat.mod_le _ _).trans (active.trans bounded)
  simp only [getValidatorChurnLimit, Uint64.toNat_max, UInt64.toNat_div, cohortCap]
  exact max_le_max_left _ (Nat.div_le_div_right converted)

/-- A finite pre-Electra exit is assigned only while its count cohort has room. -/
theorem exitQueue_count_room {fork : Fork} {s queued : BeaconState preset fork}
    (early : fork < .pectra) {amount : Gwei} {epoch : Epoch}
    (ok : exitQueue config s amount = .ok (queued, epoch))
    (finite : epoch ≠ FAR_FUTURE_EPOCH) (bound : Nat)
    (bounded : s.validators.data.size ≤ bound) :
    queued = s ∧
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length <
        max 1 (cohortCap config bound) := by
  have notElectra : ¬ .pectra ≤ fork := Nat.not_le_of_lt early
  simp only [exitQueue, notElectra, ↓reduceDIte, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq, Prod.mk.injEq] at ok
  obtain ⟨placed, scheduled, rfl, rfl⟩ := ok
  exact ⟨rfl, (exitQueueEpoch_churn scheduled finite).trans_le
    (max_le_max_left _ (validatorChurnLimit_le_cohortCap s bound bounded))⟩

/-- A successful voluntary exit reaches the exit scheduler with the original state. -/
theorem voluntaryExit_initiates {fork : Fork} {s t : BeaconState preset fork}
    {signed : SignedVoluntaryExit}
    (ok : processVoluntaryExit config checks s signed = .ok t) :
    initiateValidatorExit config s signed.message.validatorIndex = .ok t := by
  unfold processVoluntaryExit at ok
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
  exact exited

/-- Successful consolidation requests record the input to their balance-queue call.

Credential switches and ignored requests do not call that queue. -/
def consolidationRequestCalls {fork : Fork} (config : Config)
    (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (request : ConsolidationRequest) : Except TransitionError Bool := do
  if request.sourcePubkey == request.targetPubkey then return false
  if (state.pendingConsolidations electra).data.size ==
      preset.PENDING_CONSOLIDATIONS_LIMIT.toNat then return false
  if (← liftAccessor (getConsolidationChurnLimit config state)) ≤ preset.MIN_ACTIVATION_BALANCE
    then return false
  let some sourcePosition := findValidatorByPubkey state request.sourcePubkey | return false
  let some targetPosition := findValidatorByPubkey state request.targetPubkey | return false
  let sourceIndex ← liftAccessor (liftArith (Uint64.ofNatChecked sourcePosition.val))
  let targetIndex ← liftAccessor (liftArith (Uint64.ofNatChecked targetPosition.val))
  let source := state.validators.data[sourcePosition]
  let target := state.validators.data[targetPosition]
  unless hasExecutionWithdrawalCredential source &&
      credentialAddress source.withdrawalCredentials == request.sourceAddress do return false
  unless hasCompoundingWithdrawalCredential target do return false
  let epoch := getCurrentEpoch state
  unless isActiveValidator source epoch && isActiveValidator target epoch do return false
  unless source.exitEpoch == FAR_FUTURE_EPOCH && target.exitEpoch == FAR_FUTURE_EPOCH do
    return false
  let eligible ←
    liftAccessor (liftArith
      (Uint64.addChecked source.activationEpoch config.SHARD_COMMITTEE_PERIOD))
  if epoch < eligible then return false
  if 0 < (← liftAccessor (getPendingBalanceToWithdraw state electra sourceIndex)) then
    return false
  let _ ← queueConsolidation config state electra sourceIndex source targetIndex
  return true

def consolidationRequestSites {fork : Fork} (config : Config)
    (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (request : ConsolidationRequest) :
    Except TransitionError (List (ForkedBeaconState preset)) := do
  return if ← consolidationRequestCalls config state electra request then [⟨fork, state⟩] else []

/-- A request either preserves the scheduling queues or schedules its actual source. -/
theorem consolidationRequest_cases {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t) :
    departureQueues electra t = departureQueues electra s ∨
      ∃ sourceIndex source targetIndex,
        getValidator s sourceIndex = .ok source ∧
        queueConsolidation config s electra sourceIndex source targetIndex = .ok t := by
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact .inl rfl)
    | (cases ok)
    | exact .inl (switchToCompounding_departureQueues electra (liftAccessor_ok.mp ok))
    | exact .inr ⟨_, _, _, getValidator_eq_ok_iff.mpr
        (getElem?_toNat_of_ofNatChecked (by assumption)), ok⟩

set_option maxHeartbeats 800000 in
/-- A request classified as not calling churn preserves both departure queues. -/
theorem consolidationRequest_notCalled {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t)
    (classified : consolidationRequestCalls config s electra request = .ok false) :
    departureQueues electra t = departureQueues electra s := by
  unfold processConsolidationRequest at ok
  unfold consolidationRequestCalls at classified
  simp only [bind, Except.bind, pure, Except.pure] at ok classified
  repeat' split at ok
  all_goals first
    | (cases ok; rfl)
    | (cases ok)
    | exact switchToCompounding_departureQueues electra (liftAccessor_ok.mp ok)
    | (simp_all only [↓reduceIte, Bool.false_eq_true]; cases classified)

/-- A request classified as calling churn schedules its actual registry source. -/
theorem consolidationRequest_called {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t)
    (classified : consolidationRequestCalls config s electra request = .ok true) :
    ∃ sourceIndex source targetIndex,
      getValidator s sourceIndex = .ok source ∧
      queueConsolidation config s electra sourceIndex source targetIndex = .ok t := by
  unfold processConsolidationRequest at ok
  unfold consolidationRequestCalls at classified
  simp only [bind, Except.bind, pure, Except.pure] at ok classified
  repeat' split at ok
  all_goals first
    | (solve | cases ok)
    | exact ⟨_, _, _, getValidator_eq_ok_iff.mpr
        (getElem?_toNat_of_ofNatChecked (by assumption)), ok⟩
    | (simp_all only [↓reduceIte, Bool.false_eq_true]; cases classified)

/-- A successful request always has a successful classification of its churn call. -/
private theorem consolidationRequestCalls_result {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t) :
    ∃ called, consolidationRequestCalls config s electra request = .ok called := by
  unfold processConsolidationRequest at ok
  unfold consolidationRequestCalls
  split at ok
  · rename_i same
    simp only [same, ↓reduceIte, pure, Except.pure]
    exact ⟨false, rfl⟩
  · rename_i different
    simp only [different]
    repeat' first
      | (split at ok)
      | (simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok)
      | (obtain ⟨value, computed, ok⟩ := ok)
    all_goals simp_all only [bind, Except.bind, pure, Except.pure, ↓reduceIte]
    all_goals first | exact ⟨false, rfl⟩ | exact ⟨true, rfl⟩

/-- Replay requests in order, retaining each actual consolidation queue input. -/
def consolidationRequestsSites {fork : Fork} (config : Config) (electra : .pectra ≤ fork)
    (state : BeaconState preset fork) : List ConsolidationRequest →
      Except TransitionError (BeaconState preset fork × List (ForkedBeaconState preset))
  | [] => pure (state, [])
  | request :: rest => do
    let sites ← consolidationRequestSites config state electra request
    let next ← processConsolidationRequest config state electra request
    let (last, later) ← consolidationRequestsSites config electra next rest
    return (last, sites ++ later)

private theorem consolidationRequestsSites_result {fork : Fork}
    {electra : .pectra ≤ fork} {s t : BeaconState preset fork}
    {requests : List ConsolidationRequest}
    (ok : requests.foldlM (processConsolidationRequest config · electra ·) s = .ok t) :
    ∃ sites, consolidationRequestsSites config electra s requests = .ok (t, sites) := by
  induction requests generalizing s with
  | nil => cases ok; exact ⟨[], rfl⟩
  | cons request rest ih =>
    obtain ⟨next, stepped, remaining⟩ := bind_ok_iff.mp ok
    obtain ⟨called, classified⟩ := consolidationRequestCalls_result stepped
    obtain ⟨sites, replayed⟩ := ih remaining
    refine ⟨(if called then [⟨fork, s⟩] else []) ++ sites, ?_⟩
    simp only [consolidationRequestsSites, consolidationRequestSites, classified, stepped,
      replayed, bind, Except.bind, pure, Except.pure]

/-- Replayed consolidation requests produce linked calls bounded only at recorded sites. -/
theorem consolidationRequestsSites_trace {fork : Fork} (electra : .pectra ≤ fork)
    {s t : BeaconState preset fork} {sites : List (ForkedBeaconState preset)}
    {requests : List ConsolidationRequest}
    (ok : consolidationRequestsSites config electra s requests = .ok (t, sites))
    (cap : Nat)
    (rates : ∀ site ∈ sites, ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
      getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap) :
    ∃ calls, DepartureQueueTrace (s.earliestConsolidationEpoch electra)
      (s.consolidationBalanceToConsume electra) calls (t.earliestConsolidationEpoch electra)
      (t.consolidationBalanceToConsume electra) ∧ ∀ call ∈ calls, call.rate.toNat ≤ cap := by
  induction requests generalizing s sites with
  | nil => cases ok; exact ⟨[], .nil _ _, by simp⟩
  | cons request rest ih =>
    simp only [consolidationRequestsSites, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨here, recorded, middle, stepped, ⟨last, later⟩, replayed, rfl, rfl⟩ := ok
    obtain ⟨tailCalls, tail, tailRates⟩ := ih replayed
      (fun site mem h rate computed => rates site (List.mem_append_right _ mem) h rate computed)
    simp only [consolidationRequestSites, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at recorded
    obtain ⟨called, classified, rfl⟩ := recorded
    cases called with
    | false =>
      have kept := consolidationRequest_notCalled electra stepped classified
      have epoch := congrArg (fun q => q.2.2.1) kept
      have left := congrArg (fun q => q.2.2.2) kept
      change middle.earliestConsolidationEpoch electra = s.earliestConsolidationEpoch electra
        at epoch
      change middle.consolidationBalanceToConsume electra =
        s.consolidationBalanceToConsume electra at left
      rw [epoch, left] at tail
      exact ⟨tailCalls, tail, tailRates⟩
    | true =>
      obtain ⟨sourceIndex, source, targetIndex, _, scheduled⟩ :=
        consolidationRequest_called electra stepped classified
      obtain ⟨call, _, earliest, available, placed, left, rate, _⟩ :=
        queueConsolidation_call electra scheduled
      have head : DepartureQueueTrace (s.earliestConsolidationEpoch electra)
          (s.consolidationBalanceToConsume electra) [call]
          (middle.earliestConsolidationEpoch electra)
          (middle.consolidationBalanceToConsume electra) := by
        rw [← earliest, ← available, ← placed, ← left]
        exact .cons call (.nil _ _)
      refine ⟨call :: tailCalls, head.append tail, ?_⟩
      intro c member
      rcases List.mem_cons.mp member with rfl | member
      · exact rates ⟨fork, s⟩ (by simp) electra c.rate rate
      · exact tailRates c member

/-- The block prefix reaches execution requests before any consolidation queue call. -/
def blockConsolidationSites {fork : Fork} (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) :
    Except TransitionError (List (ForkedBeaconState preset)) := do
  if electra : .pectra ≤ fork ∧ fork < .glamsterdam then
    have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) electra.1
    have before : fork < .hegota := Nat.lt_trans electra.2 (by decide)
    let parentSlot := state.latestBlockHeader.slot
    let state ← processBlockHeader state block
    let state ← processBlockExecution config checks engine state block.body bellatrix
    let state ← processRandao config checks state block.body
    let state ← processEth1Data before state block.body
    let expected ← expectedDepositCount state before
    let deposits := (block.body.deposits before).data
    ensure (deposits.size = expected) (.wrongDepositCount deposits.size expected)
    let state ← block.body.proposerSlashings.data.foldlM
      (processProposerSlashing config checks) state
    let state ← block.body.attesterSlashings.data.foldlM
      (processAttesterSlashing config checks) state
    let state ← block.body.attestations.data.foldlM
      (processAttestation config checks · parentSlot ·) state
    let state ← deposits.foldlM (processDeposit config checks before) state
    let state ← block.body.voluntaryExits.data.foldlM (processVoluntaryExit config checks) state
    let state ← processBlsToExecutionChanges config checks state block.body
    let requests := block.body.executionRequests electra
    let state ← requests.deposits.data.foldlM (processDepositRequest · electra.1 ·) state
    let state ← requests.withdrawals.data.foldlM
      (processWithdrawalRequest config · electra.1 ·) state
    return (← consolidationRequestsSites config electra.1 state
      requests.consolidations.data.toList).2
  else return []

/-- Successful block processing cannot lose its consolidation sites through a replay error. -/
theorem blockConsolidationSites_result {fork : Fork}
    {engine : ExecutionEngine preset fork} {s t : BeaconState preset fork}
    {block : BeaconBlock preset fork}
    (ok : processBlock config checks engine s block = .ok t) :
    ∃ sites, blockConsolidationSites config checks engine s block = .ok sites := by
  by_cases electra : .pectra ≤ fork ∧ fork < .glamsterdam
  · have altair : .altair ≤ fork := Nat.le_trans (by decide) electra.1
    have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) electra.1
    have before : fork < .hegota := Nat.lt_trans electra.2 (by decide)
    have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt electra.2
    simp only [processBlock, processBlockAltair, altair, bellatrix, before, notGloas,
      ↓reduceDIte, pure_bind, bind_ok_iff] at ok
    obtain ⟨headed, headedOk, executed, executedOk, revealed, revealedOk, voted, votedOk,
      operated, operatedOk, _⟩ := ok
    simp only [processOperations, notGloas, electra.1, ↓reduceDIte,
      bind_ok_iff, ensure_ok_iff] at operatedOk
    obtain ⟨expected, expectedOk, _, count, proposed, proposedOk, attested, attestedOk,
      votedAtt, votedAttOk, deposited, depositedOk, exited, exitedOk, changed, changedOk,
      requestsOk⟩ := operatedOk
    simp only [processExecutionRequests, bind_ok_iff] at requestsOk
    obtain ⟨requested, requestedOk, withdrawn, withdrawnOk, consolidated⟩ := requestsOk
    obtain ⟨sites, replayed⟩ := consolidationRequestsSites_result
      (by simpa only [← Array.foldlM_toList] using consolidated)
    have ensured : ensure ((block.body.deposits before).data.size = expected)
        (TransitionError.wrongDepositCount (block.body.deposits before).data.size expected) =
          .ok () := ensure_ok_iff.mpr count
    refine ⟨sites, ?_⟩
    rw [blockConsolidationSites, dite_eq_left electra]
    simp only [headedOk, executedOk,
      revealedOk, votedOk, expectedOk, ensured, proposedOk, attestedOk,
      votedAttOk, depositedOk, exitedOk, changedOk, requestedOk, withdrawnOk,
      replayed, pure, Except.pure, bind, Except.bind]
  · exact ⟨[], by simp only [blockConsolidationSites, electra, ↓reduceDIte]; rfl⟩

def _root_.EthLib.Consensus.Step.consolidationSites {x y : ForkedBeaconState preset}
    (step : Step config checks x y) : List (ForkedBeaconState preset) :=
  match step with
  | .slot _ => []
  | .block engine signed _ _ =>
    ((blockConsolidationSites config checks engine x.state signed.message).toOption).getD []

def _root_.EthLib.Consensus.Run.consolidationSites {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → List (ForkedBeaconState preset)
  | _, .nil => []
  | _, .snoc pre step => pre.consolidationSites ++ step.consolidationSites

private structure SitePrefix {fork : Fork} (s t : BeaconState preset fork) : Prop where
  identity : RegistryIdentity s t
  active : ActiveStep s t
  effective : EffectiveKept s t

private theorem SitePrefix.refl {fork : Fork} (s : BeaconState preset fork) : SitePrefix s s :=
  ⟨.refl _, .refl _, effectiveKept_refl _⟩

private theorem SitePrefix.trans {fork : Fork} {s t u : BeaconState preset fork}
    (one : SitePrefix s t) (two : SitePrefix t u) : SitePrefix s u :=
  ⟨one.identity.trans two.identity, one.active.trans two.active,
    effectiveKept_trans one.effective two.effective
      (by simpa [validatorKeys] using one.identity.kept.length_le)⟩

private theorem SitePrefix.fold {fork : Fork} {α : Type}
    {action : BeaconState preset fork → α → Except TransitionError (BeaconState preset fork)}
    (kept : ∀ s a t, action s a = .ok t → SitePrefix s t)
    {s t : BeaconState preset fork} {items : List α}
    (ok : items.foldlM action s = .ok t) : SitePrefix s t :=
  foldlM_ok_invariant (SitePrefix s)
    (fun _ _ _ previous computed => previous.trans (kept _ _ _ computed)) (.refl s) ok

private theorem SitePrefix.weight {fork : Fork} {s t : BeaconState preset fork}
    (kept : SitePrefix s t) (unique : uniqueKeys s)
    (bound : t.validators.data.size < 2 ^ 64) :
    Quorum.weight (effectiveWeight t) (activeKeys t) =
      Quorum.weight (effectiveWeight s) (activeKeys s) := by
  classical
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by
    simp only [getCurrentEpoch, kept.active.1]
  have indices : getActiveValidatorIndices t (getCurrentEpoch t) =
      getActiveValidatorIndices s (getCurrentEpoch s) := by
    rw [epoch]
    exact kept.active.2.getActiveValidatorIndices_eq (getCurrentEpoch_le_activityFixedEpoch s)
  have grows : s.validators.data.size ≤ t.validators.data.size := by
    simpa [validatorKeys] using kept.identity.kept.length_le
  have inside (u : BeaconState preset fork) (_small : u.validators.data.size < 2 ^ 64)
      (i : ValidatorIndex) (member : i ∈ getActiveValidatorIndices u (getCurrentEpoch u)) :
      i.toNat < u.validators.data.size := by
    simp only [getActiveValidatorIndices, List.mem_filterMap, List.mem_zipIdx_iff_getElem?,
      Prod.exists] at member
    obtain ⟨v, index, found, chosen⟩ := member
    split at chosen
    · cases Option.some.inj chosen
      have inside := (List.getElem?_eq_some_iff.mp found).1
      simp only [Array.length_toList] at inside
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) inside
    · cases chosen
  rw [activeKeys, keys_weight t _ (kept.identity.unique unique) (inside t bound),
    activeKeys, keys_weight s _ unique (inside s (Nat.lt_of_le_of_lt grows bound)), indices]
  apply Finset.sum_congr rfl
  intro i member
  exact kept.effective i.toNat (inside s (Nat.lt_of_le_of_lt grows bound) i
    (List.mem_toFinset.mp member))

private theorem consolidationRequestSites_input {fork : Fork} {s : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : ConsolidationRequest}
    {sites : List (ForkedBeaconState preset)}
    (ok : consolidationRequestSites config s electra request = .ok sites)
    (site : ForkedBeaconState preset) (member : site ∈ sites) : site = ⟨fork, s⟩ := by
  simp only [consolidationRequestSites, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨called, _, rfl⟩ := ok
  cases called with
  | false => simp at member
  | true => simpa using member

private theorem consolidationRequestsSites_prefix {fork : Fork}
    {electra : .pectra ≤ fork} {s t : BeaconState preset fork}
    {sites : List (ForkedBeaconState preset)} {requests : List ConsolidationRequest}
    (ok : consolidationRequestsSites config electra s requests = .ok (t, sites))
    (site : ForkedBeaconState preset) (member : site ∈ sites) :
    ∃ u : BeaconState preset fork, site = ⟨fork, u⟩ ∧ SitePrefix s u := by
  induction requests generalizing s sites with
  | nil => cases ok; simp at member
  | cons request rest ih =>
    simp only [consolidationRequestsSites, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨here, recorded, next, stepped, ⟨last, later⟩, replayed, rfl, rfl⟩ := ok
    rcases List.mem_append.mp member with first | tail
    · exact ⟨s, consolidationRequestSites_input recorded site first, .refl s⟩
    · obtain ⟨u, same, kept⟩ := ih replayed tail
      exact ⟨u, same, (SitePrefix.mk (RegistryIdentity.processConsolidationRequest stepped)
        (stepKeeps_processConsolidationRequest stepped).2
        (effectiveKept_consolidationRequest stepped)).trans kept⟩

private theorem blockConsolidationSites_prefix {fork : Fork}
    {engine : ExecutionEngine preset fork} {s : BeaconState preset fork}
    {block : BeaconBlock preset fork} {sites : List (ForkedBeaconState preset)}
    (ok : blockConsolidationSites config checks engine s block = .ok sites)
    (site : ForkedBeaconState preset) (member : site ∈ sites) :
    ∃ u : BeaconState preset fork, site = ⟨fork, u⟩ ∧ SitePrefix s u := by
  unfold blockConsolidationSites at ok
  split at ok
  · rename_i electra
    simp only [bind_ok_iff, ensure_ok_iff, pure, Except.pure, Except.ok.injEq,
      ← Array.foldlM_toList] at ok
    obtain ⟨headed, headedOk, executed, executedOk, revealed, revealedOk, voted, votedOk,
      expected, expectedOk, _, count, proposed, proposedOk, attested, attestedOk,
      votedAtt, votedAttOk, deposited, depositedOk, exited, exitedOk, changed, changedOk,
      requested, requestedOk, withdrawn, withdrawnOk, ⟨last, recorded⟩, replayed, rfl⟩ := ok
    have head : SitePrefix s headed := by
      refine ⟨RegistryIdentity.processBlockHeader headedOk,
        (stepKeeps_processBlockHeader headedOk).2, ?_⟩
      obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
      exact effectiveKept_refl _
    have execution : SitePrefix headed executed := by
      refine ⟨RegistryIdentity.processBlockExecution executedOk,
        (stepKeeps_processBlockExecution executedOk).2, ?_⟩
      have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt electra.2
      have capella : .shapella ≤ fork := Nat.le_trans (by decide) electra.1
      simp only [processBlockExecution, notGloas, capella, ↓reduceDIte,
        bind_ok_iff] at executedOk
      obtain ⟨middle, withdrawn, payload⟩ := executedOk
      obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok payload
      simpa only [EffectiveKept, effectiveAt] using effectiveKept_withdrawals withdrawn
    have randao : SitePrefix executed revealed := by
      refine ⟨RegistryIdentity.processRandao revealedOk,
        (stepKeeps_processRandao revealedOk).2, ?_⟩
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealedOk
      exact effectiveKept_refl _
    have vote : SitePrefix revealed voted := by
      refine ⟨RegistryIdentity.processEth1Data votedOk,
        (stepKeeps_processEth1Data votedOk).2, ?_⟩
      obtain ⟨_, _, rest⟩ := processEth1Data_eq votedOk
      exact effectiveKept_data (congrArg (·.validators.data) rest)
    have proposers : SitePrefix voted proposed := SitePrefix.fold
      (fun _ _ _ h => ⟨RegistryIdentity.processProposerSlashing h,
        (stepKeeps_processProposerSlashing h).2, effectiveKept_proposerSlashing h⟩) proposedOk
    have attesters : SitePrefix proposed attested := SitePrefix.fold
      (fun _ _ _ h => ⟨RegistryIdentity.processAttesterSlashing h,
        (stepKeeps_processAttesterSlashing h).2, effectiveKept_attesterSlashing h⟩) attestedOk
    have attestations : SitePrefix attested votedAtt := SitePrefix.fold
      (fun _ _ _ h => ⟨RegistryIdentity.processAttestation h,
        (stepKeeps_processAttestation h).2,
        effectiveKept_data (by rw [(processAttestation_registry h).1])⟩) votedAttOk
    have deposits : SitePrefix votedAtt deposited := SitePrefix.fold
      (fun _ _ _ h => ⟨RegistryIdentity.processDeposit h,
        (stepKeeps_processDeposit h).2, effectiveKept_processDeposit h⟩) depositedOk
    have exits : SitePrefix deposited exited := SitePrefix.fold
      (fun _ _ _ h => ⟨RegistryIdentity.processVoluntaryExit h,
        (stepKeeps_processVoluntaryExit h).2, effectiveKept_voluntaryExit h⟩) exitedOk
    have changes : SitePrefix exited changed := by
      unfold processBlsToExecutionChanges at changedOk
      split at changedOk
      · rw [← Array.foldlM_toList] at changedOk
        exact SitePrefix.fold (fun _ _ _ h => ⟨RegistryIdentity.processBlsToExecutionChange h,
          (stepKeeps_processBlsToExecutionChange h).2, effectiveKept_blsChange h⟩) changedOk
      · cases changedOk; exact .refl _
    have requests : SitePrefix changed requested := SitePrefix.fold
      (fun _ _ _ h => ⟨RegistryIdentity.processDepositRequest h,
        (stepKeeps_processDepositRequest h).2, effectiveKept_depositRequest h⟩) requestedOk
    have withdrawals : SitePrefix requested withdrawn := SitePrefix.fold
      (fun _ _ _ h => ⟨RegistryIdentity.processWithdrawalRequest h,
        (stepKeeps_processWithdrawalRequest h).2, effectiveKept_withdrawalRequest h⟩) withdrawnOk
    obtain ⟨u, same, kept⟩ := consolidationRequestsSites_prefix replayed site member
    exact ⟨u, same, head.trans (execution.trans (randao.trans (vote.trans (proposers.trans
      (attesters.trans (attestations.trans (deposits.trans (exits.trans (changes.trans
        (requests.trans (withdrawals.trans kept)))))))))))⟩
  · cases ok; simp at member

theorem consolidationSites_provenance {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (early : y.fork < .glamsterdam)
    (site : ForkedBeaconState preset) (member : site ∈ tail.consolidationSites) :
    ∃ a b, ∃ pre : Run config checks x a, ∃ step : Step config checks a b,
      ∃ post : Run config checks b y,
        (pre.snoc step).append post = tail ∧
        site.fork = a.fork ∧
        getCurrentEpoch site.state = getCurrentEpoch a.state ∧
        Quorum.weight (effectiveWeight site.state) (activeKeys site.state) ≤
          Quorum.weight (effectiveWeight a.state) (activeKeys a.state) := by
  have _ := parameters
  have _ := caps
  induction tail with
  | nil => simp [Run.consolidationSites] at member
  | @snoc middle last pre step ih =>
    rcases List.mem_append.mp member with previous | current
    · obtain ⟨a, b, before, selected, after, same, fork, epoch, weight⟩ :=
        ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early) previous
      exact ⟨a, b, before, selected, after.snoc step,
        congrArg (fun run => run.snoc step) same, fork, epoch, weight⟩
    · refine ⟨middle, last, pre, step, .nil, rfl, ?_⟩
      cases step with
      | slot ok => simp [Step.consolidationSites] at current
      | @block fork before after engine signed due applied =>
        unfold Step.consolidationSites at current
        cases replay : blockConsolidationSites config checks engine before signed.message with
        | error err => simp [replay, Except.toOption] at current
        | ok sites =>
          simp only [replay, Except.toOption, Option.getD_some] at current
          obtain ⟨u, rfl, kept⟩ := blockConsolidationSites_prefix replay site current
          refine ⟨rfl, ?_, Nat.le_of_eq (kept.weight
            ((shared.append pre).unique (genesis_unique genesis)) ?_)⟩
          · simp only [getCurrentEpoch, kept.active.1]
          · exact Nat.lt_of_le_of_lt (u.validators.bound early) (UInt64.toNat_lt _)

end EthLib.Consensus.DirectSafety
