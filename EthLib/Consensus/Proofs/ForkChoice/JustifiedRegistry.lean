module

public import EthLib.Consensus.Proofs.ForkChoice.HonestCheckpoints

/-!
# Registry positions at justified checkpoints

Activity at any epoch requires an activation epoch below `FAR_FUTURE_EPOCH`.

This includes committee lookahead beyond the epoch of the head state.

Positions present at the anchor stay in every cached checkpoint registry.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}

/-- Phase0 beacon-chain `is_active_validator` excludes the far-future activation sentinel.

The strict exit bound applies even when the queried epoch is beyond the state's epoch. -/
theorem activationEpoch_ne_farFuture_of_isActiveAt
    {state : BeaconState preset fork} {epoch : Epoch} {position : Nat}
    (active : isActiveAt state epoch position = true) :
    ∃ validator, state.validators.data[position]? = some validator ∧
      validator.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  obtain ⟨validator, found, active⟩ := isActiveAt_eq_true_iff.mp active
  refine ⟨validator, found, ?_⟩
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
  intro far
  have low := UInt64.le_iff_toNat_le.mp active.1
  have high := UInt64.lt_iff_toNat_lt.mp active.2
  have bounded := validator.exitEpoch.toNat_lt
  have sentinel : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  rw [far, sentinel] at low
  omega

/-- A validator whose eligibility lies beyond a finalized boundary has not activated. -/
private def PendingAfter (epoch : Epoch) (validator : Validator) : Prop :=
  epoch < validator.activationEligibilityEpoch ∧ validator.activationEpoch = FAR_FUTURE_EPOCH

/-- Phase0 `is_eligible_for_activation` rejects a queue position beyond finality. -/
private theorem PendingAfter.not_eligible {epoch : Epoch} {validator : Validator}
    {state : BeaconState preset fork} (pending : PendingAfter epoch validator)
    (finalized : state.finalizedCheckpoint.epoch ≤ epoch) :
    isEligibleForActivation state validator = false := by
  have apart : ¬validator.activationEligibilityEpoch ≤ state.finalizedCheckpoint.epoch := by
    intro le
    exact UInt64.not_lt.mpr (UInt64.le_trans le finalized) pending.1
  simp [isEligibleForActivation, apart]

/-- Both registry-update paths set eligibility with checked addition.

Phase0 `process_registry_updates` sets eligibility to the next epoch, never a wrapped epoch. -/
private theorem PendingAfter.queueForActivation {epoch : Epoch} {validator queued : Validator}
    {state : BeaconState preset fork} (pending : PendingAfter epoch validator)
    (current : epoch ≤ getCurrentEpoch state)
    (ok : Consensus.queueForActivation state validator = .ok queued) : PendingAfter epoch queued := by
  unfold Consensus.queueForActivation at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
      addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨next, ⟨_, sum⟩, rfl⟩ := ok
    refine ⟨?_, pending.2⟩
    rw [UInt64.lt_iff_toNat_lt]
    have low := UInt64.le_iff_toNat_le.mp current
    simp only [UInt64.toNat_one] at sum
    dsimp only
    omega
  · cases ok
    exact pending

/-- A new registry entry is pending beyond every finite boundary.

Phase0 and Electra `get_validator_from_deposit` initialize both activation fields to FAR. -/
private theorem pendingAfter_deposit {epoch : Epoch} (finite : epoch < FAR_FUTURE_EPOCH)
    (pubkey : Cryptography.Bls.BLSPubkey) (credentials : Bytes32) (amount : Gwei) :
    PendingAfter epoch (getValidatorFromDeposit preset fork pubkey credentials amount) :=
  ⟨finite, rfl⟩

/-- The suffix appended after a boundary has no eligible or activated entries. -/
private def PendingTail (count : Nat) (epoch : Epoch) (state : BeaconState preset fork) : Prop :=
  ∀ position validator, count ≤ position → state.validators.data[position]? = some validator →
    PendingAfter epoch validator

private theorem PendingTail.of_validators {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} (holds : PendingTail count epoch state)
    (same : after.validators.data = state.validators.data := by rfl) :
    PendingTail count epoch after := by
  intro position validator outside found
  exact holds position validator outside (same ▸ found)

private theorem PendingTail.setValidatorAt {count position : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {validator : Validator}
    (holds : PendingTail count epoch state)
    (pending : count ≤ position → PendingAfter epoch validator)
    (set : state.setValidatorAt position validator = .ok after) :
    PendingTail count epoch after := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  intro index value outside found
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set] at found
  split at found
  · cases found
    exact pending (by omega)
  · exact holds _ _ outside found

private theorem PendingTail.setValidator {count : Nat} {index : ValidatorIndex} {epoch : Epoch}
    {state after : BeaconState preset fork} {validator : Validator}
    (holds : PendingTail count epoch state)
    (pending : count ≤ index.toNat → PendingAfter epoch validator)
    (set : state.setValidator index validator = .ok after) :
    PendingTail count epoch after :=
  holds.setValidatorAt pending (by rwa [← setValidator_eq_setValidatorAt])

private theorem PendingTail.initiateValidatorExit {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {index : ValidatorIndex}
    (holds : PendingTail count epoch state)
    (ok : initiateValidatorExit config state index = .ok after) :
    PendingTail count epoch after := by
  obtain ⟨validator, found, unchanged | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]
    exact holds
  · have same := (exitQueue_validators queue).1
    apply (holds.of_validators (congrArg (·.data) same)).setValidator _ set
    intro outside
    exact holds _ validator outside (getValidatorAt_eq_ok_iff.mp
      (by rwa [← getValidator_eq_getValidatorAt]))

private theorem PendingTail.updateRegistryEntry {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {index : Nat}
    (holds : PendingTail count epoch state) (current : epoch ≤ getCurrentEpoch state)
    (ok : Consensus.updateRegistryEntry config state index = .ok after) : PendingTail count epoch after := by
  simp only [Consensus.updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨validator, found, queued, joined, middle, set, rest⟩ := ok
  have pending : count ≤ index → PendingAfter epoch queued := fun outside =>
    (holds _ _ outside (getValidatorAt_eq_ok_iff.mp found)).queueForActivation current joined
  have middleHolds := holds.setValidatorAt pending set
  split at rest
  · simp only [bind_ok_iff, liftAccessor_ok] at rest
    obtain ⟨_, _, exited⟩ := rest
    exact middleHolds.initiateValidatorExit exited
  · cases rest
    exact middleHolds

private theorem PendingTail.updateRegistryEntryElectra {count : Nat} {epoch activation : Epoch}
    {state after : BeaconState preset fork} {index : Nat}
    (holds : PendingTail count epoch state) (current : epoch ≤ getCurrentEpoch state)
    (finalized : state.finalizedCheckpoint.epoch ≤ epoch)
    (ok : Consensus.updateRegistryEntryElectra config activation state index = .ok after) :
    PendingTail count epoch after := by
  simp only [Consensus.updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨validator, found, ok⟩ := ok
  have pending := fun outside => holds _ _ outside (getValidatorAt_eq_ok_iff.mp found)
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
      addChecked_ok_iff] at ok
    obtain ⟨next, ⟨_, sum⟩, set⟩ := ok
    apply holds.setValidatorAt _ set
    intro outside
    refine ⟨?_, (pending outside).2⟩
    have low := UInt64.le_iff_toNat_le.mp current
    rw [UInt64.lt_iff_toNat_lt]
    simp only [UInt64.toNat_one] at sum
    dsimp only
    omega
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact holds.initiateValidatorExit exited
  split at ok
  · rename_i eligible
    apply holds.setValidatorAt _ (liftAccessor_ok.mp ok)
    intro outside
    have no := (pending outside).not_eligible finalized
    rw [no] at eligible
    contradiction
  · cases ok
    exact holds

/-- A pre-Electra activation queue cannot select a pending suffix beyond finality. -/
private theorem PendingTail.not_mem_activationQueue {count : Nat} {epoch : Epoch}
    {state : BeaconState preset fork} (holds : PendingTail count epoch state)
    (within : state.RegistryWithinLimit) (finalized : state.finalizedCheckpoint.epoch ≤ epoch)
    {index : ValidatorIndex} (outside : count ≤ index.toNat) :
    index ∉ activationQueue state := by
  intro member
  simp only [activationQueue, List.mem_map] at member
  obtain ⟨⟨eligibility, found⟩, sorted, rfl⟩ := member
  have inEligible := (List.mergeSort_perm _ _).mem_iff.mp sorted
  simp only [List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq,
    List.mem_zipIdx_iff_getElem?, Prod.exists, Prod.mk.injEq] at inEligible
  obtain ⟨validator, i, atI, eligible, -, rfl⟩ := inEligible
  have inside : i < state.validators.data.size := by
    simpa using (List.getElem?_eq_some_iff.mp atI).1
  rw [toNat_toUInt64_of_lt within inside] at outside
  have pending := holds i validator outside (by simpa using atI)
  rw [pending.not_eligible finalized] at eligible
  contradiction

private theorem PendingTail.activateValidator {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {index : ValidatorIndex}
    (holds : PendingTail count epoch state) (inside : index.toNat < count)
    (ok : Consensus.activateValidator state index = .ok after) : PendingTail count epoch after := by
  simp only [Consensus.activateValidator, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, set⟩ := ok
  exact holds.setValidator (by omega) set

/-- Registry updates preserve the pending suffix while finality has not passed its boundary. -/
private theorem PendingTail.processRegistryUpdates {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} (holds : PendingTail count epoch state)
    (current : epoch ≤ getCurrentEpoch state)
    (finalized : state.finalizedCheckpoint.epoch ≤ epoch)
    (ok : Consensus.processRegistryUpdates config state = .ok after) : PendingTail count epoch after := by
  unfold Consensus.processRegistryUpdates at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨activation, _, folded⟩ := ok
    exact (foldlM_ok_invariant
      (fun s => PendingTail count epoch s ∧ s.slot = state.slot ∧
        s.finalizedCheckpoint = state.finalizedCheckpoint)
      (fun s index t ih step => by
        have frame := frame_updateRegistryEntryElectra step
        refine ⟨ih.1.updateRegistryEntryElectra ?_ ?_ step,
          frame.slot.trans ih.2.1, frame.finalized.trans ih.2.2⟩
        · simpa only [getCurrentEpoch, ih.2.1] using current
        · simpa only [ih.2.2] using finalized)
      ⟨holds, rfl, rfl⟩ folded).1
  · rename_i before
    simp only [bind_ok_iff] at ok
    obtain ⟨updated, first, last⟩ := ok
    have updatedHolds := (foldlM_ok_invariant
      (fun s => PendingTail count epoch s ∧ s.slot = state.slot ∧
        s.finalizedCheckpoint = state.finalizedCheckpoint)
      (fun s index t ih step => by
        have frame := frame_updateRegistryEntry step
        refine ⟨ih.1.updateRegistryEntry ?_ step,
          frame.slot.trans ih.2.1, frame.finalized.trans ih.2.2⟩
        simpa only [getCurrentEpoch, ih.2.1] using current)
      ⟨holds, rfl, rfl⟩ first)
    have allInside : ∀ index ∈ activationQueue updated, index.toNat < count := by
      intro index member
      by_contra outside
      exact updatedHolds.1.not_mem_activationQueue
        (updated.validators.bound (Nat.lt_trans (Nat.lt_of_not_ge before) (by decide)))
        (by simpa only [updatedHolds.2.2] using finalized) (by omega) member
    have fold : ∀ (indices : List ValidatorIndex) (s t : BeaconState preset fork),
        (∀ index ∈ indices, index.toNat < count) → PendingTail count epoch s →
        indices.foldlM Consensus.activateValidator s = .ok t → PendingTail count epoch t := by
      intro indices
      induction indices with
      | nil => intro s t _ holds ok; cases ok; exact holds
      | cons index rest ih =>
        intro s t inside holds ok
        rw [List.foldlM_cons, bind_ok_iff] at ok
        obtain ⟨middle, step, remaining⟩ := ok
        exact ih middle t (fun index mem => inside index (List.mem_cons_of_mem _ mem))
          (holds.activateValidator (inside index List.mem_cons_self) step) remaining
    exact fold _ _ _ (fun index member => allInside index (List.mem_of_mem_take member))
      updatedHolds.1 last

private theorem PendingTail.addValidatorToRegistry {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {pubkey : Cryptography.Bls.BLSPubkey}
    {credentials : Bytes32} {amount : Gwei}
    (holds : PendingTail count epoch state) (finite : epoch < FAR_FUTURE_EPOCH)
    (ok : addValidatorToRegistry state pubkey credentials amount = .ok after) :
    PendingTail count epoch after := by
  intro position validator outside found
  rw [addValidatorToRegistry_validators_eq_push ok, Array.getElem?_push] at found
  split at found
  · cases found
    exact pendingAfter_deposit finite _ _ _
  · exact holds _ _ outside found

private theorem PendingTail.increaseBalance {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {index : ValidatorIndex} {amount : Gwei}
    (holds : PendingTail count epoch state)
    (ok : increaseBalance state index amount = .ok after) : PendingTail count epoch after :=
  holds.of_validators (congrArg (·.data) (increaseBalance_validators ok))

private theorem PendingTail.decreaseBalance {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {index : ValidatorIndex} {amount : Gwei}
    (holds : PendingTail count epoch state)
    (ok : decreaseBalance state index amount = .ok after) : PendingTail count epoch after :=
  holds.of_validators (congrArg (·.data) (decreaseBalance_validators ok))

/-- Slashing changes exit fields and balances, but never activation fields. -/
private theorem PendingTail.slashValidator {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {index : ValidatorIndex}
    {whistleblower : Option ValidatorIndex} (holds : PendingTail count epoch state)
    (ok : slashValidator config state index whistleblower = .ok after) :
    PendingTail count epoch after := by
  obtain ⟨_, _, _, marked, _, _, slashings, _, _, _, _, last, exited, found, _, set,
    _, _, _, lowered, _, _, raised, paid, rfl⟩ := slashValidator_ok ok
  have exitedHolds := holds.initiateValidatorExit exited
  have markedHolds : PendingTail count epoch marked := by
    apply exitedHolds.setValidator _ set
    intro outside
    have pending := exitedHolds _ _ outside (getValidator_eq_ok_iff.mp found)
    exact ⟨pending.1, pending.2⟩
  have lastHolds := ((markedHolds.of_validators
    (after := { marked with slashings })).decreaseBalance lowered).increaseBalance raised
  have paidHolds := lastHolds.increaseBalance paid
  split <;> exact paidHolds.of_validators

private theorem PendingTail.applyPendingDeposit {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {deposit : PendingDeposit}
    (holds : PendingTail count epoch state) (finite : epoch < FAR_FUTURE_EPOCH)
    (ok : Consensus.applyPendingDeposit config checks state deposit = .ok after) :
    PendingTail count epoch after := by
  unfold Consensus.applyPendingDeposit at ok
  split at ok
  · split at ok
    · cases ok
      exact holds
    simp only [bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · exact holds.addValidatorToRegistry finite ok
    · cases ok
      exact holds
  · simp only [liftAccessor_ok, bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact holds.increaseBalance ok

private theorem PendingTail.applyDeposit {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {pubkey : Cryptography.Bls.BLSPubkey}
    {credentials : Bytes32} {amount : Gwei} {signature : Cryptography.Bls.BLSSignature}
    (holds : PendingTail count epoch state) (finite : epoch < FAR_FUTURE_EPOCH)
    (ok : Consensus.applyDeposit config checks state pubkey credentials amount signature = .ok after) :
    PendingTail count epoch after := by
  unfold Consensus.applyDeposit at ok
  split at ok
  · unfold applyDepositElectra at ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨middle, added, queued⟩ := ok
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq queued
        exact (holds.addValidatorToRegistry finite added).of_validators
      · cases ok
        exact holds
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp ok)
      exact holds.of_validators
  · exact holds.applyPendingDeposit finite ok

private theorem PendingTail.processDeposit {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {before : fork < .hegota} {deposit : Deposit}
    (holds : PendingTail count epoch state) (finite : epoch < FAR_FUTURE_EPOCH)
    (ok : processDeposit config checks before state deposit = .ok after) :
    PendingTail count epoch after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok ok
  exact (holds.of_validators (after := { state with eth1DepositIndex := fun _ => next })).applyDeposit
    finite applied

private theorem PendingTail.passPendingDeposits {count : Nat} {epoch : Epoch}
    {stop : PendingDeposit → Bool} {nextEpoch : Epoch} {available : Gwei}
    (finite : epoch < FAR_FUTURE_EPOCH) :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {seen : Nat} {postponed : Array PendingDeposit} {pass},
      PendingTail count epoch state →
      Consensus.passPendingDeposits config checks stop nextEpoch available state processed seen
        postponed deposits = .ok pass → PendingTail count epoch pass.1.state
  | [], _, _, _, _, _, holds, ok => by cases ok; exact holds
  | deposit :: rest, state, processed, seen, postponed, pass, holds, ok => by
    unfold Consensus.passPendingDeposits at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    split at ok
    · cases ok; exact holds
    split at ok
    · cases ok
    split at ok
    · split at ok
      · cases ok
      rename_i credited
      split at ok
      · cases ok
      cases ok
      exact PendingTail.passPendingDeposits finite (deposits := rest)
        (holds.applyPendingDeposit finite credited) ‹_›
    split at ok
    · split at ok
      · cases ok
      cases ok
      exact PendingTail.passPendingDeposits finite (deposits := rest) holds ‹_›
    split at ok
    · cases ok
    split at ok
    · cases ok; exact holds
    split at ok
    · cases ok
    rename_i credited
    split at ok
    · cases ok
    cases ok
    exact PendingTail.passPendingDeposits finite (deposits := rest)
      (holds.applyPendingDeposit finite credited) ‹_›

/-- Electra pending balances append through the same deposit constructor.

The deposit's request slot does not determine when its registry position is created. -/
private theorem PendingTail.processPendingBalances {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} (holds : PendingTail count epoch state)
    (finite : epoch < FAR_FUTURE_EPOCH)
    (ok : Consensus.processPendingBalances config checks state = .ok after) :
    PendingTail count epoch after := by
  unfold Consensus.processPendingBalances at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨middle, deposited, consolidated⟩ := ok
    have deposits : PendingTail count epoch middle := by
      unfold processPendingDeposits at deposited
      simp only [bind, Except.bind, pure, Except.pure] at deposited
      repeat' (split at deposited <;> try cases deposited)
      all_goals exact (PendingTail.passPendingDeposits finite holds ‹_›).of_validators
    exact deposits.of_validators (congrArg (·.data) (processPendingConsolidations_kept consolidated).1)
  · cases ok
    exact holds

/-- A fold preserves the same pending suffix when each successful step preserves it. -/
private theorem PendingTail.foldlM {count : Nat} {epoch : Epoch} {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    {state after : BeaconState preset fork} {items : List α}
    (holds : PendingTail count epoch state)
    (keeps : ∀ s x t, PendingTail count epoch s → step s x = .ok t → PendingTail count epoch t)
    (ok : items.foldlM step state = .ok after) : PendingTail count epoch after :=
  foldlM_ok_invariant (PendingTail count epoch) keeps holds ok

private theorem PendingTail.processDepositRequest {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork} {request : DepositRequest}
    (holds : PendingTail count epoch state)
    (ok : Consensus.processDepositRequest state electra request = .ok after) :
    PendingTail count epoch after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [Consensus.processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit,
    bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  exact holds.of_validators

private theorem PendingTail.requestPartialWithdrawal {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (holds : PendingTail count epoch state)
    (ok : Consensus.requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) : PendingTail count epoch after := by
  simp only [Consensus.requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure]
    at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    exact holds.of_validators (by rw [(computeExitEpochAndUpdateChurn_earliest churned).2.1])
  · cases ok; exact holds

private theorem PendingTail.processWithdrawalRequest {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (holds : PendingTail count epoch state)
    (ok : Consensus.processWithdrawalRequest config state electra request = .ok after) :
    PendingTail count epoch after := by
  unfold Consensus.processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact holds)
    | exact holds.initiateValidatorExit (liftAccessor_ok.mp ok)
    | exact holds.requestPartialWithdrawal ok

private theorem PendingTail.queueExcessActiveBalance {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (holds : PendingTail count epoch state)
    (ok : Consensus.queueExcessActiveBalance state electra index = .ok after) :
    PendingTail count epoch after := by
  simp only [Consensus.queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact holds.of_validators
  · cases ok; exact holds

private theorem PendingTail.switchToCompoundingValidator {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (holds : PendingTail count epoch state)
    (ok : Consensus.switchToCompoundingValidator state electra index = .ok after) :
    PendingTail count epoch after := by
  simp only [Consensus.switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, found, _, set, queued⟩ := ok
  apply PendingTail.queueExcessActiveBalance _ queued
  apply holds.setValidator _ set
  intro outside
  have pending := holds _ _ outside (getValidator_eq_ok_iff.mp found)
  exact ⟨pending.1, pending.2⟩

private theorem PendingTail.queueConsolidation {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (holds : PendingTail count epoch state)
    (found : state.validators.data[sourceIndex.toNat]? = some source)
    (ok : Consensus.queueConsolidation config state electra sourceIndex source targetIndex =
      .ok after) : PendingTail count epoch after := by
  simp only [Consensus.queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, addChecked_ok_iff, pure, Except.pure] at ok
  obtain ⟨⟨churnedState, exitEpoch⟩, churned, withdrawal, _, _, set, _, _, ok⟩ := ok
  simp only [Except.ok.injEq] at ok
  subst ok
  have validators := (computeConsolidationEpochAndUpdateChurn_earliest churned).2.1
  apply PendingTail.of_validators (same := rfl)
  apply (holds.of_validators (same := congrArg (·.data) validators)).setValidator _ set
  intro outside
  have pending := holds _ _ outside found
  exact ⟨pending.1, pending.2⟩

private theorem PendingTail.processConsolidationRequest {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork}
    {request : ConsolidationRequest} (holds : PendingTail count epoch state)
    (ok : Consensus.processConsolidationRequest config state electra request = .ok after) :
    PendingTail count epoch after := by
  unfold Consensus.processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact holds)
    | exact holds.switchToCompoundingValidator (liftAccessor_ok.mp ok)
    | exact holds.queueConsolidation (getElem?_toNat_of_ofNatChecked (by assumption)) ok

private theorem PendingTail.processExecutionRequests {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam} (holds : PendingTail count epoch state)
    (ok : Consensus.processExecutionRequests config state body electra = .ok after) :
    PendingTail count epoch after := by
  simp only [Consensus.processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
  exact ((holds.foldlM (fun _ _ _ h ok => h.processDepositRequest ok) deposits).foldlM
    (fun _ _ _ h ok => h.processWithdrawalRequest ok) withdrawals).foldlM
    (fun _ _ _ h ok => h.processConsolidationRequest ok) consolidations

/-- Registry growth along imported parent transitions retains every anchor position.

The store is fixed-fork, so these transitions do not include fork upgrades. -/
theorem Store.Reachable.anchor_registry_le_blockState
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {root : Root} {state : BeaconState preset fork}
    (stored : store.blockStates[root]? = some state) :
    anchorState.validators.data.size ≤ state.validators.data.size := by
  obtain ⟨block, found⟩ := reachable.known_of_blockState stored
  obtain ⟨post, postOk, anchored, produced⟩ := reachable.blockStatesFromParents found
  rw [stored, Option.some.injEq] at postOk
  subst post
  by_cases same : block = anchorBlock
  · rw [anchored same]
  · obtain ⟨parent, checks, engine, signed, -, parentFound, transitioned⟩ := produced same
    exact Nat.le_trans (reachable.anchor_registry_le_blockState parentFound)
      (runKept_stateTransition transitioned).grows
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

namespace Store

/-- Fork-choice `update_checkpoints` includes the supplied finalized epoch in its maximum. -/
private theorem finalized_le_updateCheckpoints (store : Store preset fork)
    (justified finalized : Checkpoint) :
    finalized.epoch ≤ (store.updateCheckpoints justified finalized).finalizedCheckpoint.epoch := by
  unfold updateCheckpoints
  split <;> dsimp only <;> split
  all_goals first | exact UInt64.le_refl _ | exact UInt64.not_lt.mp ‹_›

/-- The realized finality of an imported state is bounded by the resulting store's finality.

Fork-choice `on_block` updates realized checkpoints before pulling up the tip. -/
private theorem addBlock_finalized_states
    {store after : Store preset fork} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork} {root : Root}
    (holds : ∀ (r : Root) (s : BeaconState preset fork), store.blockStates[r]? = some s →
      s.finalizedCheckpoint.epoch ≤ store.finalizedCheckpoint.epoch)
    (added : store.addBlock config checks sources signed root = .ok after) :
    ∀ (r : Root) (s : BeaconState preset fork), after.blockStates[r]? = some s →
      s.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch := by
  have forward := (addBlock_ok added).1.2
  unfold addBlock at added
  simp only [bind_ok_iff] at added
  obtain ⟨state, -, head, -, voted, vote, recorded, record, boosted, boost, added⟩ := added
  obtain ⟨-, -, bs0⟩ := (recordBlockPtcVotes_onlyPtcVotes vote).frame
  obtain ⟨-, -, bs1, -⟩ := recordBlockTimeliness_frame record
  obtain ⟨-, -, bs2, -⟩ := updateProposerBoostRoot_frame boost
  obtain ⟨later, -, bs3, -⟩ := computePulledUpTip_frame added
  intro r s found
  rw [bs3, updateCheckpoints_blockStates, bs2, bs1, bs0,
    Std.TreeMap.getElem?_insert] at found
  split at found
  · cases found
    exact UInt64.le_trans (finalized_le_updateCheckpoints boosted _ _) later.2
  · exact UInt64.le_trans (holds _ _ found) forward

/-- Every held block state has finality at most the store's realized finality.

At the anchor the store starts finalized at the anchor epoch.

Each block import includes its post-state finality, and every handler preserves the bound. -/
theorem Reachable.blockState_finalized_le {store : Store preset fork}
    (reachable : Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState)
    {root : Root} {state : BeaconState preset fork}
    (stored : store.blockStates[root]? = some state) :
    state.finalizedCheckpoint.epoch ≤ store.finalizedCheckpoint.epoch := by
  have all : ∀ (r : Root) (s : BeaconState preset fork), store.blockStates[r]? = some s →
      s.finalizedCheckpoint.epoch ≤ store.finalizedCheckpoint.epoch := by
    clear stored state root
    induction reachable with
    | anchor made =>
      obtain ⟨anchorRoot, -, -, states⟩ := getForkchoiceStore_maps made
      obtain ⟨checkpointRoot, _, _, _, _, finalized, _, _⟩ := getForkchoiceStore_anchor made
      intro r s found
      rw [states, getElem?_insert_root] at found
      split at found
      · simp only [Option.some.injEq] at found
        subst s
        rw [finalized]
        exact UInt64.le_trans (finalized_le_currentJustified sound.ordered)
          (UInt64.le_trans sound.settled (getPreviousEpoch_le _))
      · simp at found
    | @block before after checks sources signed _ added ih =>
      unfold onBlock at added
      simp only [bind_ok_iff] at added
      obtain ⟨_, -, added⟩ := added
      split at added
      · cases added
        exact ih
      · exact addBlock_finalized_states ih added
    | tick _ handled ih =>
      obtain ⟨-, le, -, states⟩ := onTick_frame handled
      intro r s found
      exact UInt64.le_trans (ih r s (states ▸ found)) le.2
    | attestation _ handled ih =>
      obtain ⟨le, -, states⟩ := onAttestation_frame handled
      intro r s found
      exact UInt64.le_trans (ih r s (states ▸ found)) le.2
    | attesterSlashing _ handled ih =>
      obtain ⟨le, -, states⟩ := onAttesterSlashing_frame handled
      intro r s found
      exact UInt64.le_trans (ih r s (states ▸ found)) le.2
    | payloadAttestation _ handled ih =>
      obtain ⟨le, -, states⟩ := (onPayloadAttestationMessage_onlyPtcVotes handled).frame
      intro r s found
      exact UInt64.le_trans (ih r s (states ▸ found)) le.2
    | envelope _ handled ih =>
      obtain ⟨le, -, states⟩ := onExecutionPayloadEnvelope_frame handled
      intro r s found
      exact UInt64.le_trans (ih r s (states ▸ found)) le.2
    | inclusionList _ handled ih =>
      obtain ⟨le, -, states⟩ := onInclusionList_frame handled
      intro r s found
      exact UInt64.le_trans (ih r s (states ▸ found)) le.2
  exact all root state stored

end Store

namespace Models.Network

variable {sources : BlockSources preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- Cached checkpoint processing cannot remove a position already present at the anchor. -/
theorem Execution.validatorAt_checkpoint_of_anchor
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ}
    {checkpoint : Checkpoint} {state : BeaconState preset fork}
    (stateOk : ((e.world k).state w).checkpointState checkpoint = .ok state)
    {v : ValidatorIndex} (inside : v.toNat < anchorState.validators.data.size) :
    ∃ validator, state.validators.data[v.toNat]? = some validator := by
  have reached := e.reachable
    (fun u hu => (start u hu).symm ▸ Store.Reachable.anchor anchored) k w honest
  obtain ⟨base, slot, stored, -, advanced⟩ :=
    e.checkpointStates_fixedChecks anchored (start w honest)
      (Store.checkpointState_ok_iff.mp stateOk)
  have grows := reached.anchor_registry_le_blockState stored
  have later : base.validators.data.size ≤ state.validators.data.size := by
    unfold lookaheadState at advanced
    split at advanced
    · exact (runKept_processSlots (mapError_ok_iff.mp advanced)).grows
    · cases advanced
      exact Nat.le_refl _
  have bound := Nat.lt_of_lt_of_le inside (Nat.le_trans grows later)
  exact ⟨state.validators.data[v.toNat], Array.getElem?_eq_getElem bound⟩

end Models.Network

end EthLib.Consensus
