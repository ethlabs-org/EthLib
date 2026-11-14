module

public import EthLib.Consensus.Proofs.ForkChoice.HonestCheckpoints
public import EthLib.Consensus.Proofs.ForkChoice.JustifiedOrigins
import EthLib.Consensus.Proofs.ForkChoice.BlockRuns

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
    (ok : Consensus.queueForActivation state validator = .ok queued) :
    PendingAfter epoch queued := by
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
    (ok : Consensus.updateRegistryEntry config state index = .ok after) :
    PendingTail count epoch after := by
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
    (ok : Consensus.processRegistryUpdates config state = .ok after) :
    PendingTail count epoch after := by
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
    (ok : Consensus.applyDeposit config checks state pubkey credentials amount signature =
      .ok after) :
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
  exact (holds.of_validators
    (after := { state with eth1DepositIndex := fun _ => next })).applyDeposit finite applied

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
    exact deposits.of_validators
      (congrArg (·.data) (processPendingConsolidations_kept consolidated).1)
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

private theorem PendingTail.processEffectiveBalanceUpdates {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} (holds : PendingTail count epoch state)
    (ok : Consensus.processEffectiveBalanceUpdates state = .ok after) :
    PendingTail count epoch after := by
  apply holds.foldlM (fun s index t h step => ?_) ok
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at step
  obtain ⟨_, found, _, _, _, _, set⟩ := step
  apply h.setValidatorAt _ set
  intro outside
  have pending := h _ _ outside (getValidatorAt_eq_ok_iff.mp found)
  exact ⟨pending.1, pending.2⟩

private theorem PendingTail.processRewardsAndPenalties {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} (holds : PendingTail count epoch state)
    (ok : Consensus.processRewardsAndPenalties config state = .ok after) :
    PendingTail count epoch after := by
  have deltas {s t : BeaconState preset fork} {rewards penalties : Array Gwei} {index : Nat}
      (h : PendingTail count epoch s) (ok : applyDeltas rewards penalties s index = .ok t) :
      PendingTail count epoch t := by
    simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, raised, lowered⟩ := ok
    exact (h.increaseBalance raised).decreaseBalance lowered
  have allDeltas {s t : BeaconState preset fork} {ds : Array Gwei × Array Gwei}
      (h : PendingTail count epoch s) (ok : applyAllDeltas s ds = .ok t) :
      PendingTail count epoch t := h.foldlM (fun _ _ _ h ok => deltas h ok) ok
  unfold Consensus.processRewardsAndPenalties at ok
  split at ok
  · cases ok; exact holds
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, _, _, applied⟩ := ok
    exact holds.foldlM (fun _ _ _ h ok => allDeltas h ok) applied
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, applied⟩ := ok
    exact allDeltas holds applied

private theorem PendingTail.applySlashingPenalty {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {total adjusted : Gwei} {index : Nat}
    (holds : PendingTail count epoch state)
    (ok : Consensus.applySlashingPenalty state total adjusted index = .ok after) :
    PendingTail count epoch after := by
  simp only [Consensus.applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, _, _, _, _, lowered⟩ := ok
      exact holds.decreaseBalance lowered
    · cases ok; exact holds
  · cases ok; exact holds

private theorem PendingTail.applySlashingPenaltyElectra {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {perIncrement : Gwei} {index : Nat}
    (holds : PendingTail count epoch state)
    (ok : Consensus.applySlashingPenaltyElectra state perIncrement index = .ok after) :
    PendingTail count epoch after := by
  simp only [Consensus.applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, _, _, lowered⟩ := ok
      exact holds.decreaseBalance lowered
    · cases ok; exact holds
  · cases ok; exact holds

private theorem PendingTail.processSlashings {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} (holds : PendingTail count epoch state)
    (ok : Consensus.processSlashings state = .ok after) : PendingTail count epoch after := by
  unfold Consensus.processSlashings at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, applied⟩ := ok
    exact holds.foldlM (fun _ _ _ h ok => h.applySlashingPenaltyElectra ok) applied
  · exact holds.foldlM (fun _ _ _ h ok => h.applySlashingPenalty ok) ok

private theorem PendingTail.processJustificationAndFinalization {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} (holds : PendingTail count epoch state)
    (ok : Consensus.processJustificationAndFinalization state = .ok after) :
    PendingTail count epoch after :=
  holds.of_validators (by rw [(processJustificationAndFinalization_keeps ok).2.2.2.2.2.1])

private theorem PendingTail.processInactivityUpdates {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {altair : .altair ≤ fork}
    (holds : PendingTail count epoch state)
    (ok : Consensus.processInactivityUpdates config state altair = .ok after) :
    PendingTail count epoch after := by
  unfold Consensus.processInactivityUpdates at ok
  split at ok
  · cases ok; exact holds
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    exact holds.of_validators

private theorem PendingTail.processEth1DataReset {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {before : fork < .hegota}
    (holds : PendingTail count epoch state)
    (ok : Consensus.processEth1DataReset before state = .ok after) :
    PendingTail count epoch after := by
  simp only [Consensus.processEth1DataReset, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok <;> cases ok <;> exact holds.of_validators

private theorem PendingTail.processSlashingsReset {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} (holds : PendingTail count epoch state)
    (ok : Consensus.processSlashingsReset state = .ok after) : PendingTail count epoch after := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq ok
  exact holds.of_validators

private theorem PendingTail.processRandaoMixesReset {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} (holds : PendingTail count epoch state)
    (ok : Consensus.processRandaoMixesReset state = .ok after) : PendingTail count epoch after := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq ok
  exact holds.of_validators

private theorem PendingTail.processHistoricalRootsUpdate {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} (holds : PendingTail count epoch state)
    (ok : Consensus.processHistoricalRootsUpdate state = .ok after) :
    PendingTail count epoch after := by
  unfold Consensus.processHistoricalRootsUpdate at ok
  split at ok
  · cases ok
  simp only [bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    exact holds.of_validators
  · cases ok; exact holds

private theorem PendingTail.processHistoricalSummariesUpdate {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {capella : .shapella ≤ fork}
    (holds : PendingTail count epoch state)
    (ok : Consensus.processHistoricalSummariesUpdate state capella = .ok after) :
    PendingTail count epoch after := by
  unfold Consensus.processHistoricalSummariesUpdate at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals exact holds.of_validators

private theorem PendingTail.epochTail {count : Nat} {epoch : Epoch}
    {after rooted synced looked : BeaconState preset fork} {altair : .altair ≤ fork}
    (holds : PendingTail count epoch rooted)
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair)
      altair = .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : PendingTail count epoch after := by
  have syncedHolds : PendingTail count epoch synced := by
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals exact holds.of_validators
  have lookedHolds : PendingTail count epoch looked := by
    split at lookedOk
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at lookedOk
      obtain ⟨_, _, _, _, rfl⟩ := lookedOk
      exact syncedHolds.of_validators
    · cases lookedOk; exact syncedHolds
  split at windowed
  · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at windowed
    obtain ⟨_, _, _, _, rfl⟩ := windowed
    exact lookedHolds.of_validators
  · cases windowed; exact lookedHolds

/-- Finality after the epoch bounds the activation test inside the epoch.

All steps after justification preserve its finalized checkpoint. -/
private theorem PendingTail.processEpochAltair {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {altair : .altair ≤ fork}
    (holds : PendingTail count epoch state) (current : epoch ≤ getCurrentEpoch state)
    (finite : epoch < FAR_FUTURE_EPOCH) (finalized : after.finalizedCheckpoint.epoch ≤ epoch)
    (ok : Consensus.processEpochAltair config checks state altair = .ok after) :
    PendingTail count epoch after := by
  obtain ⟨justifiedState, justifiedOk, restFrame⟩ := processEpochAltair_frame ok
  unfold Consensus.processEpochAltair at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, justified, _, scored, _, rewarded, _, registered, slashedState, slashed,
    reset, resetOk, pending, pendingOk, paid, paidOk, _, balanced, _, cleared,
    mixed, mixedOk, ok⟩ := ok
  have same := Except.ok.inj (justified.symm.trans justifiedOk)
  subst justifiedState
  have preFrame := (frame_processInactivityUpdates scored).trans
    (frame_processRewardsAndPenalties rewarded)
  have beforeHolds :=
    ((holds.processJustificationAndFinalization justified).processInactivityUpdates
      scored).processRewardsAndPenalties rewarded
  have registeredHolds := beforeHolds.processRegistryUpdates
    (by simpa only [getCurrentEpoch, preFrame.slot,
      (activeStep_processJustificationAndFinalization justified).1] using current)
    (by simpa only [preFrame.finalized, restFrame.finalized] using finalized) registered
  have slashedHolds := registeredHolds.processSlashings slashed
  have resetHolds : PendingTail count epoch reset := by
    split at resetOk
    · exact slashedHolds.processEth1DataReset resetOk
    · cases resetOk; exact slashedHolds
  have pendingHolds := resetHolds.processPendingBalances finite pendingOk
  have paidHolds : PendingTail count epoch paid := by
    split at paidOk
    · simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at paidOk
      obtain ⟨_, _, rfl⟩ := paidOk
      exact pendingHolds.of_validators
    · cases paidOk; exact pendingHolds
  have mixedHolds := ((paidHolds.processEffectiveBalanceUpdates balanced).processSlashingsReset
    cleared).processRandaoMixesReset mixedOk
  split at ok <;> simp only [bind_ok_iff] at ok <;>
    obtain ⟨_, rooted, _, synced, _, looked, windowed⟩ := ok
  · exact (mixedHolds.processHistoricalSummariesUpdate rooted).epochTail synced looked windowed
  · exact (mixedHolds.processHistoricalRootsUpdate rooted).epochTail synced looked windowed

private theorem PendingTail.processEpoch {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork}
    (holds : PendingTail count epoch state) (current : epoch ≤ getCurrentEpoch state)
    (finite : epoch < FAR_FUTURE_EPOCH) (finalized : after.finalizedCheckpoint.epoch ≤ epoch)
    (ok : Consensus.processEpoch config checks state = .ok after) :
    PendingTail count epoch after := by
  obtain ⟨justifiedState, justifiedOk, restFrame⟩ := processEpoch_frame ok
  unfold Consensus.processEpoch at ok
  split at ok
  · exact holds.processEpochAltair current finite finalized ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, justified, _, rewarded, _, registered, _, slashed, _, reset, _, balanced,
      _, cleared, _, mixed, rooted, rootedOk, rotated⟩ := ok
    have same := Except.ok.inj (justified.symm.trans justifiedOk)
    subst justifiedState
    have beforeHolds :=
      (holds.processJustificationAndFinalization justified).processRewardsAndPenalties rewarded
    have preFrame := frame_processRewardsAndPenalties rewarded
    have registeredHolds := beforeHolds.processRegistryUpdates
      (by simpa only [getCurrentEpoch, preFrame.slot,
        (activeStep_processJustificationAndFinalization justified).1] using current)
      (by simpa only [preFrame.finalized, restFrame.finalized] using finalized) registered
    have rootedHolds := (((((registeredHolds.processSlashings slashed).processEth1DataReset
      reset).processEffectiveBalanceUpdates balanced).processSlashingsReset
      cleared).processRandaoMixesReset mixed).processHistoricalRootsUpdate rootedOk
    unfold processParticipationRecordUpdates at rotated
    split at rotated
    · cases rotated
    · cases rotated; exact rootedHolds.of_validators

private theorem PendingTail.applyWithdrawal {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {withdrawal : Withdrawal}
    (holds : PendingTail count epoch state)
    (ok : Consensus.applyWithdrawal state withdrawal = .ok after) :
    PendingTail count epoch after := by
  unfold Consensus.applyWithdrawal at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, set⟩ := ok
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact holds.of_validators
  · exact holds.decreaseBalance ok

private theorem PendingTail.applyExpectedWithdrawals {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals} (holds : PendingTail count epoch state)
    (ok : Consensus.applyExpectedWithdrawals state capella expected = .ok after) :
    PendingTail count epoch after := by
  unfold Consensus.applyExpectedWithdrawals at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := ok
  have appliedHolds : PendingTail count epoch applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact holds.foldlM (fun _ _ _ h ok => h.applyWithdrawal ok) appliedOk
  have indexedHolds : PendingTail count epoch indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact appliedHolds.of_validators
    · cases indexedOk; exact appliedHolds
  have queued : ∀ s : BeaconState preset fork, PendingTail count epoch s →
      PendingTail count epoch (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals s gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount else s) := by
    intro s h
    split <;> exact h.of_validators
  have partials : ∀ s : BeaconState preset fork, PendingTail count epoch s →
      PendingTail count epoch (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals s electra expected.processedPartialWithdrawalsCount
      else s) := by
    intro s h
    split <;> exact h.of_validators
  have swept : ∀ s : BeaconState preset fork, PendingTail count epoch s →
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex s gloas expected.processedBuildersSweepCount
      else pure s) = .ok finished → PendingTail count epoch finished := by
    intro s h computed
    split at computed
    · unfold updateNextWithdrawalBuilderIndex at computed
      dsimp only at computed
      split at computed
      · cases computed; exact h.of_validators
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
        obtain ⟨_, _, rfl⟩ := computed
        exact h.of_validators
    · cases computed; exact h
  have finishedHolds := swept _ (partials _ (queued _ indexedHolds)) sweptOk
  unfold updateNextWithdrawalValidatorIndex at last
  simp only [bind_ok_iff] at last
  obtain ⟨_, _, last⟩ := last
  split at last
  · cases last
  · cases last; exact finishedHolds.of_validators

private theorem PendingTail.processWithdrawals {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (holds : PendingTail count epoch state)
    (ok : Consensus.processWithdrawals state capella payload = .ok after) :
    PendingTail count epoch after := by
  unfold Consensus.processWithdrawals at ok
  split at ok
  · split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, applied⟩ := ok
      exact holds.applyExpectedWithdrawals applied
    · cases ok; exact holds
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, applied⟩ := ok
    exact holds.applyExpectedWithdrawals applied

private theorem PendingTail.processBlsToExecutionChange {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {signed : SignedBLSToExecutionChange}
    (holds : PendingTail count epoch state)
    (ok : Consensus.processBlsToExecutionChange config checks state signed = .ok after) :
    PendingTail count epoch after := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  apply holds.setValidator _ set
  intro outside
  have pending := holds _ _ outside (getValidator_eq_ok_iff.mp found)
  exact ⟨pending.1, pending.2⟩

private theorem PendingTail.processProposerSlashing {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {slashing : ProposerSlashing}
    (holds : PendingTail count epoch state)
    (ok : Consensus.processProposerSlashing config checks state slashing = .ok after) :
    PendingTail count epoch after := by
  simp only [Consensus.processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact holds.slashValidator slashed

private theorem PendingTail.processAttesterSlashing {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {slashing : AttesterSlashing preset fork}
    (holds : PendingTail count epoch state)
    (ok : Consensus.processAttesterSlashing config checks state slashing = .ok after) :
    PendingTail count epoch after := by
  simp only [Consensus.processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  refine foldlM_ok_invariant (fun step => PendingTail count epoch step.1)
    (fun step _ next before ok => ?_)
    (show PendingTail count epoch (state, false).1 from holds) folded
  obtain ⟨middle, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact before.slashValidator slashed
  · cases ok; exact before

private theorem PendingTail.processVoluntaryExit {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {signed : SignedVoluntaryExit}
    (holds : PendingTail count epoch state)
    (ok : Consensus.processVoluntaryExit config checks state signed = .ok after) :
    PendingTail count epoch after := by
  unfold Consensus.processVoluntaryExit at ok
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
  exact holds.initiateValidatorExit exited

private theorem PendingTail.processOperations {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (holds : PendingTail count epoch state) (finite : epoch < FAR_FUTURE_EPOCH)
    (preGloas : fork < .glamsterdam)
    (ok : Consensus.processOperations config checks state body parentSlot = .ok after) :
    PendingTail count epoch after := by
  unfold Consensus.processOperations at ok
  split at ok
  · exact False.elim (Nat.not_le_of_lt preGloas ‹_›)
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, _, _, _, _, proposers, _, attesters, _, attestations, _, deposits, exited,
    exits, changed, changesOk, requestsOk⟩ := ok
  have p := holds.foldlM (fun _ _ _ h ok => h.processProposerSlashing ok) proposers
  have a := p.foldlM (fun _ _ _ h ok => h.processAttesterSlashing ok) attesters
  have votes := a.foldlM (fun _ _ _ h ok =>
    h.of_validators (congrArg (·.data) (processAttestation_registry ok).1)) attestations
  have deposited := votes.foldlM (fun _ _ _ h ok => h.processDeposit finite ok) deposits
  have exitedHolds := deposited.foldlM (fun _ _ _ h ok => h.processVoluntaryExit ok) exits
  have changedHolds : PendingTail count epoch changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact exitedHolds.foldlM (fun _ _ _ h ok => h.processBlsToExecutionChange ok) changesOk
    · cases changesOk; exact exitedHolds
  split at requestsOk
  · exact changedHolds.processExecutionRequests requestsOk
  · cases requestsOk; exact changedHolds

private theorem PendingTail.processSyncAggregate {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset} (holds : PendingTail count epoch state)
    (ok : Consensus.processSyncAggregate config checks state altair aggregate = .ok after) :
    PendingTail count epoch after := by
  unfold Consensus.processSyncAggregate at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := ok
  rw [← Array.foldlM_toList] at folded
  refine holds.foldlM (fun _ _ _ h ok => ?_) folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact (h.increaseBalance raised).increaseBalance paid
  · exact h.decreaseBalance (liftAccessor_ok.mp ok)

private theorem PendingTail.processExecutionPayload {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {body : BeaconBlockBody preset fork}
    {engine : ExecutionEngine preset fork} {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (holds : PendingTail count epoch state)
    (ok : Consensus.processExecutionPayload config engine state body bellatrix = .ok after) :
    PendingTail count epoch after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
  exact holds.of_validators

private theorem PendingTail.processBlockExecution {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {body : BeaconBlockBody preset fork}
    {engine : ExecutionEngine preset fork} {bellatrix : .bellatrix ≤ fork}
    (holds : PendingTail count epoch state) (preGloas : fork < .glamsterdam)
    (ok : Consensus.processBlockExecution config checks engine state body bellatrix = .ok after) :
    PendingTail count epoch after := by
  unfold Consensus.processBlockExecution at ok
  split at ok
  · exact False.elim (Nat.not_le_of_lt preGloas ‹_›)
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, paid⟩ := ok
    exact (holds.processWithdrawals withdrawn).processExecutionPayload paid
  · dsimp only at ok
    split at ok
    · exact holds.processExecutionPayload ok
    · cases ok; exact holds

private theorem PendingTail.processBlockHeader {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (holds : PendingTail count epoch state)
    (ok : Consensus.processBlockHeader state block = .ok after) :
    PendingTail count epoch after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq ok
  exact holds.of_validators

private theorem PendingTail.processRandao {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {body : BeaconBlockBody preset fork}
    (holds : PendingTail count epoch state)
    (ok : Consensus.processRandao config checks state body = .ok after) :
    PendingTail count epoch after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq ok
  exact holds.of_validators

private theorem PendingTail.processEth1Data {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {before : fork < .hegota}
    {body : BeaconBlockBody preset fork} (holds : PendingTail count epoch state)
    (ok : Consensus.processEth1Data before state body = .ok after) :
    PendingTail count epoch after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq ok
  exact holds.of_validators (congrArg (fun s => s.validators.data) rest)

/-- Fixed-fork block processing cannot activate a pending suffix. -/
private theorem PendingTail.processBlock {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    {engine : ExecutionEngine preset fork} (holds : PendingTail count epoch state)
    (finite : epoch < FAR_FUTURE_EPOCH) (preGloas : fork < .glamsterdam)
    (ok : Consensus.processBlock config checks engine state block = .ok after) :
    PendingTail count epoch after := by
  unfold Consensus.processBlock at ok
  split at ok
  · unfold processBlockAltair stateBeforeOperations at ok
    simp only [bind_assoc, bind_ok_iff] at ok
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := ok
    have paidHolds : PendingTail count epoch paid := by
      split at paidOk
      · exact False.elim (Nat.not_le_of_lt preGloas ‹_›)
      · cases paidOk; exact holds
    have headedHolds := paidHolds.processBlockHeader headedOk
    have executedHolds : PendingTail count epoch executed := by
      split at executedOk
      · exact headedHolds.processBlockExecution preGloas executedOk
      · cases executedOk; exact headedHolds
    have revealedHolds := executedHolds.processRandao revealedOk
    have votedHolds : PendingTail count epoch voted := by
      split at votedOk
      · exact revealedHolds.processEth1Data votedOk
      · cases votedOk; exact revealedHolds
    exact (votedHolds.processOperations finite preGloas operatedOk).processSyncAggregate synced
  have beforeAltair : fork < .altair := Nat.lt_of_not_le ‹¬ Fork.altair ≤ fork›
  simp only [stateBeforeOperations,
    show ¬ Fork.glamsterdam ≤ fork from Nat.not_le_of_lt preGloas,
    show ¬ Fork.bellatrix ≤ fork from
      Nat.not_le_of_lt (Nat.lt_trans beforeAltair (by decide)),
    show fork < .hegota from Nat.lt_trans beforeAltair (by decide),
    ↓reduceDIte, pure_bind, bind_assoc, bind_ok_iff] at ok
  obtain ⟨_, header, _, randao, _, eth1, operations⟩ := ok
  exact (((holds.processBlockHeader header).processRandao randao).processEth1Data
    eth1).processOperations finite preGloas operations

private theorem PendingTail.advanceSlot {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} (holds : PendingTail count epoch state)
    (current : epoch ≤ getCurrentEpoch state) (finite : epoch < FAR_FUTURE_EPOCH)
    (finalized : after.finalizedCheckpoint.epoch ≤ epoch)
    (ok : Consensus.advanceSlot config checks state = .ok after) :
    PendingTail count epoch after := by
  obtain ⟨next, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  have cachedHolds : PendingTail count epoch cached := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact holds.of_validators
  have epochedHolds : PendingTail count epoch epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact cachedHolds.processEpoch
        (by simpa only [getCurrentEpoch, processSlot_slot cachedOk] using current)
        finite finalized epochedOk
    · cases epochedOk; exact cachedHolds
  exact epochedHolds.of_validators

private theorem PendingTail.advanceSlots {count : Nat} {epoch : Epoch}
    (finite : epoch < FAR_FUTURE_EPOCH) :
    ∀ {n : Nat} {state after : BeaconState preset fork}, PendingTail count epoch state →
      Invariant state → epoch ≤ getCurrentEpoch state → after.finalizedCheckpoint.epoch ≤ epoch →
      Consensus.advanceSlots config checks n state = .ok after → PendingTail count epoch after
  | 0, _, _, holds, _, _, _, ok => by cases ok; exact holds
  | n + 1, state, after, holds, sound, current, finalized, ok => by
    simp only [Consensus.advanceSlots, bind_ok_iff] at ok
    obtain ⟨middle, first, rest⟩ := ok
    have middleSound := (advanceSlot_invariant sound first).1
    have middleFinalized := UInt64.le_trans (advanceSlots_invariant middleSound rest).2 finalized
    have slot := advanceSlot_slot first
    have epochLe : getCurrentEpoch state ≤ getCurrentEpoch middle := by
      rw [UInt64.le_iff_toNat_le, getCurrentEpoch_toNat, getCurrentEpoch_toNat]
      exact Nat.div_le_div_right (by omega)
    exact PendingTail.advanceSlots finite (n := n)
      (holds.advanceSlot current finite middleFinalized first) middleSound
      (UInt64.le_trans current epochLe) finalized rest

private theorem PendingTail.processSlots {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {slot : Slot} (holds : PendingTail count epoch state)
    (sound : Invariant state) (current : epoch ≤ getCurrentEpoch state)
    (finite : epoch < FAR_FUTURE_EPOCH) (finalized : after.finalizedCheckpoint.epoch ≤ epoch)
    (ok : Consensus.processSlots config checks state slot = .ok after) :
    PendingTail count epoch after := by
  simp only [Consensus.processSlots, bind_ok_iff, ensure_ok_iff] at ok
  obtain ⟨_, _, advanced⟩ := ok
  exact PendingTail.advanceSlots finite holds sound current finalized advanced

private theorem PendingTail.stateTransition {count : Nat} {epoch : Epoch}
    {state after : BeaconState preset fork} {signed : SignedBeaconBlock preset fork}
    {engine : ExecutionEngine preset fork} {validateResult : Bool}
    (holds : PendingTail count epoch state) (sound : Invariant state)
    (current : epoch ≤ getCurrentEpoch state) (finite : epoch < FAR_FUTURE_EPOCH)
    (preGloas : fork < .glamsterdam) (finalized : after.finalizedCheckpoint.epoch ≤ epoch)
    (ok : Consensus.stateTransition config checks engine state signed validateResult = .ok after) :
    PendingTail count epoch after := by
  obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok ok
  have bound : advanced.finalizedCheckpoint.epoch ≤ epoch := by
    simpa only [(frame_processBlock blockOk).finalized] using finalized
  exact (holds.processSlots sound current finite bound slotsOk).processBlock finite preGloas blockOk

/-- An activated position predates a transition whose starting epoch bounds finality.

Neither Phase0 nor Electra registry updates can activate these positions while finality is bounded.

The queried activity epoch is unrestricted; only the activation sentinel is needed. -/
private theorem validatorAt_of_stateTransition_finalized_le
    {state after : BeaconState preset fork} {signed : SignedBeaconBlock preset fork}
    {engine : ExecutionEngine preset fork} {validateResult : Bool} {epoch : Epoch}
    (sound : Invariant state) (current : epoch ≤ getCurrentEpoch state)
    (finite : epoch < FAR_FUTURE_EPOCH) (preGloas : fork < .glamsterdam)
    (finalized : after.finalizedCheckpoint.epoch ≤ epoch)
    (ok : Consensus.stateTransition config checks engine state signed validateResult = .ok after)
    {position : Nat} {validator : Validator}
    (found : after.validators.data[position]? = some validator)
    (activated : validator.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    ∃ previous, state.validators.data[position]? = some previous := by
  have emptyTail : PendingTail state.validators.data.size epoch state := by
    intro index value outside read
    have inside := (Array.getElem?_eq_some_iff.mp read).1
    omega
  have pending := emptyTail.stateTransition sound current finite preGloas finalized ok
  have inside : position < state.validators.data.size := by
    by_contra outside
    exact activated (pending position validator (by omega) found).2
  exact ⟨state.validators.data[position], Array.getElem?_eq_getElem inside⟩

private theorem Store.Reachable.pendingTail_anchor
    {store : Store preset fork} (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (preGloas : fork < .glamsterdam)
    {checks : SignatureChecks} {engine : ExecutionEngine preset fork}
    (transitions : ∀ (root : Root) (block : BeaconBlock preset fork)
      (state : BeaconState preset fork), store.blocks[root]? = some block →
      store.blockStates[root]? = some state → block ≠ anchorBlock →
      ∃ parent signed, signed.message = block ∧
        store.blockStates[block.parentRoot]? = some parent ∧
        stateTransition config checks engine parent signed true = .ok state)
    {root : Root} {state : BeaconState preset fork}
    (stored : store.blockStates[root]? = some state)
    {epoch : Epoch} (low : epoch ≤ getCurrentEpoch anchorState)
    (finite : epoch < FAR_FUTURE_EPOCH) (finalized : state.finalizedCheckpoint.epoch ≤ epoch) :
    PendingTail anchorState.validators.data.size epoch state := by
  obtain ⟨block, found⟩ := reachable.known_of_blockState stored
  by_cases same : block = anchorBlock
  · obtain ⟨post, postOk, anchored, _⟩ := reachable.blockStatesFromParents found
    rw [stored, Option.some.injEq] at postOk
    subst post
    rw [anchored same]
    intro index value outside read
    have inside := (Array.getElem?_eq_some_iff.mp read).1
    omega
  obtain ⟨parent, signed, _, parentFound, transitioned⟩ :=
    transitions root block state found stored same
  have parentSound := (reachable.ordered sound).2 parentFound
  have parentFinalized := UInt64.le_trans (stateTransition_invariant parentSound transitioned).2
    finalized
  have pending := reachable.pendingTail_anchor sound preGloas transitions parentFound low
    finite parentFinalized
  have epochLe : getCurrentEpoch anchorState ≤ getCurrentEpoch parent := by
    have bound := reachable.anchorSlot_le_of_blockState parentFound
    simp only [UInt64.le_iff_toNat_le, getCurrentEpoch, computeEpochAtSlot,
      UInt64.toNat_div] at bound ⊢
    exact Nat.div_le_div_right bound
  exact pending.stateTransition parentSound (UInt64.le_trans low epochLe) finite preGloas
    finalized transitioned
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

/-- The registry suffix at a finalized boundary stays pending along the held chain.

The boundary state is reconstructed with the same checks as its descendant transitions.

This retains the lifecycle information that `RunKept` alone does not record. -/
private theorem Store.Reachable.pendingTail_of_ancestor
    {store : Store preset fork} (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (preGloas : fork < .glamsterdam)
    {checks : SignatureChecks} {engine : ExecutionEngine preset fork}
    (transitions : ∀ (root : Root) (block : BeaconBlock preset fork)
      (state : BeaconState preset fork), store.blocks[root]? = some block →
      store.blockStates[root]? = some state → block ≠ anchorBlock →
      ∃ parent signed, signed.message = block ∧
        store.blockStates[block.parentRoot]? = some parent ∧
        stateTransition config checks engine parent signed true = .ok state)
    {root : Root} {state : BeaconState preset fork} {query : Slot}
    (stored : store.blockStates[root]? = some state)
    (later : anchorState.slot ≤ query) (reached : query ≤ state.slot)
    (finite : computeEpochAtSlot preset query < FAR_FUTURE_EPOCH)
    (finalized : state.finalizedCheckpoint.epoch ≤ computeEpochAtSlot preset query)
    (status : PayloadStatus) :
    ∃ ancestorRoot base cut,
      store.blockStates[ancestorRoot]? = some base ∧
      lookaheadState config checks base query = .ok cut ∧ cut.slot = query ∧
      (·.root) <$> store.getAncestor ⟨root, status⟩ query = .ok ancestorRoot ∧
      PendingTail cut.validators.data.size (computeEpochAtSlot preset query) state := by
  obtain ⟨block, found⟩ := reachable.known_of_blockState stored
  have blockLe := Store.Reachable.slot_le_of_blockState
    (UInt64.le_of_eq anchorSlot) reachable found stored
  by_cases atQuery : state.slot = query
  · refine ⟨root, state, state, stored, ?_, atQuery, ?_, ?_⟩
    · simp [lookaheadState, atQuery, pure, Except.pure]
    · rw [Store.getAncestor_of_le found (atQuery ▸ blockLe)]
      rfl
    · intro index value outside read
      have inside := (Array.getElem?_eq_some_iff.mp read).1
      omega
  have high : query < state.slot := UInt64.lt_of_le_of_ne reached (Ne.symm atQuery)
  have notAnchor : block ≠ anchorBlock := by
    intro same
    obtain ⟨post, postOk, anchored, _⟩ := reachable.blockStatesFromParents found
    rw [stored, Option.some.injEq] at postOk
    subst post
    rw [anchored same] at high
    exact (UInt64.not_lt.mpr later) high
  obtain ⟨parent, signed, message, parentFound, transitioned⟩ :=
    transitions root block state found stored notAnchor
  obtain ⟨advanced, slotsOk, advancedSlot, _, blockOk, _⟩ := stateTransition_ok transitioned
  have parentSound := (reachable.ordered sound).2 parentFound
  have parentFinalized := UInt64.le_trans (stateTransition_invariant parentSound transitioned).2
    finalized
  obtain ⟨parentBlock, parentKnown⟩ := reachable.known_of_blockState parentFound
  have parentLe := Store.Reachable.slot_le_of_blockState
    (UInt64.le_of_eq anchorSlot) reachable parentKnown parentFound
  have stateSlot := (reachable.blockState_header found stored notAnchor).1
  have parentLt : parentBlock.slot < block.slot := UInt64.lt_of_le_of_lt parentLe
    (message ▸ (stateTransition_slot transitioned).1)
  have walk := Store.getAncestor_step (node := ⟨root, status⟩) found
    (UInt64.not_le.mpr (stateSlot ▸ high)) parentKnown parentLt
  by_cases parentReached : query ≤ parent.slot
  · obtain ⟨ancestorRoot, base, cut, held, made, atSlot, walked, pending⟩ :=
      reachable.pendingTail_of_ancestor sound anchorSlot preGloas transitions parentFound
        later parentReached finite parentFinalized (parentPayloadStatus block parentBlock)
    refine ⟨ancestorRoot, base, cut, held, made, atSlot, ?_, ?_⟩
    · rw [walk]; exact walked
    · exact pending.stateTransition parentSound
        (by
          change computeEpochAtSlot preset query ≤ computeEpochAtSlot preset parent.slot
          simp only [UInt64.le_iff_toNat_le, computeEpochAtSlot, UInt64.toNat_div]
          exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp parentReached))
        finite preGloas finalized transitioned
  · have low := UInt64.not_le.mp parentReached
    have upper : query < signed.message.slot := by rwa [← (stateTransition_slot transitioned).2]
    obtain ⟨cut, before, afterOk⟩ := processSlots_split low upper slotsOk
    have atSlot := (processSlots_slot before).2
    have cutSound := (processSlots_invariant parentSound before).1
    have emptyTail :
        PendingTail cut.validators.data.size (computeEpochAtSlot preset query) cut := by
      intro index value outside read
      have inside := (Array.getElem?_eq_some_iff.mp read).1
      omega
    have advancedFinalized :
        advanced.finalizedCheckpoint.epoch ≤ computeEpochAtSlot preset query := by
      simpa only [(frame_processBlock blockOk).finalized] using finalized
    refine ⟨block.parentRoot, parent, cut, parentFound, ?_, atSlot, ?_, ?_⟩
    · simp [lookaheadState, low, before, Except.mapError]
    · rw [walk, Store.getAncestor_of_le parentKnown
        (UInt64.le_trans parentLe (UInt64.le_of_lt low))]
      rfl
    · exact (emptyTail.processSlots cutSound (by simp [getCurrentEpoch, atSlot]) finite
        advancedFinalized afterOk).processBlock finite preGloas blockOk
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

/-- A finite activation in a held state already has a position at a finality boundary.

The boundary is after the anchor and no later than the held state.

Its epoch bounds the held state's finalized epoch.

The result identifies the boundary's ancestor root without a hash injectivity assumption. -/
theorem Store.Reachable.validatorAt_ancestor_boundary
    {store : Store preset fork} (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (preGloas : fork < .glamsterdam)
    {checks : SignatureChecks} {engine : ExecutionEngine preset fork}
    (transitions : ∀ (root : Root) (block : BeaconBlock preset fork)
      (state : BeaconState preset fork), store.blocks[root]? = some block →
      store.blockStates[root]? = some state → block ≠ anchorBlock →
      ∃ parent signed, signed.message = block ∧
        store.blockStates[block.parentRoot]? = some parent ∧
        stateTransition config checks engine parent signed true = .ok state)
    {root : Root} {state : BeaconState preset fork} {query : Slot}
    (stored : store.blockStates[root]? = some state)
    (later : anchorState.slot ≤ query) (reached : query ≤ state.slot)
    (finite : computeEpochAtSlot preset query < FAR_FUTURE_EPOCH)
    (finalized : state.finalizedCheckpoint.epoch ≤ computeEpochAtSlot preset query)
    (status : PayloadStatus) {position : Nat} {validator : Validator}
    (found : state.validators.data[position]? = some validator)
    (activated : validator.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    ∃ ancestorRoot base cut,
      store.blockStates[ancestorRoot]? = some base ∧
      lookaheadState config checks base query = .ok cut ∧ cut.slot = query ∧
      (·.root) <$> store.getAncestor ⟨root, status⟩ query = .ok ancestorRoot ∧
      ∃ previous, cut.validators.data[position]? = some previous := by
  obtain ⟨ancestorRoot, base, cut, held, made, atSlot, walked, pending⟩ :=
    reachable.pendingTail_of_ancestor sound anchorSlot preGloas transitions stored later reached
      finite finalized status
  refine ⟨ancestorRoot, base, cut, held, made, atSlot, walked, ?_⟩
  have inside : position < cut.validators.data.size := by
    by_contra outside
    exact activated (pending position validator (by omega) found).2
  exact ⟨cut.validators.data[position], Array.getElem?_eq_getElem inside⟩

private theorem lookahead_registry_le_of_le
    {base first second : BeaconState preset fork} {low high : Slot}
    (one : lookaheadState config checks base low = .ok first)
    (two : lookaheadState config checks base high = .ok second) (le : low ≤ high) :
    first.validators.data.size ≤ second.validators.data.size := by
  by_cases same : low = high
  · rw [same, two] at one
    cases one
    exact Nat.le_refl _
  have lt := UInt64.lt_of_le_of_ne le same
  unfold lookaheadState at one two
  split at one
  · rename_i advanced
    have highAfter := UInt64.lt_trans advanced lt
    simp only [highAfter, ↓reduceIte] at two
    have slotsOne := mapError_ok_iff.mp one
    have slotsTwo := mapError_ok_iff.mp two
    obtain ⟨middle, before, afterOk⟩ := processSlots_split advanced lt slotsTwo
    rw [slotsOne, Except.ok.injEq] at before
    subst middle
    exact (runKept_processSlots afterOk).grows
  · cases one
    split at two
    · exact (runKept_processSlots (mapError_ok_iff.mp two)).grows
    · cases two
      exact Nat.le_refl _

/-- A successful ancestor walk reconstructs a boundary state whose registry grows into the tip. -/
private theorem Store.Reachable.registry_at_ancestor
    {store : Store preset fork} (reachable : Store.Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    {checks : SignatureChecks} {engine : ExecutionEngine preset fork}
    (transitions : ∀ (root : Root) (block : BeaconBlock preset fork)
      (state : BeaconState preset fork), store.blocks[root]? = some block →
      store.blockStates[root]? = some state → block ≠ anchorBlock →
      ∃ parent signed, signed.message = block ∧
        store.blockStates[block.parentRoot]? = some parent ∧
        stateTransition config checks engine parent signed true = .ok state)
    {root : Root} {state : BeaconState preset fork} {query : Slot}
    (stored : store.blockStates[root]? = some state)
    (later : anchorState.slot ≤ query) (reached : query ≤ state.slot)
    (status : PayloadStatus) :
    ∃ ancestorRoot base cut,
      store.blockStates[ancestorRoot]? = some base ∧
      lookaheadState config checks base query = .ok cut ∧ cut.slot = query ∧
      (·.root) <$> store.getAncestor ⟨root, status⟩ query = .ok ancestorRoot ∧
      cut.validators.data.size ≤ state.validators.data.size := by
  obtain ⟨block, found⟩ := reachable.known_of_blockState stored
  have blockLe := Store.Reachable.slot_le_of_blockState
    (UInt64.le_of_eq anchorSlot) reachable found stored
  by_cases atQuery : state.slot = query
  · refine ⟨root, state, state, stored, ?_, atQuery, ?_, Nat.le_refl _⟩
    · simp [lookaheadState, atQuery, pure, Except.pure]
    · rw [Store.getAncestor_of_le found (atQuery ▸ blockLe)]
      rfl
  have high : query < state.slot := UInt64.lt_of_le_of_ne reached (Ne.symm atQuery)
  have notAnchor : block ≠ anchorBlock := by
    intro same
    obtain ⟨post, postOk, anchored, _⟩ := reachable.blockStatesFromParents found
    rw [stored, Option.some.injEq] at postOk
    subst post
    rw [anchored same] at high
    exact (UInt64.not_lt.mpr later) high
  obtain ⟨parent, signed, message, parentFound, transitioned⟩ :=
    transitions root block state found stored notAnchor
  obtain ⟨advanced, slotsOk, advancedSlot, _, blockOk, _⟩ := stateTransition_ok transitioned
  obtain ⟨parentBlock, parentKnown⟩ := reachable.known_of_blockState parentFound
  have parentLe := Store.Reachable.slot_le_of_blockState
    (UInt64.le_of_eq anchorSlot) reachable parentKnown parentFound
  have stateSlot := (reachable.blockState_header found stored notAnchor).1
  have parentLt : parentBlock.slot < block.slot := UInt64.lt_of_le_of_lt parentLe
    (message ▸ (stateTransition_slot transitioned).1)
  have walk := Store.getAncestor_step (node := ⟨root, status⟩) found
    (UInt64.not_le.mpr (stateSlot ▸ high)) parentKnown parentLt
  by_cases parentReached : query ≤ parent.slot
  · obtain ⟨ancestorRoot, base, cut, held, made, atSlot, walked, grows⟩ :=
      reachable.registry_at_ancestor anchorSlot transitions parentFound later parentReached
        (parentPayloadStatus block parentBlock)
    refine ⟨ancestorRoot, base, cut, held, made, atSlot, ?_,
      Nat.le_trans grows (runKept_stateTransition transitioned).grows⟩
    rw [walk]; exact walked
  · have low := UInt64.not_le.mp parentReached
    have upper : query < signed.message.slot := by rwa [← (stateTransition_slot transitioned).2]
    obtain ⟨cut, before, afterOk⟩ := processSlots_split low upper slotsOk
    refine ⟨block.parentRoot, parent, cut, parentFound, ?_, (processSlots_slot before).2, ?_,
      Nat.le_trans (runKept_processSlots afterOk).grows (runKept_processBlock blockOk).grows⟩
    · simp [lookaheadState, low, before, Except.mapError]
    · rw [walk, Store.getAncestor_of_le parentKnown
        (UInt64.le_trans parentLe (UInt64.le_of_lt low))]
      rfl
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

private theorem Store.Reachable.registry_at_cached_ancestor
    {store : Store preset fork} (reachable : Store.Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    {checks : SignatureChecks} {engine : ExecutionEngine preset fork}
    (transitions : ∀ (root : Root) (block : BeaconBlock preset fork)
      (state : BeaconState preset fork), store.blocks[root]? = some block →
      store.blockStates[root]? = some state → block ≠ anchorBlock →
      ∃ parent signed, signed.message = block ∧
        store.blockStates[block.parentRoot]? = some parent ∧
        stateTransition config checks engine parent signed true = .ok state)
    {root : Root} {state cached : BeaconState preset fork} {query target : Slot}
    (stored : store.blockStates[root]? = some state)
    (made : lookaheadState config checks state target = .ok cached)
    (later : anchorState.slot ≤ query) (reached : query ≤ target)
    (status : PayloadStatus) :
    ∃ ancestorRoot base cut,
      store.blockStates[ancestorRoot]? = some base ∧
      lookaheadState config checks base query = .ok cut ∧
      (·.root) <$> store.getAncestor ⟨root, status⟩ query = .ok ancestorRoot ∧
      cut.validators.data.size ≤ cached.validators.data.size := by
  by_cases before : query ≤ state.slot
  · obtain ⟨ancestorRoot, base, cut, held, advanced, _, walked, grows⟩ :=
      reachable.registry_at_ancestor anchorSlot transitions stored later before status
    refine ⟨ancestorRoot, base, cut, held, advanced, walked, Nat.le_trans grows ?_⟩
    unfold lookaheadState at made
    split at made
    · exact (runKept_processSlots (mapError_ok_iff.mp made)).grows
    · cases made
      exact Nat.le_refl _
  · have low := UInt64.not_le.mp before
    have high := UInt64.lt_of_lt_of_le low reached
    have slotsOk := made
    simp only [lookaheadState, high, ↓reduceIte] at slotsOk
    obtain ⟨cut, advanced⟩ : ∃ cut, lookaheadState config checks state query = .ok cut := by
      by_cases same : query = target
      · exact ⟨cached, same ▸ made⟩
      · obtain ⟨cut, first, _⟩ := processSlots_split low
          (UInt64.lt_of_le_of_ne reached same) (mapError_ok_iff.mp slotsOk)
        exact ⟨cut, by simp [lookaheadState, low, first, Except.mapError]⟩
    obtain ⟨block, found⟩ := reachable.known_of_blockState stored
    refine ⟨root, state, cut, stored, advanced, ?_,
      lookahead_registry_le_of_le advanced made reached⟩
    rw [Store.getAncestor_of_le found (UInt64.le_trans
      (Store.Reachable.slot_le_of_blockState (UInt64.le_of_eq anchorSlot) reachable found stored)
      (UInt64.le_of_lt low))]
    rfl

private theorem Store.Reachable.validatorAt_of_common_boundary
    {store : Store preset fork} (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (preGloas : fork < .glamsterdam)
    {checks : SignatureChecks} {engine : ExecutionEngine preset fork}
    (transitions : ∀ (root : Root) (block : BeaconBlock preset fork)
      (state : BeaconState preset fork), store.blocks[root]? = some block →
      store.blockStates[root]? = some state → block ≠ anchorBlock →
      ∃ parent signed, signed.message = block ∧
        store.blockStates[block.parentRoot]? = some parent ∧
        stateTransition config checks engine parent signed true = .ok state)
    {root targetRoot common : Root} {state base cached : BeaconState preset fork}
    {query target : Slot}
    (stored : store.blockStates[root]? = some state)
    (baseStored : store.blockStates[targetRoot]? = some base)
    (made : lookaheadState config checks base target = .ok cached)
    (later : anchorState.slot ≤ query) (reached : query ≤ state.slot)
    (targetLater : query ≤ target)
    (finite : computeEpochAtSlot preset query < FAR_FUTURE_EPOCH)
    (finalized : state.finalizedCheckpoint.epoch ≤ computeEpochAtSlot preset query)
    (sourceWalk : (·.root) <$> store.getAncestor ⟨root, .pending⟩ query = .ok common)
    (targetWalk : (·.root) <$> store.getAncestor ⟨targetRoot, .pending⟩ query = .ok common)
    {position : Nat} {validator : Validator}
    (found : state.validators.data[position]? = some validator)
    (activated : validator.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    ∃ previous, cached.validators.data[position]? = some previous := by
  obtain ⟨sourceRoot, sourceBase, sourceCut, held, advanced, _, walked, previous, present⟩ :=
    reachable.validatorAt_ancestor_boundary sound anchorSlot preGloas transitions stored later
      reached finite finalized .pending found activated
  obtain ⟨destRoot, destBase, destCut, destHeld, destAdvanced, destWalked, grows⟩ :=
    reachable.registry_at_cached_ancestor anchorSlot transitions baseStored made later
      targetLater .pending
  rw [sourceWalk, Except.ok.injEq] at walked
  rw [targetWalk, Except.ok.injEq] at destWalked
  subst sourceRoot
  subst destRoot
  rw [held, Option.some.injEq] at destHeld
  subst destBase
  rw [advanced, Except.ok.injEq] at destAdvanced
  subst destCut
  have bound := Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp present).1 grows
  exact ⟨cached.validators.data[position], Array.getElem?_eq_getElem bound⟩

private theorem Store.Reachable.validatorAt_of_common_boundary_total
    {store : Store preset fork} (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (preGloas : fork < .glamsterdam)
    {checks : SignatureChecks} {engine : ExecutionEngine preset fork}
    (transitions : ∀ (root : Root) (block : BeaconBlock preset fork)
      (state : BeaconState preset fork), store.blocks[root]? = some block →
      store.blockStates[root]? = some state → block ≠ anchorBlock →
      ∃ parent signed, signed.message = block ∧
        store.blockStates[block.parentRoot]? = some parent ∧
        stateTransition config checks engine parent signed true = .ok state)
    {root targetRoot common : Root} {state base cached : BeaconState preset fork}
    {query target : Slot}
    (stored : store.blockStates[root]? = some state)
    (baseStored : store.blockStates[targetRoot]? = some base)
    (made : lookaheadState config checks base target = .ok cached)
    (later : anchorState.slot ≤ query) (targetLater : query ≤ target)
    (finalized : state.finalizedCheckpoint.epoch ≤ computeEpochAtSlot preset query)
    (sourceWalk : (·.root) <$> store.getAncestor ⟨root, .pending⟩ query = .ok common)
    (targetWalk : (·.root) <$> store.getAncestor ⟨targetRoot, .pending⟩ query = .ok common)
    {position : Nat} {validator : Validator}
    (found : state.validators.data[position]? = some validator)
    (activated : validator.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    ∃ previous, cached.validators.data[position]? = some previous := by
  by_cases high : query < state.slot
  · have finite : computeEpochAtSlot preset query < FAR_FUTURE_EPOCH := by
      have le : (computeEpochAtSlot preset query).toNat ≤ query.toNat := by
        simp only [computeEpochAtSlot, UInt64.toNat_div]
        exact Nat.div_le_self _ _
      have upper := state.slot.toNat_lt
      have less := UInt64.lt_iff_toNat_lt.mp high
      change (computeEpochAtSlot preset query).toNat < 18446744073709551615
      omega
    exact reachable.validatorAt_of_common_boundary sound anchorSlot preGloas transitions stored
      baseStored made later (UInt64.le_of_lt high) targetLater finite finalized sourceWalk
      targetWalk found activated
  · obtain ⟨block, heldBlock⟩ := reachable.known_of_blockState stored
    rw [Store.getAncestor_of_le heldBlock (UInt64.le_trans
      (Store.Reachable.slot_le_of_blockState
        (UInt64.le_of_eq anchorSlot) reachable heldBlock stored)
      (UInt64.not_lt.mp high))] at sourceWalk
    have rootEq : root = common := Except.ok.inj sourceWalk
    obtain ⟨destRoot, destBase, destCut, destHeld, advanced, walked, grows⟩ :=
      reachable.registry_at_cached_ancestor anchorSlot transitions baseStored made later
        targetLater .pending
    rw [targetWalk, Except.ok.injEq] at walked
    subst destRoot
    rw [← rootEq, stored, Option.some.injEq] at destHeld
    subst destBase
    have growsBase : state.validators.data.size ≤ destCut.validators.data.size := by
      unfold lookaheadState at advanced
      split at advanced
      · exact (runKept_processSlots (mapError_ok_iff.mp advanced)).grows
      · cases advanced
        exact Nat.le_refl _
    have bound := Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp found).1
      (Nat.le_trans growsBase grows)
    exact ⟨cached.validators.data[position], Array.getElem?_eq_getElem bound⟩

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
  · obtain ⟨parent, checks, engine, signed, -, -, parentFound, transitioned⟩ := produced same
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
    exact UInt64.le_trans (finalized_le_updateCheckpoints boosted _ _) later.2.epoch_le
  · exact UInt64.le_trans (holds _ _ found) forward.epoch_le

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
      exact UInt64.le_trans (ih r s (states ▸ found)) le.2.epoch_le
    | attestation _ handled ih =>
      obtain ⟨le, -, states, -⟩ := onAttestation_frame handled
      intro r s found
      exact UInt64.le_trans (ih r s (states ▸ found)) le.2.epoch_le
    | attesterSlashing _ handled ih =>
      obtain ⟨le, -, states, -⟩ := onAttesterSlashing_frame handled
      intro r s found
      exact UInt64.le_trans (ih r s (states ▸ found)) le.2.epoch_le
    | payloadAttestation _ handled ih =>
      obtain ⟨le, -, states⟩ := (onPayloadAttestationMessage_onlyPtcVotes handled).frame
      intro r s found
      exact UInt64.le_trans (ih r s (states ▸ found)) le.2.epoch_le
    | envelope _ handled ih =>
      obtain ⟨le, -, states⟩ := onExecutionPayloadEnvelope_frame handled
      intro r s found
      exact UInt64.le_trans (ih r s (states ▸ found)) le.2.epoch_le
    | inclusionList _ handled ih =>
      obtain ⟨le, -, states⟩ := onInclusionList_frame handled
      intro r s found
      exact UInt64.le_trans (ih r s (states ▸ found)) le.2.epoch_le
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

/-- An active head position already exists in the receiver's justified balance source.

Finalized eligibility prevents activation of positions created after the finalized boundary.

This holds even at a future queried epoch. -/
theorem Execution.validatorAt_justified_of_head_active
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor)
    (preGloas : fork < .glamsterdam)
    (slots : 0 < config.SLOT_DURATION_MS)
    {horizon : Epoch} {last : ℕ} (chain : FinalizedPrefix e horizon last)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ last)
    {current : Epoch}
    (currentOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok current)
    (inHorizon : current ≤ horizon)
    (nonzero : ∀ (r : Root) (b : BeaconBlock preset fork),
      ((e.world k).state w).blocks[r]? = some b →
      b.stateRoot ≠ Vector.replicate 32 0)
    {head : ForkChoiceNode} {headState state : BeaconState preset fork}
    (headOk : ((e.world k).state w).getHead config = .ok head)
    (headStateOk : ((e.world k).state w).blockState head.root = .ok headState)
    (stateOk : ((e.world k).state w).checkpointState
      ((e.world k).state w).justifiedCheckpoint = .ok state)
    {d : Epoch} {v : ValidatorIndex}
    (active : isActiveAt headState d v.toNat = true) :
    ∃ validator, state.validators.data[v.toNat]? = some validator := by
  have _ := nonzero
  have reached := e.reachable
    (fun u hu => (start u hu).symm ▸ Store.Reachable.anchor anchored) k w honest
  have forward := e.forwardReachable
    (fun u hu => (start u hu).symm ▸ Store.ForwardReachable.anchor anchored) k w honest
  have stored := Store.blockState_ok_iff.mp headStateOk
  have transitions := fun root block post found held other =>
    e.exists_transition_of_nonanchor_block anchored honest (start w honest)
      (k := k) (root := root) (block := block) (state := post) found held other
  obtain ⟨validator, found, activated⟩ := activationEpoch_ne_farFuture_of_isActiveAt active
  obtain ⟨base, target, baseStored, targetOk, made⟩ :=
    e.checkpointStates_fixedChecks anchored (start w honest)
      (Store.checkpointState_ok_iff.mp stateOk)
  -- The fallback head is already the block used to compute the cached balance source.
  by_cases same : head.root = ((e.world k).state w).justifiedCheckpoint.root
  · rw [same, baseStored, Option.some.injEq] at stored
    subst base
    have grows : headState.validators.data.size ≤ state.validators.data.size := by
      unfold lookaheadState at made
      split at made
      · exact (runKept_processSlots (mapError_ok_iff.mp made)).grows
      · cases made
        exact Nat.le_refl _
    have bound := Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp found).1 grows
    exact ⟨state.validators.data[v.toNat], Array.getElem?_eq_getElem bound⟩
  have someViable : ((e.world k).state w).getFilteredNodeTree config ≠ .ok [] := by
    intro empty
    have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
    simp only [Store.getHead, empty, later, false_and, ↓reduceIte, bind, Except.bind] at headOk
    rcases Store.getHeadFrom_mem headOk with equal | mem
    · exact same (congrArg ForkChoiceNode.root equal)
    · exact List.not_mem_nil mem
  have finalLe := reached.blockState_finalized_le sound stored
  rcases Store.getHead_finalized headOk someViable with genesis | headWalk
  · -- With genesis finality no post-anchor append can have finite activation.
    have pending := reached.pendingTail_anchor sound preGloas transitions stored
      (epoch := 0) UInt64.zero_le (by decide) (by simpa [genesis, GENESIS_EPOCH] using finalLe)
    apply e.validatorAt_checkpoint_of_anchor anchored start honest stateOk
    by_contra outside
    exact activated (pending v.toNat validator (by omega) found).2
  · have justifiedWalk := e.getCheckpointBlock_justified_of_finalized_before anchored sound slots
      (UInt64.le_of_eq anchorSlot) start chain honest (Nat.le_refl k) bounded currentOk inHorizon
    simp only [Store.getCheckpointBlock, bind_ok_iff] at headWalk
    obtain ⟨query, queryOk, headWalk⟩ := headWalk
    have queryOk := mapError_ok_iff.mp queryOk
    have lower := e.anchorSlot_le_finalized_boundary anchored anchorSlot anchorBoundary
      (start w honest) queryOk
    have epochBound := (forward.justified_epoch_le_current sound slots
      (UInt64.le_of_eq anchorSlot) currentOk).1
    have finalBound := reached.finalized_le_justified sound
    by_cases zero : preset.SLOTS_PER_EPOCH = 0
    ·
      have currentZero : current = 0 := by
        simp only [Store.getCurrentStoreEpoch, bind_ok_iff] at currentOk
        obtain ⟨slot, _, equal⟩ := currentOk
        simpa [computeEpochAtSlot, zero, pure, Except.pure] using equal.symm
      have finalZero : ((e.world k).state w).finalizedCheckpoint.epoch = 0 := by
        exact UInt64.le_zero_iff.mp (currentZero ▸ UInt64.le_trans finalBound epochBound)
      have pending := reached.pendingTail_anchor sound preGloas transitions stored
        (epoch := 0) UInt64.zero_le (by decide) (by simpa [finalZero] using finalLe)
      have inside : v.toNat < anchorState.validators.data.size := by
        by_contra outside
        exact activated (pending v.toNat validator (by omega) found).2
      exact e.validatorAt_checkpoint_of_anchor anchored start honest stateOk inside
    have positive : 0 < preset.SLOTS_PER_EPOCH := UInt64.lt_of_le_of_ne
      UInt64.zero_le (Ne.symm zero)
    have queryEpoch := computeEpochAtSlot_computeStartSlotAtEpoch positive queryOk
    have targetLater : query ≤ target := by
      rw [UInt64.le_iff_toNat_le, (computeStartSlotAtEpoch_ok_iff.mp queryOk).2,
        (computeStartSlotAtEpoch_ok_iff.mp targetOk).2]
      exact Nat.mul_le_mul_right _ (UInt64.le_iff_toNat_le.mp finalBound)
    have targetWalk : (·.root) <$> ((e.world k).state w).getAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ query =
        .ok ((e.world k).state w).finalizedCheckpoint.root := by
      simpa [Store.getCheckpointBlock, queryOk, Except.mapError, bind, Except.bind,
        Functor.map, Except.map, pure, Except.pure] using justifiedWalk
    have sourceWalk : (·.root) <$> ((e.world k).state w).getAncestor
        ⟨head.root, .pending⟩ query = .ok ((e.world k).state w).finalizedCheckpoint.root := by
      obtain ⟨ancestor, walk, result⟩ := headWalk
      simpa [walk, Functor.map, Except.map, pure, Except.pure] using result
    exact reached.validatorAt_of_common_boundary_total sound anchorSlot preGloas transitions
      stored baseStored made (anchorSlot ▸ lower) targetLater (queryEpoch ▸ finalLe)
      sourceWalk targetWalk found activated

end Models.Network

end EthLib.Consensus
