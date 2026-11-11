module

public import EthLib.Consensus.Proofs.Transition.RegistryIdentity
public import EthLib.Consensus.Proofs.Transition.Trace

/-!
# Proofs: the lifecycle of a validator, at every fork

A validator keeps its index in the registry for the life of the chain.

An assigned activation or exit epoch stays exactly the same.

The registry also never shrinks.

Each chain step preserves assigned epochs, and composition gives the same result for a run.

A successful admission appends a validator with no activation or exit epoch assigned.

This admission fact describes the append operation, not later operations in the same chain step.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-- A position below `2^64` is its own index of 64 bits. -/
private theorem toNat_toUInt64_of_lt_pow {position : Nat} (small : position < 2 ^ 64) :
    position.toUInt64.toNat = position := by
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small]

/-- One validator, later in its life.

An activation or exit epoch that was assigned stays exactly the same. -/
structure ValidatorLifecycle (validator later : Validator) : Prop where
  activationEpoch : validator.activationEpoch ≠ FAR_FUTURE_EPOCH →
    later.activationEpoch = validator.activationEpoch
  exitEpoch : validator.exitEpoch ≠ FAR_FUTURE_EPOCH → later.exitEpoch = validator.exitEpoch

theorem ValidatorLifecycle.refl (validator : Validator) : ValidatorLifecycle validator validator :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem ValidatorLifecycle.trans {first second third : Validator}
    (one : ValidatorLifecycle first second) (two : ValidatorLifecycle second third) :
    ValidatorLifecycle first third where
  activationEpoch set := by
    have same := one.activationEpoch set
    exact (two.activationEpoch (same ▸ set)).trans same
  exitEpoch set := by
    have same := one.exitEpoch set
    exact (two.exitEpoch (same ▸ set)).trans same

/-- The registry of a later state, which may be of a later fork.

It is at least as long.

Each existing validator remains at its index, with its assigned epochs unchanged. -/
structure RegistryLifecycle {fork' : Base.Fork} (state : BeaconState preset fork)
    (after : BeaconState preset fork') : Prop where
  size_le : state.validators.data.size ≤ after.validators.data.size
  validators : ∀ (index : Nat) (validator : Validator),
    state.validators.data[index]? = some validator →
      ∃ later, after.validators.data[index]? = some later ∧ ValidatorLifecycle validator later

namespace RegistryLifecycle

theorem refl (state : BeaconState preset fork) : RegistryLifecycle state state :=
  ⟨Nat.le_refl _, fun _ validator found => ⟨validator, found, .refl validator⟩⟩

theorem trans {fork' fork'' : Base.Fork} {first : BeaconState preset fork}
    {second : BeaconState preset fork'} {third : BeaconState preset fork''}
    (one : RegistryLifecycle first second) (two : RegistryLifecycle second third) :
    RegistryLifecycle first third where
  size_le := Nat.le_trans one.size_le two.size_le
  validators index validator found := by
    obtain ⟨middle, middleFound, oneStep⟩ := one.validators index validator found
    obtain ⟨later, laterFound, twoStep⟩ := two.validators index middle middleFound
    exact ⟨later, laterFound, oneStep.trans twoStep⟩

/-- A state with the same validators, of any fork. -/
theorem of_data {fork' : Base.Fork} {after : BeaconState preset fork'}
    (same : after.validators.data = state.validators.data) : RegistryLifecycle state after :=
  ⟨Nat.le_of_eq (by rw [same]), fun index validator found =>
    ⟨validator, by rw [same]; exact found, .refl _⟩⟩

/-- Appending a validator does not change any existing entry. -/
theorem append {validator : Validator}
    (added : after.validators.data = state.validators.data.push validator) :
    RegistryLifecycle state after where
  size_le := by simp [added]
  validators index old found := by
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    refine ⟨old, ?_, .refl _⟩
    simpa [added, Array.getElem?_push, Nat.ne_of_lt inside] using found

/-- A fold whose every step keeps the lifecycle keeps it. -/
theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x s', step s x = .ok s' → RegistryLifecycle s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : RegistryLifecycle state after :=
  foldlM_ok_invariant (RegistryLifecycle state)
    (fun _ _ _ before ok => before.trans (kept _ _ _ ok)) (.refl state) computed

/-- Replacing a validator by itself later in its life. -/
theorem putValidator {index : Nat} {validator : Validator}
    (inside : index < state.validators.data.size)
    (step : ValidatorLifecycle state.validators.data[index] validator) :
    RegistryLifecycle state (state.putValidator index inside validator) where
  size_le := by simp [BeaconState.putValidator]
  validators other old found := by
    simp only [BeaconState.putValidator, RootedForkList.data_set, Array.getElem?_set]
    split
    · rename_i same
      subst same
      have equal : state.validators.data[index] = old := by
        rw [Array.getElem?_eq_getElem inside] at found
        exact Option.some.inj found
      exact ⟨validator, by simp, equal ▸ step⟩
    · exact ⟨old, found, .refl _⟩

theorem setValidator {index : ValidatorIndex} {old validator : Validator}
    (found : getValidator state index = .ok old)
    (set : state.setValidator index validator = .ok after)
    (step : ValidatorLifecycle old validator) : RegistryLifecycle state after := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  refine putValidator inside ?_
  have read : state.validators.data[index.toNat]? = some old := by
    unfold getValidator at found
    split at found
    · rename_i read
      cases found
      exact read
    · cases found
  rw [Array.getElem?_eq_getElem inside] at read
  exact Option.some.inj read ▸ step

/-- Replacing a validator at its natural-number position. -/
theorem setValidatorAt {position : Nat} {old validator : Validator}
    (found : getValidatorAt state position = .ok old)
    (set : state.setValidatorAt position validator = .ok after)
    (step : ValidatorLifecycle old validator) :
    RegistryLifecycle state after := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldEq : state.validators.data[position] = old := by
    simpa [getValidatorAt, inside] using found
  exact putValidator inside (oldEq ▸ step)

theorem increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : RegistryLifecycle state after :=
  of_data (by rw [increaseBalance_validators computed])

theorem decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : RegistryLifecycle state after :=
  of_data (by rw [decreaseBalance_validators computed])

end RegistryLifecycle

/-! ## Mutators -/

theorem registryLifecycle_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    RegistryLifecycle state after := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨far, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact .refl _
  · have same := (exitQueue_validators queue).1
    -- Only a validator with no exit epoch gets one.
    exact (RegistryLifecycle.of_data (by rw [same])).trans <|
      .setValidator ((getValidator_of_validators_eq same index).trans found) set
        ⟨fun _ => rfl, fun set => absurd far set⟩

theorem registryLifecycle_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    RegistryLifecycle state after := by
  simp only [slashValidator, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, validator, found, delay, _, marked, markedOk, _, _, _, _, _, _,
    lowered, loweredOk,
    proposer, _, _, _, raised, raisedOk, last, lastOk, done⟩ := computed
  -- Marking the validator slashed does not change its activation or exit epoch.
  exact (registryLifecycle_initiateValidatorExit exitedOk).trans <|
    ((RegistryLifecycle.setValidator found markedOk
      ⟨fun _ => rfl, fun _ => rfl⟩).trans (by exact .of_data rfl)).trans <|
    (RegistryLifecycle.decreaseBalance loweredOk).trans <|
    (RegistryLifecycle.increaseBalance raisedOk).trans <|
    (RegistryLifecycle.increaseBalance lastOk).trans
      (.of_data (by rw [(slashValidator_last done).1]))

/-! ## The steps of a block -/

theorem registryLifecycle_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : RegistryLifecycle state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact .of_data rfl

theorem registryLifecycle_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) :
    RegistryLifecycle state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact .of_data rfl

theorem registryLifecycle_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : RegistryLifecycle state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  exact .of_data (by rw [← rest])

theorem registryLifecycle_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    RegistryLifecycle state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact registryLifecycle_slashValidator slashed

theorem registryLifecycle_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    RegistryLifecycle step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact registryLifecycle_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem registryLifecycle_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    RegistryLifecycle state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step => RegistryLifecycle state step.1)
    (fun _ _ _ before ok => before.trans (registryLifecycle_slashIfSlashable ok))
    (show RegistryLifecycle state (state, false).1 from .refl state) folded

theorem registryLifecycle_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    RegistryLifecycle state after := by
  unfold processAttestation at computed
  split at computed
  · unfold processAttestationAltair at computed
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := computed
    have last : RegistryLifecycle raised after := by
      split at final
      · rw [recordPaymentWeight_eq final]
        exact .of_data rfl
      · cases final
        exact .refl _
    have flagged : ∀ (current : Bool) (participation : EpochParticipation preset fork),
        RegistryLifecycle state (setEpochParticipation state current participation) := by
      intro current participation
      unfold setEpochParticipation
      split <;> exact .of_data rfl
    exact (flagged _ _).trans ((RegistryLifecycle.increaseBalance raisedOk).trans last)
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept <;>
  · obtain ⟨_, rest⟩ := kept
    exact .of_data (by rw [← rest])

/-- Successful admission appends without replacing any existing validator. -/
theorem registryLifecycle_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    RegistryLifecycle state after :=
  .append (addValidatorToRegistry_validators_eq_push computed)

/-- The appended validator has no assigned activation or exit epoch at admission. -/
theorem addValidatorToRegistry_admission {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    ∃ validator, after.validators.data[state.validators.data.size]? = some validator ∧
      validator.activationEpoch = FAR_FUTURE_EPOCH ∧
      validator.exitEpoch = FAR_FUTURE_EPOCH ∧ RegistryLifecycle state after := by
  refine ⟨getValidatorFromDeposit preset fork pubkey withdrawalCredentials amount,
    ?_, rfl, rfl, registryLifecycle_addValidatorToRegistry computed⟩
  simp [addValidatorToRegistry_validators_eq_push computed]

theorem registryLifecycle_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    RegistryLifecycle state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact registryLifecycle_addValidatorToRegistry computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ .refl _
  · simp only [liftAccessor_ok, bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    exact .increaseBalance computed

theorem registryLifecycle_applyDeposit {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    RegistryLifecycle state after := by
  unfold applyDeposit at computed
  split at computed
  · unfold applyDepositElectra at computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, computed⟩ := computed
      split at computed
      · simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨_, added, pushed⟩ := computed
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
        exact (registryLifecycle_addValidatorToRegistry added).trans (.of_data rfl)
      · cases computed
        exact .refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
      exact .of_data rfl
  · exact registryLifecycle_applyPendingDeposit computed

theorem registryLifecycle_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    RegistryLifecycle state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact (RegistryLifecycle.of_data (state := state)
    (after := { state with eth1DepositIndex := fun _ => next }) rfl).trans
    (registryLifecycle_applyDeposit applied)

theorem registryLifecycle_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    RegistryLifecycle state after := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact registryLifecycle_initiateValidatorExit exited

/-! ## Requests of the execution layer -/

theorem registryLifecycle_processDepositRequest {electra : .pectra ≤ fork}
    {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    RegistryLifecycle state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact .of_data rfl

theorem registryLifecycle_computeExitEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {exitBalance : Gwei} {epoch : Epoch}
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    RegistryLifecycle state after := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact .of_data rfl

theorem registryLifecycle_computeConsolidationEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {balance : Gwei} {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (after, epoch)) :
    RegistryLifecycle state after := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact .of_data rfl

theorem registryLifecycle_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    RegistryLifecycle state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    exact (registryLifecycle_computeExitEpochAndUpdateChurn churned).trans (.of_data rfl)
  · cases computed
    exact .refl _

theorem registryLifecycle_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    RegistryLifecycle state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .refl _)
    | exact registryLifecycle_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact registryLifecycle_requestPartialWithdrawal computed

theorem registryLifecycle_queueExcessActiveBalance {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : queueExcessActiveBalance state electra index = .ok after) :
    RegistryLifecycle state after := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact .of_data rfl
  · cases computed
    exact .refl _

/-- A switch to compounding changes only the withdrawal credentials of the validator. -/
theorem registryLifecycle_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    RegistryLifecycle state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨validator, found, _, set, queued⟩ := computed
  exact (RegistryLifecycle.setValidator found set ⟨fun _ => rfl, fun _ => rfl⟩).trans
    (registryLifecycle_queueExcessActiveBalance queued)

/-- The source of a consolidation gets an exit epoch, which it did not have. -/
theorem registryLifecycle_queueConsolidation {electra : .pectra ≤ fork}
    {sourceIndex : ValidatorIndex}
    {source : Validator} {targetIndex : ValidatorIndex}
    (found : state.validators.data[sourceIndex.toNat]? = some source)
    (far : source.exitEpoch = FAR_FUTURE_EPOCH)
    (computed :
      queueConsolidation config state electra sourceIndex source targetIndex = .ok after) :
    RegistryLifecycle state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at computed
  obtain ⟨⟨churnedState, exitEpoch⟩, churned, withdrawable, _, _, set, _, _, computed⟩ :=
    computed
  simp only [Except.ok.injEq] at computed
  subst computed
  have churnedKept := registryLifecycle_computeConsolidationEpochAndUpdateChurn churned
  have same : churnedState.validators.data = state.validators.data := by
    simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churned
    obtain ⟨_, _, _, _, _, _, churned⟩ := churned
    cases churned
    rfl
  exact churnedKept.trans <|
    (RegistryLifecycle.setValidator (old := source)
      (by simp [getValidator, same, found]) set
      ⟨fun _ => rfl, fun set => absurd far set⟩).trans (.of_data rfl)

theorem registryLifecycle_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    RegistryLifecycle state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .refl _)
    | exact registryLifecycle_switchToCompoundingValidator (liftAccessor_ok.mp computed)
    | exact registryLifecycle_queueConsolidation
        (getElem?_toNat_of_ofNatChecked (by assumption))
        (by clear computed; simp_all) computed

theorem registryLifecycle_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    RegistryLifecycle state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processDepositRequest ok)
      depositsOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processConsolidationRequest ok)
      consolidationsOk

/-! ## Withdrawals -/

theorem registryLifecycle_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) : RegistryLifecycle state after := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact .of_data rfl
  · exact .decreaseBalance computed

theorem registryLifecycle_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    RegistryLifecycle state after := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : RegistryLifecycle state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_applyWithdrawal ok) appliedOk
  have two : RegistryLifecycle applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact .of_data rfl
    · cases indexedOk
      exact .refl _
  have queued : ∀ kept : BeaconState preset fork,
      RegistryLifecycle kept (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals kept gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact .of_data rfl
    · exact .refl _
  have partials : ∀ kept : BeaconState preset fork,
      RegistryLifecycle kept (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals kept electra expected.processedPartialWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact .of_data rfl
    · exact .refl _
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → RegistryLifecycle kept finished := by
    intro kept ok
    split at ok
    · unfold updateNextWithdrawalBuilderIndex at ok
      dsimp only at ok
      split at ok
      · cases ok
        exact .of_data rfl
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, rfl⟩ := ok
        exact .of_data rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _
  have lastKept : RegistryLifecycle finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last
      exact .of_data rfl
  exact one.trans <| two.trans <| (queued _).trans <| (partials _).trans <|
    (swept _ sweptOk).trans lastKept

theorem registryLifecycle_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) :
    RegistryLifecycle state after := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact registryLifecycle_applyExpectedWithdrawals applied
    · cases computed
      exact .refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact registryLifecycle_applyExpectedWithdrawals applied

/-- A change to an execution address changes only the withdrawal credentials of the validator. -/
theorem registryLifecycle_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    RegistryLifecycle state after := by
  obtain ⟨validator, found, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact .setValidator found set ⟨fun _ => rfl, fun _ => rfl⟩

/-! ## The parent payload and the execution part of a block -/

theorem registryLifecycle_processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    RegistryLifecycle state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  exact .of_data rfl

theorem registryLifecycle_processBuilderDepositRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    RegistryLifecycle state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .of_data rfl)

theorem registryLifecycle_processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    RegistryLifecycle state after := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact .refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact .of_data rfl

theorem registryLifecycle_settleParentPayment {gloas : .glamsterdam ≤ fork}
    (computed : settleParentPayment state gloas = .ok after) : RegistryLifecycle state after := by
  unfold settleParentPayment at computed
  split at computed
  · have settled := liftAccessor_ok.mp computed
    unfold settleBuilderPayment at settled
    split at settled
    · cases settled
      exact .of_data rfl
    · cases settled
  · simp only at computed
    split at computed <;> cases computed <;> exact .of_data rfl

theorem registryLifecycle_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    RegistryLifecycle state after := by
  unfold processParentExecutionPayload at computed
  dsimp only at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact .refl _
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, applied⟩ := computed
  unfold applyParentExecutionPayload at applied
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at applied
  obtain ⟨_, _, _, _, _, _, _, _, settled, settledOk, requested, requestedOk, _, _, rfl⟩ :=
    applied
  unfold processParentRequests at requestedOk
  simp only [bind_ok_iff, ← Array.foldlM_toList] at requestedOk
  obtain ⟨_, depositsOk, _, withdrawalsOk, _, consolidationsOk, _, buildersOk, exitsOk⟩ :=
    requestedOk
  exact (registryLifecycle_settleParentPayment settledOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processDepositRequest ok)
      depositsOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processConsolidationRequest ok)
      consolidationsOk).trans <|
    (RegistryLifecycle.foldlM
      (fun _ _ _ ok => registryLifecycle_processBuilderDepositRequest ok) buildersOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processBuilderExitRequest ok)
      exitsOk).trans (.of_data rfl)

theorem registryLifecycle_processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    RegistryLifecycle state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact .of_data rfl
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    exact .of_data rfl

theorem registryLifecycle_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    RegistryLifecycle state after := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    exact (registryLifecycle_processWithdrawals withdrawnOk).trans
      (registryLifecycle_processExecutionPayloadBid bid)
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (registryLifecycle_processWithdrawals withdrawnOk).trans
      (registryLifecycle_processExecutionPayload paid)
  · dsimp only at computed
    split at computed
    · exact registryLifecycle_processExecutionPayload computed
    · cases computed
      exact .refl _

/-! ## The sync aggregate -/

theorem registryLifecycle_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    RegistryLifecycle state after := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine RegistryLifecycle.foldlM (fun _ _ _ ok => ?_) folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact (RegistryLifecycle.increaseBalance raised).trans (.increaseBalance paid)
  · exact .decreaseBalance (liftAccessor_ok.mp ok)

/-! ## Blocks -/

theorem registryLifecycle_processOperations {body : BeaconBlockBody preset fork}
    {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    RegistryLifecycle state after := by
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    exact (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processProposerSlashing ok)
        proposersOk).trans <|
      (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processAttesterSlashing ok)
        attestersOk).trans <|
      (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processAttestation ok)
        attestedOk).trans <|
      (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processVoluntaryExit ok)
        exitsOk).trans <|
      (RegistryLifecycle.foldlM
        (fun _ _ _ ok => registryLifecycle_processBlsToExecutionChange ok) changesOk).trans <|
      RegistryLifecycle.foldlM (fun _ _ _ ok => by
        rw [processPayloadAttestation_eq ok]
        exact .refl _) paid
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  have changes : RegistryLifecycle exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact RegistryLifecycle.foldlM
        (fun _ _ _ ok => registryLifecycle_processBlsToExecutionChange ok) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ .refl _
  have requests : RegistryLifecycle changed after := by
    split at requestsOk
    · exact registryLifecycle_processExecutionRequests requestsOk
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk ▸ .refl _
  exact (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processProposerSlashing ok)
      proposersOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processAttesterSlashing ok)
      attestersOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processAttestation ok)
      attestedOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processDeposit ok)
      depositedOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processVoluntaryExit ok)
      exitsOk).trans <|
    changes.trans requests

theorem registryLifecycle_processBlock {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    RegistryLifecycle state after := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := computed
    -- From Gloas the payload of the parent runs before the header.
    have paidKept : RegistryLifecycle state paid := by
      split at paidOk
      · exact registryLifecycle_processParentExecutionPayload paidOk
      · cases paidOk
        exact .refl _
    -- From Bellatrix the execution part runs between the header and the RANDAO reveal.
    have executedKept : RegistryLifecycle headed executed := by
      split at executedOk
      · exact registryLifecycle_processBlockExecution executedOk
      · cases executedOk
        exact .refl _
    -- Heze drops the vote on the deposit contract.
    have votedKept : RegistryLifecycle revealed voted := by
      split at votedOk
      · exact registryLifecycle_processEth1Data votedOk
      · cases votedOk
        exact .refl _
    exact paidKept.trans <| (registryLifecycle_processBlockHeader headedOk).trans <|
      executedKept.trans <| (registryLifecycle_processRandao revealedOk).trans <|
      votedKept.trans <| (registryLifecycle_processOperations operatedOk).trans
        (registryLifecycle_processSyncAggregate synced)
  simp only [bind_ok_iff] at computed
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := computed
  exact (registryLifecycle_processBlockHeader headerOk).trans <|
    (registryLifecycle_processRandao randaoOk).trans <|
    (registryLifecycle_processEth1Data eth1Ok).trans
      (registryLifecycle_processOperations operationsOk)

/-! ## The steps of an epoch -/

theorem registryLifecycle_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) :
    RegistryLifecycle state after := by
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · subst same
    exact .refl _
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    exact .of_data (by rw [← rest])

theorem registryLifecycle_applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) : RegistryLifecycle state after :=
  RegistryLifecycle.foldlM (fun _ _ _ ok => by
    simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, raised, lowered⟩ := ok
    exact (RegistryLifecycle.increaseBalance raised).trans (.decreaseBalance lowered)) computed

theorem registryLifecycle_processRewardsAndPenalties
    (computed : processRewardsAndPenalties config state = .ok after) :
    RegistryLifecycle state after := by
  unfold processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_applyAllDeltas ok) applied
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact registryLifecycle_applyAllDeltas applied

/-- Joining the activation queue changes only the eligibility epoch. -/
theorem validatorLifecycle_queueForActivation {validator queued : Validator}
    (computed : queueForActivation state validator = .ok queued) :
    ValidatorLifecycle validator queued := by
  unfold queueForActivation at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem registryLifecycle_updateRegistryEntry {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) :
    RegistryLifecycle state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, queued, queuedOk, marked, markedOk, computed⟩ := computed
  have set := RegistryLifecycle.setValidatorAt found markedOk
    (validatorLifecycle_queueForActivation queuedOk)
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, exited⟩ := computed
    exact set.trans (registryLifecycle_initiateValidatorExit exited)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ set

/-- A validator eligible for activation has no activation epoch yet. -/
theorem activationEpoch_of_isEligibleForActivation {validator : Validator}
    (eligible : isEligibleForActivation state validator = true) :
    validator.activationEpoch = FAR_FUTURE_EPOCH := by
  simp only [isEligibleForActivation, Bool.and_eq_true, beq_iff_eq] at eligible
  exact eligible.2

/-- Activating a validator that has no activation epoch yet. -/
theorem registryLifecycle_activateValidator {index : ValidatorIndex} {validator : Validator}
    (found : getValidator state index = .ok validator)
    (far : validator.activationEpoch = FAR_FUTURE_EPOCH)
    (computed : activateValidator state index = .ok after) : RegistryLifecycle state after := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨old, oldFound, _, _, set⟩ := computed
  have same := Except.ok.inj (oldFound.symm.trans found)
  subst same
  exact .setValidator oldFound set ⟨fun set => absurd far set, fun _ => rfl⟩

/-- Each index in the activation queue is that of a validator eligible for activation. -/
theorem mem_activationQueue {index : ValidatorIndex} (member : index ∈ activationQueue state) :
    ∃ (position : Nat) (validator : Validator), position.toUInt64 = index ∧
      state.validators.data[position]? = some validator ∧
      isEligibleForActivation state validator = true := by
  simp only [activationQueue, List.mem_map, List.mem_mergeSort] at member
  obtain ⟨⟨eligibleEpoch, queuedIndex⟩, member, equal⟩ := member
  simp only [List.mem_filterMap] at member
  obtain ⟨⟨validator, position⟩, positionOk, selected⟩ := member
  split at selected
  · rename_i eligible
    simp only [Option.some.injEq, Prod.mk.injEq] at selected
    obtain ⟨_, rfl⟩ := selected
    refine ⟨position, validator, equal, ?_, eligible⟩
    simpa only [Array.getElem?_toList] using (List.mem_zipIdx_iff_getElem?.mp positionOk)
  · cases selected

/-- The activation queue holds each index at most once, while the registry is below `2^64`. -/
theorem activationQueue_nodup (small : state.validators.data.size < 2 ^ 64) :
    (activationQueue state).Nodup := by
  let entries := state.validators.data.toList.zipIdx.filterMap fun (validator, index) =>
    if isEligibleForActivation state validator then
      some (validator.activationEligibilityEpoch, index.toUInt64)
    else none
  -- The positions of the registry increase, and below `2^64` their indices of 64 bits differ.
  have base : state.validators.data.toList.zipIdx.Pairwise (fun a b => a.2 < b.2) := by
    have := List.pairwise_lt_range' (s := 0) (n := state.validators.data.toList.length)
    rw [← List.zipIdx_map_snd 0] at this
    exact List.pairwise_map.mp this
  have distinct : entries.Pairwise (fun a b => a.2 ≠ b.2) := by
    apply List.Pairwise.filterMap _ ?_ (List.Pairwise.and_mem.mp base)
    rintro ⟨v, i⟩ ⟨w, j⟩ ⟨mi, mj, lt⟩ a ha b hb
    simp only [Option.ite_none_right_eq_some, Option.some.injEq] at ha hb
    obtain ⟨_, rfl⟩ := ha
    obtain ⟨_, rfl⟩ := hb
    have hi : i < state.validators.data.size := by simpa using (List.mem_zipIdx' mi).1
    have hj : j < state.validators.data.size := by simpa using (List.mem_zipIdx' mj).1
    intro equal
    dsimp only at equal lt
    have equalNat := congrArg UInt64.toNat equal
    rw [toNat_toUInt64_of_lt_pow (by omega), toNat_toUInt64_of_lt_pow (by omega)] at equalNat
    omega
  have unique : (entries.map (·.2)).Nodup := List.pairwise_map.mpr distinct
  exact ((List.mergeSort_perm entries _).map (·.2)).nodup_iff.mpr unique

/-- Activating distinct validators, each eligible for activation at the start. -/
theorem registryLifecycle_foldActivateValidator :
    ∀ {indices : List ValidatorIndex} {state after : BeaconState preset fork},
      indices.Nodup →
      (∀ index ∈ indices, ∃ validator, getValidator state index = .ok validator ∧
        validator.activationEpoch = FAR_FUTURE_EPOCH) →
      indices.foldlM activateValidator state = .ok after → RegistryLifecycle state after
  | [], state, after, _, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  | index :: rest, state, after, unique, eligible, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, tail⟩ := computed
    obtain ⟨validator, found, far⟩ := eligible index List.mem_cons_self
    obtain ⟨absent, restUnique⟩ := List.nodup_cons.mp unique
    refine (registryLifecycle_activateValidator found far first).trans
      (registryLifecycle_foldActivateValidator restUnique (fun other member => ?_) tail)
    -- The other validators of the queue are not touched by this activation.
    have distinct : other ≠ index := fun same => absent (same ▸ member)
    obtain ⟨otherValidator, otherFound, otherFar⟩ := eligible other (List.mem_cons_of_mem _ member)
    simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at first
    obtain ⟨_, _, _, _, set⟩ := first
    exact ⟨otherValidator, (getValidator_setValidator_of_ne set distinct).trans otherFound,
      otherFar⟩

theorem registryLifecycle_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) :
    RegistryLifecycle state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, computed⟩ := computed
    refine RegistryLifecycle.foldlM (fun state _ _ ok => ?_) computed
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨validator, found, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, set⟩ := ok
      exact .setValidatorAt found set ⟨fun _ => rfl, fun _ => rfl⟩
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, exited⟩ := ok
      exact registryLifecycle_initiateValidatorExit exited
    split at ok
    · rename_i eligible
      rw [liftAccessor_ok] at ok
      have far := activationEpoch_of_isEligibleForActivation eligible
      exact .setValidatorAt found ok ⟨fun set => absurd far set, fun _ => rfl⟩
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _
  rename_i notElectra
  simp only [bind_ok_iff] at computed
  obtain ⟨updated, updatedOk, activated⟩ := computed
  -- Before Electra the registry is within its limit, far below `2^64`.
  have before : fork < .glamsterdam := Nat.lt_trans (Nat.lt_of_not_le notElectra) (by decide)
  have small : updated.validators.data.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (updated.validators.bound before) (UInt64.toNat_lt _)
  refine (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_updateRegistryEntry ok)
    updatedOk).trans (registryLifecycle_foldActivateValidator
      (List.Nodup.sublist (List.take_sublist _ _) (activationQueue_nodup small))
      (fun index member => ?_) activated)
  obtain ⟨position, validator, equal, found, eligible⟩ :=
    mem_activationQueue (List.mem_of_mem_take member)
  refine ⟨validator, ?_, activationEpoch_of_isEligibleForActivation eligible⟩
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have exact : index.toNat = position := by
    rw [← equal, toNat_toUInt64_of_lt_pow (by omega)]
  simp [getValidator, exact, found]

theorem registryLifecycle_processSlashings (computed : processSlashings state = .ok after) :
    RegistryLifecycle state after := by
  unfold processSlashings at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    refine RegistryLifecycle.foldlM (fun _ _ _ ok => ?_) applied
    simp only [applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, _, _, lowered⟩ := ok
        exact .decreaseBalance lowered
      · simp only [pure, Except.pure, Except.ok.injEq] at ok
        exact ok ▸ .refl _
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _
  · refine RegistryLifecycle.foldlM (fun _ _ _ ok => ?_) computed
    simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, _, _, _, _, lowered⟩ := ok
        exact .decreaseBalance lowered
      · simp only [pure, Except.pure, Except.ok.injEq] at ok
        exact ok ▸ .refl _
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _

theorem registryLifecycle_processEth1DataReset {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) :
    RegistryLifecycle state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .of_data rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

/-- An update of effective balances changes only the effective balances. -/
theorem registryLifecycle_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    RegistryLifecycle state after := by
  unfold processEffectiveBalanceUpdates at computed
  refine RegistryLifecycle.foldlM (fun _ _ _ ok => ?_) computed
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨validator, found, _, _, _, _, set⟩ := ok
  exact .setValidatorAt found set ⟨fun _ => rfl, fun _ => rfl⟩

theorem registryLifecycle_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) :
    RegistryLifecycle state after := by
  unfold processHistoricalRootsUpdate at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact .of_data rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem registryLifecycle_processParticipationRecordUpdates
    (computed : processParticipationRecordUpdates state = .ok after) :
    RegistryLifecycle state after := by
  unfold processParticipationRecordUpdates at computed
  split at computed
  · cases computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  exact .of_data rfl

/-! ## The steps of an epoch from Altair -/

theorem registryLifecycle_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) :
    RegistryLifecycle state after := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact .of_data rfl

theorem registryLifecycle_passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      RegistryLifecycle state pass.1.state
  | [], _, _, _, _, _, computed => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .refl _
  | deposit :: rest, state, processed, count, postponed, pass, computed => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact .refl _
    split at computed
    · cases computed
    split at computed
    · split at computed
      · cases computed
      rename_i credited
      split at computed
      · cases computed
      cases computed
      exact (registryLifecycle_applyPendingDeposit credited).trans
        (registryLifecycle_passPendingDeposits (deposits := rest) ‹_›)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact registryLifecycle_passPendingDeposits (deposits := rest) ‹_›
    split at computed
    · cases computed
    split at computed
    · cases computed
      exact .refl _
    split at computed
    · cases computed
    rename_i credited
    split at computed
    · cases computed
    cases computed
    exact (registryLifecycle_applyPendingDeposit credited).trans
      (registryLifecycle_passPendingDeposits (deposits := rest) ‹_›)

theorem registryLifecycle_processPendingDeposits {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    RegistryLifecycle state after := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals exact (registryLifecycle_passPendingDeposits ‹_›).trans (.of_data rfl)

theorem registryLifecycle_passPendingConsolidations {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      RegistryLifecycle state result.1
  | [], _, _, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .refl _
  | consolidation :: rest, state, result, computed => by
    simp only [passPendingConsolidations, bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨source, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨⟨passed, read⟩, passedOk, computed⟩ := computed
      cases computed
      exact registryLifecycle_passPendingConsolidations (result := (passed, read)) passedOk
    split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨passed, read⟩, passedOk, computed⟩ :=
      computed
    cases computed
    exact (RegistryLifecycle.decreaseBalance loweredOk).trans <|
      (RegistryLifecycle.increaseBalance raisedOk).trans
        (registryLifecycle_passPendingConsolidations (result := (passed, read)) passedOk)

theorem registryLifecycle_processPendingBalances
    (computed : processPendingBalances config checks state = .ok after) :
    RegistryLifecycle state after := by
  unfold processPendingBalances at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, deposited, consolidated⟩ := computed
    refine (registryLifecycle_processPendingDeposits deposited).trans ?_
    unfold processPendingConsolidations at consolidated
    simp only [bind, Except.bind, pure, Except.pure] at consolidated
    repeat' (split at consolidated <;> try cases consolidated)
    all_goals exact (registryLifecycle_passPendingConsolidations ‹_›).trans (.of_data rfl)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

/-- The steps that close an epoch from Altair, after the history. -/
private theorem registryLifecycle_epochEnd {altair : .altair ≤ fork}
    {rooted synced looked : BeaconState preset fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair) altair =
      .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : RegistryLifecycle rooted after := by
  have syncedKept : RegistryLifecycle rooted synced := by
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals exact .of_data rfl
  have lookedKept : RegistryLifecycle synced looked := by
    split at lookedOk
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at lookedOk
      obtain ⟨_, _, _, _, rfl⟩ := lookedOk
      exact .of_data rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at lookedOk
      exact lookedOk ▸ .refl _
  have windowedKept : RegistryLifecycle looked after := by
    split at windowed
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at windowed
      obtain ⟨_, _, _, _, rfl⟩ := windowed
      exact .of_data rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at windowed
      exact windowed ▸ .refl _
  exact syncedKept.trans (lookedKept.trans windowedKept)

theorem registryLifecycle_processEpochAltair {altair : .altair ≤ fork}
    (computed : processEpochAltair config checks state altair = .ok after) :
    RegistryLifecycle state after := by
  unfold processEpochAltair at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk, balanced,
    balancedOk, cleared, clearedOk, mixed, mixedOk, computed⟩ := computed
  have resetKept : RegistryLifecycle slashed reset := by
    split at resetOk
    · exact registryLifecycle_processEth1DataReset resetOk
    · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
      exact resetOk ▸ .refl _
  have paidKept : RegistryLifecycle pending paid := by
    split at paidOk
    · simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at paidOk
      obtain ⟨_, _, rfl⟩ := paidOk
      exact .of_data rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
      exact paidOk ▸ .refl _
  have clearedKept : RegistryLifecycle balanced cleared := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
    exact .of_data rfl
  have mixedKept : RegistryLifecycle cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    exact .of_data rfl
  have head : RegistryLifecycle state mixed :=
    (registryLifecycle_processJustificationAndFinalization justifiedOk).trans <|
    (registryLifecycle_processInactivityUpdates scoredOk).trans <|
    (registryLifecycle_processRewardsAndPenalties rewardedOk).trans <|
    (registryLifecycle_processRegistryUpdates registeredOk).trans <|
    (registryLifecycle_processSlashings slashedOk).trans <|
    resetKept.trans <|
    (registryLifecycle_processPendingBalances pendingOk).trans <|
    paidKept.trans <|
    (registryLifecycle_processEffectiveBalanceUpdates balancedOk).trans <|
    clearedKept.trans mixedKept
  split at computed <;> simp only [bind_ok_iff] at computed <;>
    obtain ⟨rooted, rootedOk, synced, syncedOk, looked, lookedOk, windowed⟩ := computed
  · have rootedKept : RegistryLifecycle mixed rooted := by
      unfold processHistoricalSummariesUpdate at rootedOk
      simp only [bind, Except.bind, pure, Except.pure] at rootedOk
      repeat' (split at rootedOk <;> try cases rootedOk)
      all_goals first
        | exact .refl _
        | exact .of_data rfl
    exact head.trans <| rootedKept.trans (registryLifecycle_epochEnd syncedOk lookedOk windowed)
  · exact head.trans <| (registryLifecycle_processHistoricalRootsUpdate rootedOk).trans
      (registryLifecycle_epochEnd syncedOk lookedOk windowed)

theorem registryLifecycle_processEpoch
    (computed : processEpoch config checks state = .ok after) : RegistryLifecycle state after := by
  unfold processEpoch at computed
  split at computed
  · exact registryLifecycle_processEpochAltair computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  have clearedKept : RegistryLifecycle balanced cleared := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
    exact .of_data rfl
  have mixedKept : RegistryLifecycle cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    exact .of_data rfl
  exact (registryLifecycle_processJustificationAndFinalization justifiedOk).trans <|
    (registryLifecycle_processRewardsAndPenalties rewardedOk).trans <|
    (registryLifecycle_processRegistryUpdates registeredOk).trans <|
    (registryLifecycle_processSlashings slashedOk).trans <|
    (registryLifecycle_processEth1DataReset resetOk).trans <|
    (registryLifecycle_processEffectiveBalanceUpdates balancedOk).trans <|
    clearedKept.trans <| mixedKept.trans <|
    (registryLifecycle_processHistoricalRootsUpdate rootedOk).trans
      (registryLifecycle_processParticipationRecordUpdates rotated)

/-! ## Slots, upgrades and chains -/

theorem registryLifecycle_advanceSlot (computed : advanceSlot config checks state = .ok after) :
    RegistryLifecycle state after := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have cachedKept : RegistryLifecycle state cached := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact .of_data rfl
  have epochedKept : RegistryLifecycle cached epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact registryLifecycle_processEpoch epochedOk
    · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
      exact epochedOk ▸ .refl _
  exact cachedKept.trans (epochedKept.trans (.of_data rfl))

/-- Queueing a validator that is not yet active changes its eligibility and effective balance. -/
theorem registryLifecycle_queuePreActivation {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queuePreActivation state electra index = .ok after) :
    RegistryLifecycle state after := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨validator, found, _, -, _, -, _, set₁, _, set₂, rfl⟩ := computed
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  have reset := RegistryLifecycle.setValidator (old := validator) (by exact found) set₂
    ⟨fun _ => rfl, fun _ => rfl⟩
  exact RegistryLifecycle.trans (by exact .of_data rfl) (reset.trans (.of_data rfl))

theorem registryLifecycle_upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    RegistryLifecycle pre.state post.val.state := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact .of_data (upgradeToAltair_spec upgraded).1
  · subst computed
    exact .of_data rfl
  · subst computed
    exact .of_data rfl
  · subst computed
    exact .of_data rfl
  · obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, -, _, -, _, -, _, -, _, queued, compounded⟩ := upgraded
    have compoundedKept := RegistryLifecycle.foldlM (fun _ _ _ ok => by
      unfold queueCompoundingExcess at ok
      split at ok
      · split at ok
        · exact registryLifecycle_queueExcessActiveBalance (liftAccessor_ok.mp ok)
        · cases ok
          exact .refl _
      · cases ok
        exact .refl _) compounded
    have queuedKept := RegistryLifecycle.foldlM
      (fun _ _ _ ok => registryLifecycle_queuePreActivation ok) queued
    exact RegistryLifecycle.trans (by exact .of_data rfl) (queuedKept.trans compoundedKept)
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact .of_data (upgradeToFulu_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact .of_data (upgradeToGloas_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact .of_data (upgradeHezeFields_lists _).1

/-- Every step of a chain keeps the lifecycle of the validators. -/
theorem RegistryLifecycle.chainStep {first last : ForkedBeaconState preset}
    (step : ChainStep config checks first last) : RegistryLifecycle first.state last.state := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    have rest := processUpgrades_induction
      (property := fun post => RegistryLifecycle advanced post.state)
      (fun before ok => before.trans (registryLifecycle_upgradeNext ok)) (.refl advanced) upgrades
    exact (registryLifecycle_advanceSlot slotOk).trans rest
  | block engine signed validate ok =>
    exact registryLifecycle_processBlock (applySignedBlock_ok ok).2.1

/-- A run preserves the assigned epochs of every existing registry entry. -/
theorem Run.registryLifecycle {first last : ForkedBeaconState preset}
    (run : Run config checks first last) : RegistryLifecycle first.state last.state := by
  induction run with
  | nil => exact .refl _
  | snoc pre step ih => exact ih.trans (RegistryLifecycle.chainStep step.chainStep)

/-! ## Admissions within one step -/

-- Keeping both epochs unassigned lets activity checks rule out a later exit request.
private def Unassigned (v : Validator) : Prop :=
  v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH

private def UnassignedFrom (n : Nat) {fork : Fork} (s : BeaconState preset fork) : Prop :=
  ∀ i v, n ≤ i → s.validators.data[i]? = some v → Unassigned v

private theorem unassignedFrom_size (s : BeaconState preset fork) :
    UnassignedFrom s.validators.data.size s := by
  intro i v large found
  have := (Array.getElem?_eq_some_iff.mp found).1
  omega

private def UnassignedKept {f g : Fork} (s : BeaconState preset f)
    (t : BeaconState preset g) : Prop :=
  ∀ n, UnassignedFrom n s → UnassignedFrom n t

namespace UnassignedKept

private theorem refl (s : BeaconState preset fork) : UnassignedKept s s := fun _ => id

private theorem trans {f g h : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    {u : BeaconState preset h} (one : UnassignedKept s t) (two : UnassignedKept t u) :
    UnassignedKept s u := fun n => two n ∘ one n

private theorem of_data {g : Fork} {t : BeaconState preset g}
    (same : t.validators.data = state.validators.data := by rfl) : UnassignedKept state t := by
  intro n h i v hi found
  exact h i v hi (same ▸ found)

private theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (keeps : ∀ s a t, step s a = .ok t → UnassignedKept s t) {xs : List α}
    (ok : xs.foldlM step state = .ok after) : UnassignedKept state after :=
  foldlM_ok_invariant (UnassignedKept state)
    (fun _ _ _ h ok => h.trans (keeps _ _ _ ok)) (refl state) ok

private theorem setValidatorAt {i : Nat} {old v : Validator}
    (found : getValidatorAt state i = .ok old)
    (set : state.setValidatorAt i v = .ok after)
    (keeps : Unassigned old → Unassigned v) : UnassignedKept state after := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldEq : state.validators.data[i] = old := by simpa [getValidatorAt, inside] using found
  intro n h j w large read
  simp only [BeaconState.putValidator, RootedForkList.data_set, Array.getElem?_set] at read
  split at read
  · rename_i same
    subst j
    cases read
    apply keeps (h i old large ?_)
    simp [Array.getElem?_eq_getElem inside, oldEq]
  · exact h j w large read

private theorem setValidator {i : ValidatorIndex} {old v : Validator}
    (found : getValidator state i = .ok old)
    (set : state.setValidator i v = .ok after)
    (keeps : Unassigned old → Unassigned v) : UnassignedKept state after :=
  setValidatorAt (by rwa [← getValidator_eq_getValidatorAt])
    (by rwa [← setValidator_eq_setValidatorAt]) keeps

private theorem append {v : Validator}
    (added : after.validators.data = state.validators.data.push v)
    (pending : Unassigned v) : UnassignedKept state after := by
  intro n h i w large found
  rw [added, Array.getElem?_push] at found
  split at found
  · cases found; exact pending
  · exact h i w large found

private theorem increaseBalance {i : ValidatorIndex} {amount : Gwei}
    (ok : Consensus.increaseBalance state i amount = .ok after) : UnassignedKept state after :=
  of_data (congrArg (·.data) (increaseBalance_validators ok))

private theorem decreaseBalance {i : ValidatorIndex} {amount : Gwei}
    (ok : Consensus.decreaseBalance state i amount = .ok after) : UnassignedKept state after :=
  of_data (congrArg (·.data) (decreaseBalance_validators ok))

private theorem applyPendingDeposit {deposit : PendingDeposit}
    (ok : Consensus.applyPendingDeposit config checks state deposit = .ok after) :
    UnassignedKept state after := by
  unfold Consensus.applyPendingDeposit at ok
  split at ok
  · split at ok
    · cases ok; exact refl _
    simp only [bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · exact append (addValidatorToRegistry_validators_eq_push ok) ⟨rfl, rfl⟩
    · cases ok; exact refl _
  · simp only [liftAccessor_ok, bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact increaseBalance ok

private theorem applyDeposit {pubkey : BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    {signature : BLSSignature}
    (ok : Consensus.applyDeposit config checks state pubkey credentials amount signature =
      .ok after) : UnassignedKept state after := by
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
        exact (append (addValidatorToRegistry_validators_eq_push added) ⟨rfl, rfl⟩).trans
          (of_data (state := middle))
      · cases ok; exact refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp ok)
      exact of_data
  · exact applyPendingDeposit ok

private theorem processDeposit {before : fork < .hegota} {deposit : Deposit}
    (ok : Consensus.processDeposit config checks before state deposit = .ok after) :
    UnassignedKept state after := by
  obtain ⟨_, _, next, _, credited⟩ := processDeposit_ok ok
  exact (of_data (state := state)
    (t := { state with eth1DepositIndex := fun _ => next })).trans (applyDeposit credited)

private theorem inactive {v : Validator} (pending : Unassigned v) (e : Epoch) :
    isActiveValidator v e = false := by
  simp only [isActiveValidator, pending.1, pending.2, Bool.and_eq_false_iff,
    decide_eq_false_iff_not]
  by_cases h : FAR_FUTURE_EPOCH ≤ e
  · exact Or.inr (UInt64.not_lt.mpr h)
  · exact Or.inl h

private theorem initiateValidatorExit {i : ValidatorIndex} {v : Validator}
    (found : getValidator state i = .ok v) (notPending : ¬Unassigned v)
    (ok : Consensus.initiateValidatorExit config state i = .ok after) :
    UnassignedKept state after := by
  obtain ⟨old, read, unchanged | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]; exact refl _
  · have equal := Except.ok.inj (read.symm.trans found)
    have same := (exitQueue_validators queue).1
    exact (of_data (congrArg (·.data) same)).trans <|
      setValidator ((getValidator_of_validators_eq same i).trans read) set
        (fun h => False.elim (notPending (equal ▸ h)))

private theorem processVoluntaryExit {signed : SignedVoluntaryExit}
    (ok : Consensus.processVoluntaryExit config checks state signed = .ok after) :
    UnassignedKept state after := by
  unfold Consensus.processVoluntaryExit at ok
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
  obtain ⟨v, found, _, active, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
  exact initiateValidatorExit found (fun h => by rw [inactive h] at active; cases active) exited

private theorem processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (ok : Consensus.processBlsToExecutionChange config checks state signed = .ok after) :
    UnassignedKept state after := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  apply setValidator found set
  rintro ⟨activation, exit⟩
  exact ⟨activation, exit⟩

private theorem processEffectiveBalanceUpdates
    (ok : Consensus.processEffectiveBalanceUpdates state = .ok after) :
    UnassignedKept state after := by
  apply foldlM (fun _ _ _ ok => ?_) ok
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, _, _, _, _, set⟩ := ok
  apply setValidatorAt found set
  intro h
  exact h

private theorem queueExcessActiveBalance {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.queueExcessActiveBalance state electra index = .ok after) :
    UnassignedKept state after := by
  simp only [Consensus.queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact of_data
  · cases ok; exact refl _

private theorem switchToCompoundingValidator {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.switchToCompoundingValidator state electra index = .ok after) :
    UnassignedKept state after := by
  simp only [Consensus.switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, found, _, set, queued⟩ := ok
  refine (setValidator found set (fun h => h)).trans (queueExcessActiveBalance queued)

private theorem requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (ok : Consensus.requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) : UnassignedKept state after := by
  simp only [Consensus.requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure,
    Except.pure] at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    have same := (computeExitEpochAndUpdateChurn_earliest churned).2.1
    exact (of_data (by rw [same])).trans of_data
  · cases ok; exact refl _

private theorem cannotRequest {v : Validator} (pending : Unassigned v) :
    canRequest config state v = .ok false := by
  simp [canRequest, inactive pending, pure, Except.pure]

private theorem processWithdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : Consensus.processWithdrawalRequest config state electra request = .ok after) :
    UnassignedKept state after := by
  unfold Consensus.processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact refl _)
    | exact requestPartialWithdrawal ok
    | (apply initiateValidatorExit (config := config)
         (by rw [getValidator, getElem?_toNat_of_ofNatChecked (by assumption)])
         ?_ (liftAccessor_ok.mp ok)
       intro pending
       have rejected := cannotRequest (config := config) (state := state) pending
       simp_all)

private theorem queueConsolidation {electra : .pectra ≤ fork}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (found : state.validators.data[sourceIndex.toNat]? = some source)
    (notPending : ¬Unassigned source)
    (ok : Consensus.queueConsolidation config state electra sourceIndex source targetIndex =
      .ok after) : UnassignedKept state after := by
  simp only [Consensus.queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, pure, Except.pure] at ok
  obtain ⟨⟨churned, _⟩, churn, _, _, _, set, _, _, ok⟩ := ok
  simp only [Except.ok.injEq] at ok
  subst ok
  have same := (computeConsolidationEpochAndUpdateChurn_earliest churn).2.1
  have read : getValidator churned sourceIndex = .ok source := by
    rw [getValidator, same, found]
  exact (of_data (by rw [same])).trans <|
    (setValidator read set (fun h => False.elim (notPending h))).trans of_data

private theorem processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (ok : Consensus.processConsolidationRequest config state electra request = .ok after) :
    UnassignedKept state after := by
  unfold Consensus.processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact refl _)
    | exact switchToCompoundingValidator (liftAccessor_ok.mp ok)
    | (apply queueConsolidation (getElem?_toNat_of_ofNatChecked (by assumption)) ?_ ok
       intro pending
       have no := inactive pending (getCurrentEpoch state)
       simp_all)

private theorem processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (ok : Consensus.processDepositRequest state electra request = .ok after) :
    UnassignedKept state after :=
  of_data (congrArg (·.data) (processDepositRequest_ok ok).2.1)

private theorem processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (ok : Consensus.processExecutionRequests config state body electra = .ok after) :
    UnassignedKept state after := by
  simp only [Consensus.processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
  exact (foldlM (fun _ _ _ ok => processDepositRequest ok) deposits).trans <|
    (foldlM (fun _ _ _ ok => processWithdrawalRequest ok) withdrawals).trans
      (foldlM (fun _ _ _ ok => processConsolidationRequest ok) consolidations)

private theorem passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      Consensus.passPendingDeposits config checks stop nextEpoch available state processed count
        postponed deposits = .ok pass → UnassignedKept state pass.1.state
  | [], _, _, _, _, _, ok => by cases ok; exact refl _
  | deposit :: rest, state, processed, count, postponed, pass, ok => by
    unfold Consensus.passPendingDeposits at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    split at ok
    · cases ok; exact refl _
    split at ok
    · cases ok
    split at ok
    · split at ok
      · cases ok
      rename_i credited
      split at ok
      · cases ok
      cases ok
      exact (applyPendingDeposit credited).trans (passPendingDeposits (deposits := rest) ‹_›)
    split at ok
    · split at ok
      · cases ok
      cases ok
      exact passPendingDeposits (deposits := rest) ‹_›
    split at ok
    · cases ok
    split at ok
    · cases ok; exact refl _
    split at ok
    · cases ok
    rename_i credited
    split at ok
    · cases ok
    cases ok
    exact (applyPendingDeposit credited).trans (passPendingDeposits (deposits := rest) ‹_›)

private theorem processPendingBalances
    (ok : Consensus.processPendingBalances config checks state = .ok after) :
    UnassignedKept state after := by
  unfold Consensus.processPendingBalances at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨middle, deposited, consolidated⟩ := ok
    have deposits : UnassignedKept state middle := by
      unfold processPendingDeposits at deposited
      simp only [bind, Except.bind, pure, Except.pure] at deposited
      repeat' (split at deposited <;> try cases deposited)
      all_goals exact (passPendingDeposits ‹_›).trans of_data
    exact deposits.trans
      (of_data (by rw [(processPendingConsolidations_kept consolidated).1]))
  · cases ok; exact refl _

private theorem queuePreActivation {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.queuePreActivation state electra index = .ok after) :
    UnassignedKept state after := by
  simp only [Consensus.queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨v, found, _, _, _, _, _, set₁, _, set₂, rfl⟩ := ok
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  exact (of_data (state := state)).trans <|
    (setValidator (old := v) (by exact found) set₂ (fun h => h)).trans of_data

private theorem upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (ok : Consensus.upgradeNext config checks pre = .ok post) :
    UnassignedKept pre.state post.val.state := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact of_data (upgradeToAltair_spec upgraded).1
  · subst ok; exact of_data
  · subst ok; exact of_data
  · subst ok; exact of_data
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, _, _, _, _, _, _, _, _, queued, compounded⟩ := upgraded
    have tail := foldlM (fun _ _ _ ok => by
      unfold queueCompoundingExcess at ok
      split at ok
      · split at ok
        · exact queueExcessActiveBalance (liftAccessor_ok.mp ok)
        · cases ok; exact refl _
      · cases ok; exact refl _) compounded
    have head := foldlM (fun _ _ _ ok => queuePreActivation ok) queued
    exact (of_data (state := state)).trans (head.trans tail)
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact of_data (upgradeToFulu_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact of_data (upgradeToGloas_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact of_data (upgradeHezeFields_lists _).1

private theorem historicalRoots
    (ok : processHistoricalRootsUpdate state = .ok after) : UnassignedKept state after := by
  unfold processHistoricalRootsUpdate at ok
  split at ok
  · cases ok
  simp only [bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    exact of_data
  · cases ok; exact refl _

private theorem historicalSummaries {capella : .shapella ≤ fork}
    (ok : processHistoricalSummariesUpdate state capella = .ok after) :
    UnassignedKept state after := by
  unfold processHistoricalSummariesUpdate at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals exact of_data

private theorem epochTail {altair : .altair ≤ fork} {rooted synced looked : BeaconState preset fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair)
      altair = .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : UnassignedKept rooted after := by
  have first : UnassignedKept rooted synced := by
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals exact of_data
  have second : UnassignedKept synced looked := by
    split at lookedOk
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at lookedOk
      obtain ⟨_, _, _, _, rfl⟩ := lookedOk
      exact of_data
    · cases lookedOk; exact refl _
  have third : UnassignedKept looked after := by
    split at windowed
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at windowed
      obtain ⟨_, _, _, _, rfl⟩ := windowed
      exact of_data
    · cases windowed; exact refl _
  exact first.trans (second.trans third)

end UnassignedKept

-- Before the admission phase, no operation changes the length of the validator registry.
private def RegistrySize {f g : Fork} (s : BeaconState preset f) (t : BeaconState preset g) :
    Prop := t.validators.data.size = s.validators.data.size

namespace RegistrySize

private theorem refl (s : BeaconState preset fork) : RegistrySize s s := rfl

private theorem trans {f g h : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    {u : BeaconState preset h} (one : RegistrySize s t) (two : RegistrySize t u) :
    RegistrySize s u := Eq.trans two one

private theorem of_data {g : Fork} {t : BeaconState preset g}
    (same : t.validators.data = state.validators.data := by rfl) : RegistrySize state t :=
  congrArg Array.size same

private theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (keeps : ∀ s a t, step s a = .ok t → RegistrySize s t) {xs : List α}
    (ok : xs.foldlM step state = .ok after) : RegistrySize state after :=
  foldlM_ok_invariant (RegistrySize state)
    (fun _ _ _ h ok => h.trans (keeps _ _ _ ok)) (refl state) ok

private theorem inactivity {altair : .altair ≤ fork}
    (ok : processInactivityUpdates config state altair = .ok after) :
    RegistrySize state after := by
  unfold processInactivityUpdates at ok
  split at ok
  · cases ok; rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    rfl

private theorem eth1Reset {before : fork < .hegota}
    (ok : processEth1DataReset before state = .ok after) : RegistrySize state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok <;> cases ok <;> rfl

private theorem executionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (ok : processExecutionPayload config engine state body bellatrix = .ok after) :
    RegistrySize state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
  rfl

private theorem executionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (ok : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    RegistrySize state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok ok
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    rfl
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at recordedOk
    subst recordedOk
    rfl

private theorem blockExecution {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (ok : processBlockExecution config checks engine state body bellatrix = .ok after) :
    RegistrySize state after := by
  unfold processBlockExecution at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, bid⟩ := ok
    exact trans (sameSizes_processWithdrawals withdrawn).1 (executionPayloadBid bid)
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, paid⟩ := ok
    exact trans (sameSizes_processWithdrawals withdrawn).1 (executionPayload paid)
  · dsimp only at ok
    split at ok
    · exact executionPayload ok
    · cases ok; rfl

private theorem builderDeposit {gloas : .glamsterdam ≤ fork} {request : BuilderDepositRequest}
    (ok : processBuilderDepositRequest config checks state gloas request = .ok after) :
    RegistrySize state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first | (cases ok; done) | (cases ok; rfl)

private theorem builderExit {gloas : .glamsterdam ≤ fork} {request : BuilderExitRequest}
    (ok : processBuilderExitRequest config state gloas request = .ok after) :
    RegistrySize state after := by
  rcases processBuilderExitRequest_cases ok with rfl | ⟨_, _, _, _, _, exited⟩
  · rfl
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    rfl

private theorem parentPayload {gloas : .glamsterdam ≤ fork} {body : BeaconBlockBody preset fork}
    (ok : processParentExecutionPayload config checks state gloas body = .ok after) :
    RegistrySize state after := by
  rcases processParentExecutionPayload_ok ok with ⟨_, _, rfl⟩ |
    ⟨_, settled, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk,
      buildersOk, exitsOk, _, rfl⟩
  · rfl
  · have first : RegistrySize state settled := by rw [settleParentPayment_eq settledOk]; rfl
    exact first.trans <|
      (foldlM (fun _ _ _ ok => of_data (congrArg (·.data) (processDepositRequest_ok ok).2.1))
        depositsOk).trans <|
      (foldlM (fun _ _ _ ok => (sameSizes_processWithdrawalRequest ok).1) withdrawalsOk).trans <|
      (foldlM (fun _ _ _ ok => (sameSizes_processConsolidationRequest ok).1)
        consolidationsOk).trans <|
      (foldlM (fun _ _ _ ok => builderDeposit ok) buildersOk).trans <|
      (foldlM (fun _ _ _ ok => builderExit ok) exitsOk).trans (of_data rfl)

end RegistrySize

private theorem newUnassigned_processEpochAltair {altair : .altair ≤ fork}
    (ok : processEpochAltair config checks state altair = .ok after) :
    UnassignedFrom state.validators.data.size after := by
  unfold processEpochAltair at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk, balanced,
    balancedOk, cleared, clearedOk, mixed, mixedOk, ok⟩ := ok
  have resetSize : RegistrySize slashed reset := by
    split at resetOk
    · exact RegistrySize.eth1Reset resetOk
    · cases resetOk; rfl
  have before : RegistrySize state reset :=
    RegistrySize.trans (sameSizes_processJustificationAndFinalization justifiedOk).1 <|
    (RegistrySize.inactivity scoredOk).trans <|
    RegistrySize.trans (processRewardsAndPenalties_sameSizes rewardedOk).1 <|
    RegistrySize.trans (sameSizes_processRegistryUpdates registeredOk).1 <|
    RegistrySize.trans (sameSizes_processSlashings slashedOk).1 resetSize
  -- All assignments precede pending deposits, so this suffix is empty at admission's start.
  have atReset : UnassignedFrom state.validators.data.size reset := by
    rw [← before]
    exact unassignedFrom_size reset
  have paidKept : UnassignedKept pending paid := by
    split at paidOk
    · simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at paidOk
      obtain ⟨_, _, rfl⟩ := paidOk
      exact UnassignedKept.of_data
    · cases paidOk; exact UnassignedKept.refl _
  have clearKept : UnassignedKept balanced cleared := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
    exact UnassignedKept.of_data
  have mixKept : UnassignedKept cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    exact UnassignedKept.of_data
  have atMixed := ((UnassignedKept.processPendingBalances pendingOk).trans <|
    paidKept.trans <| (UnassignedKept.processEffectiveBalanceUpdates balancedOk).trans <|
    clearKept.trans mixKept) _ atReset
  split at ok <;> simp only [bind_ok_iff] at ok <;>
    obtain ⟨rooted, rootOk, synced, syncOk, looked, lookOk, windowOk⟩ := ok
  · exact ((UnassignedKept.historicalSummaries rootOk).trans
      (UnassignedKept.epochTail syncOk lookOk windowOk)) _ atMixed
  · exact ((UnassignedKept.historicalRoots rootOk).trans
      (UnassignedKept.epochTail syncOk lookOk windowOk)) _ atMixed

private theorem newUnassigned_processEpoch
    (ok : processEpoch config checks state = .ok after) :
    UnassignedFrom state.validators.data.size after := by
  unfold processEpoch at ok
  split at ok
  · exact newUnassigned_processEpochAltair ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, justified, _, rewarded, _, registered, _, slashed, _, reset, balanced,
    balancedOk, cleared, clearOk, mixed, mixOk, rooted, rootOk, rotated⟩ := ok
  have first : RegistrySize state balanced :=
    RegistrySize.trans (sameSizes_processJustificationAndFinalization justified).1 <|
    RegistrySize.trans (processRewardsAndPenalties_sameSizes rewarded).1 <|
    RegistrySize.trans (sameSizes_processRegistryUpdates registered).1 <|
    RegistrySize.trans (sameSizes_processSlashings slashed).1 <|
    (RegistrySize.eth1Reset reset).trans (sameSizes_processEffectiveBalanceUpdates balancedOk).1
  have clearKept : UnassignedKept balanced cleared := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearOk
    exact UnassignedKept.of_data
  have mixKept : UnassignedKept cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixOk
    exact UnassignedKept.of_data
  have last : UnassignedKept rooted after := by
    unfold processParticipationRecordUpdates at rotated
    split at rotated
    · cases rotated
    · cases rotated; exact UnassignedKept.of_data
  apply (clearKept.trans (mixKept.trans ((UnassignedKept.historicalRoots rootOk).trans last))) _
  rw [← first]
  exact unassignedFrom_size balanced

private theorem newUnassigned_advanceSlot
    (ok : advanceSlot config checks state = .ok after) :
    UnassignedFrom state.validators.data.size after := by
  obtain ⟨next, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have first : cached.validators.data = state.validators.data := by rw [cachedEq]
  have second : UnassignedFrom cached.validators.data.size epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact newUnassigned_processEpoch epochedOk
    · cases epochedOk; exact unassignedFrom_size _
  exact (UnassignedKept.of_data (state := epoched)) _ (first ▸ second)

private theorem newUnassigned_processOperations {body : BeaconBlockBody preset fork}
    {parentSlot : Slot} (ok : processOperations config checks state body parentSlot = .ok after) :
    UnassignedFrom state.validators.data.size after := by
  unfold processOperations at ok
  split at ok
  -- Gloas block requests enqueue deposits; they do not admit validators in this step.
  · have sizes := (sameSizes_processOperationsGloas ok).1
    rw [← sizes]
    exact unassignedFrom_size after
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, _, _, _, _, proposers, _, attesters, attested, attestations, _, deposited,
    exited, exits, changed, changes, requests⟩ := ok
  have before : RegistrySize state attested :=
    (RegistrySize.foldlM (fun _ _ _ ok => (sameSizes_processProposerSlashing ok).1)
      proposers).trans <|
    (RegistrySize.foldlM (fun _ _ _ ok => (sameSizes_processAttesterSlashing ok).1)
      attesters).trans <|
    RegistrySize.foldlM (fun _ _ _ ok => (sameSizes_processAttestation ok).1) attestations
  have changesKept : UnassignedKept exited changed := by
    unfold processBlsToExecutionChanges at changes
    split at changes
    · rw [← Array.foldlM_toList] at changes
      exact UnassignedKept.foldlM
        (fun _ _ _ ok => UnassignedKept.processBlsToExecutionChange ok) changes
    · cases changes; exact UnassignedKept.refl _
  have requestsKept : UnassignedKept changed after := by
    split at requests
    · exact UnassignedKept.processExecutionRequests requests
    · cases requests; exact UnassignedKept.refl _
  apply ((UnassignedKept.foldlM (fun _ _ _ ok => UnassignedKept.processDeposit ok)
    deposited).trans <|
    (UnassignedKept.foldlM (fun _ _ _ ok => UnassignedKept.processVoluntaryExit ok) exits).trans <|
    changesKept.trans requestsKept) _
  rw [← before]
  exact unassignedFrom_size attested

private theorem newUnassigned_processBlock {block : BeaconBlock preset fork}
    (ok : processBlock config checks engine state block = .ok after) :
    UnassignedFrom state.validators.data.size after := by
  unfold processBlock at ok
  split at ok
  · unfold processBlockAltair at ok
    simp only [bind_ok_iff] at ok
    obtain ⟨paid, paidOk, headed, headOk, executed, executionOk, revealed, randaoOk, voted,
      voteOk, operated, operationsOk, syncOk⟩ := ok
    have paidSize : RegistrySize state paid := by
      split at paidOk
      · exact RegistrySize.parentPayload paidOk
      · cases paidOk; rfl
    have executionSize : RegistrySize headed executed := by
      split at executionOk
      · exact RegistrySize.blockExecution executionOk
      · cases executionOk; rfl
    have randaoSize : RegistrySize executed revealed := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq randaoOk
      rfl
    have voteSize : RegistrySize revealed voted := by
      split at voteOk
      · obtain ⟨_, _, rest⟩ := processEth1Data_eq voteOk
        rw [← rest]; rfl
      · cases voteOk; rfl
    have before := paidSize.trans <|
      RegistrySize.trans (sameSizes_processBlockHeader headOk).1 <|
      executionSize.trans (randaoSize.trans voteSize)
    have pending := newUnassigned_processOperations operationsOk
    -- Sync rewards change balances, not validators.
    unfold processSyncAggregate at syncOk
    simp only [bind_ok_iff] at syncOk
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := syncOk
    rw [← Array.foldlM_toList] at folded
    have kept : UnassignedKept operated after := UnassignedKept.foldlM (fun _ _ _ ok => by
      unfold applySyncReward at ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, raised, _, _, paid⟩ := ok
        exact (UnassignedKept.increaseBalance raised).trans (UnassignedKept.increaseBalance paid)
      · exact UnassignedKept.decreaseBalance (liftAccessor_ok.mp ok)) folded
    exact kept _ (before ▸ pending)
  simp only [bind_ok_iff] at ok
  obtain ⟨_, header, _, randao, voted, eth1, operations⟩ := ok
  have headSize := (sameSizes_processBlockHeader header).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, randaoEq⟩ := processRandao_eq randao
  obtain ⟨_, _, eth1Eq⟩ := processEth1Data_eq eth1
  have before : voted.validators.data.size = state.validators.data.size := by
    have same := congrArg (fun s => s.validators.data.size) eth1Eq
    rw [randaoEq] at same
    exact same.trans headSize
  exact before ▸ newUnassigned_processOperations operations

/-- Pending balance processing retains unassigned activation and exit epochs. -/
theorem processPendingBalances_epochs_unassigned {n : Nat}
    (ok : processPendingBalances config checks state = .ok after)
    (pending : ∀ i v, n ≤ i → state.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH) :
    ∀ i v, n ≤ i → after.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH :=
  UnassignedKept.processPendingBalances ok n pending

/-- A withdrawal request retains unassigned activation and exit epochs. -/
theorem processWithdrawalRequest_epochs_unassigned {n : Nat} {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config state electra request = .ok after)
    (pending : ∀ i v, n ≤ i → state.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH) :
    ∀ i v, n ≤ i → after.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH :=
  UnassignedKept.processWithdrawalRequest ok n pending

/-- A consolidation request retains unassigned activation and exit epochs. -/
theorem processConsolidationRequest_epochs_unassigned {n : Nat} {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (ok : processConsolidationRequest config state electra request = .ok after)
    (pending : ∀ i v, n ≤ i → state.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH) :
    ∀ i v, n ≤ i → after.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH :=
  UnassignedKept.processConsolidationRequest ok n pending

/-- An epoch leaves newly admitted validators with both epochs unassigned. -/
theorem processEpoch_new_validator_epochs_unassigned
    (ok : processEpoch config checks state = .ok after) :
    ∀ i v, state.validators.data.size ≤ i → after.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH :=
  newUnassigned_processEpoch ok

/-- A slot leaves newly admitted validators with both epochs unassigned. -/
theorem advanceSlot_new_validator_epochs_unassigned
    (ok : advanceSlot config checks state = .ok after) :
    ∀ i v, state.validators.data.size ≤ i → after.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH :=
  newUnassigned_advanceSlot ok

/-- Block operations leave newly admitted validators with both epochs unassigned. -/
theorem processOperations_new_validator_epochs_unassigned {body : BeaconBlockBody preset fork}
    {parentSlot : Slot}
    (ok : processOperations config checks state body parentSlot = .ok after) :
    ∀ i v, state.validators.data.size ≤ i → after.validators.data[i]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH :=
  newUnassigned_processOperations ok

/-- A validator admitted within one step still has both epochs unassigned at its endpoint. -/
theorem Step.new_validator_epochs_unassigned {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (i : Nat) (v : Validator)
    (newIndex : x.state.validators.data.size ≤ i)
    (found : y.state.validators.data[i]? = some v) :
    v.activationEpoch = FAR_FUTURE_EPOCH ∧ v.exitEpoch = FAR_FUTURE_EPOCH := by
  have pending : UnassignedFrom x.state.validators.data.size y.state := by
    cases step with
    | slot ok =>
      obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
      have tail := processUpgrades_induction
        (property := fun post => UnassignedKept advanced post.state)
        (fun before ok => before.trans (UnassignedKept.upgradeNext ok))
        (UnassignedKept.refl advanced) upgrades
      exact tail _ (newUnassigned_advanceSlot slotOk)
    | block engine signed due ok =>
      exact newUnassigned_processBlock (applySignedBlock_ok ok).2.1
  exact pending i v newIndex found

/-- A validator admitted within one step still has no assigned exit at its endpoint. -/
theorem Step.new_validator_exit_unassigned {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (i : Nat) (v : Validator)
    (newIndex : x.state.validators.data.size ≤ i)
    (found : y.state.validators.data[i]? = some v) : v.exitEpoch = FAR_FUTURE_EPOCH :=
  (step.new_validator_epochs_unassigned i v newIndex found).2

end EthLib.Consensus
