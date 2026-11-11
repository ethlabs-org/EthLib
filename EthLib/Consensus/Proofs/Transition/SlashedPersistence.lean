module

public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle

/-!
# Persistence of slashing at a validator's registry index

Before Gloas, a successful transition cannot clear a slashed flag or remove its registry entry.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {s t : BeaconState preset fork}

/-- Each slashed validator remains slashed at the same registry index. -/
def SlashedPersistence {f h : Fork} (s : BeaconState preset f)
    (t : BeaconState preset h) : Prop :=
  ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v → v.slashed = true →
    ∃ w, t.validators.data[i]? = some w ∧ w.slashed = true

namespace SlashedPersistence

-- Every operation has the same fork bound, including operations that preserve all validators.
set_option linter.unusedVariables false

theorem refl (s : BeaconState preset fork) : SlashedPersistence s s :=
  fun _ v found flag => ⟨v, found, flag⟩

theorem trans {f g h : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    {u : BeaconState preset h} (one : SlashedPersistence s t) (two : SlashedPersistence t u) :
    SlashedPersistence s u := by
  intro i v found flag
  obtain ⟨w, read, slashed⟩ := one i v found flag
  exact two i w read slashed

theorem of_data {f h : Fork} {s : BeaconState preset f} {t : BeaconState preset h}
    (same : t.validators.data = s.validators.data := by rfl) : SlashedPersistence s t := by
  intro i v found flag
  exact ⟨v, same.symm ▸ found, flag⟩

theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (keeps : ∀ s a t, step s a = .ok t → SlashedPersistence s t) {xs : List α}
    (ok : xs.foldlM step s = .ok t) : SlashedPersistence s t :=
  foldlM_ok_invariant (SlashedPersistence s)
    (fun _ _ _ h ok => h.trans (keeps _ _ _ ok)) (refl s) ok

-- The write either selects this index or leaves the original entry intact.
private theorem setValidatorAt {i : Nat} {old v : Validator}
    (found : getValidatorAt s i = .ok old)
    (set : s.setValidatorAt i v = .ok t)
    (keeps : old.slashed = true → v.slashed = true) : SlashedPersistence s t := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldEq : s.validators.data[i] = old := by simpa [getValidatorAt, inside] using found
  intro j w read flag
  simp only [BeaconState.putValidator, RootedForkList.data_set, Array.getElem?_set]
  split
  · rename_i same
    subst j
    have equal : old = w := by
      rw [Array.getElem?_eq_getElem inside, oldEq] at read
      exact Option.some.inj read
    exact ⟨v, by simp, keeps (equal ▸ flag)⟩
  · exact ⟨w, read, flag⟩

private theorem setValidator {i : ValidatorIndex} {old v : Validator}
    (found : getValidator s i = .ok old) (set : s.setValidator i v = .ok t)
    (keeps : old.slashed = true → v.slashed = true) : SlashedPersistence s t :=
  setValidatorAt (by rwa [← getValidator_eq_getValidatorAt])
    (by rwa [← setValidator_eq_setValidatorAt]) keeps

private theorem append {v : Validator}
    (added : t.validators.data = s.validators.data.push v) : SlashedPersistence s t := by
  intro i w found flag
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  refine ⟨w, ?_, flag⟩
  simpa [added, Array.getElem?_push, Nat.ne_of_lt inside] using found

theorem increaseBalance {i : ValidatorIndex} {amount : Gwei} (early : fork < .glamsterdam)
    (ok : Consensus.increaseBalance s i amount = .ok t) : SlashedPersistence s t :=
  of_data (congrArg (·.data) (increaseBalance_validators ok))

theorem decreaseBalance {i : ValidatorIndex} {amount : Gwei} (early : fork < .glamsterdam)
    (ok : Consensus.decreaseBalance s i amount = .ok t) : SlashedPersistence s t :=
  of_data (congrArg (·.data) (decreaseBalance_validators ok))

private theorem initiateValidatorExit {i : ValidatorIndex}
    (ok : Consensus.initiateValidatorExit config s i = .ok t) : SlashedPersistence s t := by
  obtain ⟨v, found, unchanged | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]; exact refl _
  · have same := (exitQueue_validators queue).1
    exact (of_data (congrArg (·.data) same)).trans
      (setValidator ((getValidator_of_validators_eq same i).trans found) set id)

private theorem slashValidator {i : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (early : fork < .glamsterdam)
    (ok : Consensus.slashValidator config s i whistleblower = .ok t) :
    SlashedPersistence s t := by
  obtain ⟨_, _, _, marked, _, _, slashings, _, _, _, _, _, exited, read, _, set,
    _, _, _, lowered, _, _, raised, paid, rfl⟩ := slashValidator_ok ok
  -- Slashing sets the selected flag to true, regardless of its previous value.
  have first := (initiateValidatorExit exited).trans (setValidator read set (fun _ => rfl))
  have second := (of_data (s := marked) (t := { marked with slashings })).trans
    ((decreaseBalance early lowered).trans
      ((increaseBalance early raised).trans (increaseBalance early paid)))
  apply (first.trans second).trans
  split <;> exact of_data

theorem processProposerSlashing {slashing : ProposerSlashing} (early : fork < .glamsterdam)
    (ok : Consensus.processProposerSlashing config checks s slashing = .ok t) :
    SlashedPersistence s t := by
  simp only [Consensus.processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact slashValidator early slashed

private theorem slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (early : fork < .glamsterdam)
    (ok : Consensus.slashIfSlashable config step index = .ok next) :
    SlashedPersistence step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [Consensus.slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact slashValidator early slashed
  · cases ok; exact refl _

theorem processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (early : fork < .glamsterdam)
    (ok : Consensus.processAttesterSlashing config checks s slashing = .ok t) :
    SlashedPersistence s t := by
  simp only [Consensus.processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  exact foldlM_ok_invariant (fun step => SlashedPersistence s step.1)
    (fun _ _ _ before ok => before.trans (slashIfSlashable early ok))
    (show SlashedPersistence s (s, false).1 from refl s) folded

private theorem applyPendingDeposit {deposit : PendingDeposit} (early : fork < .glamsterdam)
    (ok : Consensus.applyPendingDeposit config checks s deposit = .ok t) :
    SlashedPersistence s t := by
  unfold Consensus.applyPendingDeposit at ok
  split at ok
  · split at ok
    · cases ok; exact refl _
    simp only [bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · exact append (addValidatorToRegistry_validators_eq_push ok)
    · cases ok; exact refl _
  · simp only [liftAccessor_ok, bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact increaseBalance early ok

private theorem applyDeposit {pubkey : BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    {signature : BLSSignature} (early : fork < .glamsterdam)
    (ok : Consensus.applyDeposit config checks s pubkey credentials amount signature = .ok t) :
    SlashedPersistence s t := by
  unfold Consensus.applyDeposit at ok
  split at ok
  · unfold applyDepositElectra at ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, added, pushed⟩ := ok
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
        exact (append (addValidatorToRegistry_validators_eq_push added)).trans of_data
      · cases ok; exact refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp ok)
      exact of_data
  · exact applyPendingDeposit early ok

theorem processDeposit {before : fork < .hegota} {deposit : Deposit}
    (early : fork < .glamsterdam)
    (ok : Consensus.processDeposit config checks before s deposit = .ok t) :
    SlashedPersistence s t := by
  obtain ⟨_, _, next, _, credited⟩ := processDeposit_ok ok
  exact (of_data (s := s)
    (t := { s with eth1DepositIndex := fun _ => next })).trans (applyDeposit early credited)

theorem processVoluntaryExit {signed : SignedVoluntaryExit} (early : fork < .glamsterdam)
    (ok : Consensus.processVoluntaryExit config checks s signed = .ok t) :
    SlashedPersistence s t := by
  unfold Consensus.processVoluntaryExit at ok
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
  exact initiateValidatorExit exited

theorem processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (early : fork < .glamsterdam)
    (ok : Consensus.processBlsToExecutionChange config checks s signed = .ok t) :
    SlashedPersistence s t := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact setValidator found set id

theorem processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (early : fork < .glamsterdam)
    (ok : Consensus.processDepositRequest s electra request = .ok t) :
    SlashedPersistence s t :=
  of_data (congrArg (·.data) (processDepositRequest_ok ok).2.1)

private theorem requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (ok : Consensus.requestPartialWithdrawal config s electra index validator amount owed =
      .ok t) : SlashedPersistence s t := by
  simp only [Consensus.requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure,
    Except.pure] at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    exact (of_data (by rw [(computeExitEpochAndUpdateChurn_earliest churned).2.1])).trans of_data
  · cases ok; exact refl _

theorem processWithdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (early : fork < .glamsterdam)
    (ok : Consensus.processWithdrawalRequest config s electra request = .ok t) :
    SlashedPersistence s t := by
  unfold Consensus.processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact refl _)
    | exact initiateValidatorExit (liftAccessor_ok.mp ok)
    | exact requestPartialWithdrawal ok

private theorem queueExcessActiveBalance {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.queueExcessActiveBalance s electra index = .ok t) :
    SlashedPersistence s t := by
  simp only [Consensus.queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact of_data
  · cases ok; exact refl _

private theorem switchToCompoundingValidator {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.switchToCompoundingValidator s electra index = .ok t) :
    SlashedPersistence s t := by
  simp only [Consensus.switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, found, _, set, queued⟩ := ok
  exact (setValidator found set id).trans (queueExcessActiveBalance queued)

private theorem queueConsolidation {electra : .pectra ≤ fork}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (found : s.validators.data[sourceIndex.toNat]? = some source)
    (ok : Consensus.queueConsolidation config s electra sourceIndex source targetIndex =
      .ok t) : SlashedPersistence s t := by
  simp only [Consensus.queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, pure, Except.pure] at ok
  obtain ⟨⟨churned, _⟩, churn, _, _, _, set, _, _, ok⟩ := ok
  simp only [Except.ok.injEq] at ok
  subst ok
  have same := (computeConsolidationEpochAndUpdateChurn_earliest churn).2.1
  have read : getValidator churned sourceIndex = .ok source := by
    rw [getValidator, same, found]
  exact (of_data (by rw [same])).trans ((setValidator read set id).trans of_data)

theorem processConsolidationRequest {electra : .pectra ≤ fork} {request : ConsolidationRequest}
    (early : fork < .glamsterdam)
    (ok : Consensus.processConsolidationRequest config s electra request = .ok t) :
    SlashedPersistence s t := by
  unfold Consensus.processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact refl _)
    | exact switchToCompoundingValidator (liftAccessor_ok.mp ok)
    | exact queueConsolidation (getElem?_toNat_of_ofNatChecked (by assumption)) ok

private theorem processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam} (early : fork < .glamsterdam)
    (ok : Consensus.processExecutionRequests config s body electra = .ok t) :
    SlashedPersistence s t := by
  simp only [Consensus.processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
  exact (foldlM (fun _ _ _ ok => processDepositRequest early ok) deposits).trans <|
    (foldlM (fun _ _ _ ok => processWithdrawalRequest early ok) withdrawals).trans
      (foldlM (fun _ _ _ ok => processConsolidationRequest early ok) consolidations)

private theorem updateRegistryEntry {index : Nat}
    (ok : Consensus.updateRegistryEntry config s index = .ok t) : SlashedPersistence s t := by
  simp only [Consensus.updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, queued, queue, _, set, ok⟩ := ok
  have flag : queued.slashed = v.slashed := by
    unfold queueForActivation at queue
    split at queue
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queue
      obtain ⟨_, _, rfl⟩ := queue
      rfl
    · cases queue; rfl
  have first := setValidatorAt found set (fun h => flag.trans h)
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact first.trans (initiateValidatorExit exited)
  · cases ok; exact first

private theorem activateValidator {index : ValidatorIndex}
    (ok : Consensus.activateValidator s index = .ok t) : SlashedPersistence s t := by
  simp only [Consensus.activateValidator, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, _, _, set⟩ := ok
  exact setValidator found set id

private theorem updateRegistryEntryElectra {epoch : Epoch} {index : Nat}
    (ok : Consensus.updateRegistryEntryElectra config epoch s index = .ok t) :
    SlashedPersistence s t := by
  simp only [Consensus.updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, set⟩ := ok
    exact setValidatorAt found set id
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact initiateValidatorExit exited
  split at ok
  · exact setValidatorAt found (liftAccessor_ok.mp ok) id
  · cases ok; exact refl _

theorem processRegistryUpdates (early : fork < .glamsterdam)
    (ok : Consensus.processRegistryUpdates config s = .ok t) : SlashedPersistence s t := by
  unfold Consensus.processRegistryUpdates at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact foldlM (fun _ _ _ ok => updateRegistryEntryElectra ok) ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, updated, activated⟩ := ok
    exact (foldlM (fun _ _ _ ok => updateRegistryEntry ok) updated).trans
      (foldlM (fun _ _ _ ok => activateValidator ok) activated)

private theorem passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} (early : fork < .glamsterdam) :
    ∀ {deposits : List PendingDeposit} {s : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      Consensus.passPendingDeposits config checks stop nextEpoch available s processed count
        postponed deposits = .ok pass → SlashedPersistence s pass.1.state
  | [], _, _, _, _, _, ok => by cases ok; exact refl _
  | deposit :: rest, s, processed, count, postponed, pass, ok => by
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
      exact (applyPendingDeposit early credited).trans
        (passPendingDeposits early (deposits := rest) ‹_›)
    split at ok
    · split at ok
      · cases ok
      cases ok
      exact passPendingDeposits early (deposits := rest) ‹_›
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
    exact (applyPendingDeposit early credited).trans
      (passPendingDeposits early (deposits := rest) ‹_›)

theorem processPendingDeposits {electra : .pectra ≤ fork} (early : fork < .glamsterdam)
    (ok : Consensus.processPendingDeposits config checks s electra = .ok t) :
    SlashedPersistence s t := by
  unfold Consensus.processPendingDeposits at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals exact (passPendingDeposits early ‹_›).trans of_data

theorem processPendingConsolidations {electra : .pectra ≤ fork}
    (early : fork < .glamsterdam)
    (ok : Consensus.processPendingConsolidations s electra = .ok t) : SlashedPersistence s t :=
  of_data (by rw [(processPendingConsolidations_kept ok).1])

private theorem processPendingBalances (early : fork < .glamsterdam)
    (ok : Consensus.processPendingBalances config checks s = .ok t) :
    SlashedPersistence s t := by
  unfold Consensus.processPendingBalances at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, deposited, consolidated⟩ := ok
    exact (processPendingDeposits early deposited).trans
      (processPendingConsolidations early consolidated)
  · cases ok; exact refl _

theorem processEffectiveBalanceUpdates (early : fork < .glamsterdam)
    (ok : Consensus.processEffectiveBalanceUpdates s = .ok t) : SlashedPersistence s t := by
  apply foldlM (fun _ _ _ ok => ?_) ok
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, _, _, _, _, set⟩ := ok
  exact setValidatorAt found set id

theorem processJustificationAndFinalization (early : fork < .glamsterdam)
    (ok : Consensus.processJustificationAndFinalization s = .ok t) : SlashedPersistence s t := by
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok ok
  · subst same; exact refl _
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    exact of_data (by rw [← rest])

theorem processInactivityUpdates {altair : .altair ≤ fork} (early : fork < .glamsterdam)
    (ok : Consensus.processInactivityUpdates config s altair = .ok t) :
    SlashedPersistence s t := by
  unfold Consensus.processInactivityUpdates at ok
  split at ok
  · cases ok; exact refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    exact of_data

theorem processEth1DataReset {before : fork < .hegota} (early : fork < .glamsterdam)
    (ok : Consensus.processEth1DataReset before s = .ok t) : SlashedPersistence s t := by
  simp only [Consensus.processEth1DataReset, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok <;> cases ok <;> exact of_data

private theorem applyAllDeltas {deltas : Array Gwei × Array Gwei} (early : fork < .glamsterdam)
    (ok : Consensus.applyAllDeltas s deltas = .ok t) : SlashedPersistence s t :=
  foldlM (fun _ _ _ ok => by
    simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, raised, lowered⟩ := ok
    exact (increaseBalance early raised).trans (decreaseBalance early lowered)) ok

private theorem processRewardsAndPenalties (early : fork < .glamsterdam)
    (ok : Consensus.processRewardsAndPenalties config s = .ok t) : SlashedPersistence s t := by
  unfold Consensus.processRewardsAndPenalties at ok
  split at ok
  · cases ok; exact refl _
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, _, _, applied⟩ := ok
    exact foldlM (fun _ _ _ ok => applyAllDeltas early ok) applied
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, applied⟩ := ok
    exact applyAllDeltas early applied

theorem processSlashings (early : fork < .glamsterdam)
    (ok : Consensus.processSlashings s = .ok t) : SlashedPersistence s t := by
  unfold Consensus.processSlashings at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, applied⟩ := ok
    refine foldlM (fun _ _ _ ok => ?_) applied
    unfold applySlashingPenaltyElectra at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    repeat' split at ok
    all_goals first
      | (cases ok; done)
      | (cases ok; exact refl _)
      | exact decreaseBalance early (liftAccessor_ok.mp ok)
  · refine foldlM (fun _ _ _ ok => ?_) ok
    unfold applySlashingPenalty at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    repeat' split at ok
    all_goals first
      | (cases ok; done)
      | (cases ok; exact refl _)
      | exact decreaseBalance early (liftAccessor_ok.mp ok)

private theorem historicalRoots
    (ok : processHistoricalRootsUpdate s = .ok t) : SlashedPersistence s t := by
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
    (ok : processHistoricalSummariesUpdate s capella = .ok t) : SlashedPersistence s t := by
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
      else pure looked) = .ok t) : SlashedPersistence rooted t := by
  have first : SlashedPersistence rooted synced := by
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals exact of_data
  have second : SlashedPersistence synced looked := by
    split at lookedOk
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at lookedOk
      obtain ⟨_, _, _, _, rfl⟩ := lookedOk
      exact of_data
    · cases lookedOk; exact refl _
  have third : SlashedPersistence looked t := by
    split at windowed
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at windowed
      obtain ⟨_, _, _, _, rfl⟩ := windowed
      exact of_data
    · cases windowed; exact refl _
  exact first.trans (second.trans third)

private theorem processEpochAltair {altair : .altair ≤ fork} (early : fork < .glamsterdam)
    (ok : Consensus.processEpochAltair config checks s altair = .ok t) :
    SlashedPersistence s t := by
  unfold Consensus.processEpochAltair at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, justifiedOk, _, scoredOk, _, rewardedOk, _, registeredOk, slashed, slashedOk,
    reset, resetOk, pending, pendingOk, paid, paidOk, balanced, balancedOk, cleared, clearedOk,
    mixed, mixedOk, ok⟩ := ok
  have resetKept : SlashedPersistence slashed reset := by
    split at resetOk
    · exact processEth1DataReset early resetOk
    · cases resetOk; exact refl _
  have paidKept : SlashedPersistence pending paid := by
    split at paidOk
    · simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at paidOk
      obtain ⟨_, _, rfl⟩ := paidOk
      exact of_data
    · cases paidOk; exact refl _
  have clearKept : SlashedPersistence balanced cleared := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
    exact of_data
  have mixKept : SlashedPersistence cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    exact of_data
  have head := (processJustificationAndFinalization early justifiedOk).trans <|
    (processInactivityUpdates early scoredOk).trans <|
    (processRewardsAndPenalties early rewardedOk).trans <|
    (processRegistryUpdates early registeredOk).trans <|
    (processSlashings early slashedOk).trans <| resetKept.trans <|
    (processPendingBalances early pendingOk).trans <| paidKept.trans <|
    (processEffectiveBalanceUpdates early balancedOk).trans <| clearKept.trans mixKept
  split at ok <;> simp only [bind_ok_iff] at ok <;>
    obtain ⟨_, roots, _, sync, _, look, window⟩ := ok
  · exact head.trans ((historicalSummaries roots).trans (epochTail sync look window))
  · exact head.trans ((historicalRoots roots).trans (epochTail sync look window))

theorem processEpoch (early : fork < .glamsterdam)
    (ok : Consensus.processEpoch config checks s = .ok t) : SlashedPersistence s t := by
  unfold Consensus.processEpoch at ok
  split at ok
  · exact processEpochAltair early ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, justified, _, rewarded, _, registered, _, slashed, _, reset, balanced,
    balancedOk, cleared, clearOk, mixed, mixOk, rooted, rootOk, rotated⟩ := ok
  have clearKept : SlashedPersistence balanced cleared := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearOk
    exact of_data
  have mixKept : SlashedPersistence cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixOk
    exact of_data
  have last : SlashedPersistence rooted t := by
    unfold processParticipationRecordUpdates at rotated
    split at rotated
    · cases rotated
    · cases rotated; exact of_data
  exact (processJustificationAndFinalization early justified).trans <|
    (processRewardsAndPenalties early rewarded).trans <|
    (processRegistryUpdates early registered).trans <| (processSlashings early slashed).trans <|
    (processEth1DataReset early reset).trans <|
    (processEffectiveBalanceUpdates early balancedOk).trans <|
    clearKept.trans <| mixKept.trans <| (historicalRoots rootOk).trans last

theorem processSlot (early : fork < .glamsterdam)
    (ok : Consensus.processSlot s = .ok t) : SlashedPersistence s t := by
  obtain ⟨_, _, _, _, same⟩ := processSlot_ok ok
  exact of_data (by rw [same])

theorem advanceSlot (early : fork < .glamsterdam)
    (ok : Consensus.advanceSlot config checks s = .ok t) : SlashedPersistence s t := by
  obtain ⟨_, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  have second : SlashedPersistence cached epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact processEpoch early epochedOk
    · cases epochedOk; exact refl _
  exact (processSlot early cachedOk).trans (second.trans of_data)

private theorem applyWithdrawal {withdrawal : Withdrawal} (early : fork < .glamsterdam)
    (ok : Consensus.applyWithdrawal s withdrawal = .ok t) : SlashedPersistence s t := by
  unfold Consensus.applyWithdrawal at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, set⟩ := ok
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact of_data
  · exact decreaseBalance early ok

private theorem applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals} (early : fork < .glamsterdam)
    (ok : Consensus.applyExpectedWithdrawals s capella expected = .ok t) :
    SlashedPersistence s t := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  unfold Consensus.applyExpectedWithdrawals at ok
  simp only [notGloas, ↓reduceDIte] at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := ok
  have one : SlashedPersistence s applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact foldlM (fun _ _ _ ok => applyWithdrawal early ok) appliedOk
  have two : SlashedPersistence applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact of_data
    · cases indexedOk; exact refl _
  have partials : ∀ kept : BeaconState preset fork,
      SlashedPersistence kept (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals kept electra expected.processedPartialWithdrawalsCount
      else kept) := by
    intro kept
    split <;> exact of_data
  have lastKept : SlashedPersistence finished t := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last; exact of_data
  cases sweptOk
  exact one.trans (two.trans ((partials _).trans lastKept))

private theorem processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (early : fork < .glamsterdam)
    (ok : Consensus.processWithdrawals s capella payload = .ok t) : SlashedPersistence s t := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [Consensus.processWithdrawals, notGloas, ↓reduceDIte, bind_ok_iff,
    ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, applied⟩ := ok
  exact applyExpectedWithdrawals early applied

private theorem executionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (ok : processExecutionPayload config engine s body bellatrix = .ok t) :
    SlashedPersistence s t := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
  exact of_data

theorem processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork} (early : fork < .glamsterdam)
    (ok : Consensus.processBlockExecution config checks engine s body bellatrix = .ok t) :
    SlashedPersistence s t := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [Consensus.processBlockExecution, notGloas, ↓reduceDIte] at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, paid⟩ := ok
    exact (processWithdrawals early withdrawn).trans (executionPayload paid)
  · split at ok
    · exact executionPayload ok
    · cases ok; exact refl _

theorem processBlockHeader {block : BeaconBlock preset fork} (early : fork < .glamsterdam)
    (ok : Consensus.processBlockHeader s block = .ok t) : SlashedPersistence s t := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq ok
  exact of_data

theorem processRandao {body : BeaconBlockBody preset fork} (early : fork < .glamsterdam)
    (ok : Consensus.processRandao config checks s body = .ok t) : SlashedPersistence s t := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq ok
  exact of_data

theorem processEth1Data {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    (early : fork < .glamsterdam)
    (ok : Consensus.processEth1Data before s body = .ok t) : SlashedPersistence s t := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq ok
  exact of_data (by rw [← rest])

theorem processAttestation {attestation : Attestation preset fork} {parentSlot : Slot}
    (early : fork < .glamsterdam)
    (ok : Consensus.processAttestation config checks s parentSlot attestation = .ok t) :
    SlashedPersistence s t := by
  unfold Consensus.processAttestation at ok
  split at ok
  · unfold processAttestationAltair at ok
    simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := ok
    have last : SlashedPersistence raised t := by
      split at final
      · rw [recordPaymentWeight_eq final]; exact of_data
      · cases final; exact refl _
    have flagged : ∀ (current : Bool) (participation : EpochParticipation preset fork),
        SlashedPersistence s (setEpochParticipation s current participation) := by
      intro current participation
      unfold setEpochParticipation
      split <;> exact of_data
    exact (flagged _ _).trans ((increaseBalance early raisedOk).trans last)
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := ok
  have kept := recordPendingAttestation_ok recorded
  split at kept <;>
  · obtain ⟨_, rest⟩ := kept
    exact of_data (by rw [← rest])

theorem processSyncAggregate {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (early : fork < .glamsterdam)
    (ok : Consensus.processSyncAggregate config checks s altair aggregate = .ok t) :
    SlashedPersistence s t := by
  unfold Consensus.processSyncAggregate at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := ok
  rw [← Array.foldlM_toList] at folded
  exact foldlM (fun _ _ _ ok => by
    unfold applySyncReward at ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, raised, _, _, paid⟩ := ok
      exact (increaseBalance early raised).trans (increaseBalance early paid)
    · exact decreaseBalance early (liftAccessor_ok.mp ok)) folded

private theorem operations {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (early : fork < .glamsterdam)
    (ok : processOperations config checks s body parentSlot = .ok t) : SlashedPersistence s t := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [processOperations, notGloas, ↓reduceDIte, bind_ok_iff, ensure_ok_iff,
    ← Array.foldlM_toList] at ok
  obtain ⟨_, _, _, _, _, proposers, _, attesters, _, attested, _, deposits, exited,
    exits, changed, changes, requests⟩ := ok
  have changesKept : SlashedPersistence exited changed := by
    unfold processBlsToExecutionChanges at changes
    split at changes
    · rw [← Array.foldlM_toList] at changes
      exact foldlM (fun _ _ _ ok => processBlsToExecutionChange early ok) changes
    · cases changes; exact refl _
  have requestsKept : SlashedPersistence changed t := by
    split at requests
    · exact processExecutionRequests early requests
    · cases requests; exact refl _
  exact (foldlM (fun _ _ _ ok => processProposerSlashing early ok) proposers).trans <|
    (foldlM (fun _ _ _ ok => processAttesterSlashing early ok) attesters).trans <|
    (foldlM (fun _ _ _ ok => processAttestation early ok) attested).trans <|
    (foldlM (fun _ _ _ ok => processDeposit early ok) deposits).trans <|
    (foldlM (fun _ _ _ ok => processVoluntaryExit early ok) exits).trans <|
    changesKept.trans requestsKept

theorem processBlock {block : BeaconBlock preset fork} (early : fork < .glamsterdam)
    (ok : Consensus.processBlock config checks engine s block = .ok t) :
    SlashedPersistence s t := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  unfold Consensus.processBlock at ok
  split at ok
  · simp only [processBlockAltair, notGloas, ↓reduceDIte, bind_ok_iff] at ok
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := ok
    have paidKept : SlashedPersistence s paid := by
      cases paidOk; exact refl _
    have executedKept : SlashedPersistence headed executed := by
      split at executedOk
      · exact processBlockExecution early executedOk
      · cases executedOk; exact refl _
    have votedKept : SlashedPersistence revealed voted := by
      split at votedOk
      · exact processEth1Data early votedOk
      · cases votedOk; exact refl _
    exact paidKept.trans <| (processBlockHeader early headedOk).trans <|
      executedKept.trans <| (processRandao early revealedOk).trans <|
      votedKept.trans <| (operations early operatedOk).trans (processSyncAggregate early synced)
  simp only [bind_ok_iff] at ok
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := ok
  exact (processBlockHeader early headerOk).trans <| (processRandao early randaoOk).trans <|
    (processEth1Data early eth1Ok).trans (operations early operationsOk)

private theorem queuePreActivation {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.queuePreActivation s electra index = .ok t) : SlashedPersistence s t := by
  simp only [Consensus.queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨v, found, _, _, _, _, _, set₁, _, set₂, rfl⟩ := ok
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  exact (of_data (s := s)).trans ((setValidator (old := v) (by exact found) set₂ id).trans of_data)

theorem upgradeNext {s : ForkedBeaconState preset}
    {result : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (early : result.val.fork < .glamsterdam)
    (ok : Consensus.upgradeNext config checks s = .ok result) :
    SlashedPersistence s.state result.val.state := by
  obtain ⟨fork, state⟩ := s
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
    exact (of_data (s := state)).trans (head.trans tail)
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact of_data (upgradeToFulu_spec upgraded).1
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.lt_irrefl _ early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim ((by decide : ¬Fork.hegota < Fork.glamsterdam) early)

theorem processUpgrades {s t : ForkedBeaconState preset} (early : t.fork < .glamsterdam)
    (ok : Consensus.processUpgrades config checks s = .ok t) :
    SlashedPersistence s.state t.state := by
  fun_induction Consensus.processUpgrades config checks s generalizing t with
  | case1 s due ih =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
    -- Fork monotonicity puts every intermediate upgrade before the final fork bound.
    exact (upgradeNext (Nat.lt_of_le_of_lt (processUpgrades_fork_le rest) early) nextOk).trans
      (ih next early rest)
  | case2 s notDue => cases ok; exact refl _

end SlashedPersistence

theorem Step.slashedPersistence {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (early : y.fork < .glamsterdam) :
    SlashedPersistence x.state y.state := by
  cases step with
  | block engine signed due ok =>
    exact SlashedPersistence.processBlock early (applySignedBlock_ok ok).2.1
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    exact (SlashedPersistence.advanceSlot
      (Nat.lt_of_le_of_lt (processUpgrades_fork_le upgrades) early) slotOk).trans
      (SlashedPersistence.processUpgrades early upgrades)

theorem Run.slashedPersistence {x y : ForkedBeaconState preset}
    (run : Run config checks x y) (early : y.fork < .glamsterdam) :
    SlashedPersistence x.state y.state := by
  induction run with
  | nil => exact SlashedPersistence.refl _
  | snoc pre step ih =>
    exact (ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early)).trans
      (step.slashedPersistence early)

end EthLib.Consensus
