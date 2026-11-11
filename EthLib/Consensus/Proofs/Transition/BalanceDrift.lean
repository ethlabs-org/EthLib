module

public import EthLib.Consensus.Proofs.Transition.Trace
public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Consensus.Proofs.Transition.EpochUpdates
public import EthLib.Consensus.Proofs.Transition.Genesis
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Effective-balance changes from the actual balance path

Loss uses initial slack, balance debits and rounding; gain uses initial excess and credits.

An epoch's effective-balance update reads its intermediate balance, before later upgrades.

For this reason a slot's balance path includes that intermediate state, not just its endpoints.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

def actualBalanceAt (s : ForkedBeaconState preset) (i : Nat) : Nat :=
  ((s.state.balances.data[i]?).map (·.toNat)).getD 0

def effectiveAt (s : ForkedBeaconState preset) (i : Nat) : Nat :=
  ((s.state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0

/-- Include the state before fork upgrades, where the effective balance was last updated. -/
def _root_.EthLib.Consensus.Step.balancePath {x y : ForkedBeaconState preset}
    (step : Step config checks x y) :
    List (ForkedBeaconState preset) :=
  match step with
  | .block _ _ _ _ => [x, y]
  | .slot _ => match (advanceSlot config checks x.state).toOption with
    | none => [x, y]
    | some s => [x, ⟨x.fork, s⟩, y]

def _root_.EthLib.Consensus.Run.balancePath {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → List (ForkedBeaconState preset)
  | _, .nil => [x]
  | _, .snoc pre step => pre.balancePath ++ step.balancePath

def pathCredits (i : Nat) : List (ForkedBeaconState preset) → Nat
  | x :: y :: rest => (actualBalanceAt y i - actualBalanceAt x i) + pathCredits i (y :: rest)
  | _ => 0

def pathDebits (i : Nat) : List (ForkedBeaconState preset) → Nat
  | x :: y :: rest => (actualBalanceAt x i - actualBalanceAt y i) + pathDebits i (y :: rest)
  | _ => 0

structure CapOrder (preset : Preset) : Prop where
  activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE
  compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA

theorem reachable_effective_alignment {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (aligned : MaxEffectiveBalancesAligned preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (early : x.fork < .glamsterdam) (v : Validator) (found : v ∈ x.state.validators.data.toList) :
    v.effectiveBalance.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
  have _ := increment
  have _ := early
  have invariant {y : ForkedBeaconState preset} (trace : Run config checks g y) :
      Invariant y.state := by
    induction trace with
    | nil =>
      obtain ⟨_, _, _, ok⟩ := genesis
      exact (initializeBeaconStateFromEth1_invariant ok).2
    | snoc pre step ih =>
      cases step with
      | slot ok => exact (advanceSlotAcross_invariant ih ok).1
      | block engine signed due ok =>
        exact (frame_processBlock (applySignedBlock_ok ok).2.1).invariant ih
  have whole := (invariant run).aligned aligned v (by simpa using found)
  have numeric := congrArg UInt64.toNat whole
  simpa only [UInt64.toNat_mod, UInt64.reduceToNat] using numeric

private def EffectiveKept {f h : Fork} (s : BeaconState preset f)
    (t : BeaconState preset h) : Prop :=
  ∀ i, i < s.validators.data.size → effectiveAt ⟨h, t⟩ i = effectiveAt ⟨f, s⟩ i

private theorem effectiveKept_refl {f : Fork} (s : BeaconState preset f) : EffectiveKept s s :=
  fun _ _ => rfl

private theorem effectiveKept_trans {f h k : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} {u : BeaconState preset k}
    (one : EffectiveKept s t) (two : EffectiveKept t u)
    (grows : s.validators.data.size ≤ t.validators.data.size) : EffectiveKept s u :=
  fun i inside => (two i (Nat.lt_of_lt_of_le inside grows)).trans (one i inside)

private theorem effectiveKept_data {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} (same : t.validators.data = s.validators.data := by rfl) :
    EffectiveKept s t := by
  intro i _
  simp only [effectiveAt, same]

private theorem effectiveKept_setValidatorAt {f : Fork} {s t : BeaconState preset f}
    {index : Nat} {old v : Validator} (found : getValidatorAt s index = .ok old)
    (set : s.setValidatorAt index v = .ok t)
    (same : v.effectiveBalance = old.effectiveBalance) : EffectiveKept s t := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have read : s.validators.data[index]? = some old := by
    simpa [getValidatorAt, inside] using found
  intro i _
  by_cases eq : i = index
  · subst i
    simp [effectiveAt, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      read, same]
  · simp [effectiveAt, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Ne.symm eq]

private theorem effectiveKept_setValidator {f : Fork} {s t : BeaconState preset f}
    {index : ValidatorIndex} {old v : Validator} (found : getValidator s index = .ok old)
    (set : s.setValidator index v = .ok t)
    (same : v.effectiveBalance = old.effectiveBalance) : EffectiveKept s t :=
  effectiveKept_setValidatorAt (by rwa [← getValidator_eq_getValidatorAt])
    (by rwa [← setValidator_eq_setValidatorAt]) same

private theorem effectiveKept_increase {f : Fork} {s t : BeaconState preset f}
    {index amount : UInt64} (ok : increaseBalance s index amount = .ok t) : EffectiveKept s t :=
  effectiveKept_data (congrArg (·.data) (increaseBalance_validators ok))

private theorem effectiveKept_decrease {f : Fork} {s t : BeaconState preset f}
    {index amount : UInt64} (ok : decreaseBalance s index amount = .ok t) : EffectiveKept s t :=
  effectiveKept_data (congrArg (·.data) (decreaseBalance_validators ok))

private theorem effectiveKept_exit {f : Fork} {s t : BeaconState preset f}
    {index : ValidatorIndex} (ok : initiateValidatorExit config s index = .ok t) :
    EffectiveKept s t := by
  obtain ⟨v, found, unchanged | ⟨_, queued, epoch, withdrawal, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]; exact effectiveKept_refl _
  · have same := (exitQueue_validators queue).1
    exact effectiveKept_trans (effectiveKept_data (congrArg (·.data) same))
      (effectiveKept_setValidator (old := v)
        (by rw [getValidator_of_validators_eq same]; exact found) set rfl)
      (by rw [same])

private theorem effectiveKept_slash {f : Fork} {s t : BeaconState preset f}
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config s index whistleblower = .ok t) : EffectiveKept s t := by
  obtain ⟨_, _, _, marked, _, _, slashings, _, _, _, _, last, exited, found, _, set,
    _, _, _, lowered, _, _, raised, paid, rfl⟩ := slashValidator_ok ok
  have first := effectiveKept_trans (effectiveKept_exit exited)
    (effectiveKept_setValidator found set rfl) (frame_initiateValidatorExit exited).registryGrows
  have second := effectiveKept_trans (effectiveKept_decrease lowered)
    (effectiveKept_trans (effectiveKept_increase raised) (effectiveKept_increase paid)
      (frame_increaseBalance raised).registryGrows) (frame_decreaseBalance lowered).registryGrows
  have middle := effectiveKept_trans (effectiveKept_data (s := marked)
    (t := { marked with slashings })) second (Nat.le_refl _)
  have total := effectiveKept_trans first middle
    ((frame_initiateValidatorExit exited).registryGrows.trans
      (Nat.le_of_eq (sameSizes_setValidator set).1.symm))
  split <;> exact total

private theorem effectiveKept_fold {f : Fork} {s t : BeaconState preset f}
    {α ε : Type} {step : BeaconState preset f → α → Except ε _} {xs : List α}
    (kept : ∀ a b c, step a b = .ok c → EffectiveKept a c)
    (grows : ∀ a b c, step a b = .ok c → a.validators.data.size ≤ c.validators.data.size)
    (ok : xs.foldlM step s = .ok t) : EffectiveKept s t := by
  have result := foldlM_ok_invariant
    (fun t => EffectiveKept s t ∧ s.validators.data.size ≤ t.validators.data.size)
    (fun a b c previous computed =>
      ⟨effectiveKept_trans previous.1 (kept a b c computed) previous.2,
        previous.2.trans (grows a b c computed)⟩)
    ⟨effectiveKept_refl s, Nat.le_refl _⟩ ok
  exact result.1

private theorem effectiveKept_add {f : Fork} {s t : BeaconState preset f}
    {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (ok : addValidatorToRegistry s key credentials amount = .ok t) : EffectiveKept s t := by
  intro i inside
  simp [effectiveAt, addValidatorToRegistry_validators_eq_push ok, Array.getElem?_push,
    Nat.ne_of_lt inside]

private theorem effectiveKept_deposit {f : Fork} {s t : BeaconState preset f}
    {deposit : PendingDeposit}
    (ok : applyPendingDeposit config checks s deposit = .ok t) : EffectiveKept s t := by
  unfold applyPendingDeposit at ok
  split at ok
  · split at ok
    · cases ok; exact effectiveKept_refl _
    simp only [bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · exact effectiveKept_add ok
    · cases ok; exact effectiveKept_refl _
  · simp only [liftAccessor_ok, bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact effectiveKept_increase ok

private theorem effectiveKept_applyDeposit {f : Fork} {s t : BeaconState preset f}
    {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    {signature : Cryptography.Bls.BLSSignature}
    (ok : applyDeposit config checks s key credentials amount signature = .ok t) :
    EffectiveKept s t := by
  unfold applyDeposit at ok
  split at ok
  · unfold applyDepositElectra at ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨middle, added, queued⟩ := ok
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq queued
        exact effectiveKept_trans (effectiveKept_add added) (effectiveKept_data rfl)
          (frame_addValidatorToRegistry added).registryGrows
      · cases ok; exact effectiveKept_refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp ok)
      exact effectiveKept_refl _
  · exact effectiveKept_deposit ok

private theorem effectiveKept_processDeposit {f : Fork} {s t : BeaconState preset f}
    {before : f < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) : EffectiveKept s t := by
  obtain ⟨_, _, next, _, credited⟩ := processDeposit_ok ok
  exact effectiveKept_trans (effectiveKept_data (s := s)
    (t := { s with eth1DepositIndex := fun _ => next }))
    (effectiveKept_applyDeposit credited) (Nat.le_refl _)

private theorem effectiveKept_registryEntry {f : Fork} {s t : BeaconState preset f}
    {index : Nat} (ok : updateRegistryEntry config s index = .ok t) : EffectiveKept s t := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, queued, queue, marked, set, ok⟩ := ok
  have same : queued.effectiveBalance = v.effectiveBalance := by
    unfold queueForActivation at queue
    split at queue
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queue
      obtain ⟨_, _, rfl⟩ := queue
      rfl
    · cases queue; rfl
  have first := effectiveKept_setValidatorAt found set same
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact effectiveKept_trans first (effectiveKept_exit exited)
      (Nat.le_of_eq (sameSizes_setValidatorAt set).1.symm)
  · cases ok; exact first

private theorem effectiveKept_activate {f : Fork} {s t : BeaconState preset f}
    {index : ValidatorIndex} (ok : activateValidator s index = .ok t) : EffectiveKept s t := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, _, _, set⟩ := ok
  exact effectiveKept_setValidator found set rfl

private theorem effectiveKept_registryElectra {f : Fork} {s t : BeaconState preset f}
    {epoch : Epoch} {index : Nat}
    (ok : updateRegistryEntryElectra config epoch s index = .ok t) : EffectiveKept s t := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, set⟩ := ok
    exact effectiveKept_setValidatorAt found set rfl
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact effectiveKept_exit exited
  split at ok
  · exact effectiveKept_setValidatorAt found (liftAccessor_ok.mp ok) rfl
  · cases ok; exact effectiveKept_refl _

private theorem effectiveKept_registry {f : Fork} {s t : BeaconState preset f}
    (ok : processRegistryUpdates config s = .ok t) : EffectiveKept s t := by
  unfold processRegistryUpdates at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact effectiveKept_fold (fun _ _ _ => effectiveKept_registryElectra)
      (fun _ _ _ ok => (frame_updateRegistryEntryElectra ok).registryGrows) ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, updated, activated⟩ := ok
    exact effectiveKept_trans
      (effectiveKept_fold (fun _ _ _ => effectiveKept_registryEntry)
        (fun _ _ _ ok => (frame_updateRegistryEntry ok).registryGrows) updated)
      (effectiveKept_fold (fun _ _ _ => effectiveKept_activate)
        (fun _ _ _ ok => (frame_activateValidator ok).registryGrows) activated)
      (foldlM_ok_invariant (fun t => s.validators.data.size ≤ t.validators.data.size)
        (fun _ _ _ previous ok => previous.trans (frame_updateRegistryEntry ok).registryGrows)
        (Nat.le_refl _) updated)

private theorem effectiveKept_excess {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {index : ValidatorIndex}
    (ok : queueExcessActiveBalance s electra index = .ok t) : EffectiveKept s t := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact effectiveKept_refl _
  · cases ok; exact effectiveKept_refl _

private theorem effectiveKept_compounding {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {index : ValidatorIndex}
    (ok : switchToCompoundingValidator s electra index = .ok t) : EffectiveKept s t := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, found, _, set, queued⟩ := ok
  exact effectiveKept_trans (effectiveKept_setValidator found set rfl)
    (effectiveKept_excess queued) (Nat.le_of_eq (sameSizes_setValidator set).1.symm)

private theorem effectiveKept_consolidate {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (found : s.validators.data[sourceIndex.toNat]? = some source)
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    EffectiveKept s t := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, Base.Uint64.addChecked_ok_iff, pure, Except.pure] at ok
  obtain ⟨⟨churnedState, exitEpoch⟩, churned, withdrawal, _, marked, set, _, _, ok⟩ := ok
  simp only [Except.ok.injEq] at ok
  subst ok
  have validators := (computeConsolidationEpochAndUpdateChurn_earliest churned).2.1
  have read : getValidator churnedState sourceIndex = .ok source := by
    rw [getValidator, validators, found]
  exact effectiveKept_trans (effectiveKept_data (by rw [validators]))
    (effectiveKept_trans (effectiveKept_setValidator read set rfl) (effectiveKept_data rfl)
      (Nat.le_of_eq (sameSizes_setValidator set).1.symm)) (by rw [validators])

private theorem effectiveKept_consolidationRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t) : EffectiveKept s t := by
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact effectiveKept_refl _)
    | exact effectiveKept_compounding (liftAccessor_ok.mp ok)
    | exact effectiveKept_consolidate (getElem?_toNat_of_ofNatChecked (by assumption)) ok

private theorem effectiveKept_partial {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {index : ValidatorIndex} {v : Validator} {amount owed : Gwei}
    (ok : requestPartialWithdrawal config s electra index v amount owed = .ok t) :
    EffectiveKept s t := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    exact effectiveKept_data (by rw [(computeExitEpochAndUpdateChurn_earliest churned).2.1])
  · cases ok; exact effectiveKept_refl _

private theorem effectiveKept_withdrawalRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) : EffectiveKept s t := by
  unfold processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact effectiveKept_refl _)
    | exact effectiveKept_exit (liftAccessor_ok.mp ok)
    | exact effectiveKept_partial ok

private theorem effectiveKept_depositRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : DepositRequest}
    (ok : processDepositRequest s electra request = .ok t) : EffectiveKept s t := by
  obtain ⟨start, recorded⟩ := recordDepositRequestsStart_eq (state := s) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit,
    bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  exact effectiveKept_refl _

private theorem effectiveKept_requests {f : Fork} {s t : BeaconState preset f}
    {body : BeaconBlockBody preset f} {electra : .pectra ≤ f ∧ f < .glamsterdam}
    (ok : processExecutionRequests config s body electra = .ok t) : EffectiveKept s t := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨deposited, deposits, withdrawn, withdrawals, consolidations⟩ := ok
  have first := effectiveKept_fold (fun _ _ _ => effectiveKept_depositRequest)
    (fun _ _ _ ok => (registryLifecycle_processDepositRequest ok).size_le) deposits
  have grows := RegistryLifecycle.foldlM
    (fun _ _ _ ok => registryLifecycle_processDepositRequest ok) deposits
  have second := effectiveKept_fold (fun _ _ _ => effectiveKept_withdrawalRequest)
    (fun _ _ _ ok => (registryLifecycle_processWithdrawalRequest ok).size_le) withdrawals
  have grows' := RegistryLifecycle.foldlM
    (fun _ _ _ ok => registryLifecycle_processWithdrawalRequest ok) withdrawals
  exact effectiveKept_trans first (effectiveKept_trans second
    (effectiveKept_fold (fun _ _ _ => effectiveKept_consolidationRequest)
      (fun _ _ _ ok => (registryLifecycle_processConsolidationRequest ok).size_le) consolidations)
    grows'.size_le) grows.size_le

private theorem effectiveKept_withdrawals {f : Fork} {s t : BeaconState preset f}
    {capella : .shapella ≤ f} {payload : Until .glamsterdam f (ExecutionPayload preset f)}
    (ok : processWithdrawals s capella payload = .ok t) : EffectiveKept s t := by
  have applied {s t : BeaconState preset f} {expected : ExpectedWithdrawals}
      (ok : applyExpectedWithdrawals s capella expected = .ok t) : EffectiveKept s t := by
    unfold applyExpectedWithdrawals at ok
    simp only [bind_ok_iff] at ok
    obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := ok
    have one : EffectiveKept s applied := by
      unfold applyWithdrawals at appliedOk
      rw [← Array.foldlM_toList] at appliedOk
      refine effectiveKept_fold (fun _ _ _ ok => ?_)
        (fun _ _ _ ok => (registryLifecycle_applyWithdrawal ok).size_le) appliedOk
      unfold applyWithdrawal at ok
      split at ok
      · simp only [bind_ok_iff] at ok
        obtain ⟨_, _, set⟩ := ok
        obtain ⟨_, rfl⟩ := setBuilder_ok set
        exact effectiveKept_refl _
      · exact effectiveKept_decrease ok
    have indexedSame : indexed.validators = applied.validators := by
      unfold updateNextWithdrawalIndex at indexedOk
      split at indexedOk
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
        obtain ⟨_, _, rfl⟩ := indexedOk
        rfl
      · cases indexedOk; rfl
    have sweptSame : finished.validators = indexed.validators := by
      have swept {a : BeaconState preset f}
          (computed : (if gloas : .glamsterdam ≤ f then
            updateNextWithdrawalBuilderIndex a gloas expected.processedBuildersSweepCount
            else pure a) = .ok finished) : finished.validators = a.validators := by
        split at computed
        · unfold updateNextWithdrawalBuilderIndex at computed
          dsimp only at computed
          split at computed
          · cases computed; rfl
          · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
            obtain ⟨_, _, rfl⟩ := computed
            rfl
        · cases computed; rfl
      rw [swept sweptOk]
      split <;> (try split) <;> rfl
    have lastSame : t.validators = finished.validators := by
      unfold updateNextWithdrawalValidatorIndex at last
      simp only [bind_ok_iff] at last
      obtain ⟨_, _, last⟩ := last
      split at last
      · cases last
      · cases last; rfl
    intro i inside
    simpa only [effectiveAt, lastSame, sweptSame, indexedSame] using one i inside
  unfold processWithdrawals at ok
  split at ok
  · split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, appliedOk⟩ := ok
      exact applied appliedOk
    · cases ok; exact effectiveKept_refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, appliedOk⟩ := ok
    exact applied appliedOk

private theorem effectiveKept_sync {f : Fork} {s t : BeaconState preset f}
    {altair : .altair ≤ f} {aggregate : SyncAggregate preset}
    (ok : processSyncAggregate config checks s altair aggregate = .ok t) : EffectiveKept s t := by
  unfold processSyncAggregate at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := ok
  rw [← Array.foldlM_toList] at folded
  refine effectiveKept_fold (fun _ _ _ ok => ?_)
    (fun _ _ _ ok => (frame_applySyncReward ok).registryGrows) folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact effectiveKept_trans (effectiveKept_increase raised) (effectiveKept_increase paid)
      (frame_increaseBalance raised).registryGrows
  · exact effectiveKept_decrease (liftAccessor_ok.mp ok)

private theorem effectiveKept_proposerSlashing {f : Fork} {s t : BeaconState preset f}
    {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t) : EffectiveKept s t := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact effectiveKept_slash slashed

private theorem effectiveKept_attesterSlashing {f : Fork} {s t : BeaconState preset f}
    {slashing : AttesterSlashing preset f}
    (ok : processAttesterSlashing config checks s slashing = .ok t) : EffectiveKept s t := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  have result := foldlM_ok_invariant
    (fun step => EffectiveKept s step.1 ∧ s.validators.data.size ≤ step.1.validators.data.size)
    (fun step _ next before ok => ?_)
    (show EffectiveKept s (s, false).1 ∧ s.validators.data.size ≤ (s, false).1.validators.data.size
      from ⟨effectiveKept_refl _, Nat.le_refl _⟩) folded
  · exact result.1
  · obtain ⟨middle, slashedAny⟩ := step
    simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨_, slashed, rfl⟩ := ok
      exact ⟨effectiveKept_trans before.1 (effectiveKept_slash slashed) before.2,
        before.2.trans (frame_slashValidator slashed).registryGrows⟩
    · cases ok; exact before

private theorem effectiveKept_voluntaryExit {f : Fork} {s t : BeaconState preset f}
    {signed : SignedVoluntaryExit}
    (ok : processVoluntaryExit config checks s signed = .ok t) : EffectiveKept s t := by
  unfold processVoluntaryExit at ok
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
  exact effectiveKept_exit exited

private theorem effectiveKept_blsChange {f : Fork} {s t : BeaconState preset f}
    {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) : EffectiveKept s t := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact effectiveKept_setValidator found set rfl

private theorem effectiveKept_operations {f : Fork} {s t : BeaconState preset f}
    (early : f < .glamsterdam) {body : BeaconBlockBody preset f} {parentSlot : Slot}
    (ok : processOperations config checks s body parentSlot = .ok t) : EffectiveKept s t := by
  unfold processOperations at ok
  split at ok
  · rename_i later
    exact False.elim (Nat.not_le_of_lt early later)
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, _, _, _, _, proposers, _, attesters, _, attestations, _, deposits, exited,
    exits, changed, changesOk, requestsOk⟩ := ok
  have changes : EffectiveKept exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact effectiveKept_fold (fun _ _ _ => effectiveKept_blsChange)
        (fun _ _ _ ok => (frame_processBlsToExecutionChange ok).registryGrows) changesOk
    · cases changesOk; exact effectiveKept_refl _
  have requests : EffectiveKept changed t := by
    split at requestsOk
    · exact effectiveKept_requests requestsOk
    · cases requestsOk; exact effectiveKept_refl _
  have compose {a b c : BeaconState preset f} (one : EffectiveKept a b)
      (two : EffectiveKept b c) (size : a.validators.data.size ≤ b.validators.data.size) :=
    effectiveKept_trans one two size
  apply compose (effectiveKept_fold (fun _ _ _ => effectiveKept_proposerSlashing)
    (fun _ _ _ ok => (frame_processProposerSlashing ok).registryGrows) proposers)
  · apply compose (effectiveKept_fold (fun _ _ _ => effectiveKept_attesterSlashing)
      (fun _ _ _ ok => (frame_processAttesterSlashing ok).registryGrows) attesters)
    · apply compose (effectiveKept_fold
        (fun _ _ _ ok => effectiveKept_data (by rw [(processAttestation_registry ok).1]))
        (fun _ _ _ ok => (frame_processAttestation ok).registryGrows) attestations)
      · apply compose (effectiveKept_fold (fun _ _ _ => effectiveKept_processDeposit)
          (fun _ _ _ ok => (frame_processDeposit ok).registryGrows) deposits)
        · apply compose (effectiveKept_fold (fun _ _ _ => effectiveKept_voluntaryExit)
            (fun _ _ _ ok => (frame_processVoluntaryExit ok).registryGrows) exits)
          · apply compose changes requests
            unfold processBlsToExecutionChanges at changesOk
            split at changesOk
            · rw [← Array.foldlM_toList] at changesOk
              exact (RegistryLifecycle.foldlM
                (fun _ _ _ ok => registryLifecycle_processBlsToExecutionChange ok) changesOk).size_le
            · cases changesOk; exact Nat.le_refl _
          · exact (RegistryLifecycle.foldlM
              (fun _ _ _ ok => registryLifecycle_processVoluntaryExit ok) exits).size_le
        · exact (RegistryLifecycle.foldlM
            (fun _ _ _ ok => registryLifecycle_processDeposit ok) deposits).size_le
      · exact (RegistryLifecycle.foldlM
          (fun _ _ _ ok => registryLifecycle_processAttestation ok) attestations).size_le
    · exact (RegistryLifecycle.foldlM
        (fun _ _ _ ok => registryLifecycle_processAttesterSlashing ok) attesters).size_le
  · exact (RegistryLifecycle.foldlM
      (fun _ _ _ ok => registryLifecycle_processProposerSlashing ok) proposers).size_le

private theorem effectiveKept_block {f : Fork} {s t : BeaconState preset f}
    {engine : ExecutionEngine preset f} {block : BeaconBlock preset f}
    (early : f < .glamsterdam) (ok : processBlock config checks engine s block = .ok t) :
    EffectiveKept s t := by
  have header {a b : BeaconState preset f} {block : BeaconBlock preset f}
      (ok : processBlockHeader a block = .ok b) : b.validators = a.validators := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq ok
    rfl
  have randao {a b : BeaconState preset f} {body : BeaconBlockBody preset f}
      (ok : processRandao config checks a body = .ok b) : b.validators = a.validators := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq ok
    rfl
  have vote {a b : BeaconState preset f} {body : BeaconBlockBody preset f} {before : f < .hegota}
      (ok : processEth1Data before a body = .ok b) : b.validators = a.validators := by
    obtain ⟨_, _, rest⟩ := processEth1Data_eq ok
    rw [← rest]
  have execution {a b : BeaconState preset f} {body : BeaconBlockBody preset f}
      {bellatrix : .bellatrix ≤ f}
      (ok : processBlockExecution config checks engine a body bellatrix = .ok b) :
      EffectiveKept a b := by
    have payload {a b : BeaconState preset f} {bellatrix : .bellatrix ≤ f ∧ f < .glamsterdam}
        (ok : processExecutionPayload config engine a body bellatrix = .ok b) :
        b.validators = a.validators := by
      obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
      rfl
    unfold processBlockExecution at ok
    split at ok
    · exact False.elim (Nat.not_le_of_lt early (by assumption))
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, withdrawn, paid⟩ := ok
      intro i inside
      simpa only [effectiveAt, payload paid] using effectiveKept_withdrawals withdrawn i inside
    · dsimp only at ok
      split at ok
      · exact effectiveKept_data (congrArg (·.data) (payload ok))
      · cases ok; exact effectiveKept_refl _
  unfold processBlock at ok
  split at ok
  · unfold processBlockAltair at ok
    simp only [bind_ok_iff] at ok
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, operated, operatedOk, synced⟩ := ok
    have paidSame : paid = s := by
      split at paidOk
      · exact False.elim (Nat.not_le_of_lt early (by assumption))
      · cases paidOk; rfl
    subst paid
    have executionStep : EffectiveKept headed executed := by
      split at executedOk
      · exact execution executedOk
      · cases executedOk; exact effectiveKept_refl _
    have votedSame : voted.validators = revealed.validators := by
      split at votedOk
      · exact vote votedOk
      · cases votedOk; rfl
    have head : EffectiveKept s voted := by
      intro i inside
      have size : i < headed.validators.data.size := by simpa [header headedOk] using inside
      simpa only [effectiveAt, votedSame, randao revealedOk, header headedOk] using
        executionStep i size
    have grows := (frame_processBlockHeader headedOk).registryGrows.trans
      ((by
        split at executedOk
        · exact (frame_processBlockExecution executedOk).registryGrows
        · cases executedOk; exact Nat.le_refl _) :
          headed.validators.data.size ≤ executed.validators.data.size)
    have grows' : s.validators.data.size ≤ voted.validators.data.size := by
      simpa [votedSame, randao revealedOk] using grows
    exact effectiveKept_trans head
      (effectiveKept_trans (effectiveKept_operations early operatedOk) (effectiveKept_sync synced)
        (frame_processOperations operatedOk).registryGrows) grows'
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, headed, _, revealed, _, voted, operated⟩ := ok
    intro i inside
    have kept := effectiveKept_operations early operated i
      (by simpa [vote voted, randao revealed, header headed] using inside)
    simpa only [effectiveAt, vote voted, randao revealed, header headed] using kept

private theorem effectiveKept_pending {f : Fork} {s t : BeaconState preset f}
    (ok : processPendingBalances config checks s = .ok t) : EffectiveKept s t := by
  have pass {stop : PendingDeposit → Bool} {nextEpoch : Epoch} {available : Gwei} :
      ∀ {deposits : List PendingDeposit} {state : BeaconState preset f} {processed : Gwei}
        {count : Nat} {postponed : Array PendingDeposit} {result},
        passPendingDeposits config checks stop nextEpoch available state processed count
          postponed deposits = .ok result → EffectiveKept state result.1.state := by
    intro deposits
    induction deposits with
    | nil => intro state processed count postponed result ok; cases ok; exact effectiveKept_refl _
    | cons deposit rest ih =>
      intro state processed count postponed result ok
      unfold passPendingDeposits at ok
      simp only [bind, Except.bind, pure, Except.pure] at ok
      split at ok
      · cases ok; exact effectiveKept_refl _
      split at ok
      · cases ok
      split at ok
      · split at ok
        · cases ok
        rename_i credited
        split at ok
        · cases ok
        cases ok
        exact effectiveKept_trans (effectiveKept_deposit credited) (ih ‹_›)
          (registryLifecycle_applyPendingDeposit credited).size_le
      split at ok
      · split at ok
        · cases ok
        cases ok
        exact ih ‹_›
      split at ok
      · cases ok
      split at ok
      · cases ok; exact effectiveKept_refl _
      split at ok
      · cases ok
      rename_i credited
      split at ok
      · cases ok
      cases ok
      exact effectiveKept_trans (effectiveKept_deposit credited) (ih ‹_›)
        (registryLifecycle_applyPendingDeposit credited).size_le
  unfold processPendingBalances at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨middle, deposited, consolidated⟩ := ok
    have deposits : EffectiveKept s middle := by
      unfold processPendingDeposits at deposited
      simp only [bind, Except.bind, pure, Except.pure] at deposited
      repeat' (split at deposited <;> try cases deposited)
      all_goals
        intro i inside
        exact pass ‹_› i inside
    intro i inside
    simpa only [effectiveAt, (processPendingConsolidations_kept consolidated).1] using
      deposits i inside
  · cases ok; exact effectiveKept_refl _

private theorem balanceDrift_slashings {f : Fork} {s t : BeaconState preset f}
    (ok : processSlashings s = .ok t) : t.validators = s.validators := by
  have fold {step : BeaconState preset f → Nat → Except TransitionError _} {xs : List Nat}
      (kept : ∀ a i b, step a i = .ok b → b.validators = a.validators)
      (ok : xs.foldlM step s = .ok t) : t.validators = s.validators :=
    foldlM_ok_invariant (fun t => t.validators = s.validators)
      (fun _ _ _ previous ok => (kept _ _ _ ok).trans previous) rfl ok
  unfold processSlashings at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, applied⟩ := ok
    refine fold (fun _ _ _ ok => ?_) applied
    simp only [applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, _, _, lowered⟩ := ok
        exact decreaseBalance_validators lowered
      · cases ok; rfl
    · cases ok; rfl
  · refine fold (fun _ _ _ ok => ?_) ok
    simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, _, _, _, _, lowered⟩ := ok
        exact decreaseBalance_validators lowered
      · cases ok; rfl
    · cases ok; rfl

private theorem balanceDrift_reset {f : Fork} {s t : BeaconState preset f}
    {before : f < .hegota} (ok : processEth1DataReset before s = .ok t) :
    t.validators = s.validators ∧ t.balances = s.balances := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok <;> cases ok <;> exact ⟨rfl, rfl⟩

private theorem balanceDrift_inactivity {f : Fork} {s t : BeaconState preset f}
    {altair : .altair ≤ f} (ok : processInactivityUpdates config s altair = .ok t) :
    t.validators = s.validators ∧ t.balances = s.balances := by
  unfold processInactivityUpdates at ok
  split at ok
  · cases ok; exact ⟨rfl, rfl⟩
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    exact ⟨rfl, rfl⟩

private theorem balanceDrift_historical {f : Fork} {s t : BeaconState preset f}
    (ok : processHistoricalRootsUpdate s = .ok t) :
    t.validators = s.validators ∧ t.balances = s.balances := by
  unfold processHistoricalRootsUpdate at ok
  split at ok
  · cases ok
  simp only [bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    exact ⟨rfl, rfl⟩
  · cases ok; exact ⟨rfl, rfl⟩

private theorem balanceDrift_summaries {f : Fork} {s t : BeaconState preset f}
    {capella : .shapella ≤ f} (ok : processHistoricalSummariesUpdate s capella = .ok t) :
    t.validators = s.validators ∧ t.balances = s.balances := by
  unfold processHistoricalSummariesUpdate at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals exact ⟨rfl, rfl⟩

private theorem balanceDrift_epochEnd {f : Fork} {s t : BeaconState preset f}
    {altair : .altair ≤ f} {synced looked : BeaconState preset f}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates s altair)
      altair = .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ f then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ f then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok t) : t.validators = s.validators ∧ t.balances = s.balances := by
  have sync : synced.validators = s.validators ∧ synced.balances = s.balances := by
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals exact ⟨rfl, rfl⟩
  have look : looked.validators = synced.validators ∧ looked.balances = synced.balances := by
    split at lookedOk
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at lookedOk
      obtain ⟨_, _, _, _, rfl⟩ := lookedOk
      exact ⟨rfl, rfl⟩
    · cases lookedOk; exact ⟨rfl, rfl⟩
  have window : t.validators = looked.validators ∧ t.balances = looked.balances := by
    split at windowed
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at windowed
      obtain ⟨_, _, _, _, rfl⟩ := windowed
      exact ⟨rfl, rfl⟩
    · cases windowed; exact ⟨rfl, rfl⟩
  exact ⟨window.1.trans (look.1.trans sync.1), window.2.trans (look.2.trans sync.2)⟩

private theorem balanceDrift_epoch {f : Fork} {s t : BeaconState preset f}
    (early : f < .glamsterdam) (ok : processEpoch config checks s = .ok t) :
    ∃ before after, EffectiveKept s before ∧
      processEffectiveBalanceUpdates before = .ok after ∧
      t.validators = after.validators ∧ t.balances = before.balances := by
  have balances {a b : BeaconState preset f} (ok : processEffectiveBalanceUpdates a = .ok b) :
      b.balances = a.balances := by
    unfold processEffectiveBalanceUpdates at ok
    refine foldlM_ok_invariant (fun b => b.balances = a.balances)
      (fun _ _ _ previous step => ?_) rfl ok
    simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at step
    obtain ⟨_, _, _, _, _, _, set⟩ := step
    obtain ⟨_, rfl⟩ := setValidatorAt_ok set
    exact previous
  have tail {a b c d : BeaconState preset f}
      (clear : processSlashingsReset a = .ok b) (mix : processRandaoMixesReset b = .ok c)
      (same : d.validators = c.validators ∧ d.balances = c.balances) :
      d.validators = a.validators ∧ d.balances = a.balances := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clear
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mix
    exact same
  unfold processEpoch at ok
  split at ok
  · unfold processEpochAltair at ok
    simp only [bind_ok_iff] at ok
    obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
      registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk,
      balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, ok⟩ := ok
    have paidEq : paid = pending := by
      split at paidOk
      · exact False.elim (Nat.not_le_of_lt early (by assumption))
      · cases paidOk; rfl
    subst paid
    have resetSame : reset.validators = slashed.validators := by
      split at resetOk
      · exact (balanceDrift_reset resetOk).1
      · cases resetOk; rfl
    have first : EffectiveKept s pending := by
      have one := effectiveKept_trans (effectiveKept_registry registeredOk)
        (effectiveKept_trans (effectiveKept_data
          (by rw [resetSame, balanceDrift_slashings slashedOk]))
          (effectiveKept_pending pendingOk) (by rw [resetSame, balanceDrift_slashings slashedOk]))
        (registryLifecycle_processRegistryUpdates registeredOk).size_le
      intro i inside
      have same : rewarded.validators = s.validators := by
        rw [processRewardsAndPenalties_frame rewardedOk]
        exact (balanceDrift_inactivity scoredOk).1.trans
          (processJustificationAndFinalization_keeps justifiedOk).2.2.2.2.2.1
      simpa only [effectiveAt, same] using one i (by simpa [same] using inside)
    refine ⟨pending, balanced, first, balancedOk, ?_⟩
    have last : t.validators = mixed.validators ∧ t.balances = mixed.balances := by
      split at ok <;> simp only [bind_ok_iff] at ok <;>
        obtain ⟨_, rooted, _, synced, _, looked, windowed⟩ := ok
      · have endStep := balanceDrift_epochEnd synced looked windowed
        have roots := balanceDrift_summaries rooted
        exact ⟨endStep.1.trans roots.1, endStep.2.trans roots.2⟩
      · have endStep := balanceDrift_epochEnd synced looked windowed
        have roots := balanceDrift_historical rooted
        exact ⟨endStep.1.trans roots.1, endStep.2.trans roots.2⟩
    have final := tail clearedOk mixedOk last
    exact ⟨final.1, final.2.trans (balances balancedOk)⟩
  · simp only [bind_ok_iff] at ok
    obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk,
      slashed, slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk,
      mixed, mixedOk, rooted, rootedOk, rotated⟩ := ok
    have same : rewarded.validators = s.validators := by
      rw [processRewardsAndPenalties_frame rewardedOk]
      exact (processJustificationAndFinalization_keeps justifiedOk).2.2.2.2.2.1
    have first : EffectiveKept s reset := by
      intro i inside
      simpa only [effectiveAt, (balanceDrift_reset resetOk).1,
        balanceDrift_slashings slashedOk, same] using
        effectiveKept_registry registeredOk i (by simpa [same] using inside)
    have rotatedSame : t.validators = rooted.validators ∧ t.balances = rooted.balances := by
      unfold processParticipationRecordUpdates at rotated
      split at rotated
      · cases rotated
      · cases rotated; exact ⟨rfl, rfl⟩
    have roots := balanceDrift_historical rootedOk
    have final := tail clearedOk mixedOk
      ⟨rotatedSame.1.trans roots.1, rotatedSame.2.trans roots.2⟩
    exact ⟨reset, balanced, first, balancedOk, final.1, final.2.trans (balances balancedOk)⟩

private theorem balanceDrift_update_upper {f : Fork} {s t : BeaconState preset f}
    (ok : processEffectiveBalanceUpdates s = .ok t) (i : Nat) :
    effectiveAt ⟨f, t⟩ i ≤ max (effectiveAt ⟨f, s⟩ i) (actualBalanceAt ⟨f, s⟩ i) := by
  have result := foldlM_ok_invariant
    (fun t => t.balances = s.balances ∧
      effectiveAt ⟨f, t⟩ i ≤ max (effectiveAt ⟨f, s⟩ i) (actualBalanceAt ⟨f, s⟩ i))
    (fun a index b previous step => ?_)
    ⟨rfl, Nat.le_max_left _ _⟩ ok
  · exact result.2
  · simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at step
    obtain ⟨old, found, balance, read, next, updated, set⟩ := step
    obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
    refine ⟨previous.1, ?_⟩
    have found' := getValidatorAt_eq_ok_iff.mp found
    have read' := getBalanceAt_eq_ok_iff.mp read
    by_cases eq : i = index
    · subst i
      have bound := updatedEffectiveBalance_le_max updated
      have funded : balance.toNat = actualBalanceAt ⟨f, s⟩ index := by
        simp only [actualBalanceAt, ← previous.1, read', Option.map_some, Option.getD_some]
      have oldBound := previous.2
      simp only [effectiveAt, found', Option.map_some, Option.getD_some] at oldBound
      simp only [effectiveAt, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
        Array.getElem?_set_self, Option.map_some, Option.getD_some]
      rw [funded] at bound
      omega
    · simpa [effectiveAt, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
        Ne.symm eq] using previous.2

private theorem balanceDrift_slot_upper {f : Fork} {s t : BeaconState preset f}
    (early : f < .glamsterdam) (ok : advanceSlot config checks s = .ok t)
    (i : Nat) (inside : i < s.validators.data.size) :
    effectiveAt ⟨f, t⟩ i ≤ max (effectiveAt ⟨f, s⟩ i) (actualBalanceAt ⟨f, t⟩ i) := by
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨next, _, cached, cache, advanced, advance, rfl⟩ := ok
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
  unfold epochIfLast at advance
  split at advance
  · obtain ⟨before, after, kept, updated, validators, balances⟩ := balanceDrift_epoch early advance
    have bound := balanceDrift_update_upper updated i
    have same := kept i inside
    rw [same] at bound
    simpa only [effectiveAt, actualBalanceAt, validators, balances] using bound
  · cases advance
    exact Nat.le_max_left _ _

private theorem balanceDrift_upgrade_upper {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (ok : upgradeNext config checks s = .ok t) (early : t.val.fork < .glamsterdam) (i : Nat) :
    effectiveAt t.val i ≤ effectiveAt s i := by
  have reset {f : Fork} {a b : BeaconState preset f} {electra : .pectra ≤ f}
      {index : ValidatorIndex} (ok : queuePreActivation a electra index = .ok b) :
      effectiveAt ⟨f, b⟩ i ≤ effectiveAt ⟨f, a⟩ i := by
    simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, _, _, balance, _, validator, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := setBalance_ok balance
    obtain ⟨inside, rfl⟩ := setValidator_ok validator
    by_cases eq : i = index.toNat
    · subst i
      simp [effectiveAt, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set]
    · simp [effectiveAt, BeaconState.putValidator, BeaconState.putBalance,
        Serialization.Ssz.RootedForkList.data_set,
        Ne.symm eq]
  obtain ⟨fork, state⟩ := s
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [effectiveAt, (upgradeToAltair_spec upgraded).1, Nat.le_refl]
  · subst ok; exact Nat.le_refl _
  · subst ok; exact Nat.le_refl _
  · subst ok; exact Nat.le_refl _
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, _, _, _, _, _, _, _, middle, queued, compounded⟩ := upgraded
    have one := foldlM_ok_invariant
      (fun t => effectiveAt ⟨.pectra, t⟩ i ≤ effectiveAt ⟨.dencun, state⟩ i)
      (fun _ _ _ previous ok => (reset ok).trans previous) (Nat.le_refl _) queued
    refine foldlM_ok_invariant
      (fun t => effectiveAt ⟨.pectra, t⟩ i ≤ effectiveAt ⟨.dencun, state⟩ i)
      (fun a index b previous ok => ?_) one compounded
    unfold queueCompoundingExcess at ok
    split at ok
    · split at ok
      · have step := liftAccessor_ok.mp ok
        simp only [queueExcessActiveBalance, bind_ok_iff] at step
        obtain ⟨_, _, step⟩ := step
        split at step
        · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
          obtain ⟨_, _, _, _, _, set, rfl⟩ := step
          obtain ⟨_, rfl⟩ := setBalance_ok set
          exact previous
        · cases step; exact previous
      · cases ok; exact previous
    · cases ok; exact previous
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [effectiveAt, (upgradeToFulu_spec upgraded).1, Nat.le_refl]
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.lt_irrefl _ early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim ((by decide : ¬Fork.hegota < Fork.glamsterdam) early)

private theorem balanceDrift_upgrades_upper {s t : ForkedBeaconState preset}
    (ok : processUpgrades config checks s = .ok t) (early : t.fork < .glamsterdam) (i : Nat) :
    effectiveAt t i ≤ effectiveAt s i := by
  fun_induction processUpgrades config checks s generalizing t with
  | case1 s due ih =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
    exact (ih next rest early).trans (balanceDrift_upgrade_upper nextOk
      (Nat.lt_of_le_of_lt (processUpgrades_fork_le rest) early) i)
  | case2 s notDue => cases ok; exact Nat.le_refl _

private theorem balanceDrift_credits_append (i : Nat) (a b : List (ForkedBeaconState preset))
    (x : ForkedBeaconState preset) :
    pathCredits i (a ++ x :: b) = pathCredits i (a ++ [x]) + pathCredits i (x :: b) := by
  induction a with
  | nil => simp [pathCredits]
  | cons first rest ih =>
    cases rest with
    | nil => simp [pathCredits]
    | cons second rest => simpa [pathCredits, Nat.add_assoc] using ih

private theorem balanceDrift_path_last {x y : ForkedBeaconState preset}
    (run : Run config checks x y) : ∃ pre, run.balancePath = pre ++ [y] := by
  induction run with
  | nil => exact ⟨[], rfl⟩
  | @snoc middle last pre step ih =>
    cases step with
    | @block fork before after engine signed due ok =>
      exact ⟨pre.balancePath ++ [⟨fork, before⟩], by
        simp [Run.balancePath, Step.balancePath, List.append_assoc]⟩
    | slot ok =>
      obtain ⟨next, advance, upgrade⟩ := bind_ok_iff.mp ok
      exact ⟨pre.balancePath ++ [middle, ⟨middle.fork, next⟩], by
        simp [Run.balancePath, Step.balancePath, advance, Except.toOption, List.append_assoc]⟩

private theorem balanceDrift_gain {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (i : Nat) (present : i < x.state.validators.data.size) :
    max (effectiveAt y i) (actualBalanceAt y i) ≤
      max (effectiveAt x i) (actualBalanceAt x i) + pathCredits i tail.balancePath := by
  induction tail with
  | nil => simp [Run.balancePath, pathCredits]
  | @snoc middle last pre step ih =>
    have forkLe := step.chainStep.fork_le
    have middleEarly := Nat.lt_of_le_of_lt forkLe early
    have bound := ih middleEarly
    have inside := Nat.lt_of_lt_of_le present pre.registryLifecycle.size_le
    obtain ⟨initial, path⟩ := balanceDrift_path_last pre
    cases step with
    | @block fork before after engine signed due ok =>
      have kept := effectiveKept_block early (applySignedBlock_ok ok).2.1 i inside
      have credits : pathCredits i (pre.snoc (.block engine signed due ok)).balancePath =
          pathCredits i pre.balancePath +
            (actualBalanceAt ⟨fork, after⟩ i - actualBalanceAt ⟨fork, before⟩ i) := by
        simp only [Run.balancePath, Step.balancePath, path, List.append_assoc]
        simp only [List.cons_append, List.nil_append]
        rw [balanceDrift_credits_append]
        simp [pathCredits]
      rw [credits, kept]
      dsimp only at *
      omega
    | slot ok =>
      obtain ⟨next, advanced, upgraded⟩ := bind_ok_iff.mp ok
      have update := balanceDrift_slot_upper middleEarly advanced i inside
      change effectiveAt ⟨middle.fork, next⟩ i ≤
        max (effectiveAt middle i) (actualBalanceAt ⟨middle.fork, next⟩ i) at update
      have upgrade := balanceDrift_upgrades_upper upgraded early i
      have credits : pathCredits i (pre.snoc (.slot ok)).balancePath =
          pathCredits i pre.balancePath +
            ((actualBalanceAt ⟨middle.fork, next⟩ i - actualBalanceAt middle i) +
              (actualBalanceAt last i - actualBalanceAt ⟨middle.fork, next⟩ i)) := by
        simp only [Run.balancePath, Step.balancePath, advanced, Except.toOption,
          path, List.append_assoc]
        simp only [List.cons_append, List.nil_append]
        rw [balanceDrift_credits_append]
        simp [pathCredits]
      rw [credits]
      omega

theorem effective_loss_from_balance {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (early : y.fork < .glamsterdam)
    (i : Nat) (v : Validator) (found : x.state.validators.data[i]? = some v)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    effectiveAt x i - effectiveAt y i ≤
      (effectiveAt x i - actualBalanceAt x i) + pathDebits i tail.balancePath +
        (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) := by
  sorry

theorem effective_gain_from_balance {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (i : Nat) (present : i < x.state.validators.data.size) :
    effectiveAt y i - effectiveAt x i ≤
      (actualBalanceAt x i - effectiveAt x i) + pathCredits i tail.balancePath := by
  have bound := balanceDrift_gain tail early i present
  omega

/-- New keys are bounded from their actual admission balance, not a fictitious zero receipt. -/
theorem joining_growth_from_admission {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (early : y.fork < .glamsterdam)
    (i : Nat) (newKey : x.state.validators.data.size ≤ i)
    (present : i < y.state.validators.data.size) :
    effectiveAt y i ≤ pathCredits i tail.balancePath := by
  sorry

/-- A single hysteresis update loses less than one increment beyond its actual balance gap. -/
theorem hysteresis_loss (largest balance old next : Gwei)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (cap : old ≤ largest)
    (ok : updatedEffectiveBalance preset largest balance old = .ok next) :
    old.toNat - next.toNat ≤ old.toNat - balance.toNat +
      (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) := by
  rcases updatedEffectiveBalance_cases ok with rfl | rfl
  · omega
  · have rounded : balance % preset.EFFECTIVE_BALANCE_INCREMENT ≤ balance :=
      UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_mod]; exact Nat.mod_le _ _)
    have remainder := Nat.mod_lt balance.toNat increment
    have capped := UInt64.le_iff_toNat_le.mp cap
    rw [Base.Uint64.toNat_min, UInt64.toNat_sub_of_le _ _ rounded, UInt64.toNat_mod]
    omega

theorem hysteresis_gain (largest balance old next : Gwei)
    (ok : updatedEffectiveBalance preset largest balance old = .ok next) :
    next.toNat - old.toNat ≤ balance.toNat - old.toNat := by
  rcases updatedEffectiveBalance_eq_or_le ok with rfl | ⟨below, _⟩
  · omega
  · exact Nat.sub_le_sub_right (UInt64.le_iff_toNat_le.mp below) _

/-- Rounding cannot cross an aligned reference still covered by balance and cap. -/
theorem hysteresis_reference_le (reference largest balance old next : Gwei)
    (aligned : reference.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (previous : reference ≤ old) (funded : reference ≤ balance) (cap : reference ≤ largest)
    (ok : updatedEffectiveBalance preset largest balance old = .ok next) : reference ≤ next := by
  rcases updatedEffectiveBalance_cases ok with rfl | rfl
  · exact previous
  · have rounded : balance % preset.EFFECTIVE_BALANCE_INCREMENT ≤ balance :=
      UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_mod]; exact Nat.mod_le _ _)
    have quotient := Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp funded)
      (c := preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    have product := Nat.mul_le_mul_left preset.EFFECTIVE_BALANCE_INCREMENT.toNat quotient
    have referenceDivision := Nat.mod_add_div reference.toNat
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    have balanceDivision := Nat.mod_add_div balance.toNat
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    rw [aligned] at referenceDivision
    rw [UInt64.le_iff_toNat_le, Base.Uint64.toNat_min,
      UInt64.toNat_sub_of_le _ _ rounded, UInt64.toNat_mod]
    have cap := UInt64.le_iff_toNat_le.mp cap
    omega

/-- An effective-balance update cannot increase the funding held at any registry position. -/
theorem updateEffectiveBalance_funding {fork : Fork} {s t : BeaconState preset fork}
    {index : Nat} (ok : updateEffectiveBalance s index = .ok t) (i : Nat) :
    max (effectiveAt ⟨fork, t⟩ i) (actualBalanceAt ⟨fork, t⟩ i) ≤
      max (effectiveAt ⟨fork, s⟩ i) (actualBalanceAt ⟨fork, s⟩ i) := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨validator, found, balance, read, effective, updated, set⟩ := ok
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have old : s.validators.data[index]? = some validator := by
    simpa [getValidatorAt, inside] using found
  by_cases same : i = index
  · subst i
    have actual : actualBalanceAt ⟨fork, s⟩ index = balance.toNat := by
      simp [actualBalanceAt, getBalanceAt_eq_ok_iff.mp read]
    have bound := updatedEffectiveBalance_le_max updated
    simpa [effectiveAt, actualBalanceAt, BeaconState.putValidator,
      Serialization.Ssz.RootedForkList.data_set, old, ← actual] using
      (max_le bound (Nat.le_max_right validator.effectiveBalance.toNat balance.toNat))
  · simp [effectiveAt, actualBalanceAt, BeaconState.putValidator,
      Serialization.Ssz.RootedForkList.data_set, Ne.symm same]

/-- The full effective-balance pass cannot mint funding, including at inactive positions. -/
theorem processEffectiveBalanceUpdates_funding {fork : Fork} {s t : BeaconState preset fork}
    (ok : processEffectiveBalanceUpdates s = .ok t) (i : Nat) :
    max (effectiveAt ⟨fork, t⟩ i) (actualBalanceAt ⟨fork, t⟩ i) ≤
      max (effectiveAt ⟨fork, s⟩ i) (actualBalanceAt ⟨fork, s⟩ i) := by
  unfold processEffectiveBalanceUpdates at ok
  exact foldlM_ok_invariant
    (fun t => max (effectiveAt ⟨fork, t⟩ i) (actualBalanceAt ⟨fork, t⟩ i) ≤
      max (effectiveAt ⟨fork, s⟩ i) (actualBalanceAt ⟨fork, s⟩ i))
    (fun _ _ _ previous step => (updateEffectiveBalance_funding step i).trans previous)
    (Nat.le_refl _) ok

end EthLib.Consensus
