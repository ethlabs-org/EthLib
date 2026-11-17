module

public import EthLib.Consensus.Proofs.Transition.BalanceDrift
public import EthLib.Consensus.Proofs.Transition.EpochUpdates
public import EthLib.Consensus.Proofs.Transition.Trace
public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.Operations
public import EthLib.Consensus.Proofs.Transition.PendingConsolidations
public import EthLib.Consensus.Proofs.Transition.RewardDeltas
public import EthLib.Consensus.Proofs.Mutators
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.ChainRoots
import EthLib.Consensus.Proofs.Transition.Committees
import EthLib.Consensus.Proofs.Transition.DepositCarry
import EthLib.Consensus.Proofs.Transition.EpochDecomposition
import EthLib.Consensus.Proofs.Transition.EpochPending
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.Requests
import EthLib.Consensus.Proofs.Transition.ValidatorCaps
import EthLib.Consensus.Proofs.Transition.Withdrawals

/-!
# The rise of the effective balances over the end of an epoch

The effective balances of the validators active in the next epoch rise by at most a gain.

A validator below its largest effective balance rises only past the upward band.

It then rises by at most its balance, which the branch and the epoch transition bound.

A validator at its largest effective balance rises only after a change of credentials.

The epoch also moves balance to other validators.

Those transfers are deposits within the churn, due consolidations, proposer and whistleblower rewards.

Each goes to a bounded number of recipients, and each recipient adds at most the upward band.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-! ## The rise of an effective balance over the end of an epoch -/

/-! ### Slashes, assigned exits and withdrawal epochs inside one epoch -/

/-- A later record of a validator keeps its slash and its assigned exit.

Once the exit is assigned, the withdrawal epoch only rises, and only a slash moves it. -/
private def RiseWd (v w : Validator) : Prop :=
  (v.slashed = true → w.slashed = true) ∧
    (v.exitEpoch ≠ FAR_FUTURE_EPOCH → w.exitEpoch = v.exitEpoch ∧
      v.withdrawableEpoch ≤ w.withdrawableEpoch ∧
        (w.slashed = true ∨ w.withdrawableEpoch = v.withdrawableEpoch))

/-- A record with the same slash, exit and withdrawal epoch is a later record. -/
private theorem RiseWd.of_eq {v w : Validator} (slashed : w.slashed = v.slashed)
    (exit : w.exitEpoch = v.exitEpoch) (withdrawable : w.withdrawableEpoch = v.withdrawableEpoch) :
    RiseWd v w :=
  ⟨fun h => slashed.trans h, fun _ => ⟨exit, withdrawable ▸ UInt64.le_refl _, .inr withdrawable⟩⟩

/-- Later records compose. -/
private theorem RiseWd.trans {u v w : Validator} (one : RiseWd u v) (two : RiseWd v w) :
    RiseWd u w := by
  refine ⟨two.1 ∘ one.1, fun assigned => ?_⟩
  obtain ⟨exit, le, moved⟩ := one.2 assigned
  obtain ⟨exit', le', moved'⟩ := two.2 (by rw [exit]; exact assigned)
  refine ⟨exit'.trans exit, UInt64.le_trans le le', ?_⟩
  rcases moved' with slashed | same
  · exact .inl slashed
  · rcases moved with slashed | same'
    · exact .inl (two.1 slashed)
    · exact .inr (same.trans same')

/-- Each validator of a state has a later record at its position in another state. -/
private def RiseKeep {f g : Fork} (s : BeaconState preset f) (t : BeaconState preset g) : Prop :=
  ∀ (i : ℕ) (v : Validator), s.validators.data[i]? = some v →
    ∃ w, t.validators.data[i]? = some w ∧ RiseWd v w

/-- The same registry keeps every record. -/
private theorem RiseKeep.of_data {f g : Fork} {s : BeaconState preset f}
    {t : BeaconState preset g} (same : t.validators.data = s.validators.data) : RiseKeep s t :=
  fun _ v found => ⟨v, by rw [same]; exact found, RiseWd.of_eq rfl rfl rfl⟩

/-- Kept records compose. -/
private theorem RiseKeep.trans {f g h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset g} {u : BeaconState preset h} (one : RiseKeep s t)
    (two : RiseKeep t u) : RiseKeep s u := by
  intro i v found
  obtain ⟨w, read, step⟩ := one i v found
  obtain ⟨x, read', step'⟩ := two i w read
  exact ⟨x, read', step.trans step'⟩

/-- Writing a later record at a position keeps every record. -/
private theorem RiseKeep.setAt {f : Fork} {s t : BeaconState preset f} {i : ℕ}
    {old v : Validator} (found : getValidatorAt s i = .ok old)
    (set : s.setValidatorAt i v = .ok t) (step : RiseWd old v) : RiseKeep s t := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldEq : s.validators.data[i] = old := by simpa [getValidatorAt, inside] using found
  intro j w read
  by_cases same : j = i
  · subst j
    have eq : w = old := by simpa [Array.getElem?_eq_getElem inside, oldEq] using read.symm
    subst w
    refine ⟨v, ?_, step⟩
    simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, inside]
  · refine ⟨w, ?_, RiseWd.of_eq rfl rfl rfl⟩
    simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, same, Ne.symm same] using read

/-- Writing a later record at an index keeps every record. -/
private theorem RiseKeep.set {f : Fork} {s t : BeaconState preset f} {i : ValidatorIndex}
    {old v : Validator} (found : getValidator s i = .ok old)
    (written : s.setValidator i v = .ok t) (step : RiseWd old v) : RiseKeep s t :=
  RiseKeep.setAt (by rwa [← getValidator_eq_getValidatorAt])
    (by rwa [← setValidator_eq_setValidatorAt]) step

/-- Appending a validator keeps every record. -/
private theorem RiseKeep.append {f : Fork} {s t : BeaconState preset f} {v : Validator}
    (added : t.validators.data = s.validators.data.push v) : RiseKeep s t := by
  intro i old found
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  refine ⟨old, ?_, RiseWd.of_eq rfl rfl rfl⟩
  simpa [added, Array.getElem?_push, Nat.ne_of_lt inside] using found

/-- Starting an exit assigns it only to a validator without one. -/
private theorem RiseKeep.exit {f : Fork} {s t : BeaconState preset f} {i : ValidatorIndex}
    (ok : initiateValidatorExit config s i = .ok t) : RiseKeep s t := by
  obtain ⟨v, found, ⟨_, rfl⟩ | ⟨far, queued, _, _, queue, _, written⟩⟩ :=
    initiateValidatorExit_ok ok
  · exact RiseKeep.of_data rfl
  · have same := (exitQueue_validators queue).1
    exact (RiseKeep.of_data (congrArg (·.data) same)).trans
      (RiseKeep.set ((getValidator_of_validators_eq same i).trans found) written
        ⟨id, fun assigned => absurd far assigned⟩)

/-- A slashing marks the validator and only delays its withdrawal. -/
private theorem RiseKeep.slash {f : Fork} {s t : BeaconState preset f} {i : ValidatorIndex}
    {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config s i whistleblower = .ok t) : RiseKeep s t := by
  obtain ⟨exited, validator, withdrawal, marked, _, _, _, _, _, _, _, last, exitedOk,
    found, _, markedOk, _, _, _, lowered, _, _, raised, final, done⟩ := slashValidator_ok ok
  have same := (slashValidator_last (last := last) (after := t) (index := i)
    (by subst done; rfl)).1.trans ((increaseBalance_validators final).trans
    ((increaseBalance_validators raised).trans (decreaseBalance_validators lowered)))
  have step : RiseWd validator { validator with
      slashed := true
      withdrawableEpoch := max validator.withdrawableEpoch withdrawal } := by
    refine ⟨fun _ => rfl, fun _ => ⟨rfl, ?_, .inl rfl⟩⟩
    show validator.withdrawableEpoch ≤ max validator.withdrawableEpoch withdrawal
    rw [UInt64.max_def]
    split
    · assumption
    · exact UInt64.le_refl _
  exact (RiseKeep.exit exitedOk).trans ((RiseKeep.set found markedOk step).trans
    (RiseKeep.of_data (congrArg (·.data) same)))

/-! ### The pending consolidations inside one epoch -/

/-- The queue keeps a list, and each other entry has a source that exits after an epoch. -/
private def QueueFrom (L : List PendingConsolidation) (e : Epoch) {f : Fork}
    (s : BeaconState preset f) : Prop :=
  ∀ electra : .pectra ≤ f, (∀ c ∈ L, c ∈ (s.pendingConsolidations electra).data.toList) ∧
    ∀ c ∈ (s.pendingConsolidations electra).data.toList, c ∈ L ∨
      ∃ w, s.validators.data[c.sourceIndex.toNat]? = some w ∧ e < w.exitEpoch ∧
        w.exitEpoch ≠ FAR_FUTURE_EPOCH

/-- A step that keeps the queue and every record keeps the property of the queue. -/
private theorem QueueFrom.kept {f : Fork} {s t : BeaconState preset f}
    {L : List PendingConsolidation} {e : Epoch} (holds : QueueFrom L e s) (keep : RiseKeep s t)
    (queue : .pectra ≤ f → SamePendingQueue s t) : QueueFrom L e t := by
  intro electra
  obtain ⟨old, new⟩ := holds electra
  rw [show t.pendingConsolidations electra = s.pendingConsolidations electra from
    congrFun (queue electra) electra]
  refine ⟨old, fun c member => ?_⟩
  rcases new c member with listed | ⟨w, read, later, assigned⟩
  · exact .inl listed
  · obtain ⟨w', read', step⟩ := keep _ w read
    obtain ⟨exit, -, -⟩ := step.2 assigned
    exact .inr ⟨w', read', by rw [exit]; exact later, by rw [exit]; exact assigned⟩

/-- A block step keeps the slot, every record, and the property of the queue up to now. -/
private def RiseStep {f : Fork} (s t : BeaconState preset f) : Prop :=
  t.slot = s.slot ∧ RiseKeep s t ∧
    ∀ L e, e ≤ getCurrentEpoch s → QueueFrom L e s → QueueFrom L e t

/-- A step that keeps the slot, every record and the queue. -/
private theorem RiseStep.of_same {f : Fork} {s t : BeaconState preset f} (slot : t.slot = s.slot)
    (keep : RiseKeep s t) (queue : .pectra ≤ f → SamePendingQueue s t) : RiseStep s t :=
  ⟨slot, keep, fun _ _ _ holds => holds.kept keep queue⟩

/-- A step that keeps the slot, the registry and the queue. -/
private theorem RiseStep.of_data {f : Fork} {s t : BeaconState preset f} (slot : t.slot = s.slot)
    (same : t.validators.data = s.validators.data)
    (queue : .pectra ≤ f → SamePendingQueue s t) : RiseStep s t :=
  RiseStep.of_same slot (RiseKeep.of_data same) queue

/-- Steps compose. -/
private theorem RiseStep.trans {f : Fork} {s u t : BeaconState preset f} (one : RiseStep s u)
    (two : RiseStep u t) : RiseStep s t := by
  refine ⟨two.1.trans one.1, one.2.1.trans two.2.1, fun L e le holds => ?_⟩
  have epoch : getCurrentEpoch u = getCurrentEpoch s := by simp only [getCurrentEpoch, one.1]
  exact two.2.2 L e (epoch ▸ le) (one.2.2 L e le holds)

/-- A fold of steps is a step. -/
private theorem RiseStep.fold {f : Fork} {s t : BeaconState preset f} {α ε : Type}
    {step : BeaconState preset f → α → Except ε (BeaconState preset f)} {xs : List α}
    (kept : ∀ a item b, step a item = .ok b → RiseStep a b)
    (ok : xs.foldlM step s = .ok t) : RiseStep s t :=
  foldlM_ok_invariant (RiseStep s)
    (fun _ _ _ prior computed => prior.trans (kept _ _ _ computed))
    (RiseStep.of_data rfl rfl fun _ => rfl) ok

/-! ### The steps of a block keep the records and the queue -/

section RiseSteps

variable {f : Fork} {s t : BeaconState preset f}

/-- A proposer slashing slashes one validator. -/
private theorem riseStep_processProposerSlashing {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t) : RiseStep s t := by
  have frame := frame_processProposerSlashing ok
  refine RiseStep.of_same frame.slot ?_ (fun _ => SamePendingQueue.proposer ok)
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact RiseKeep.slash slashed

/-- An attester slashing slashes some validators. -/
private theorem riseStep_processAttesterSlashing {slashing : AttesterSlashing preset f}
    (ok : processAttesterSlashing config checks s slashing = .ok t) : RiseStep s t := by
  have frame := frame_processAttesterSlashing ok
  refine RiseStep.of_same frame.slot ?_ (fun _ => SamePendingQueue.attester ok)
  have one {a b : BeaconState preset f × Bool} {i : ValidatorIndex}
      (ok : slashIfSlashable config a i = .ok b) : RiseKeep a.1 b.1 := by
    obtain ⟨u, flag⟩ := a
    simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨_, slashed, rfl⟩ := ok
      exact RiseKeep.slash slashed
    · cases ok; exact RiseKeep.of_data rfl
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  exact foldlM_ok_invariant (fun x : BeaconState preset f × Bool => RiseKeep s x.1)
    (fun _ _ _ prior ok => prior.trans (one ok)) (RiseKeep.of_data rfl) folded

/-- An attestation keeps the registry. -/
private theorem riseStep_processAttestation {attestation : Attestation preset f} {parent : Slot}
    (ok : processAttestation config checks s parent attestation = .ok t) : RiseStep s t :=
  RiseStep.of_data (frame_processAttestation ok).slot
    (congrArg (·.data) (processAttestation_registry ok).1)
    (fun electra => SamePendingQueue.attestation electra ok)

/-- A pending deposit raises a balance or appends a validator. -/
private theorem riseKeep_applyPendingDeposit {deposit : PendingDeposit}
    (ok : applyPendingDeposit config checks s deposit = .ok t) : RiseKeep s t := by
  unfold applyPendingDeposit at ok
  split at ok
  · split at ok
    · cases ok; exact RiseKeep.of_data rfl
    simp only [bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · exact RiseKeep.append (addValidatorToRegistry_validators_eq_push ok)
    · cases ok; exact RiseKeep.of_data rfl
  · simp only [liftAccessor_ok, bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact RiseKeep.of_data (congrArg (·.data) (increaseBalance_validators ok))

/-- A deposit of a block raises a balance, appends a validator or queues a pending deposit. -/
private theorem riseStep_processDeposit {before : f < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) : RiseStep s t := by
  refine RiseStep.of_same (frame_processDeposit ok).slot ?_
    (fun electra => SamePendingQueue.deposit electra ok)
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok ok
  refine (RiseKeep.of_data (t := { s with eth1DepositIndex := fun _ => next }) rfl).trans ?_
  unfold applyDeposit at applied
  split at applied
  · unfold applyDepositElectra at applied
    split at applied
    · simp only [bind_ok_iff] at applied
      obtain ⟨_, _, applied⟩ := applied
      split at applied
      · simp only [bind_ok_iff, liftAccessor_ok] at applied
        obtain ⟨middle, added, queued⟩ := applied
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq queued
        exact (RiseKeep.append (addValidatorToRegistry_validators_eq_push added)).trans
          (RiseKeep.of_data (s := middle) rfl)
      · cases applied; exact RiseKeep.of_data rfl
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp applied)
      exact RiseKeep.of_data rfl
  · exact riseKeep_applyPendingDeposit applied

/-- A voluntary exit starts an exit. -/
private theorem riseStep_processVoluntaryExit {signed : SignedVoluntaryExit}
    (ok : processVoluntaryExit config checks s signed = .ok t) : RiseStep s t := by
  refine RiseStep.of_same (frame_processVoluntaryExit ok).slot ?_
    (fun _ => SamePendingQueue.voluntary ok)
  unfold processVoluntaryExit at ok
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
  exact RiseKeep.exit exited

/-- A change of credentials keeps the slash, the exit and the withdrawal epoch. -/
private theorem riseStep_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) : RiseStep s t := by
  refine RiseStep.of_same (frame_processBlsToExecutionChange ok).slot ?_
    (fun _ => SamePendingQueue.bls ok)
  obtain ⟨_, found, _, _, _, written⟩ := processBlsToExecutionChange_ok ok
  exact RiseKeep.set found written (RiseWd.of_eq rfl rfl rfl)

/-- A deposit request only queues a pending deposit. -/
private theorem riseStep_processDepositRequest {electra : .pectra ≤ f} {request : DepositRequest}
    (ok : processDepositRequest s electra request = .ok t) : RiseStep s t :=
  RiseStep.of_data (frame_processDepositRequest ok).slot
    (congrArg (·.data) (processDepositRequest_ok ok).2.1)
    (fun _ => SamePendingQueue.depositRequest ok)

/-- A partial withdrawal request keeps the registry. -/
private theorem riseKeep_requestPartialWithdrawal {electra : .pectra ≤ f}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (ok : requestPartialWithdrawal config s electra index validator amount owed = .ok t) :
    RiseKeep s t := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    have same := (computeExitEpochAndUpdateChurn_earliest churned).2.1
    exact RiseKeep.of_data (by rw [← same])
  · cases ok; exact RiseKeep.of_data rfl

/-- A withdrawal request starts an exit or queues a partial withdrawal. -/
private theorem riseStep_processWithdrawalRequest {electra : .pectra ≤ f}
    {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) : RiseStep s t := by
  refine RiseStep.of_same (frame_processWithdrawalRequest ok).slot ?_
    (fun _ => SamePendingQueue.withdrawalRequest ok)
  unfold processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact RiseKeep.of_data rfl)
    | exact RiseKeep.exit (liftAccessor_ok.mp ok)
    | exact riseKeep_requestPartialWithdrawal ok

/-- A switch to compounding credentials keeps the slash, the exit and the withdrawal epoch. -/
private theorem riseStep_switchToCompoundingValidator {electra : .pectra ≤ f}
    {index : ValidatorIndex}
    (ok : switchToCompoundingValidator s electra index = .ok t) : RiseStep s t := by
  refine RiseStep.of_same (frame_switchToCompoundingValidator ok).slot ?_
    (fun _ => SamePendingQueue.compounding ok)
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, found, middle, written, queued⟩ := ok
  have rest : t.validators = middle.validators := by
    unfold queueExcessActiveBalance at queued
    simp only [bind_ok_iff] at queued
    obtain ⟨_, _, queued⟩ := queued
    split at queued
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
      obtain ⟨_, _, _, _, _, set, rfl⟩ := queued
      obtain ⟨_, rfl⟩ := setBalance_ok set
      rfl
    · cases queued; rfl
  exact (RiseKeep.set found written (RiseWd.of_eq rfl rfl rfl)).trans
    (RiseKeep.of_data (congrArg (·.data) rest))

end RiseSteps

section RiseQueue

variable {f : Fork} {s t : BeaconState preset f}

/-- A queued consolidation assigns an exit after the current epoch to a source without one. -/
private theorem riseStep_queueConsolidation {electra : .pectra ≤ f}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (found : s.validators.data[sourceIndex.toNat]? = some source)
    (far : source.exitEpoch = FAR_FUTURE_EPOCH)
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    RiseStep s t := by
  have frame := frame_queueConsolidation found ok
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at ok
  obtain ⟨⟨churned, epoch⟩, churnOk, withdrawal, added, written, set, pending, appended, final⟩ :=
    ok
  cases final
  have data := appendWithinLimit_data appended
  have churnRegistry := (computeConsolidationEpochAndUpdateChurn_earliest churnOk).2.1
  have churnQueue : churned.pendingConsolidations = s.pendingConsolidations := by
    simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churnOk
    obtain ⟨_, _, _, _, _, _, final⟩ := churnOk
    cases final; rfl
  have queueEq : written.pendingConsolidations = churned.pendingConsolidations := by
    obtain ⟨_, rfl⟩ := setValidator_ok set
    rfl
  have sum := (Uint64.addChecked_ok_iff.mp added).2
  have assigned : epoch ≠ FAR_FUTURE_EPOCH := by
    intro eq
    have bound := withdrawal.toNat_lt
    rw [eq] at sum
    have farNat : FAR_FUTURE_EPOCH.toNat = 18446744073709551615 := rfl
    rw [farNat] at sum
    omega
  have later : (getCurrentEpoch s).toNat < epoch.toNat := by
    cases first : computeActivationExitEpoch preset (getCurrentEpoch s) with
    | error =>
      simp [computeConsolidationEpochAndUpdateChurn, first, liftArith, Except.mapError, bind,
        Except.bind] at churnOk
    | ok firstEpoch =>
      have early := UInt64.le_iff_toNat_le.mp
        (computeConsolidationEpochAndUpdateChurn_first first churnOk).1
      have firstEq := (computeActivationExitEpoch_ok_iff.mp first).2
      omega
  have read : getValidator churned sourceIndex = .ok source := by
    rw [getValidator, churnRegistry, found]
  have keep : RiseKeep s written :=
    (RiseKeep.of_data (by rw [churnRegistry])).trans
      (RiseKeep.set read set ⟨id, fun h => absurd far h⟩)
  refine ⟨frame.slot, keep.trans (RiseKeep.of_data rfl), fun L e le holds => ?_⟩
  intro electra'
  obtain ⟨old, new⟩ := holds electra'
  change (∀ c ∈ L, c ∈ pending.data.toList) ∧ ∀ c ∈ pending.data.toList, c ∈ L ∨
    ∃ w, written.validators.data[c.sourceIndex.toNat]? = some w ∧ e < w.exitEpoch ∧
      w.exitEpoch ≠ FAR_FUTURE_EPOCH
  rw [data, queueEq, churnQueue, Array.toList_push]
  refine ⟨fun c member => List.mem_append_left _ (old c member), fun c member => ?_⟩
  rcases List.mem_append.mp member with member | member
  · rcases new c member with listed | ⟨w, read', bound, assignedW⟩
    · exact .inl listed
    · obtain ⟨w', read'', step⟩ := keep _ w read'
      obtain ⟨exit, -, -⟩ := step.2 assignedW
      exact .inr ⟨w', read'', by rw [exit]; exact bound, by rw [exit]; exact assignedW⟩
  · rw [List.mem_singleton] at member
    subst member
    refine .inr ⟨_, getValidator_eq_ok_iff.mp (getValidator_setValidator_self set), ?_, assigned⟩
    show e < epoch
    apply UInt64.lt_iff_toNat_lt.mpr
    have := UInt64.le_iff_toNat_le.mp le
    omega

/-- A consolidation request switches credentials or queues a consolidation. -/
private theorem riseStep_processConsolidationRequest {electra : .pectra ≤ f}
    {request : ConsolidationRequest}
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processConsolidationRequest config s electra request = .ok t) : RiseStep s t := by
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals try first
    | (cases ok; done)
    | (cases ok; exact RiseStep.of_data rfl rfl (fun _ => rfl))
    | exact riseStep_switchToCompoundingValidator (liftAccessor_ok.mp ok)
  rename_i bothFar _ _ _ _ _ _ _ _
  exact riseStep_queueConsolidation (getElem?_toNat_of_ofNatChecked (by assumption))
    (beq_iff_eq.mp ((Bool.and_eq_true _ _).mp bothFar).1) delay ok

/-- The requests of the execution layer keep the records and the queue. -/
private theorem riseStep_processExecutionRequests {body : BeaconBlockBody preset f}
    {electra : .pectra ≤ f ∧ f < .glamsterdam}
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processExecutionRequests config s body electra = .ok t) : RiseStep s t := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
  exact (RiseStep.fold (fun _ _ _ ok => riseStep_processDepositRequest ok) deposits).trans <|
    (RiseStep.fold (fun _ _ _ ok => riseStep_processWithdrawalRequest ok) withdrawals).trans
      (RiseStep.fold (fun _ _ _ ok => riseStep_processConsolidationRequest delay ok)
        consolidations)

end RiseQueue

section RiseBlock

variable {f : Fork} {s t : BeaconState preset f}

/-- The execution part of a block keeps the registry. -/
private theorem riseStep_processBlockExecution {engine : ExecutionEngine preset f}
    {body : BeaconBlockBody preset f} {bellatrix : .bellatrix ≤ f} (early : f < .glamsterdam)
    (ok : processBlockExecution config checks engine s body bellatrix = .ok t) :
    RiseStep s t := by
  refine RiseStep.of_data (frame_processBlockExecution ok).slot ?_
    (fun _ => SamePendingQueue.blockExecution early ok)
  have withdrawn {u w : BeaconState preset f} {capella : .shapella ≤ f}
      {payload : Until .glamsterdam f (ExecutionPayload preset f)}
      (ok : processWithdrawals u capella payload = .ok w) : w.validators = u.validators := by
    unfold processWithdrawals at ok
    rw [dite_eq_right (show ¬ .glamsterdam ≤ f from Nat.not_le_of_lt early)] at ok
    simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, applied⟩ := ok
    unfold applyExpectedWithdrawals at applied
    simp only [bind_ok_iff] at applied
    obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := applied
    have one : applied.validators = u.validators := by
      unfold applyWithdrawals at appliedOk
      rw [← Array.foldlM_toList] at appliedOk
      exact foldlM_ok_invariant (fun x => x.validators = u.validators)
        (fun _ _ _ prior ok => by
          unfold applyWithdrawal at ok
          split at ok
          · simp only [bind_ok_iff] at ok
            obtain ⟨_, _, set⟩ := ok
            obtain ⟨_, rfl⟩ := setBuilder_ok set
            exact prior
          · exact (decreaseBalance_validators ok).trans prior) rfl appliedOk
    have two : indexed.validators = applied.validators := by
      unfold updateNextWithdrawalIndex at indexedOk
      split at indexedOk
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
        obtain ⟨_, _, rfl⟩ := indexedOk
        rfl
      · cases indexedOk; rfl
    simp only [dite_eq_right (show ¬ .glamsterdam ≤ f from Nat.not_le_of_lt early),
      pure, Except.pure, Except.ok.injEq] at sweptOk
    subst finished
    have lastKept : w.validators = indexed.validators := by
      split at last <;>
      unfold updateNextWithdrawalValidatorIndex at last
      all_goals
        simp only [bind_ok_iff] at last
        obtain ⟨_, _, last⟩ := last
        split at last
        · cases last
        · cases last; rfl
    exact lastKept.trans (two.trans one)
  unfold processBlockExecution at ok
  rw [dite_eq_right (show ¬ .glamsterdam ≤ f from Nat.not_le_of_lt early)] at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawnOk, paid⟩ := ok
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok paid
    exact congrArg (·.data) (withdrawn withdrawnOk)
  · dsimp only at ok
    split at ok
    · obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
      rfl
    · cases ok; rfl

/-- The sync aggregate keeps the registry. -/
private theorem riseStep_processSyncAggregate {altair : .altair ≤ f}
    {aggregate : SyncAggregate preset}
    (ok : processSyncAggregate config checks s altair aggregate = .ok t) : RiseStep s t := by
  obtain ⟨balances, rfl⟩ := processSyncAggregate_eq ok
  exact RiseStep.of_data rfl rfl (fun _ => rfl)

/-- The operations of a block keep the records and the queue. -/
private theorem riseStep_processOperations {body : BeaconBlockBody preset f} {parent : Slot}
    (early : f < .glamsterdam) (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processOperations config checks s body parent = .ok t) : RiseStep s t := by
  unfold processOperations at ok
  rw [dite_eq_right (show ¬ .glamsterdam ≤ f from Nat.not_le_of_lt early)] at ok
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, _, _, _, _, proposers, _, attesters, _, attested, _, deposits, exited,
    exits, changed, changes, requests⟩ := ok
  have c : RiseStep exited changed := by
    unfold processBlsToExecutionChanges at changes
    split at changes
    · rw [← Array.foldlM_toList] at changes
      exact RiseStep.fold (fun _ _ _ ok => riseStep_processBlsToExecutionChange ok) changes
    · cases changes; exact RiseStep.of_data rfl rfl (fun _ => rfl)
  have r : RiseStep changed t := by
    split at requests
    · exact riseStep_processExecutionRequests delay requests
    · cases requests; exact RiseStep.of_data rfl rfl (fun _ => rfl)
  exact (RiseStep.fold (fun _ _ _ ok => riseStep_processProposerSlashing ok) proposers).trans <|
    (RiseStep.fold (fun _ _ _ ok => riseStep_processAttesterSlashing ok) attesters).trans <|
    (RiseStep.fold (fun _ _ _ ok => riseStep_processAttestation ok) attested).trans <|
    (RiseStep.fold (fun _ _ _ ok => riseStep_processDeposit ok) deposits).trans <|
    (RiseStep.fold (fun _ _ _ ok => riseStep_processVoluntaryExit ok) exits).trans <|
    c.trans r

/-- A block before Gloas keeps the records and the queue. -/
private theorem riseStep_processBlock {engine : ExecutionEngine preset f}
    {block : BeaconBlock preset f} (early : f < .glamsterdam)
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processBlock config checks engine s block = .ok t) : RiseStep s t := by
  have header {u w : BeaconState preset f} (headed : processBlockHeader u block = .ok w) :
      RiseStep u w := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headed
    exact RiseStep.of_data rfl rfl (fun _ => rfl)
  have randao {u w : BeaconState preset f} (revealed : processRandao config checks u block.body =
      .ok w) : RiseStep u w := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealed
    exact RiseStep.of_data rfl rfl (fun _ => rfl)
  have vote {u w : BeaconState preset f} {before : f < .hegota}
      (voted : processEth1Data before u block.body = .ok w) : RiseStep u w := by
    obtain ⟨_, _, rest⟩ := processEth1Data_eq voted
    exact RiseStep.of_data (by rw [← rest]) (by rw [← rest]) (fun _ => by
      unfold SamePendingQueue
      rw [← rest])
  unfold processBlock at ok
  split at ok
  · unfold processBlockAltair at ok
    simp only [stateBeforeOperations, bind_assoc, bind_ok_iff] at ok
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, operated, operatedOk, synced⟩ := ok
    rw [dite_eq_right (show ¬ .glamsterdam ≤ f from Nat.not_le_of_lt early)] at paidOk
    cases paidOk
    have e : RiseStep headed executed := by
      split at executedOk
      · exact riseStep_processBlockExecution early executedOk
      · cases executedOk; exact RiseStep.of_data rfl rfl (fun _ => rfl)
    have v : RiseStep revealed voted := by
      split at votedOk
      · exact vote votedOk
      · cases votedOk; exact RiseStep.of_data rfl rfl (fun _ => rfl)
    exact (header headedOk).trans <| e.trans <| (randao revealedOk).trans <| v.trans <|
      (riseStep_processOperations early delay operatedOk).trans
        (riseStep_processSyncAggregate synced)
  · rename_i notAltair
    have notGloas : ¬ Fork.glamsterdam ≤ f :=
      fun h => notAltair (Nat.le_trans (by decide) h)
    have notBellatrix : ¬ Fork.bellatrix ≤ f :=
      fun h => notAltair (Nat.le_trans (by decide) h)
    have beforeHeze : f < .hegota := Nat.lt_trans (Nat.lt_of_not_le notAltair) (by decide)
    simp only [stateBeforeOperations, notGloas, notBellatrix, beforeHeze, ↓reduceDIte,
      pure_bind, bind_assoc, bind_ok_iff] at ok
    obtain ⟨headed, headedOk, revealed, revealedOk, voted, votedOk, operated⟩ := ok
    exact (header headedOk).trans <| (randao revealedOk).trans <| (vote votedOk).trans
      (riseStep_processOperations early delay operated)

end RiseBlock


/-- Inside one epoch before Gloas, records stay later and the queue keeps its property. -/
private theorem run_riseKeep {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (same : getCurrentEpoch y.state = getCurrentEpoch x.state)
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    RiseKeep x.state y.state ∧ ∀ L, QueueFrom L (getCurrentEpoch x.state) x.state →
      QueueFrom L (getCurrentEpoch x.state) y.state :=
  Run.induction_of_same_epoch
    (fun w _ => RiseKeep x.state w.state ∧ ∀ L, QueueFrom L (getCurrentEpoch x.state) x.state →
      QueueFrom L (getCurrentEpoch x.state) w.state)
    ⟨RiseKeep.of_data rfl, fun _ h => h⟩
    (fun _ _ _ ok pre early prior => by
      have step := riseStep_processBlock early delay (applySignedBlock_ok ok).2.1
      have le := currentEpoch_le_of_chainSteps pre.chainSteps
      exact ⟨prior.1.trans step.2.1, fun L holds => step.2.2 L _ le (prior.2 L holds)⟩)
    (fun _ _ lastEq cachedOk _ prior => by
      subst lastEq
      obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
      exact prior)
    tail early same

end EthLib.Consensus
