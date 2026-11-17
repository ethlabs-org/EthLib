module

public import EthLib.Consensus.Proofs.Transition.BalanceDrift
public import EthLib.Consensus.Proofs.Transition.EpochUpdates
public import EthLib.Consensus.Proofs.Transition.Trace
public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.Operations
public import EthLib.Consensus.Proofs.Transition.PendingConsolidations
public import EthLib.Consensus.Proofs.Transition.RewardDeltas
public import EthLib.Consensus.Proofs.Mutators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
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

/-! ### The records and credentials up to the update of the effective balances -/

/-- Each validator of a state has a later record with the same credentials in another state. -/
private def RecKeep {f g : Fork} (s : BeaconState preset f) (t : BeaconState preset g) : Prop :=
  ∀ (i : ℕ) (v : Validator), s.validators.data[i]? = some v →
    ∃ w, t.validators.data[i]? = some w ∧ RiseWd v w ∧
      w.withdrawalCredentials = v.withdrawalCredentials

/-- The same registry keeps every record. -/
private theorem RecKeep.of_data {f g : Fork} {s : BeaconState preset f}
    {t : BeaconState preset g} (same : t.validators.data = s.validators.data) : RecKeep s t :=
  fun _ v found => ⟨v, by rw [same]; exact found, RiseWd.of_eq rfl rfl rfl, rfl⟩

/-- Kept records compose. -/
private theorem RecKeep.trans {f g h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset g} {u : BeaconState preset h} (one : RecKeep s t)
    (two : RecKeep t u) : RecKeep s u := by
  intro i v found
  obtain ⟨w, read, step, same⟩ := one i v found
  obtain ⟨x, read', step', same'⟩ := two i w read
  exact ⟨x, read', step.trans step', same'.trans same⟩

/-- Kept records keep the records alone. -/
private theorem RecKeep.rise {f g : Fork} {s : BeaconState preset f}
    {t : BeaconState preset g} (kept : RecKeep s t) : RiseKeep s t := by
  intro i v found
  obtain ⟨w, read, step, -⟩ := kept i v found
  exact ⟨w, read, step⟩

/-- Writing a later record with the same credentials keeps every record. -/
private theorem RecKeep.setAt {f : Fork} {s t : BeaconState preset f} {i : ℕ}
    {old v : Validator} (found : getValidatorAt s i = .ok old)
    (set : s.setValidatorAt i v = .ok t) (step : RiseWd old v)
    (same : v.withdrawalCredentials = old.withdrawalCredentials) : RecKeep s t := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldEq : s.validators.data[i] = old := by simpa [getValidatorAt, inside] using found
  intro j w read
  by_cases here : j = i
  · subst j
    have eq : w = old := by simpa [Array.getElem?_eq_getElem inside, oldEq] using read.symm
    subst w
    refine ⟨v, ?_, step, same⟩
    simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, inside]
  · refine ⟨w, ?_, RiseWd.of_eq rfl rfl rfl, rfl⟩
    simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set, here, Ne.symm here] using read

/-- Starting an exit assigns it only to a validator without one, and keeps every credential. -/
private theorem RecKeep.exit {f : Fork} {s t : BeaconState preset f} {i : ValidatorIndex}
    (ok : initiateValidatorExit config s i = .ok t) : RecKeep s t := by
  obtain ⟨v, found, ⟨_, rfl⟩ | ⟨far, queued, _, _, queue, _, written⟩⟩ :=
    initiateValidatorExit_ok ok
  · exact RecKeep.of_data rfl
  · have same := (exitQueue_validators queue).1
    have read : getValidator queued i = .ok v := (getValidator_of_validators_eq same i).trans found
    rw [getValidator_eq_getValidatorAt] at read
    rw [setValidator_eq_setValidatorAt] at written
    exact (RecKeep.of_data (congrArg (·.data) same)).trans
      (RecKeep.setAt read written ⟨id, fun assigned => absurd far assigned⟩ rfl)

/-- The registry updates keep every record and every credential. -/
private theorem recKeep_processRegistryUpdates {f : Fork} {s t : BeaconState preset f}
    (ok : processRegistryUpdates config s = .ok t) : RecKeep s t := by
  have fold {α : Type} {step : BeaconState preset f → α → Except TransitionError _}
      {xs : List α} {u w : BeaconState preset f}
      (kept : ∀ a item b, step a item = .ok b → RecKeep a b)
      (ok : xs.foldlM step u = .ok w) : RecKeep u w :=
    foldlM_ok_invariant (RecKeep u) (fun _ _ _ prior computed => prior.trans (kept _ _ _ computed))
      (RecKeep.of_data rfl) ok
  unfold processRegistryUpdates at ok
  split at ok
  · obtain ⟨epoch, _, folded⟩ := bind_ok_iff.mp ok
    refine fold (fun u i w ok => ?_) folded
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨v, found, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, written⟩ := ok
      exact RecKeep.setAt found written (RiseWd.of_eq rfl rfl rfl) rfl
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, exited⟩ := ok
      exact RecKeep.exit exited
    split at ok
    · exact RecKeep.setAt found (liftAccessor_ok.mp ok) (RiseWd.of_eq rfl rfl rfl) rfl
    · cases ok; exact RecKeep.of_data rfl
  · obtain ⟨u, first, last⟩ := bind_ok_iff.mp ok
    refine (fold (fun a i b ok => ?_) first).trans (fold (fun a i b ok => ?_) last)
    · simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨validator, found, queued, queuedOk, marked, markedOk, ok⟩ := ok
      have same : RiseWd validator queued ∧
          queued.withdrawalCredentials = validator.withdrawalCredentials := by
        unfold queueForActivation at queuedOk
        split at queuedOk
        · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at queuedOk
          obtain ⟨_, _, rfl⟩ := queuedOk
          exact ⟨RiseWd.of_eq rfl rfl rfl, rfl⟩
        · simp only [pure, Except.pure, Except.ok.injEq] at queuedOk
          rw [← queuedOk]
          exact ⟨RiseWd.of_eq rfl rfl rfl, rfl⟩
      have set := RecKeep.setAt found markedOk same.1 same.2
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, exited⟩ := ok
        exact set.trans (RecKeep.exit exited)
      · simp only [pure, Except.pure, Except.ok.injEq] at ok
        exact ok ▸ set
    · simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, found, _, _, set⟩ := ok
      rw [getValidator_eq_getValidatorAt] at found
      rw [setValidator_eq_setValidatorAt] at set
      exact RecKeep.setAt found set (RiseWd.of_eq rfl rfl rfl) rfl

private theorem pendingDeposits_validators {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} (ok : processPendingDeposits config checks s electra = .ok t)
    (i : ℕ) (inside : i < s.validators.data.size) :
    t.validators.data[i]? = s.validators.data[i]? := by
  obtain ⟨_, _, applied, _, next, _, _, _, _, _, _, _, _, appliedOk, rfl⟩ :=
    processPendingDeposits_applied ok
  have kept := foldlM_ok_invariant
    (fun u : BeaconState preset f => s.validators.data.size ≤ u.validators.data.size ∧
      u.validators.data[i]? = s.validators.data[i]?)
    (fun u deposit u' previous step => by
      rcases applyPendingDeposit_cases step with rfl | ⟨index, raised⟩ | ⟨_, added⟩
      · exact previous
      · rw [increaseBalance_validators raised]
        exact previous
      · rw [addValidatorToRegistry_validators_eq_push added, Array.size_push,
          Array.getElem?_push]
        refine ⟨by omega, ?_⟩
        split
        · omega
        · exact previous.2)
    ⟨Nat.le_refl _, rfl⟩ appliedOk
  exact kept.2

/-- From Electra, the pending deposits run one pass with the churn available. -/
private theorem pendingDeposits_pass {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} (ok : processPendingDeposits config checks s electra = .ok t) :
    ∃ (churn available : Gwei) (stop : PendingDeposit → Bool)
      (pass : PendingDepositsPass preset f) (read applied moved : List PendingDeposit),
      depositChurnLimit config s = .ok churn ∧
      available.toNat = (s.depositBalanceToConsume electra).toNat + churn.toNat ∧
      PassPendingDepositsFacts config checks stop (getCurrentEpoch s + 1) available s 0 0 #[]
        (s.pendingDeposits electra).data.toList pass read applied moved ∧
      pass.processed ≤ available ∧ t.balances = pass.state.balances := by
  unfold processPendingDeposits at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals
    have added := liftAccessor_ok.mp
      ‹liftAccessor (liftArith (addChecked (getCurrentEpoch s) 1)) = .ok _›
    rw [liftArith, mapError_ok_iff, addChecked_ok_iff] at added
    obtain rfl := UInt64.toNat_inj.mp (added.2.trans (toNat_add_of_lt added.1).symm)
    have avail := liftAccessor_ok.mp
      ‹liftAccessor (liftArith (addChecked (s.depositBalanceToConsume electra) _)) = .ok _›
    rw [liftArith, mapError_ok_iff, addChecked_ok_iff] at avail
    have churned := liftAccessor_ok.mp ‹liftAccessor (depositChurnLimit config s) = .ok _›
    have passed := ‹passPendingDeposits config checks _ _ _ s 0 0 #[] _ = .ok _›
    obtain ⟨read, applied, moved, facts⟩ := passPendingDeposits_applied passed
    exact ⟨_, _, _, _, read, applied, moved, churned, avail.2, facts,
      passPendingDeposits_processed_le passed UInt64.zero_le, rfl⟩

/-- A first match in a longer registry that lies in a prefix is the first match there. -/
private theorem findIdx?_of_prefix {u s : Array Validator} {p : Validator → Bool} {k : ℕ}
    (inside : k < s.size) (same : ∀ j < s.size, u[j]? = s[j]?) (found : u.findIdx? p = some k) :
    s.findIdx? p = some k := by
  obtain ⟨lt, hit, earlier⟩ := Array.findIdx?_eq_some_iff_getElem.mp found
  have get : ∀ j (lj : j < s.size) (lu : j < u.size), u[j] = s[j] := by
    intro j lj lu
    have := same j lj
    rw [Array.getElem?_eq_getElem lu, Array.getElem?_eq_getElem lj] at this
    exact Option.some.inj this
  refine Array.findIdx?_eq_some_iff_getElem.mpr ⟨inside, ?_, fun j lt' => ?_⟩
  · rw [← get k inside lt]; exact hit
  · rw [← get j (Nat.lt_trans lt' inside) (Nat.lt_trans lt' lt)]; exact earlier j lt'

/-- The status that the pending deposits read of a key is that of its first validator. -/
private theorem depositTargetStatus_of_found {f : Fork} {s : BeaconState preset f} {next : Epoch}
    {pubkey : Cryptography.Bls.BLSPubkey} {i : ℕ} {status : Bool × Bool}
    (found : s.validators.data.findIdx? (·.pubkey == pubkey) = some i)
    (ok : depositTargetStatus s next pubkey = .ok status) :
    ∃ v, s.validators.data[i]? = some v ∧
      status = (decide (v.exitEpoch < FAR_FUTURE_EPOCH), decide (v.withdrawableEpoch < next)) := by
  unfold depositTargetStatus at ok
  rw [found] at ok
  simp only [bind, Except.bind, liftArith, Except.mapError] at ok
  split at ok
  · cases ok
  rename_i index converted
  have conv : ofNatChecked i = .ok index := by
    split at converted
    · cases converted
    · rename_i v h
      cases converted
      exact h
  obtain ⟨_, same⟩ := ofNatChecked_ok_iff.mp conv
  rw [same] at ok
  split at ok
  · rename_i v read
    cases ok
    exact ⟨v, read, rfl⟩
  · cases ok

/-- Applied deposits credit an old position only with deposits whose key first sits there. -/
private theorem appliedDeposits_balances {f : Fork} {s : BeaconState preset f} :
    ∀ (A : List PendingDeposit) (u w : BeaconState preset f), BalancesMatch u →
      s.validators.data.size ≤ u.validators.data.size →
      (∀ j < s.validators.data.size, u.validators.data[j]? = s.validators.data[j]?) →
      A.foldlM (applyPendingDeposit config checks) u = .ok w →
      ∀ i < s.validators.data.size, actualBalanceAt ⟨f, w⟩ i ≤ actualBalanceAt ⟨f, u⟩ i +
        pendingAmount (A.filter fun d =>
          s.validators.data.findIdx? (·.pubkey == d.pubkey) == some i)
  | [], u, w, _, _, _, ok, i, _ => by
    cases ok
    simp [pendingAmount]
  | d :: rest, u, w, matched, grows, same, ok, i, inside => by
    rw [List.foldlM_cons, bind_ok_iff] at ok
    obtain ⟨u1, step, ok⟩ := ok
    have matched1 := (applyPendingDeposit_kept step).1 matched
    have one : (s.validators.data.size ≤ u1.validators.data.size ∧
        ∀ j < s.validators.data.size, u1.validators.data[j]? = s.validators.data[j]?) ∧
        actualBalanceAt ⟨f, u1⟩ i ≤ actualBalanceAt ⟨f, u⟩ i +
          (if (s.validators.data.findIdx? (·.pubkey == d.pubkey) == some i) = true then
            d.amount.toNat else 0) := by
      cases known : u.validators.data.findIdx? (·.pubkey == d.pubkey) with
      | some k =>
        obtain ⟨⟨balance, raised, before, after, value⟩, others⟩ :=
          applyPendingDeposit_known_balances known step
        have validators : u1.validators = u.validators := by
          simp only [applyPendingDeposit, known, liftAccessor_ok, bind_ok_iff] at step
          obtain ⟨_, _, raised⟩ := step
          exact increaseBalance_validators raised
        refine ⟨⟨by rw [validators]; exact grows, fun j lt => by rw [validators]; exact same j lt⟩,
          ?_⟩
        by_cases here : k = i
        · subst here
          have first := findIdx?_of_prefix inside same known
          simp only [first, beq_self_eq_true, ↓reduceIte]
          simp [actualBalanceAt, before, after, value]
        · have kept : actualBalanceAt ⟨f, u1⟩ i = actualBalanceAt ⟨f, u⟩ i := by
            simp [actualBalanceAt, others i (Ne.symm here)]
          omega
      | none =>
        unfold applyPendingDeposit at step
        split at step
        · split at step
          · cases step
            exact ⟨⟨grows, same⟩, Nat.le_add_right _ _⟩
          simp only [bind_ok_iff] at step
          obtain ⟨_, _, step⟩ := step
          split at step
          · obtain ⟨validators, balances⟩ := addValidatorToRegistry_push step matched
            have small : i < u.balances.data.size := by
              have := matched; unfold BalancesMatch at this; omega
            refine ⟨⟨by rw [validators, Array.size_push]; omega, fun j lt => ?_⟩, ?_⟩
            · rw [validators, Array.getElem?_push]
              split
              · omega
              · exact same j lt
            · simp only [actualBalanceAt, balances, Array.getElem?_push, Nat.ne_of_lt small,
                ↓reduceIte]
              exact Nat.le_add_right _ _
          · cases step
            exact ⟨⟨grows, same⟩, Nat.le_add_right _ _⟩
        · rename_i position found
          rw [known] at found
          cases found
    have later := appliedDeposits_balances rest u1 w matched1 one.1.1 one.1.2 ok i inside
    have two := one.2
    simp only [List.filter_cons]
    split
    · rename_i hit
      simp only [hit, ↓reduceIte] at two
      simp only [pendingAmount, List.map_cons, List.sum_cons] at later ⊢
      omega
    · rename_i miss
      simp only [miss, Bool.false_eq_true, ↓reduceIte] at two
      omega

/-- Pending amounts grow with the filter. -/
private theorem pendingAmount_filter_le (l : List PendingDeposit) {p q : PendingDeposit → Bool}
    (le : ∀ d ∈ l, p d = true → q d = true) :
    pendingAmount (l.filter p) ≤ pendingAmount (l.filter q) := by
  induction l with
  | nil => simp [pendingAmount]
  | cons d rest ih =>
    have tail := ih (fun x member => le x (List.mem_cons_of_mem _ member))
    simp only [List.filter_cons]
    by_cases hp : p d = true
    · simp only [hp, le d List.mem_cons_self hp, ↓reduceIte, pendingAmount, List.map_cons,
        List.sum_cons] at tail ⊢
      omega
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      split
      · simp only [pendingAmount, List.map_cons, List.sum_cons] at tail ⊢
        omega
      · exact tail

/-- From Electra, the pending deposits credit at most the limit of validators per epoch.

They credit the validators that do not withdraw at most the churn available. -/
private theorem rise_pendingDeposits {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} (ok : processPendingDeposits config checks s electra = .ok t)
    (matched : BalancesMatch s) :
    ∃ (credit : ℕ → ℕ) (keys : Finset ℕ),
      keys.card ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat ∧ (∀ i ∉ keys, credit i = 0) ∧
      (∀ i < s.validators.data.size,
        actualBalanceAt ⟨f, t⟩ i ≤ actualBalanceAt ⟨f, s⟩ i + credit i) ∧
      ∀ (U : Finset ℕ) (churn : Gwei), depositChurnLimit config s = .ok churn →
        (∀ i ∈ U, ∃ v, s.validators.data[i]? = some v ∧
          ¬ v.withdrawableEpoch < getCurrentEpoch s + 1) →
        ∑ i ∈ U, credit i ≤ (s.depositBalanceToConsume electra).toNat + churn.toNat := by
  obtain ⟨churn, available, stop, pass, read, applied, moved, churned, avail, facts, within,
    balances⟩ := pendingDeposits_pass ok
  let tgt (d : PendingDeposit) := s.validators.data.findIdx? (·.pubkey == d.pubkey)
  refine ⟨fun i => pendingAmount (applied.filter fun d => tgt d == some i),
    (applied.filterMap tgt).toFinset, ?_, ?_, ?_, ?_⟩
  · refine (List.toFinset_card_le _).trans ((List.length_filterMap_le _ _).trans
      (facts.appliedSublist.length_le.trans ?_))
    have := facts.bounded
    omega
  · intro i absent
    show pendingAmount _ = 0
    have empty : (applied.filter fun d => tgt d == some i) = [] := by
      rw [List.filter_eq_nil_iff]
      intro d member hit
      apply absent
      rw [List.mem_toFinset, List.mem_filterMap]
      exact ⟨d, member, by simpa using hit⟩
    rw [empty]
    rfl
  · intro i inside
    have bound := appliedDeposits_balances applied s pass.state matched (Nat.le_refl _)
      (fun _ _ => rfl) facts.applies i inside
    simpa only [actualBalanceAt, balances] using bound
  · intro U churn' churnedOk hU
    rw [churnedOk] at churned
    cases churned
    -- The credits to the validators of `U` come from the deposits whose key first sits in `U`.
    let inU (d : PendingDeposit) : Bool := match tgt d with
      | some i => decide (i ∈ U)
      | none => false
    have split (A : List PendingDeposit) :
        ∑ i ∈ U, pendingAmount (A.filter fun d => tgt d == some i) =
          pendingAmount (A.filter inU) := by
      induction A with
      | nil => simp [pendingAmount]
      | cons d rest ih =>
        have each : ∀ i, pendingAmount ((d :: rest).filter fun d => tgt d == some i) =
            (if tgt d = some i then d.amount.toNat else 0) +
              pendingAmount (rest.filter fun d => tgt d == some i) := by
          intro i
          simp only [List.filter_cons]
          split
          · rename_i hit
            simp only [beq_iff_eq] at hit
            simp [hit, pendingAmount]
          · rename_i miss
            simp only [beq_iff_eq] at miss
            simp [miss]
        rw [Finset.sum_congr rfl (fun i _ => each i), Finset.sum_add_distrib, ih]
        simp only [List.filter_cons]
        cases hd : tgt d with
        | none => simp [inU, hd]
        | some j =>
          simp only [Option.some.injEq, Finset.sum_ite_eq, inU, hd]
          by_cases member : j ∈ U
          · simp [member, pendingAmount]
          · simp [member]
    show ∑ i ∈ U, pendingAmount (applied.filter fun d => tgt d == some i) ≤ _
    rw [split, facts.appliedFilter, List.filter_filter]
    have le := pendingAmount_filter_le read (q := fun deposit =>
        (depositTargetStatus s (getCurrentEpoch s + 1) deposit.pubkey).toOption ==
          some (false, false))
      (p := fun d => inU d && ((depositTargetStatus s (getCurrentEpoch s + 1) d.pubkey).toOption !=
          some (true, false))) (by
        intro d member both
        simp only [Bool.and_eq_true] at both
        obtain ⟨inside, applies⟩ := both
        obtain ⟨status, statusOk⟩ := facts.statusOk d member
        cases hd : tgt d with
        | none => simp [inU, hd] at inside
        | some j =>
          simp only [inU, hd, decide_eq_true_eq] at inside
          obtain ⟨v, read, rfl⟩ := depositTargetStatus_of_found hd statusOk
          obtain ⟨v', read', notWithdrawn⟩ := hU j inside
          rw [read, Option.some.injEq] at read'
          subst v'
          simp only [statusOk, Except.toOption, bne_iff_ne, ne_eq] at applies
          simp only [statusOk, Except.toOption, beq_iff_eq]
          simp only [notWithdrawn, decide_false] at applies ⊢
          cases h : decide (v.exitEpoch < FAR_FUTURE_EPOCH)
          · rfl
          · rw [h] at applies
            exact absurd rfl applies)
    have used := facts.used
    have availLe := UInt64.le_iff_toNat_le.mp within
    simp only [UInt64.toNat_zero, Nat.zero_add] at used
    omega

/-- A balance increase adds its amount at its own index and keeps every other balance. -/
private theorem actualBalanceAt_increaseBalance {fork : Fork} {u w : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei} (computed : increaseBalance u index delta = .ok w)
    (j : Nat) : actualBalanceAt ⟨fork, w⟩ j =
      actualBalanceAt ⟨fork, u⟩ j + if index.toNat = j then delta.toNat else 0 := by
  cases found : u.balances.data[j]? with
  | none =>
    obtain ⟨inside, _, rfl⟩ := increaseBalance_eq_ok_iff.mp computed
    have apart : index.toNat ≠ j := by
      rintro rfl
      rw [Array.getElem?_eq_getElem inside] at found
      cases found
    simp [actualBalanceAt, BeaconState.putBalance, found, apart]
  | some balance =>
    obtain ⟨raised, located, value⟩ := balance_increaseBalance computed found
    simp only [actualBalanceAt, found, located, Option.map_some, Option.getD_some, value]

/-- A balance decrease subtracts its amount at its own index and keeps every other balance. -/
private theorem actualBalanceAt_decreaseBalance {fork : Fork} {u w : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei} (computed : decreaseBalance u index delta = .ok w)
    (j : Nat) : actualBalanceAt ⟨fork, w⟩ j =
      actualBalanceAt ⟨fork, u⟩ j - if index.toNat = j then delta.toNat else 0 := by
  cases found : u.balances.data[j]? with
  | none =>
    obtain ⟨inside, rfl⟩ := decreaseBalance_eq_ok_iff.mp computed
    have apart : index.toNat ≠ j := by
      rintro rfl
      rw [Array.getElem?_eq_getElem inside] at found
      cases found
    simp [actualBalanceAt, BeaconState.putBalance, found, apart]
  | some balance =>
    obtain ⟨lowered, located, value⟩ := balance_decreaseBalance computed found
    simp only [actualBalanceAt, found, located, Option.map_some, Option.getD_some, value]
    split <;> omega

/-- A consolidation moves at most the effective balance of a due source that is not slashed. -/
private def consolidationGain {f : Fork} (s : BeaconState preset f) (next : Epoch)
    (c : PendingConsolidation) : ℕ :=
  match s.validators.data[c.sourceIndex.toNat]? with
  | some w => if w.slashed = false ∧ w.withdrawableEpoch ≤ next then w.effectiveBalance.toNat
    else 0
  | none => 0

/-- A pass of the consolidations keeps the registry and credits each target at most its gains. -/
private theorem passConsolidations_gain {f : Fork} {next : Epoch} :
    ∀ {list : List PendingConsolidation} {s : BeaconState preset f} {result},
      passPendingConsolidations next s list = .ok result →
      result.1.validators = s.validators ∧
      ∀ i, actualBalanceAt ⟨f, result.1⟩ i ≤ actualBalanceAt ⟨f, s⟩ i +
        (list.map fun c => if c.targetIndex.toNat = i then consolidationGain s next c else 0).sum
  | [], _, _, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨rfl, fun _ => Nat.le_add_right _ _⟩
  | consolidation :: rest, s, result, computed => by
    unfold passPendingConsolidations at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
    rename_i source sourceOk
    have sourceRead := getValidator_eq_ok_iff.mp (liftAccessor_ok.mp sourceOk)
    split at computed
    · split at computed
      · cases computed
      rename_i recur
      cases computed
      obtain ⟨same, bound⟩ := passConsolidations_gain recur
      refine ⟨same, fun i => (bound i).trans ?_⟩
      simp only [List.map_cons, List.sum_cons]
      omega
    split at computed
    · cases computed
      exact ⟨rfl, fun _ => Nat.le_add_right _ _⟩
    rename_i notSlashed waiting
    split at computed
    · cases computed
    split at computed
    · cases computed
    rename_i loweredState loweredOk
    split at computed
    · cases computed
    rename_i raisedState raisedOk
    split at computed
    · cases computed
    rename_i recur
    cases computed
    have lowered := liftAccessor_ok.mp loweredOk
    have raised := liftAccessor_ok.mp raisedOk
    have validators : raisedState.validators = s.validators :=
      (increaseBalance_validators raised).trans (decreaseBalance_validators lowered)
    obtain ⟨same, bound⟩ := passConsolidations_gain recur
    have gains : ∀ c, consolidationGain raisedState next c = consolidationGain s next c := by
      intro c
      simp only [consolidationGain, validators]
    simp only [gains] at bound
    refine ⟨same.trans validators, fun i => ?_⟩
    have down := actualBalanceAt_decreaseBalance lowered i
    have up := actualBalanceAt_increaseBalance raised i
    have head : (if consolidation.targetIndex.toNat = i then
        consolidationGain s next consolidation else 0) =
        if consolidation.targetIndex.toNat = i then source.effectiveBalance.toNat else 0 := by
      have clear : source.slashed = false := by simpa using notSlashed
      have due : source.withdrawableEpoch ≤ next := UInt64.not_lt.mp waiting
      simp [consolidationGain, sourceRead, clear, due]
    have moved := Base.Uint64.toNat_min ‹Gwei› source.effectiveBalance
    have movedLe : (min ‹Gwei› source.effectiveBalance).toNat ≤ source.effectiveBalance.toNat := by
      rw [moved]; exact Nat.min_le_right _ _
    have later := bound i
    simp only [List.map_cons, List.sum_cons, head]
    split at up <;> split <;> omega

/-- The slashings of an epoch never raise a balance. -/
private theorem slashings_lower {f : Fork} {s t : BeaconState preset f} (early : f < .glamsterdam)
    (ok : processSlashings s = .ok t) (i : ℕ) :
    actualBalanceAt ⟨f, t⟩ i ≤ actualBalanceAt ⟨f, s⟩ i := by
  have key {penalty : Validator → ℕ}
      (facts : ∀ i, (i < s.validators.data.size → ∃ validator,
        s.validators.data[i]? = some validator ∧
        t.balances.data[i]?.map UInt64.toNat =
          s.balances.data[i]?.map fun balance => balance.toNat - penalty validator) ∧
        (s.validators.data.size ≤ i → t.balances.data[i]? = s.balances.data[i]?)) :
      actualBalanceAt ⟨f, t⟩ i ≤ actualBalanceAt ⟨f, s⟩ i := by
    by_cases inside : i < s.validators.data.size
    · obtain ⟨v, _, eq⟩ := (facts i).1 inside
      simp only [actualBalanceAt]
      cases h : s.balances.data[i]? <;> cases h' : t.balances.data[i]? <;> simp_all
    · simp [actualBalanceAt, (facts i).2 (by omega)]
  by_cases electra : .pectra ≤ f
  · obtain ⟨_, _, _, _, _, rest⟩ :=
      processSlashings_balances_toNat_of_electra electra (s.validators.bound early) ok
    exact key rest
  · obtain ⟨_, _, _, _, _, rest⟩ :=
      processSlashings_balances_toNat_of_lt_electra (Nat.lt_of_not_le electra) ok
    exact key rest

end EthLib.Consensus
