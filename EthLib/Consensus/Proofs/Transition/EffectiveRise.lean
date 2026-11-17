module

public import EthLib.Consensus.Proofs.Transition.BalanceDrift
public import EthLib.Consensus.Proofs.Transition.EpochUpdates
public import EthLib.Consensus.Proofs.Transition.Trace
public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.Operations
public import EthLib.Consensus.Proofs.Transition.PendingConsolidations
public import EthLib.Consensus.Proofs.Transition.RewardDeltas
public import EthLib.Consensus.Proofs.Mutators
public import EthLib.Consensus.Proofs.Transition.FfgStake
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import EthLib.Consensus.Proofs.Transition.EpochPassAtCall
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.ChainRoots
import EthLib.Consensus.Proofs.Transition.Committees
import EthLib.Consensus.Proofs.Transition.DepositCarry
import EthLib.Consensus.Proofs.Transition.EpochDecomposition
import EthLib.Consensus.Proofs.Transition.EpochPending
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.Requests
import EthLib.Consensus.Proofs.Transition.ValidatorCaps
import EthLib.Consensus.Proofs.Transition.ValidatorKeys
import EthLib.Consensus.Proofs.Transition.Withdrawals

/-!
# The rise of the effective balances over the end of an epoch

The effective balances of the validators active in the next epoch rise by at most a gain.

A validator below its largest effective balance rises only past the upward band.

It then rises by at most its balance, which the branch and the epoch transition bound.

A validator at its largest effective balance rises only after a change of credentials.

The epoch also moves balance to other validators.

Those transfers are deposits within the churn, due consolidations, and proposer and whistleblower
rewards.

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

/-! ### The end of an epoch -/

/-- The registry updates keep every balance. -/
private theorem registryUpdates_balances {f : Fork} {s t : BeaconState preset f}
    (ok : processRegistryUpdates config s = .ok t) : t.balances = s.balances := by
  have fold {α : Type} {step : BeaconState preset f → α → Except TransitionError _}
      {xs : List α} {u w : BeaconState preset f}
      (kept : ∀ a item b, step a item = .ok b → b.balances = a.balances)
      (ok : xs.foldlM step u = .ok w) : w.balances = u.balances :=
    foldlM_ok_invariant (fun b => b.balances = u.balances)
      (fun _ _ _ prior computed => (kept _ _ _ computed).trans prior) rfl ok
  have set {a b : BeaconState preset f} {i : ℕ} {v : Validator}
      (ok : a.setValidatorAt i v = .ok b) : b.balances = a.balances := by
    obtain ⟨_, rfl⟩ := setValidatorAt_ok ok
    rfl
  have exit {a b : BeaconState preset f} {i : ValidatorIndex}
      (ok : initiateValidatorExit config a i = .ok b) : b.balances = a.balances :=
    (initiateValidatorExit_balances_eq_and_pendingConsolidations_eq ok).1
  unfold processRegistryUpdates at ok
  split at ok
  · obtain ⟨epoch, _, folded⟩ := bind_ok_iff.mp ok
    refine fold (fun u i w ok => ?_) folded
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · obtain ⟨_, _, written⟩ := bind_ok_iff.mp ok
      exact set (liftAccessor_ok.mp written)
    split at ok
    · obtain ⟨_, _, exited⟩ := bind_ok_iff.mp ok
      exact exit (liftAccessor_ok.mp exited)
    split at ok
    · exact set (liftAccessor_ok.mp ok)
    · cases ok; rfl
  · obtain ⟨u, first, last⟩ := bind_ok_iff.mp ok
    refine (fold (fun a i b ok => ?_) last).trans (fold (fun a i b ok => ?_) first)
    · simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, _, _, written⟩ := ok
      obtain ⟨_, rfl⟩ := setValidator_ok written
      rfl
    · simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, _, _, marked, markedOk, ok⟩ := ok
      split at ok
      · obtain ⟨_, _, exited⟩ := bind_ok_iff.mp ok
        exact (exit (liftAccessor_ok.mp exited)).trans (set markedOk)
      · cases ok; exact set markedOk

/-- The update of one effective balance changes only the validator at its position.

It keeps the other fields of that validator and every balance. -/
private theorem updateEffectiveBalance_read {f : Fork} {s t : BeaconState preset f} {j : ℕ}
    (ok : updateEffectiveBalance s j = .ok t) :
    t.balances = s.balances ∧ ∃ validator balance next,
      s.validators.data[j]? = some validator ∧ s.balances.data[j]? = some balance ∧
      updatedEffectiveBalance preset (withdrawalMaxEffectiveBalance preset f validator) balance
        validator.effectiveBalance = .ok next ∧
      ∀ i, t.validators.data[i]? =
        if i = j then some { validator with effectiveBalance := next }
        else s.validators.data[i]? := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨validator, found, balance, read, next, updated, set⟩ := ok
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  refine ⟨rfl, validator, balance, next, getValidatorAt_eq_ok_iff.mp found,
    getBalanceAt_eq_ok_iff.mp read, updated, fun i => ?_⟩
  by_cases same : i = j
  · subst i
    simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set]
  · simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, Ne.symm same, same]

/-- A validator with only its effective balance cleared, to compare the other fields. -/
private def withoutEffective (v : Validator) : Validator := { v with effectiveBalance := 0 }

/-- The update of the effective balances keeps every other field of each validator. -/
private theorem effectiveUpdates_others {f : Fork} {s t : BeaconState preset f}
    (ok : processEffectiveBalanceUpdates s = .ok t) (i : ℕ) :
    (t.validators.data[i]?).map withoutEffective =
      (s.validators.data[i]?).map withoutEffective := by
  unfold processEffectiveBalanceUpdates at ok
  refine foldlM_ok_invariant
    (fun w : BeaconState preset f =>
      (w.validators.data[i]?).map withoutEffective = (s.validators.data[i]?).map withoutEffective)
    (fun a j b prior step => ?_) rfl ok
  obtain ⟨-, validator, -, next, found, -, -, reads⟩ := updateEffectiveBalance_read step
  rw [reads i]
  split
  · rename_i here
    subst here
    rw [← prior, found]
    rfl
  · exact prior

/-- Updates of the effective balances at other positions keep a position and every balance. -/
private theorem updates_untouched {f : Fork} {i : ℕ} :
    ∀ {L : List ℕ} {s t : BeaconState preset f}, i ∉ L →
      L.foldlM updateEffectiveBalance s = .ok t →
      t.balances = s.balances ∧ t.validators.data[i]? = s.validators.data[i]?
  | [], _, _, _, ok => by cases ok; exact ⟨rfl, rfl⟩
  | j :: rest, s, t, absent, ok => by
    rw [List.foldlM_cons, bind_ok_iff] at ok
    obtain ⟨u, step, ok⟩ := ok
    obtain ⟨balances, _, _, _, _, _, _, reads⟩ := updateEffectiveBalance_read step
    have other : i ≠ j := fun same => absent (same ▸ List.mem_cons_self)
    obtain ⟨later, kept⟩ := updates_untouched (fun member => absent (List.mem_cons_of_mem _ member))
      ok
    refine ⟨later.trans balances, kept.trans ?_⟩
    rw [reads i]
    simp [other]

private theorem rise_update {f : Fork} {s t : BeaconState preset f}
    (ok : processEffectiveBalanceUpdates s = .ok t) {i : ℕ} {v : Validator}
    (found : s.validators.data[i]? = some v) :
    effectiveAt ⟨f, t⟩ i ≤ v.effectiveBalance.toNat ∨
      (v.effectiveBalance.toNat + preset.upwardBand < actualBalanceAt ⟨f, s⟩ i ∧
        effectiveAt ⟨f, t⟩ i ≤ actualBalanceAt ⟨f, s⟩ i ∧
        effectiveAt ⟨f, t⟩ i ≤ (withdrawalMaxEffectiveBalance preset f v).toNat) := by
  unfold processEffectiveBalanceUpdates at ok
  have member : i ∈ List.range s.validators.data.size :=
    List.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1
  obtain ⟨A, B, split⟩ := List.append_of_mem member
  have nodup := List.nodup_range (n := s.validators.data.size)
  rw [split] at nodup ok
  rw [List.nodup_append] at nodup
  have notA : i ∉ A := fun inA => nodup.2.2 i inA i List.mem_cons_self rfl
  have notB : i ∉ B := (List.nodup_cons.mp nodup.2.1).1
  rw [List.foldlM_append, bind_ok_iff] at ok
  obtain ⟨u, first, rest⟩ := ok
  rw [List.foldlM_cons, bind_ok_iff] at rest
  obtain ⟨u1, step, last⟩ := rest
  obtain ⟨balances1, read1⟩ := updates_untouched notA first
  obtain ⟨balances3, read3⟩ := updates_untouched notB last
  obtain ⟨balances2, validator, balance, next, located, balanceRead, updated, reads⟩ :=
    updateEffectiveBalance_read step
  rw [read1, found, Option.some.injEq] at located
  subst validator
  have balanceValue : balance.toNat = actualBalanceAt ⟨f, s⟩ i := by
    simp [actualBalanceAt, ← balances1, balanceRead]
  have eff : effectiveAt ⟨f, t⟩ i = next.toNat := by
    simp [effectiveAt, read3, reads i]
  rw [eff, ← balanceValue]
  rcases updatedEffectiveBalance_split updated with ⟨rfl, -, -⟩ | ⟨rfl, crossed⟩
  · exact .inl (Nat.le_refl _)
  · have rounded : balance % preset.EFFECTIVE_BALANCE_INCREMENT ≤ balance :=
      UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_mod]; exact Nat.mod_le _ _)
    have value : (min (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT)
        (withdrawalMaxEffectiveBalance preset f v)).toNat =
        min (balance.toNat - balance.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
          (withdrawalMaxEffectiveBalance preset f v).toNat := by
      rw [Base.Uint64.toNat_min, UInt64.toNat_sub_of_le _ _ rounded, UInt64.toNat_mod]
    rw [value]
    have := Nat.mod_le balance.toNat preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    have low := Nat.min_le_left (balance.toNat - balance.toNat %
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (withdrawalMaxEffectiveBalance preset f v).toNat
    rcases crossed with down | up
    · exact .inl (by omega)
    · exact .inr ⟨up, by omega, Nat.min_le_right _ _⟩

/-- The pending balances keep every existing validator. -/
private theorem pendingBalances_validators {f : Fork} {s t : BeaconState preset f}
    (ok : processPendingBalances config checks s = .ok t) (i : ℕ)
    (inside : i < s.validators.data.size) :
    t.validators.data[i]? = s.validators.data[i]? := by
  unfold processPendingBalances at ok
  split at ok
  · obtain ⟨deposited, depositedOk, consolidatedOk⟩ := bind_ok_iff.mp ok
    rw [(processPendingConsolidations_kept consolidatedOk).1]
    exact pendingDeposits_validators depositedOk i inside
  · cases ok; rfl

/-- A trace that starts with a stage runs that stage, then the rest. -/
private theorem trace_cons {σ ε : Type} {action : EpochStage → σ → Except ε σ} {k : EpochStage}
    {ks : List EpochStage} {s t : σ} (trace : EpochTrace action (k :: ks) s t) :
    ∃ u, action k s = .ok u ∧ EpochTrace action ks u t := by
  cases trace with
  | cons first rest => exact ⟨_, first, rest⟩

/-- An empty trace ends where it starts. -/
private theorem trace_nil {σ ε : Type} {action : EpochStage → σ → Except ε σ} {s t : σ}
    (trace : EpochTrace action [] s t) : s = t := by
  cases trace
  rfl

/-- Two registries that agree on a position, up to its effective balance, agree on its activity. -/
private theorem isActiveAt_eq_of_others {f g : Fork} {a : BeaconState preset f}
    {b : BeaconState preset g} {i : ℕ} (epoch : Epoch)
    (same : (b.validators.data[i]?).map withoutEffective =
      (a.validators.data[i]?).map withoutEffective) :
    isActiveAt b epoch i = isActiveAt a epoch i := by
  unfold isActiveAt
  cases hb : b.validators.data[i]? <;> cases ha : a.validators.data[i]? <;>
    simp only [hb, ha, Option.map_none, Option.map_some, reduceCtorEq,
      Option.some.injEq] at same ⊢
  rename_i w v
  have activation := congrArg Validator.activationEpoch same
  have exit := congrArg Validator.exitEpoch same
  simp only [withoutEffective] at activation exit
  simp only [Option.getD_some, isActiveValidator, activation, exit]

/-- From Altair and before Gloas, the steps of an epoch transition up to the pending balances.

The rewards read the state after the inactivity update, which follows justification.

The registry updates, the slashings and the reset after the rewards only lower balances.

Up to the pending balances the steps keep the slot, the queue, the churn left, activity, effective
balances, credentials, slashes and assigned exits.

The pending balances lead to the update of the effective balances, which gives the registry. -/
private theorem rise_epoch {f : Fork} {c t : BeaconState preset f} (altair : .altair ≤ f)
    (early : f < .glamsterdam) (ok : processEpoch config checks c = .ok t) :
    ∃ justified scored rewarded reset before after : BeaconState preset f,
      processJustificationAndFinalization c = .ok justified ∧
      processInactivityUpdates config justified altair = .ok scored ∧
      processRewardsAndPenalties config scored = .ok rewarded ∧
      (∀ i, actualBalanceAt ⟨f, reset⟩ i ≤ actualBalanceAt ⟨f, rewarded⟩ i) ∧
      processPendingBalances config checks reset = .ok before ∧
      processEffectiveBalanceUpdates before = .ok after ∧ t.validators = after.validators ∧
      reset.slot = c.slot ∧ c.validators.data.size ≤ reset.validators.data.size ∧
      (∀ epoch ≤ activityFixedEpoch c, ∀ i, isActiveAt reset epoch i = isActiveAt c epoch i) ∧
      EffectiveKept c reset ∧ RecKeep c reset ∧
      (ExitsOrdered c → ExitsOrdered reset) ∧ (BalancesMatch c → BalancesMatch reset) ∧
      (PendingConsolidationInvariant config c → PendingConsolidationInvariant config reset) ∧
      reset.pendingConsolidations = c.pendingConsolidations ∧
      reset.depositBalanceToConsume = c.depositBalanceToConsume := by
  have hegota : f < .hegota := Nat.lt_trans early (by decide)
  have notGloas : ¬ .glamsterdam ≤ f := Nat.not_le_of_lt early
  have trace := processEpoch_trace ok
  change EpochTrace _ ([.justification, .inactivity, .rewards, .registry, .slashings,
    .eth1Reset] ++ ([.pendingDeposits, .pendingConsolidations] ++ ([.payments,
      .effectiveBalances] ++ [.slashingsReset, .randaoReset, .history, .participation,
        .syncCommittees, .proposerLookahead, .ptcWindow]))) _ _ at trace
  obtain ⟨reset, head, rest⟩ := EpochTrace.append_iff.mp trace
  obtain ⟨before, pending, rest⟩ := EpochTrace.append_iff.mp rest
  obtain ⟨after, updates, rest⟩ := EpochTrace.append_iff.mp rest
  obtain ⟨justified, jA, head⟩ := trace_cons head
  obtain ⟨scored, sA, head⟩ := trace_cons head
  obtain ⟨rewarded, rA, head⟩ := trace_cons head
  obtain ⟨registered, gA, head⟩ := trace_cons head
  obtain ⟨slashed, lA, head⟩ := trace_cons head
  obtain ⟨reset', eA, head⟩ := trace_cons head
  cases trace_nil head
  obtain ⟨deposited, dA, pending⟩ := trace_cons pending
  obtain ⟨before', cA, pending⟩ := trace_cons pending
  cases trace_nil pending
  obtain ⟨paid, pA, updates⟩ := trace_cons updates
  obtain ⟨after', uA, updates⟩ := trace_cons updates
  cases trace_nil updates
  have jE := EpochStage.action_cases.mp jA
  have sE := EpochStage.action_cases.mp sA
  have rE := EpochStage.action_cases.mp rA
  have gE := EpochStage.action_cases.mp gA
  have lE := EpochStage.action_cases.mp lA
  have eE := EpochStage.action_cases.mp eA
  have dE := EpochStage.action_cases.mp dA
  have cE := EpochStage.action_cases.mp cA
  have pE := EpochStage.action_cases.mp pA
  have uE := EpochStage.action_cases.mp uA
  have jOk : processJustificationAndFinalization c = .ok justified := jE
  have sOk : processInactivityUpdates config justified altair = .ok scored := by
    simpa only [EpochStage.Edge, altair, ↓reduceDIte] using sE
  have rOk : processRewardsAndPenalties config scored = .ok rewarded := rE
  have gOk : processRegistryUpdates config rewarded = .ok registered := gE
  have lOk : processSlashings registered = .ok slashed := lE
  have eOk : processEth1DataReset hegota slashed = .ok reset := by
    simpa only [EpochStage.Edge, hegota, ↓reduceDIte] using eE
  have paidEq : before = paid := by
    simpa only [EpochStage.Edge, notGloas, ↓reduceDIte] using pE
  subst paidEq
  have uOk : processEffectiveBalanceUpdates before = .ok after := uE
  -- The steps after the update keep the registry.
  have last : t.validators = after.validators :=
    EpochTrace.transport (fun a b : BeaconState preset f => b.validators = a.validators)
      (fun _ => rfl) (fun {_ _ _} one two => two.trans one) (fun k member a b computed =>
        (EpochStage.action_cases.mp computed).validators_eq (by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact ⟨nofun, nofun, nofun⟩)) rest
  -- The pending balances.
  have pendingOk : processPendingBalances config checks reset = .ok before := by
    unfold processPendingBalances
    by_cases electra : .pectra ≤ f
    · simp only [electra, ↓reduceDIte]
      have dOk : processPendingDeposits config checks reset electra = .ok deposited := by
        simpa only [EpochStage.Edge, electra, ↓reduceDIte] using dE
      have cOk : processPendingConsolidations deposited electra = .ok before := by
        simpa only [EpochStage.Edge, electra, ↓reduceDIte] using cE
      exact bind_ok_iff.mpr ⟨_, dOk, cOk⟩
    · simp only [electra, ↓reduceDIte]
      have one : reset = deposited := by
        simpa only [EpochStage.Edge, electra, ↓reduceDIte] using dE
      have two : deposited = before := by
        simpa only [EpochStage.Edge, electra, ↓reduceDIte] using cE
      rw [one, two]
      rfl
  -- What each step before the pending balances keeps.
  have jRec := jE.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have sRec := sE.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have eRec := eE.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have rSame := rE.validators_eq ⟨nofun, nofun, nofun⟩
  have lSame := lE.validators_eq ⟨nofun, nofun, nofun⟩
  have laws := mutatorEpochFrameLaws.toEpochStepLaws (preset := preset) (fork := f)
  have frame : MutatorFrame justified reset :=
    (laws.epochEdge (stage := .inactivity) ⟨nofun, nofun, nofun, nofun⟩ sA).trans <|
    (laws.epochEdge (stage := .rewards) ⟨nofun, nofun, nofun, nofun⟩ rA).trans <|
    (laws.epochEdge (stage := .registry) ⟨nofun, nofun, nofun, nofun⟩ gA).trans <|
    (laws.epochEdge (stage := .slashings) ⟨nofun, nofun, nofun, nofun⟩ lA).trans
      (laws.epochEdge (stage := .eth1Reset) ⟨nofun, nofun, nofun, nofun⟩ eA)
  have growsG : rewarded.validators.data.size ≤ registered.validators.data.size :=
    (frame_processRegistryUpdates gOk).registryGrows
  have sizeR : registered.validators.data.size = reset.validators.data.size := by
    rw [eRec.1, lSame]
  have rewardedV : rewarded.validators = c.validators := by
    rw [rSame, sRec.1, jRec.1]
  have growsReset : c.validators.data.size ≤ reset.validators.data.size := by
    rw [← sizeR, ← rewardedV]; exact growsG
  have keptReset : EffectiveKept c reset :=
    effectiveKept_trans (effectiveKept_data (by rw [rewardedV]))
      (effectiveKept_trans (effectiveKept_registry gOk)
        (effectiveKept_data (by rw [eRec.1, lSame])) growsG) (by rw [rewardedV])
  have recReset : RecKeep c reset :=
    (RecKeep.of_data (by rw [rewardedV])).trans
      ((recKeep_processRegistryUpdates gOk).trans (RecKeep.of_data (by rw [eRec.1, lSame])))
  -- Activity at the reset reads the registry after the epoch, which keeps it.
  have activeReset : ∀ epoch ≤ activityFixedEpoch c, ∀ i,
      isActiveAt reset epoch i = isActiveAt c epoch i := by
    intro epoch le i
    by_cases inside : i < reset.validators.data.size
    · have others : (t.validators.data[i]?).map withoutEffective =
          (reset.validators.data[i]?).map withoutEffective := by
        rw [last, effectiveUpdates_others uOk i]
        by_cases electra : .pectra ≤ f
        · have dOk : processPendingDeposits config checks reset electra = .ok deposited := by
            simpa only [EpochStage.Edge, electra, ↓reduceDIte] using dE
          have cOk : processPendingConsolidations deposited electra = .ok before := by
            simpa only [EpochStage.Edge, electra, ↓reduceDIte] using cE
          rw [(processPendingConsolidations_kept cOk).1, pendingDeposits_validators dOk i inside]
        · have one : reset = deposited := by
            simpa only [EpochStage.Edge, electra, ↓reduceDIte] using dE
          have two : deposited = before := by
            simpa only [EpochStage.Edge, electra, ↓reduceDIte] using cE
          rw [one, two]
      rw [← isActiveAt_eq_of_others epoch others]
      exact activeKept_processEpoch ok epoch le i
    · have absent : reset.validators.data[i]? = Option.none := Array.getElem?_eq_none (by omega)
      have absent' : c.validators.data[i]? = Option.none := Array.getElem?_eq_none (by omega)
      simp only [isActiveAt, absent, absent', Option.map_none]
  refine ⟨justified, scored, rewarded, reset, before, after, jOk, sOk, rOk, fun i => ?_,
    pendingOk, uOk, last, ?_, growsReset, activeReset, keptReset, recReset, fun h => ?_,
    fun h => ?_, fun h => ?_, ?_, ?_⟩
  · have one : actualBalanceAt ⟨f, reset⟩ i = actualBalanceAt ⟨f, slashed⟩ i := by
      simp only [actualBalanceAt, eRec.2.1]
    have two := slashings_lower early lOk i
    have three : actualBalanceAt ⟨f, registered⟩ i = actualBalanceAt ⟨f, rewarded⟩ i := by
      simp only [actualBalanceAt, registryUpdates_balances gOk]
    omega
  · rw [frame.slot, jRec.2.2.2.2]
  · apply frame.exitsOrdered
    unfold ExitsOrdered at h ⊢
    rw [jRec.1]
    exact h
  · apply frame.balancesMatch
    unfold BalancesMatch at h ⊢
    rw [jRec.1, jRec.2.1]
    exact h
  · exact eE.pendingConsolidationInvariant <| lE.pendingConsolidationInvariant <|
      gE.pendingConsolidationInvariant <| rE.pendingConsolidationInvariant <|
      sE.pendingConsolidationInvariant <| jE.pendingConsolidationInvariant h
  · rw [eE.samePendingQueue nofun, lE.samePendingQueue nofun, gE.samePendingQueue nofun,
      rE.samePendingQueue nofun, sE.samePendingQueue nofun, jE.samePendingQueue nofun]
  · rw [eE.depositCarry nofun, lE.depositCarry nofun, gE.depositCarry nofun,
      rE.depositCarry nofun, sE.depositCarry nofun, jE.depositCarry nofun]

/-- From Altair and before Gloas, the slot that ends an epoch, read from its last state.

The rewards read the state after the inactivity update, which follows justification.

The steps after them up to the pending balances only lower balances, and keep the reads.

An effective balance after the slot rises only past the upward band.

It rises to at most the balance after the pending balances and the largest value before. -/
private theorem rise_edge {z z' : ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks z = .ok z') (early : z'.fork < .glamsterdam)
    (altair : .altair ≤ z.fork)
    (next : (getCurrentEpoch z'.state).toNat = (getCurrentEpoch z.state).toNat + 1) :
    ∃ cached justified scored rewarded reset before : BeaconState preset z.fork,
      processSlot z.state = .ok cached ∧
      processJustificationAndFinalization cached = .ok justified ∧
      processInactivityUpdates config justified altair = .ok scored ∧
      processRewardsAndPenalties config scored = .ok rewarded ∧
      (∀ i, actualBalanceAt ⟨z.fork, reset⟩ i ≤ actualBalanceAt ⟨z.fork, rewarded⟩ i) ∧
      processPendingBalances config checks reset = .ok before ∧
      reset.slot = z.state.slot ∧ z.state.validators.data.size ≤ reset.validators.data.size ∧
      (∀ epoch ≤ activityFixedEpoch z.state, ∀ i,
        isActiveAt reset epoch i = isActiveAt z.state epoch i) ∧
      EffectiveKept z.state reset ∧ RecKeep z.state reset ∧
      (ExitsOrdered z.state → ExitsOrdered reset) ∧
      (BalancesMatch z.state → BalancesMatch reset) ∧
      (PendingConsolidationInvariant config z.state →
        PendingConsolidationInvariant config reset) ∧
      reset.pendingConsolidations = z.state.pendingConsolidations ∧
      reset.depositBalanceToConsume = z.state.depositBalanceToConsume ∧
      ∀ (i : ℕ) (v : Validator), z.state.validators.data[i]? = some v →
        effectiveAt z' i ≤ v.effectiveBalance.toNat ∨
          (v.effectiveBalance.toNat + preset.upwardBand < actualBalanceAt ⟨z.fork, before⟩ i ∧
            effectiveAt z' i ≤ actualBalanceAt ⟨z.fork, before⟩ i ∧
            effectiveAt z' i ≤ (withdrawalMaxEffectiveBalance preset z.fork v).toNat) := by
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
  have forkEarly : z.fork < .glamsterdam := by
    have := processUpgrades_fork_le upgraded
    exact Nat.lt_of_le_of_lt this early
  obtain ⟨nextSlot, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok advancedOk
  have slotAfter : z'.state.slot = nextSlot := processUpgrades_slot upgraded
  have cachedOk' := cachedOk
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  unfold epochIfLast at epochedOk
  split at epochedOk
  swap
  · rename_i inside
    have same := nextSlot_epoch_of_inside sum inside
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, slotAfter] at next
    omega
  obtain ⟨justified, scored, rewarded, reset, before, after, justifiedOk, scoredOk, rewardedOk,
    lower, pendingOk, updated, validators, slot, size, active, kept, rec, exits, matched, holds,
    queue, carry⟩ := rise_epoch altair forkEarly epochedOk
  subst cachedEq
  refine ⟨_, justified, scored, rewarded, reset, before, cachedOk', justifiedOk, scoredOk,
    rewardedOk, lower, pendingOk, slot, size, active, kept, rec, exits, matched, holds, queue,
    carry, fun i v found => ?_⟩
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  obtain ⟨w, read, -, sameKeys⟩ := rec i v found
  have insideReset := (Array.getElem?_eq_some_iff.mp read).1
  have readBefore : before.validators.data[i]? = some w := by
    rw [pendingBalances_validators pendingOk i insideReset]; exact read
  have effective : w.effectiveBalance.toNat = v.effectiveBalance.toNat := by
    have one := kept i inside
    simp only [effectiveAt, read, found, Option.map_some, Option.getD_some] at one
    exact one
  have upgradedLe := balanceDrift_upgrades_upper upgraded early i
  have endSame : effectiveAt ⟨z.fork, { epoched with slot := nextSlot }⟩ i =
      effectiveAt ⟨z.fork, after⟩ i := by
    simp only [effectiveAt, validators]
  have capSame : withdrawalMaxEffectiveBalance preset z.fork w =
      withdrawalMaxEffectiveBalance preset z.fork v := by
    unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance hasCompoundingWithdrawalCredential
    rw [sameKeys]
  rw [← effective, ← capSame]
  rcases rise_update updated readBefore with low | ⟨crossed, belowBalance, belowCap⟩
  · exact .inl (by omega)
  · exact .inr ⟨crossed, by omega, by omega⟩

/-! ### The rise of one validator, in natural numbers -/

/-- The rise of one effective balance over the end of an epoch, from bounds on its balance.

Off the debited validators it is at most its crossing, plus the band and transfers if any.

On them it is at most the upward band, its credit and its transfers. -/
private theorem rise_one {EB effY band bal aZ aR aP flag extra blocksSync slotsSync pc dep
      slashBack nSync capR capZ capP minAct : ℕ}
    (update : effY ≤ EB ∨ (EB + band < bal ∧ effY ≤ bal ∧ effY ≤ capZ))
    (balance : bal ≤ aZ + flag + extra)
    (branch : aZ ≤ aR + blocksSync + pc + dep) (blocks : blocksSync ≤ slotsSync)
    (converted : capZ ≠ capR → aZ ≤ minAct + blocksSync + pc + dep)
    (activation : capR ≤ EB → capZ ≠ capR → minAct ≤ EB) :
    ((aR ≤ aP + slashBack + nSync → capR = capP →
      effY - EB ≤ (if EB < capP then
          (if EB + band < aP + slashBack + nSync + (flag + slotsSync) then
            aP + slashBack + nSync + (flag + slotsSync) - EB else 0)
        else (if band < flag + slotsSync then flag + slotsSync else 0)) +
        (if pc + extra + dep = 0 then 0 else band) + (pc + extra) + dep) ∧
    ((EB < capR → aR ≤ EB + band) →
      effY - EB ≤ band + (flag + slotsSync) + (pc + extra) + dep)) := by
  constructor
  · intro nondebited caps
    rcases update with low | ⟨crossed, belowBalance, belowCap⟩
    · have : effY - EB = 0 := by omega
      omega
    by_cases below : EB < capP
    · simp only [below, ↓reduceIte]
      split <;> split <;> omega
    · simp only [below, ↓reduceIte]
      by_cases same : capZ = capR
      · omega
      · have conv := converted same
        have act := activation (by omega) same
        split <;> split <;> omega
  · intro debited
    rcases update with low | ⟨crossed, belowBalance, belowCap⟩
    · omega
    by_cases below : EB < capR
    · have := debited below
      omega
    · by_cases same : capZ = capR
      · omega
      · have conv := converted same
        have act := activation (by omega) same
        omega

/-- The rises add up to the crossings, bands, largest credits, transfers and deposit caps. -/
private theorem rise_sum {U A D B : Finset ℕ} {rise crossing transfer : ℕ → ℕ}
    {band creditMax capMax : ℕ}
    (each : ∀ i ∈ U, i ∉ B → rise i ≤ crossing i + (if i ∈ A then band else 0) +
      (if i ∈ D then band + creditMax else 0) + transfer i)
    (deposited : ∀ i ∈ U, i ∈ B → rise i ≤ capMax) :
    ∑ i ∈ U, rise i ≤ ∑ i ∈ U, crossing i + (U ∩ A).card * band +
      (U ∩ D).card * (band + creditMax) + ∑ i ∈ U, transfer i + (U ∩ B).card * capMax := by
  have pointwise : ∀ i ∈ U, rise i ≤ crossing i + (if i ∈ A then band else 0) +
      (if i ∈ D then band + creditMax else 0) + transfer i + (if i ∈ B then capMax else 0) := by
    intro i member
    by_cases inB : i ∈ B
    · have := deposited i member inB
      simp only [inB, ↓reduceIte]
      omega
    · have := each i member inB
      simp only [inB, ↓reduceIte]
      omega
  refine (Finset.sum_le_sum pointwise).trans (le_of_eq ?_)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_const,
    Nat.mul_add]
  rfl

/-- States that agree on activity in an epoch, with a longer later registry, share its actives. -/
private theorem activeFilter_eq {f g : Fork} {a : BeaconState preset f}
    {b : BeaconState preset g} {ep : Epoch} (active : ∀ i, isActiveAt b ep i = isActiveAt a ep i)
    (grows : a.validators.data.size ≤ b.validators.data.size) :
    (Finset.range b.validators.data.size).filter (fun i => isActiveAt b ep i = true) =
      (Finset.range a.validators.data.size).filter (fun i => isActiveAt a ep i = true) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, active]
  constructor
  · rintro ⟨-, hit⟩
    obtain ⟨v, found, -⟩ := isActiveAt_eq_true_iff.mp hit
    exact ⟨(Array.getElem?_eq_some_iff.mp found).1, hit⟩
  · rintro ⟨inside, hit⟩
    exact ⟨Nat.lt_of_lt_of_le inside grows, hit⟩

/-- Within one epoch before Gloas, the churn left of the pending deposits stays. -/
private theorem run_depositCarry {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (same : getCurrentEpoch y.state = getCurrentEpoch x.state) :
    ∀ (one : .pectra ≤ y.fork) (two : .pectra ≤ x.fork),
      y.state.depositBalanceToConsume one = x.state.depositBalanceToConsume two :=
  Run.induction_of_same_epoch
    (fun w _ => ∀ (one : .pectra ≤ w.fork) (two : .pectra ≤ x.fork),
      w.state.depositBalanceToConsume one = x.state.depositBalanceToConsume two)
    (fun _ _ => rfl)
    (fun _ _ _ ok _ early prior one two => by
      rw [show _ = _ from congrFun (depositCarry_processBlock early (applySignedBlock_ok ok).2.1)
        one]
      exact prior one two)
    (fun _ _ lastEq cachedOk _ prior => by
      subst lastEq
      obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
      exact prior)
    tail early same

/-- Gains of distinct entries, each on a distinct list with a value, sum to at most the values.

Their keys number at most that list. -/
private theorem gain_sum_le {list due : List PendingConsolidation}
    {gain value : PendingConsolidation → ℕ} (key : PendingConsolidation → ℕ)
    (nodupList : list.Nodup) (nodupDue : due.Nodup)
    (into : ∀ c ∈ list, 0 < gain c → c ∈ due ∧ gain c = value c) :
    (list.map gain).sum ≤ (due.map value).sum ∧
      (((list.filter fun c => 0 < gain c).map key).toFinset).card ≤ due.length := by
  have dropZero : ∀ l : List PendingConsolidation,
      (l.map gain).sum = ((l.filter fun c => 0 < gain c).map gain).sum := by
    intro l
    induction l with
    | nil => rfl
    | cons c rest ih =>
      simp only [List.map_cons, List.sum_cons, List.filter_cons]
      split
      · simp [ih]
      · rename_i zero
        simp only [decide_eq_true_eq, Nat.not_lt, Nat.le_zero] at zero
        rw [zero, ih, Nat.zero_add]
  set S := list.filter fun c => 0 < gain c with hS
  have nodupS : S.Nodup := nodupList.filter _
  have sub : S.toFinset ⊆ due.toFinset := by
    intro c member
    rw [List.mem_toFinset, hS, List.mem_filter, decide_eq_true_eq] at member
    exact List.mem_toFinset.mpr (into c member.1 member.2).1
  have values : (S.map gain).sum = (S.map value).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro c member
    rw [hS, List.mem_filter, decide_eq_true_eq] at member
    exact (into c member.1 member.2).2
  refine ⟨?_, ?_⟩
  · rw [dropZero, values, ← List.sum_toFinset _ nodupS, ← List.sum_toFinset _ nodupDue]
    exact Finset.sum_le_sum_of_subset sub
  · refine (List.toFinset_card_le _).trans ?_
    rw [List.length_map, ← List.toFinset_card_of_nodup nodupS,
      ← List.toFinset_card_of_nodup nodupDue]
    exact Finset.card_le_card sub


/-- Before Gloas, a successful deposit churn read is a share of the total active balance.

The share is the total over the churn quotient, or the minimum if that is larger.

It is rounded down to a whole number of increments, then capped by the maximum. -/
private theorem depositChurnLimit_toNat_of_lt {fork : Fork} {state : BeaconState preset fork}
    {total churn : Gwei} (early : fork < .glamsterdam)
    (totalOk : getTotalActiveBalance state = .ok total)
    (computed : depositChurnLimit config state = .ok churn) :
    churn.toNat = min config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat
      (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
          (total.toNat / config.CHURN_LIMIT_QUOTIENT.toNat) -
        max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
          (total.toNat / config.CHURN_LIMIT_QUOTIENT.toNat) %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  rw [depositChurnLimit_of_lt early] at computed
  simp only [getActivationExitChurnLimit, getBalanceChurnLimit, totalOk, bind, Except.bind,
    pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  rw [toNat_min, toNat_roundToIncrement, toNat_max, UInt64.toNat_div]

/-- The effective balances of the validators active in the next epoch rise by at most the gain.

This is the gain bound (rise) of the fast confirmation rule.

It is read by `quorumDrift_le_quorumReserve`.

The epoch starts at `R`, right after its epoch transition, where the hysteresis holds.

One branch leads from `R` to the call's state `P`, inside the epoch.

Another leads from `R` to `y` in the next epoch.

Every read is at `P`.

The branch of `P` has at most `n` blocks.

`branchCorrections` gives a set of debited validators, at most the payload limits per block.

Off that set, a balance at `R` exceeds the one at `P` by at most the slashing and sync amounts.

Off that set, the largest effective balance stays.

A validator below its cap rises only past the upward band, and by at most its balance.

A validator at its cap rises only after a conversion (L4a), and then by at most its credits.

The epoch also transfers balance to other validators, to a bounded number of recipients.

They are churn-limited deposits, due consolidations, proposer credits and whistleblower rewards.

From Fulu a block deposit only queues, so no block deposit credits a balance inside the epoch.

The three hypotheses marked TEMPORARY are lemmas of other modules that have not landed yet. -/
theorem effectiveRise_le
    -- TEMPORARY: S13a moves this lemma to RewardDeltas
    (penaltyEntries_le : ∀ {config : Config} {fork : Fork} {state : BeaconState preset fork}
      {total : Gwei} (altair : .altair ≤ fork) (_within : state.RegistryWithinLimit)
      (_active : getTotalActiveBalance state = .ok total)
      {source target head inactivity : Array Gwei × Array Gwei}
      (_sourceOk : getFlagIndexDeltas state altair ⟨0, by decide⟩ = .ok source)
      (_targetOk : getFlagIndexDeltas state altair ⟨1, by decide⟩ = .ok target)
      (_headOk : getFlagIndexDeltas state altair ⟨2, by decide⟩ = .ok head)
      (_inactivityOk : getInactivityPenaltyDeltas config state = .ok inactivity)
      {j : Nat} (inside : j < state.validators.data.size),
      (source.2.getD j 0).toNat + (target.2.getD j 0).toNat + (head.2.getD j 0).toNat +
          (inactivity.2.getD j 0).toNat = 0 ∨
        ∃ base, isEligibleValidator (getPreviousEpoch state) state.validators.data[j] = .ok true ∧
          getBaseReward state total j.toUInt64 = .ok base ∧
          (source.2.getD j 0).toNat + (target.2.getD j 0).toNat + (head.2.getD j 0).toNat +
              (inactivity.2.getD j 0).toNat ≤
            base.toNat * (TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat) /
                WEIGHT_DENOMINATOR.toNat +
              state.validators.data[j].effectiveBalance.toNat *
                (((state.inactivityScores altair).data[j]?.map UInt64.toNat).getD 0) /
                (config.INACTIVITY_SCORE_BIAS.toNat *
                  (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat))
    -- TEMPORARY: S13a moves this lemma to RewardDeltas
    (toNat_getBaseReward_le : ∀ {fork : Fork} {state : BeaconState preset fork} {total : Gwei}
      (_altair : .altair ≤ fork) {base : Gwei}
      {index : ValidatorIndex} (_computed : getBaseReward state total index = .ok base)
      {validator : Validator} (_found : state.validators.data[index.toNat]? = some validator),
      base.toNat ≤ validator.effectiveBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat /
          total.toNat.sqrt))
    -- TEMPORARY: prover A's `branchCorrections` (BranchLedger) replaces this hypothesis
    (branchCorrections : ∀ {x y : ForkedBeaconState preset} (tail : Run config checks x y)
        (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ y.fork)
        (same : getCurrentEpoch y.state = getCurrentEpoch x.state)
        (matched : BalancesMatch x.state) (exits : ExitsOrdered x.state),
        let state := y.state
        let inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
        let slots := preset.SLOTS_PER_EPOCH.toNat
        let p := parameters preset y.fork
        let positions := Finset.range state.validators.data.size
        let validator (i : ℕ) := state.validators.data[i]?
        let effective (i : ℕ) := balanceAt state i
        let current (i : ℕ) := isActiveAt state (getCurrentEpoch state) i
        let before (i : ℕ) := isActiveAt state (getPreviousEpoch state) i
        let recent (i : ℕ) := before i || current i
        let slashed (i : ℕ) := ((validator i).map (·.slashed)).getD false
        let total := max inc (∑ i ∈ positions with current i, effective i)
        let root := (integerSquareroot (UInt64.ofNat total)).toNat
        let perIncrement := inc * preset.BASE_REWARD_FACTOR.toNat / root
        let base (i : ℕ) := if .altair ≤ y.fork then effective i / inc * perIncrement
          else effective i * preset.BASE_REWARD_FACTOR.toNat / root / BASE_REWARDS_PER_EPOCH.toNat
        let seatReward := if .altair ≤ y.fork then
            total / inc * perIncrement * SYNC_REWARD_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat /
              slots / preset.SYNC_COMMITTEE_SIZE.toNat
          else 0
        let seats (i : ℕ) := if altair : .altair ≤ y.fork then
            ((state.currentSyncCommittee altair).value.pubkeys.toList.filter fun key =>
              (validator i).any (·.pubkey == key)).length
          else 0
        let sync (i : ℕ) := seats i * seatReward
        let syncProposer := if .altair ≤ y.fork then
            slots * preset.SYNC_COMMITTEE_SIZE.toNat *
              (seatReward * PROPOSER_WEIGHT.toNat /
                (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat))
          else 0
        let proposerCredit := (∑ i ∈ positions with recent i, base i) + syncProposer
        let whistleblowerP :=
          (∑ i ∈ positions with slashed i, effective i) / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
        let slashBack (i : ℕ) :=
          if slashed i then effective i / p.MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0
        let blocks := tail.blockCount
        let debited :=
          ((if .shapella ≤ y.fork then preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat else 0) +
          (if .pectra ≤ y.fork then preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat else 0)) *
            blocks
        let blockDeposits := if h : y.fork < .hegota then
            (if .pectra ≤ y.fork then 0
             else min (preset.MAX_DEPOSITS.toNat * blocks) (state.eth1DepositIndex h).toNat)
          else 0
        let creditedP :=
          (if proposerCredit = 0 ∧ seatReward = 0 ∧ positions.filter (slashed ·) = ∅ then 0
            else blocks) + blockDeposits
        ∃ (debitedKeys creditedKeys : Finset ValidatorIndex) (pc deposit : ValidatorIndex → ℕ),
          debitedKeys.card ≤ debited ∧ creditedKeys.card ≤ creditedP ∧
          (∀ v, v ∉ debitedKeys → actualBalanceAt x v.toNat ≤
            actualBalanceAt y v.toNat + slashBack v.toNat + blocks * sync v.toNat) ∧
          (∀ v, actualBalanceAt y v.toNat ≤
            actualBalanceAt x v.toNat + blocks * sync v.toNat + pc v + deposit v) ∧
          (∀ v, v ∉ creditedKeys → pc v = 0 ∧ deposit v = 0) ∧
          (.pectra ≤ y.fork → ∀ v, deposit v = 0) ∧
          ∑ v ∈ creditedKeys, pc v ≤ proposerCredit + whistleblowerP ∧
          (∃ slashedNow : Finset ValidatorIndex,
            (∀ v ∈ slashedNow, (∀ validator, x.state.validators.data[v.toNat]? = some validator →
                validator.slashed = false) ∧ slashed v.toNat = true ∧
              ∃ validator, x.state.validators.data[v.toNat]? = some validator ∧
                validator.activationEpoch ≤ getCurrentEpoch x.state ∧
                getCurrentEpoch x.state < validator.withdrawableEpoch) ∧
            ∑ v ∈ creditedKeys, pc v ≤ (∑ i ∈ positions with recent i, base i) + syncProposer +
              (∑ v ∈ slashedNow, effective v.toNat) / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ∧
          (∀ v validator later, x.state.validators.data[v.toNat]? = some validator →
            y.state.validators.data[v.toNat]? = some later →
            withdrawalMaxEffectiveBalance preset y.fork later ≠
              withdrawalMaxEffectiveBalance preset x.fork validator →
            actualBalanceAt y v.toNat ≤ preset.MIN_ACTIVATION_BALANCE.toNat +
              blocks * sync v.toNat + pc v + deposit v) ∧
          (∃ proposerKeys depositKeys : Finset ValidatorIndex,
            creditedKeys = proposerKeys ∪ depositKeys ∧
            proposerKeys.card ≤ (if proposerCredit = 0 ∧ seatReward = 0 ∧
              positions.filter (slashed ·) = ∅ then 0 else blocks) ∧
            depositKeys.card ≤ blockDeposits ∧
            (∀ v, v ∉ proposerKeys → pc v = 0) ∧ (∀ v, v ∉ depositKeys → deposit v = 0)) ∧
          (∀ v validator, v ∉ debitedKeys → x.state.validators.data[v.toNat]? = some validator →
            ∃ later, y.state.validators.data[v.toNat]? = some later ∧
              withdrawalMaxEffectiveBalance preset y.fork later =
                withdrawalMaxEffectiveBalance preset x.fork validator) ∧
          x.fork = y.fork ∧ EffectiveKept x.state y.state)
    {g R P y : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) (history : Run config checks g R)
    (tailP : Run config checks R P) (tailS : Run config checks R y) (caps : CapOrder preset)
    (withdrawDelay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (bands : preset.IncrementWithinUpwardBand)
    (lookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (hysteresis : Hysteresis R.state) (early : y.fork < .glamsterdam)
    (fulu : .fusaka ≤ P.fork)
    (callEpoch : getCurrentEpoch P.state = getCurrentEpoch R.state)
    (next : (getCurrentEpoch y.state).toNat = (getCurrentEpoch R.state).toNat + 1)
    {n : ℕ} (debitedKeys : Finset ValidatorIndex) :
    let state := P.state
    let epoch := getCurrentEpoch state
    let inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    let slots := preset.SLOTS_PER_EPOCH.toNat
    let p := parameters preset P.fork
    let positions := Finset.range state.validators.data.size
    let validator (i : ℕ) := state.validators.data[i]?
    let effective (i : ℕ) := balanceAt state i
    let actual (i : ℕ) := ((state.balances.data[i]?).map (·.toNat)).getD 0
    let cap (i : ℕ) :=
      ((validator i).map fun v => (withdrawalMaxEffectiveBalance preset P.fork v).toNat).getD 0
    let capMax := if .pectra ≤ P.fork then preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
      else preset.MAX_EFFECTIVE_BALANCE.toNat
    let current (i : ℕ) := isActiveAt state epoch i
    let upcoming (i : ℕ) := isActiveAt state (epoch + 1) i
    let before (i : ℕ) := isActiveAt state (getPreviousEpoch state) i
    let recent (i : ℕ) := before i || current i
    let slashed (i : ℕ) := ((validator i).map (·.slashed)).getD false
    let total := max inc (∑ i ∈ positions with current i, effective i)
    let root := (integerSquareroot (UInt64.ofNat total)).toNat
    let perIncrement := inc * preset.BASE_REWARD_FACTOR.toNat / root
    let base (i : ℕ) := if .altair ≤ P.fork then effective i / inc * perIncrement
      else effective i * preset.BASE_REWARD_FACTOR.toNat / root / BASE_REWARDS_PER_EPOCH.toNat
    let num := max 1 ((∑ i ∈ positions with before i, effective i) / inc)
    let den := max 1 (total / inc)
    let flagWeight := (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum
    let seatReward := if .altair ≤ P.fork then
        total / inc * perIncrement * SYNC_REWARD_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat /
          slots / preset.SYNC_COMMITTEE_SIZE.toNat
      else 0
    let seats (i : ℕ) := if altair : .altair ≤ P.fork then
        ((state.currentSyncCommittee altair).value.pubkeys.toList.filter fun key =>
          (validator i).any (·.pubkey == key)).length
      else 0
    let sync (i : ℕ) := seats i * seatReward
    let depositChurn :=
      let limit := max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
        (total / config.CHURN_LIMIT_QUOTIENT.toNat)
      min config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat (limit - limit % inc)
    let credit (i : ℕ) :=
      (if .altair ≤ P.fork then base i * flagWeight * num / (WEIGHT_DENOMINATOR.toNat * den)
       else 3 * (base i * max num den / den) + base i) + slots * sync i
    let syncProposer := if .altair ≤ P.fork then
        slots * preset.SYNC_COMMITTEE_SIZE.toNat *
          (seatReward * PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat))
      else 0
    let proposerCredit := (∑ i ∈ positions with recent i, base i) + syncProposer
    let whistleblower := (∑ i ∈ positions with (validator i).any (fun v =>
        v.activationEpoch ≤ epoch && epoch < v.withdrawableEpoch), effective i) /
      p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
    let depositCredit := if electra : .pectra ≤ P.fork then
        (state.depositBalanceToConsume electra).toNat + depositChurn else 0
    let due := if electra : .pectra ≤ P.fork then
        (state.pendingConsolidations electra).data.toList.filter fun c =>
          ((validator c.sourceIndex.toNat).map fun v =>
            v.slashed || decide (v.withdrawableEpoch ≤ epoch + 1)).getD false
      else []
    let dueStake := (due.map fun c => effective c.sourceIndex.toNat).sum
    let proposers := if .altair ≤ P.fork then slots else 2 * slots
    let depositRecipients := if .pectra ≤ P.fork then preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat
      else slots * preset.MAX_DEPOSITS.toNat
    let recipients := (if .pectra ≤ P.fork then depositRecipients else 0) + due.length + proposers
    let debited := ((if .shapella ≤ P.fork then preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat else 0) +
      (if .pectra ≤ P.fork then preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat else 0)) * n
    let transfers := depositCredit + dueStake + proposerCredit + whistleblower
    let depositGain := if .pectra ≤ P.fork then 0 else depositRecipients * capMax
    let slashBack (i : ℕ) :=
      if slashed i then effective i / p.MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0
    let syncP (i : ℕ) := n * sync i
    let creditMax := positions.sup fun i => if upcoming i then credit i else 0
    let crossing := ∑ i ∈ positions with upcoming i,
      if effective i < cap i then
        (let top := actual i + slashBack i + syncP i + credit i
         if effective i + preset.upwardBand < top then top - effective i else 0)
      else (if preset.upwardBand < credit i then credit i else 0)
    let headroom := ∑ i ∈ positions with upcoming i, (capMax - effective i)
    debitedKeys.card ≤ debited →
    (∀ v, v ∉ debitedKeys → actualBalanceAt R v.toNat ≤
      actualBalanceAt P v.toNat + slashBack v.toNat + syncP v.toNat) →
    (∀ v validator, v ∉ debitedKeys → R.state.validators.data[v.toNat]? = some validator →
      ∃ later, P.state.validators.data[v.toNat]? = some later ∧
        withdrawalMaxEffectiveBalance preset P.fork later =
          withdrawalMaxEffectiveBalance preset R.fork validator) →
    ∑ i ∈ positions with upcoming i, (effectiveAt y i - effective i) ≤
      min headroom (crossing + (recipients + debited) * preset.upwardBand +
        debited * creditMax + transfers + depositGain)
  := by
  have hPR : P.fork = R.fork := Run.fork_eq_of_same_epoch tailP callEpoch
  obtain ⟨fR, r⟩ := R
  obtain ⟨F, q⟩ := P
  dsimp only at hPR
  subst fR
  intro state epoch inc slots p positions validator effective actual cap capMax current upcoming
    before recent slashed total root perIncrement base num den flagWeight seatReward seats sync
    depositChurn credit syncProposer proposerCredit whistleblower depositCredit due dueStake
    proposers depositRecipients recipients debited transfers depositGain slashBack syncP creditMax
    crossing headroom debitedCard offDebited capsKept
  have altair : .altair ≤ F := Nat.le_trans (by decide) fulu
  have electraF : .pectra ≤ F := Nat.le_trans (by decide) fulu
  -- The branch of `y` leaves the epoch at one slot, from its last state `z` in the epoch.
  obtain ⟨z, z', toZ, edge, fromZ', zEpoch, z'Epoch⟩ := Run.split_next tailS next
  have zFork : z.fork = F := Run.fork_eq_of_same_epoch toZ zEpoch
  obtain ⟨fZ, zs⟩ := z
  dsimp only at zFork
  subst fZ
  have z'Early : z'.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps fromZ'.chainSteps) early
  have Fearly : F < .glamsterdam := by
    have := fork_le_of_chainSteps (Run.nil.snoc (.slot edge)).chainSteps
    exact Nat.lt_of_le_of_lt this z'Early
  -- The epoch `e` of the branches, and the next one.
  obtain ⟨e, he⟩ : ∃ e, getCurrentEpoch r = e := ⟨_, rfl⟩
  have epochP : getCurrentEpoch q = e := callEpoch.trans he
  have epochZ : getCurrentEpoch zs = e := zEpoch.trans he
  have nextR : (getCurrentEpoch y.state).toNat = e.toNat + 1 := by rw [← he]; exact next
  have small := (getCurrentEpoch y.state).toNat_lt
  have nextNat : (e + 1).toNat = e.toNat + 1 := by
    rw [UInt64.toNat_add]
    simp only [UInt64.toNat_one]
    omega
  have fixedNext : e + 1 ≤ activityFixedEpoch r := by
    rw [UInt64.le_iff_toNat_le, activityFixedEpoch_toNat, nextNat, he]
    exact Nat.le_min.mpr ⟨by omega, by omega⟩
  have fixedNow : e ≤ activityFixedEpoch r := he ▸ getCurrentEpoch_le_activityFixedEpoch r
  have fixedBefore : getPreviousEpoch r ≤ activityFixedEpoch r :=
    UInt64.le_trans (getPreviousEpoch_le r) (getCurrentEpoch_le_activityFixedEpoch r)
  -- What the states of the epoch keep from `R`.
  have activeP := activeKept_of_chainSteps tailP.chainSteps
  have activeZ := activeKept_of_chainSteps toZ.chainSteps
  have keptP : EffectiveKept r q := tailP.effectiveKept_of_same_epoch Fearly callEpoch
  have keptZ : EffectiveKept r zs := toZ.effectiveKept_of_same_epoch Fearly zEpoch
  have growsP := tailP.registryLifecycle.size_le
  have growsZ := toZ.registryLifecycle.size_le
  have keysP := (validatorKeys_prefix_and_distinct_of_chainSteps tailP.chainSteps).1
  have keysZ := (validatorKeys_prefix_and_distinct_of_chainSteps toZ.chainSteps).1
  have committeeP := Run.currentSyncCommittee_eq_of_same_epoch tailP Fearly callEpoch
  have committeeZ := Run.currentSyncCommittee_eq_of_same_epoch toZ Fearly zEpoch
  -- The reachable invariants.
  have histZ := history.append toZ
  have histP := history.append tailP
  have invG : Invariant g.state := by
    obtain ⟨_, _, _, ok⟩ := genesis
    exact (initializeBeaconStateFromEth1_invariant ok).2
  have invR := Run.invariant invG history
  have invZ := Run.invariant invG histZ
  have invP := Run.invariant invG histP
  have holdsZ : PendingConsolidationInvariant config zs := fun electra =>
    histZ.pendingConsolidation_invariant genesis Fearly electra withdrawDelay
  have holdsP : PendingConsolidationInvariant config q := fun electra =>
    histP.pendingConsolidation_invariant genesis Fearly electra withdrawDelay
  have holdsR : PendingConsolidationInvariant config r := fun electra =>
    history.pendingConsolidation_invariant genesis Fearly electra withdrawDelay
  -- The slashes, exits, withdrawal epochs and queues inside the epoch.
  obtain ⟨wdP, queueP⟩ := run_riseKeep tailP Fearly callEpoch withdrawDelay
  obtain ⟨wdZ, queueZ⟩ := run_riseKeep toZ Fearly zEpoch withdrawDelay
  -- The slot that ends the epoch.
  have nextZ : (getCurrentEpoch z'.state).toNat = (getCurrentEpoch zs).toNat + 1 := by
    rw [z'Epoch, epochZ]; exact nextR
  obtain ⟨cached, justified, scored, rewarded, reset, beforeState, cachedOk, justifiedOk,
    scoredOk, rewardedOk, lower, pendingOk, resetSlot, resetSize, resetActive, resetKept,
    resetRec, resetExits, resetMatch, resetHolds, resetQueue, resetCarry, updateBound⟩ :=
    rise_edge edge z'Early altair nextZ
  -- The sums of effective balances active in an epoch up to the fixed one read the same.
  have sumPR : ∀ ep ≤ activityFixedEpoch r,
      ∑ i ∈ (Finset.range q.validators.data.size).filter (fun i => isActiveAt q ep i = true),
        ((q.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0 =
      ∑ i ∈ (Finset.range r.validators.data.size).filter (fun i => isActiveAt r ep i = true),
        ((r.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0 :=
    fun ep le => activeSum_eq (fun i => activeP ep le i) keptP growsP
  have sumZR : ∀ ep ≤ activityFixedEpoch r,
      ∑ i ∈ (Finset.range zs.validators.data.size).filter (fun i => isActiveAt zs ep i = true),
        ((zs.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0 =
      ∑ i ∈ (Finset.range r.validators.data.size).filter (fun i => isActiveAt r ep i = true),
        ((r.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0 :=
    fun ep le => activeSum_eq (fun i => activeZ ep le i) keptZ growsZ
  have prevP : getPreviousEpoch q = getPreviousEpoch r := by
    unfold getPreviousEpoch; rw [epochP, he]
  have prevZ : getPreviousEpoch zs = getPreviousEpoch r := by
    unfold getPreviousEpoch; rw [epochZ, he]
  have totalR : total = max inc
      (∑ i ∈ (Finset.range r.validators.data.size).filter (fun i => isActiveAt r e i = true),
        ((r.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0) := by
    rw [← sumPR e fixedNow]
    simp only [total, positions, current, effective, balanceAt, epoch, state, epochP]
  have numR : num = max 1
      ((∑ i ∈ (Finset.range r.validators.data.size).filter
        (fun i => isActiveAt r (getPreviousEpoch r) i = true),
        ((r.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0) / inc) := by
    rw [← sumPR _ fixedBefore]
    simp only [num, positions, before, effective, balanceAt, state, prevP]
  -- The positions active in an epoch up to the fixed one are the same at `R`, `P` and `z`.
  have filterP : ∀ ep ≤ activityFixedEpoch r,
      (Finset.range q.validators.data.size).filter (fun i => isActiveAt q ep i = true) =
        (Finset.range r.validators.data.size).filter (fun i => isActiveAt r ep i = true) :=
    fun ep le => activeFilter_eq (fun i => activeP ep le i) growsP
  have filterZ : ∀ ep ≤ activityFixedEpoch r,
      (Finset.range zs.validators.data.size).filter (fun i => isActiveAt zs ep i = true) =
        (Finset.range r.validators.data.size).filter (fun i => isActiveAt r ep i = true) :=
    fun ep le => activeFilter_eq (fun i => activeZ ep le i) growsZ
  -- The effective balances of the old positions read the same at `R`, `P` and `z`.
  have effPR : ∀ i < r.validators.data.size, effective i = effectiveAt ⟨F, r⟩ i :=
    fun i inside => keptP i inside
  have effZR : ∀ i < r.validators.data.size, effectiveAt ⟨F, zs⟩ i = effectiveAt ⟨F, r⟩ i :=
    fun i inside => keptZ i inside
  -- The state that the rewards read is the last state of the epoch, after justification.
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have justifiedSame :=
    (show EpochStage.Edge config checks .justification cached justified from justifiedOk).records
      ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have Jvalidators : justified.validators = zs.validators := by rw [justifiedSame.1, cachedEq]
  have Jbalances : justified.balances = zs.balances := by rw [justifiedSame.2.1, cachedEq]
  have JEpoch : getCurrentEpoch justified = e := by
    rw [← epochZ]; simp only [getCurrentEpoch, justifiedSame.2.2.2.2, cachedEq]
  have JPrev : getPreviousEpoch justified = getPreviousEpoch r := by
    unfold getPreviousEpoch; rw [JEpoch, he]
  have sumJ : ∀ ep,
      ∑ i ∈ (Finset.range justified.validators.data.size).filter
          (fun i => isActiveAt justified ep i = true),
        ((justified.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0 =
      ∑ i ∈ (Finset.range zs.validators.data.size).filter (fun i => isActiveAt zs ep i = true),
        ((zs.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0 := by
    intro ep
    have same : ∀ i, isActiveAt justified ep i = isActiveAt zs ep i := fun i => by
      simp only [isActiveAt, Jvalidators]
    simp only [same, Jvalidators]
  have totalJ : max inc (∑ i ∈ (Finset.range justified.validators.data.size).filter
      (fun i => isActiveAt justified (getCurrentEpoch justified) i = true),
      ((justified.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0) = total := by
    rw [sumJ, JEpoch, sumZR e fixedNow, totalR]
  have numJ : max 1 ((∑ i ∈ (Finset.range justified.validators.data.size).filter
      (fun i => isActiveAt justified (getPreviousEpoch justified) i = true),
      ((justified.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0) / inc) = num := by
    rw [sumJ, JPrev, sumZR _ fixedBefore, numR]
  -- The rewards credit each old position at most its flag credit.
  obtain ⟨flagP, flagEq⟩ : ∃ fl : ℕ → ℕ, ∀ i, fl i = (if .altair ≤ F then
      base i * flagWeight * num / (WEIGHT_DENOMINATOR.toNat * den)
      else 3 * (base i * max num den / den) + base i) := ⟨_, fun _ => rfl⟩
  have creditEq : ∀ i, credit i = flagP i + slots * sync i := by
    intro i; rw [flagEq]
  have effJ : ∀ i < r.validators.data.size,
      ((justified.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0 = effective i := by
    intro i inside
    rw [effPR i inside, ← effZR i inside]
    simp only [effectiveAt, Jvalidators]
  have balJ : ∀ i, ((justified.balances.data[i]?).map (·.toNat)).getD 0 =
      actualBalanceAt ⟨F, zs⟩ i := by
    intro i
    simp only [actualBalanceAt, Jbalances]
  have rewardBound : ∀ i < r.validators.data.size, actualBalanceAt ⟨F, rewarded⟩ i ≤
      actualBalanceAt ⟨F, zs⟩ i + flagP i := by
    intro i inside
    have insideJ : i < justified.validators.data.size := by
      rw [Jvalidators]; exact Nat.lt_of_lt_of_le inside growsZ
    have bound := (processRewardsAndPenalties_balance_le_of_inactivityUpdates penaltyEntries_le
      toNat_getBaseReward_le altair (justified.validators.bound Fearly) scoredOk rewardedOk i
      insideJ).1
    dsimp only at bound
    rw [totalJ, numJ, effJ i inside, balJ] at bound
    simp only [flagEq, altair, ↓reduceIte, base, perIncrement, root, den, flagWeight]
    exact bound
  -- The validators of `P` active in the next epoch are old, and active then at `R`, `z` and later.
  have fixedZ : activityFixedEpoch zs = activityFixedEpoch r := by
    simp only [activityFixedEpoch, epochZ, he]
  have upcomingR : ∀ i, upcoming i = isActiveAt r (e + 1) i := by
    intro i
    show isActiveAt q (getCurrentEpoch q + 1) i = _
    rw [epochP]
    exact activeP _ fixedNext i
  have upcomingZ : ∀ i, isActiveAt zs (e + 1) i = isActiveAt r (e + 1) i :=
    fun i => activeZ _ fixedNext i
  have upcomingReset : ∀ i, isActiveAt reset (e + 1) i = isActiveAt r (e + 1) i :=
    fun i => (resetActive _ (fixedZ ▸ fixedNext) i).trans (upcomingZ i)
  have insideU : ∀ i, upcoming i = true → i < r.validators.data.size := by
    intro i up
    rw [upcomingR] at up
    obtain ⟨v, found, -⟩ := isActiveAt_eq_true_iff.mp up
    exact (Array.getElem?_eq_some_iff.mp found).1
  have resetEpoch : getCurrentEpoch reset = e := by
    rw [← epochZ]; simp only [getCurrentEpoch, resetSlot]
  -- The pending balances credit at most the churn and the due consolidations.
  obtain ⟨pd, cs, pdKeys, csKeys, pendingBound, pdCard, pdOff, csCard, csOff, pdSum, csSum⟩ :
      ∃ (pd cs : ℕ → ℕ) (pdKeys csKeys : Finset ℕ),
        (∀ i < r.validators.data.size, actualBalanceAt ⟨F, beforeState⟩ i ≤
          actualBalanceAt ⟨F, reset⟩ i + pd i + cs i) ∧
        pdKeys.card ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat ∧
        (∀ i ∉ pdKeys, pd i = 0) ∧ csKeys.card ≤ due.length ∧ (∀ i ∉ csKeys, cs i = 0) ∧
        ∑ i ∈ positions with upcoming i, pd i ≤ depositCredit ∧
        ∑ i ∈ positions with upcoming i, cs i ≤ dueStake := by
    have electra := electraF
    unfold processPendingBalances at pendingOk
    simp only [electra, ↓reduceDIte] at pendingOk
    obtain ⟨deposited, depositedOk, consolidatedOk⟩ := bind_ok_iff.mp pendingOk
    have matchedReset := resetMatch invZ.balancesMatch
    obtain ⟨pd, pdKeys, pdCard, pdOff, pdBound, pdSumFn⟩ :=
      rise_pendingDeposits depositedOk matchedReset
    obtain ⟨result, passed, balances, -⟩ := processPendingConsolidations_pass consolidatedOk
    obtain ⟨-, csBound⟩ := passConsolidations_gain passed
    have depositedSlot : deposited.slot = reset.slot :=
      (frame_processPendingDeposits depositedOk).slot
    have depositedEpoch : getCurrentEpoch deposited = e := by
      rw [← resetEpoch]; simp only [getCurrentEpoch, depositedSlot]
    have depositedQueue : deposited.pendingConsolidations electra =
        zs.pendingConsolidations electra := by
      rw [show deposited.pendingConsolidations = reset.pendingConsolidations from
        processPendingDeposits_pendingConsolidations depositedOk, resetQueue]
    have depositedRead := pendingDeposits_validators depositedOk
    -- Every entry of the queue at `z` that can pay is in the due list of `P`, with its value.
    have into : ∀ c ∈ (deposited.pendingConsolidations electra).data.toList,
        0 < consolidationGain deposited (getCurrentEpoch deposited + 1) c →
        c ∈ due ∧ consolidationGain deposited (getCurrentEpoch deposited + 1) c =
          effective c.sourceIndex.toNat := by
      intro c member positive
      have memberZ : c ∈ (zs.pendingConsolidations electra).data.toList := by
        rw [← depositedQueue]; exact member
      obtain ⟨vReset, readReset, -, ordered, -⟩ :=
        ((resetHolds holdsZ) electra).2 c (by rw [resetQueue]; exact memberZ)
      have insideReset := (Array.getElem?_eq_some_iff.mp readReset).1
      have readDep : deposited.validators.data[c.sourceIndex.toNat]? = some vReset := by
        rw [depositedRead _ insideReset]; exact readReset
      have gainEq : consolidationGain deposited (getCurrentEpoch deposited + 1) c =
          if vReset.slashed = false ∧ vReset.withdrawableEpoch ≤ getCurrentEpoch deposited + 1
          then vReset.effectiveBalance.toNat else 0 := by
        simp only [consolidationGain, readDep]
      rw [gainEq] at positive ⊢
      split at positive
      swap
      · exact absurd positive (Nat.lt_irrefl 0)
      rename_i cond
      obtain ⟨clear, dueReset⟩ := cond
      rw [depositedEpoch] at dueReset
      have dueNat := UInt64.le_iff_toNat_le.mp dueReset
      rw [nextNat] at dueNat
      have exitLe : vReset.exitEpoch.toNat ≤ e.toNat := by omega
      obtain ⟨vZ, readZ, -, -, assignedZ⟩ := (holdsZ electra).2 c memberZ
      -- The entry was already queued at `R`.
      have inR : c ∈ (r.pendingConsolidations electra).data.toList := by
        have queued := (queueZ (r.pendingConsolidations electra).data.toList
          (fun _ => ⟨fun _ h => h, fun _ h => .inl h⟩)) electra
        rcases queued.2 c memberZ with listed | ⟨w, readW, later, assigned⟩
        · exact listed
        · obtain ⟨later', readLater, step, -⟩ := resetRec _ w readW
          rw [readReset, Option.some.injEq] at readLater
          subst later'
          have exitSame := (step.2 assigned).1
          rw [he] at later
          have := UInt64.lt_iff_toNat_lt.mp later
          rw [← exitSame] at this
          omega
      obtain ⟨vR, readR, -, -, assignedR⟩ := (holdsR electra).2 c inR
      -- The withdrawal epoch at `R` is due by the next epoch.
      obtain ⟨wZ, readWZ, stepZ⟩ := wdZ _ vR readR
      rw [readZ, Option.some.injEq] at readWZ
      subst wZ
      obtain ⟨-, -, movedZ⟩ := stepZ.2 assignedR
      obtain ⟨wReset, readWReset, stepReset, -⟩ := resetRec _ vZ readZ
      rw [readReset, Option.some.injEq] at readWReset
      subst wReset
      have wdLe' := (stepReset.2 assignedZ).2.1
      have clearZ : vZ.slashed = false := by
        cases flag : vZ.slashed
        · rfl
        · have := stepReset.1 flag
          rw [this] at clear
          cases clear
      have wdR : vR.withdrawableEpoch ≤ e + 1 := by
        rcases movedZ with slashedZ | same
        · rw [slashedZ] at clearZ; cases clearZ
        · rw [← same]; exact UInt64.le_trans wdLe' dueReset
      -- At `P` the source is slashed or due.
      obtain ⟨wQ, readQ, stepQ⟩ := wdP _ vR readR
      obtain ⟨-, -, movedQ⟩ := stepQ.2 assignedR
      have inQ := ((queueP (r.pendingConsolidations electra).data.toList
        (fun _ => ⟨fun _ h => h, fun _ h => .inl h⟩)) electra).1 c inR
      have insideR := (Array.getElem?_eq_some_iff.mp readR).1
      refine ⟨?_, ?_⟩
      · simp only [due, electra, dite_true, List.mem_filter]
        refine ⟨inQ, ?_⟩
        simp only [validator, state, readQ, Option.map_some, Option.getD_some, Bool.or_eq_true,
          decide_eq_true_eq]
        rcases movedQ with slashedQ | same
        · exact .inl slashedQ
        · right
          rw [same]
          show vR.withdrawableEpoch ≤ getCurrentEpoch q + 1
          rw [epochP]
          exact wdR
      · rw [ite_eq_left ⟨clear, by rw [depositedEpoch]; exact dueReset⟩]
        have one := resetKept _ (Nat.lt_of_lt_of_le insideR growsZ)
        simp only [effectiveAt, readReset, readZ, Option.map_some, Option.getD_some] at one
        rw [one, effPR _ insideR, ← effZR _ insideR]
        simp [effectiveAt, readZ]
    have nodupZ : (zs.pendingConsolidations electra).data.toList.Nodup :=
      List.Nodup.of_map _ (holdsZ electra).1
    have nodupList : (deposited.pendingConsolidations electra).data.toList.Nodup := by
      rw [depositedQueue]; exact nodupZ
    have nodupDue : due.Nodup := by
      simp only [due, electra, dite_true]
      exact (List.Nodup.of_map _ (holdsP electra).1).filter _
    obtain ⟨gainSum, keysCard⟩ := gain_sum_le (·.targetIndex.toNat) nodupList nodupDue into
    -- The churn of the pending deposits reads the total active balance of `P`.
    obtain ⟨churn, -, -, -, -, -, -, churned, -⟩ := pendingDeposits_pass depositedOk
    obtain ⟨total', totalOk⟩ : ∃ total', getTotalActiveBalance reset = .ok total' := by
      cases h : getTotalActiveBalance reset with
      | error err =>
        rw [depositChurnLimit_of_lt Fearly] at churned
        simp [getActivationExitChurnLimit, getBalanceChurnLimit, h, bind, Except.bind] at churned
      | ok t => exact ⟨t, rfl⟩
    have churnValue : churn.toNat = depositChurn := by
      have value := depositChurnLimit_toNat_of_lt Fearly totalOk churned
      have totalValue := getTotalActiveBalance_toNat totalOk
      have sumReset := activeSum_eq (e := e)
        (fun i => resetActive e (by rw [fixedZ]; exact fixedNow) i) resetKept resetSize
      rw [resetEpoch, sumReset, sumZR e fixedNow, ← totalR] at totalValue
      rw [value, totalValue]
    have carry : (reset.depositBalanceToConsume electra).toNat =
        (q.depositBalanceToConsume electra).toNat := by
      rw [resetCarry, run_depositCarry toZ Fearly zEpoch electra electra,
        ← run_depositCarry tailP Fearly callEpoch electra electra]
    refine ⟨pd, fun i => ((deposited.pendingConsolidations electra).data.toList.map fun c =>
        if c.targetIndex.toNat = i then
          consolidationGain deposited (getCurrentEpoch deposited + 1) c else 0).sum, pdKeys,
      (((deposited.pendingConsolidations electra).data.toList.filter fun c =>
        0 < consolidationGain deposited (getCurrentEpoch deposited + 1) c).map
          (·.targetIndex.toNat)).toFinset, fun i inside => ?_, pdCard,
      pdOff, keysCard, fun i absent => ?_, ?_, ?_⟩
    · have one := csBound i
      have two := pdBound i (Nat.lt_of_lt_of_le inside (Nat.le_trans growsZ resetSize))
      have same : actualBalanceAt ⟨F, beforeState⟩ i = actualBalanceAt ⟨F, result.1⟩ i := by
        simp only [actualBalanceAt, balances]
      dsimp only at one two same ⊢
      omega
    · apply List.sum_eq_zero
      intro x member
      obtain ⟨c, cMem, rfl⟩ := List.mem_map.mp member
      split
      · rename_i hit
        by_contra nonzero
        apply absent
        rw [List.mem_toFinset, List.mem_map]
        exact ⟨c, List.mem_filter.mpr ⟨cMem, decide_eq_true (Nat.pos_of_ne_zero nonzero)⟩, hit⟩
      · rfl
    · have bound := pdSumFn (positions.filter fun i => upcoming i = true) churn churned
        (fun i member => by
          have up := (Finset.mem_filter.mp member).2
          rw [upcomingR, ← upcomingReset] at up
          obtain ⟨v, found, active⟩ := isActiveAt_eq_true_iff.mp up
          refine ⟨v, found, ?_⟩
          have ordered := resetExits invZ.exitsOrdered v (Array.mem_of_getElem? found)
          simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
          rw [resetEpoch]
          exact UInt64.not_lt.mpr (UInt64.le_of_lt (UInt64.lt_of_lt_of_le active.2 ordered)))
      simp only [depositCredit, electra, dite_true]
      rw [← carry, ← churnValue]
      exact bound
    · have swap : ∀ l : List PendingConsolidation,
          ∑ i ∈ positions with upcoming i, (l.map fun c => if c.targetIndex.toNat = i then
            consolidationGain deposited (getCurrentEpoch deposited + 1) c else 0).sum ≤
          (l.map (consolidationGain deposited (getCurrentEpoch deposited + 1))).sum := by
        intro l
        induction l with
        | nil => simp
        | cons c rest ih =>
          simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, Finset.sum_ite_eq]
          split <;> omega
      refine (swap _).trans (gainSum.trans (le_of_eq ?_))
      rfl
  -- The corrections of the branch of `y` inside the epoch.
  have bc := branchCorrections toZ Fearly fulu zEpoch invR.balancesMatch
    invR.exitsOrdered
  extract_lets stateZ pZ positionsZ validatorZ effectiveZ currentZ beforeZ recentZ
    slashedZ totalZ rootZ perIncrementZ baseZ seatRewardZ seatsZ syncZ syncProposerZ
    proposerCreditZ whistleblowerZ slashBackZ blocksZ debitedZ blockDepositsZ creditedZ at bc
  obtain ⟨debS, creditedKeys, pc, dep, -, -, -, upS, -, electraDep, -,
    ⟨slashedNow, slashedFacts, pcSlashed⟩, converted,
    ⟨proposerKeys, depositKeys, credSplit, propCard, -, pcOff, -⟩, -, -, -⟩ := bc
  have depZero : ∀ v, dep v = 0 := electraDep electraF
  -- The reads of the branch of `y` are those of `P`.
  have totalZeq : totalZ = total := by
    simp only [totalZ, positionsZ, currentZ, effectiveZ, stateZ, balanceAt]
    rw [epochZ, sumZR e fixedNow, ← totalR]
  have rootZeq : rootZ = root := by simp only [rootZ, root, totalZeq]
  have perIncrementZeq : perIncrementZ = perIncrement := by
    simp only [perIncrementZ, perIncrement, rootZeq]
  have seatRewardZeq : seatRewardZ = seatReward := by
    simp only [seatRewardZ, seatReward, totalZeq, perIncrementZeq]
  have syncProposerZeq : syncProposerZ = syncProposer := by
    simp only [syncProposerZ, syncProposer, seatRewardZeq]
  have pubkeyZP : ∀ i < r.validators.data.size,
      (zs.validators.data[i]?).map (·.pubkey) = (q.validators.data[i]?).map (·.pubkey) := by
    intro i inside
    obtain ⟨vR, readR⟩ : ∃ v, r.validators.data[i]? = some v :=
      ⟨_, Array.getElem?_eq_getElem inside⟩
    obtain ⟨wZ, readZ, keyZ⟩ := validators_getElem?_of_validatorKeys_prefix keysZ readR
    obtain ⟨wP, readP, keyP⟩ := validators_getElem?_of_validatorKeys_prefix keysP readR
    simp only [readZ, readP, Option.map_some, keyZ, keyP]
  have syncZeq : ∀ i < r.validators.data.size, syncZ i = sync i := by
    intro i inside
    simp only [syncZ, sync, seatRewardZeq]
    congr 1
    simp only [seatsZ, seats]
    rw [dite_eq_left_of_eq_true (eq_true altair), dite_eq_left_of_eq_true (eq_true altair)]
    refine seats_eq altair altair ?_ (pubkeyZP i inside)
    rw [committeeZ altair altair, committeeP altair altair]
  have baseZeq : ∀ i < r.validators.data.size, baseZ i = base i := by
    intro i inside
    have one : effectiveZ i = effective i := by
      simp only [effectiveZ, stateZ]
      rw [show balanceAt zs i = effectiveAt ⟨F, zs⟩ i from rfl, effZR i inside, ← effPR i inside]
    simp only [baseZ, base, one, perIncrementZeq, rootZeq]
  have setP : positions.filter (fun i => recent i = true) =
      (Finset.range r.validators.data.size).filter
        (fun i => isActiveAt r (getPreviousEpoch r) i = true) ∪
      (Finset.range r.validators.data.size).filter (fun i => isActiveAt r e i = true) := by
    simp only [positions, recent, before, current, state, epoch, Bool.or_eq_true,
      Finset.filter_or]
    rw [prevP, epochP, filterP _ fixedBefore, filterP _ fixedNow]
  have recentZeq : ∑ i ∈ positionsZ with recentZ i, baseZ i =
      ∑ i ∈ positions with recent i, base i := by
    have setZ : positionsZ.filter (fun i => recentZ i = true) =
        (Finset.range r.validators.data.size).filter
          (fun i => isActiveAt r (getPreviousEpoch r) i = true) ∪
        (Finset.range r.validators.data.size).filter (fun i => isActiveAt r e i = true) := by
      simp only [positionsZ, recentZ, beforeZ, currentZ, stateZ, Bool.or_eq_true,
        Finset.filter_or]
      rw [prevZ, epochZ, filterZ _ fixedBefore, filterZ _ fixedNow]
    rw [setZ, setP]
    refine Finset.sum_congr rfl fun i member => baseZeq i ?_
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range] at member
    rcases member with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
  -- The positions below the registry size are indices.
  have toIdx : ∀ i < r.validators.data.size, (UInt64.ofNat i).toNat = i := by
    intro i inside
    have := BeaconState.validators_size_lt_of_lt_glamsterdam Fearly r
    exact UInt64.toNat_ofNat_of_lt' (Nat.lt_trans inside this)
  have slotsPos : 0 < slots := by
    by_contra zero
    have zero : slots = 0 := by omega
    have epochY := getCurrentEpoch_toNat y.state
    have epochR := getCurrentEpoch_toNat r
    simp only [slots] at zero
    rw [zero, Nat.div_zero] at epochY epochR
    rw [he] at epochR
    omega
  -- The blocks of the epoch fit its slots.
  have blocksLe : toZ.blockCount ≤ slots := by
    have epochR := getCurrentEpoch_toNat r
    have epochZ' := getCurrentEpoch_toNat zs
    rw [epochZ, ← he] at epochZ'
    have sameQuotient : zs.slot.toNat / slots = r.slot.toNat / slots := by
      simp only [slots]
      omega
    have bound := toZ.blocks_le_slots (a := r.slot.toNat / slots * slots)
      (b := r.slot.toNat / slots * slots + slots - 1) (Nat.div_mul_le_self _ _) (by
        have split := Nat.div_add_mod zs.slot.toNat slots
        have small := Nat.mod_lt zs.slot.toNat slotsPos
        rw [sameQuotient, Nat.mul_comm] at split
        show zs.slot.toNat ≤ _
        omega)
    omega
  -- The largest effective balances are at most the largest of the fork.
  have capLe : ∀ v : Validator, (withdrawalMaxEffectiveBalance preset F v).toNat ≤ capMax := by
    intro v
    simp only [capMax, electraF, ↓reduceIte, withdrawalMaxEffectiveBalance, getMaxEffectiveBalance]
    split
    · exact Nat.le_refl _
    · exact UInt64.le_iff_toNat_le.mp caps.compounding
  have cappedR := history.effectiveBalance_capped genesis caps.activation caps.compounding Fearly
  -- The crossing of each validator.
  obtain ⟨cross, crossEq⟩ : ∃ f : ℕ → ℕ, ∀ i, f i = (if effective i < cap i then
      (if effective i + preset.upwardBand < actual i + slashBack i + syncP i + credit i then
        actual i + slashBack i + syncP i + credit i - effective i else 0)
      else (if preset.upwardBand < credit i then credit i else 0)) := ⟨_, fun _ => rfl⟩
  have crossingEq : crossing = ∑ i ∈ positions with upcoming i, cross i := by
    simp only [crossing, crossEq]
  -- The rise of each validator active in the next epoch.
  have each : ∀ i ∈ positions, upcoming i = true →
      effectiveAt y i - effective i ≤ capMax - effective i ∧
      (UInt64.ofNat i ∉ debitedKeys → effectiveAt y i - effective i ≤ cross i +
        (if pc (UInt64.ofNat i) + (pd i + cs i) = 0 then 0
          else preset.upwardBand) + (pc (UInt64.ofNat i) + (pd i + cs i))) ∧
      (UInt64.ofNat i ∈ debitedKeys → effectiveAt y i - effective i ≤ preset.upwardBand +
        credit i + (pc (UInt64.ofNat i) + (pd i + cs i))) := by
    intro i member up
    have inside := insideU i up
    have idx := toIdx i inside
    obtain ⟨vR, readR⟩ : ∃ v, r.validators.data[i]? = some v :=
      ⟨_, Array.getElem?_eq_getElem inside⟩
    obtain ⟨vZ, readZ⟩ : ∃ v, zs.validators.data[i]? = some v :=
      ⟨_, Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le inside growsZ)⟩
    have effR : effective i = vR.effectiveBalance.toNat := by
      rw [effPR i inside]; simp [effectiveAt, readR]
    have effZ : vZ.effectiveBalance.toNat = vR.effectiveBalance.toNat := by
      have := effZR i inside
      simpa [effectiveAt, readZ, readR] using this
    have insideZ' : i < z'.state.validators.data.size :=
      Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le inside growsZ)
        (Run.nil.snoc (.slot edge)).registryLifecycle.size_le
    have yEff : effectiveAt y i = effectiveAt z' i :=
      fromZ'.effectiveKept_of_same_epoch early z'Epoch.symm i insideZ'
    have upd := updateBound i vZ readZ
    rw [← yEff, effZ, ← effR] at upd
    -- The balance at the update.
    have balChain : actualBalanceAt ⟨F, beforeState⟩ i ≤
        actualBalanceAt ⟨F, zs⟩ i + flagP i + (0 + pd i + cs i) := by
      have a := pendingBound i inside
      have b := lower i
      have c := rewardBound i inside
      dsimp only at a b c ⊢
      omega
    -- The branch of `y` inside the epoch.
    have upI := upS (UInt64.ofNat i)
    rw [idx, syncZeq i inside] at upI
    have blocksI : blocksZ * sync i ≤ slots * sync i := Nat.mul_le_mul_right _ blocksLe
    have convI : (withdrawalMaxEffectiveBalance preset F vZ).toNat ≠
        (withdrawalMaxEffectiveBalance preset F vR).toNat →
        actualBalanceAt ⟨F, zs⟩ i ≤ preset.MIN_ACTIVATION_BALANCE.toNat + blocksZ * sync i +
          pc (UInt64.ofNat i) + dep (UInt64.ofNat i) := by
      intro differ
      have := converted (UInt64.ofNat i) vR vZ (by rw [idx]; exact readR) (by rw [idx]; exact readZ)
        (fun same => differ (by rw [same]))
      rw [idx, syncZeq i inside] at this
      exact this
    have actI : (withdrawalMaxEffectiveBalance preset F vR).toNat ≤ effective i →
        (withdrawalMaxEffectiveBalance preset F vZ).toNat ≠
          (withdrawalMaxEffectiveBalance preset F vR).toNat →
        preset.MIN_ACTIVATION_BALANCE.toNat ≤ effective i := by
      intro le _
      have low : preset.MIN_ACTIVATION_BALANCE.toNat ≤
          (withdrawalMaxEffectiveBalance preset F vR).toNat := by
        simp only [withdrawalMaxEffectiveBalance, electraF, ↓reduceIte, getMaxEffectiveBalance]
        split
        · exact UInt64.le_iff_toNat_le.mp caps.compounding
        · exact Nat.le_refl _
      omega
    have one := rise_one (EB := effective i) (effY := effectiveAt y i)
      (band := preset.upwardBand) (bal := actualBalanceAt ⟨F, beforeState⟩ i)
      (aZ := actualBalanceAt ⟨F, zs⟩ i) (aR := actualBalanceAt ⟨F, r⟩ i) (aP := actual i)
      (flag := flagP i) (extra := 0 + pd i + cs i) (blocksSync := blocksZ * sync i)
      (slotsSync := slots * sync i) (pc := pc (UInt64.ofNat i)) (dep := dep (UInt64.ofNat i))
      (slashBack := slashBack i) (nSync := syncP i)
      (capR := (withdrawalMaxEffectiveBalance preset F vR).toNat)
      (capZ := (withdrawalMaxEffectiveBalance preset F vZ).toNat) (capP := cap i)
      (minAct := preset.MIN_ACTIVATION_BALANCE.toNat) upd balChain upI blocksI convI actI
    rw [depZero] at one
    have capRle : vR.effectiveBalance.toNat ≤ (withdrawalMaxEffectiveBalance preset F vR).toNat :=
      UInt64.le_iff_toNat_le.mp (cappedR vR (Array.mem_of_getElem? readR))
    refine ⟨?_, fun absent => ?_, fun present => ?_⟩
    · have := capLe vZ
      have := capLe vR
      dsimp only at upd
      rw [effR] at upd
      apply Nat.sub_le_sub_right
      rcases upd with low | ⟨-, -, high⟩ <;> omega
    · have nondebited := offDebited (UInt64.ofNat i) absent
      rw [idx] at nondebited
      obtain ⟨later, readP, sameCap⟩ :=
        capsKept (UInt64.ofNat i) vR absent (by rw [idx]; exact readR)
      rw [idx] at readP
      have capEq : (withdrawalMaxEffectiveBalance preset F vR).toNat = cap i := by
        simp only [cap, validator, state, readP, Option.map_some, Option.getD_some]
        rw [sameCap]
      have bound := one.1 nondebited capEq
      rw [crossEq, creditEq]
      simp only [Nat.zero_add, Nat.add_zero] at bound ⊢
      exact bound
    · have debitedI : effective i < (withdrawalMaxEffectiveBalance preset F vR).toNat →
          actualBalanceAt ⟨F, r⟩ i ≤ effective i + preset.upwardBand := by
        intro below
        obtain ⟨balance, readBal⟩ : ∃ b, r.balances.data[i]? = some b :=
          ⟨_, Array.getElem?_eq_getElem (by rw [invR.balancesMatch]; exact inside)⟩
        have hys := hysteresis.up i vR balance readR readBal
          (UInt64.lt_iff_toNat_lt.mpr (by rw [← effR]; exact below))
        simp only [actualBalanceAt, readBal, Option.map_some, Option.getD_some]
        rw [effR]
        exact hys
      have bound := one.2 debitedI
      rw [creditEq]
      simp only [Nat.zero_add, Nat.add_zero] at bound ⊢
      exact bound
  -- The recipients of the proposer credits fit the proposers.
  have inKeys : ∀ i, 0 < pc (UInt64.ofNat i) → UInt64.ofNat i ∈ proposerKeys := by
    intro i positive
    by_contra absent
    rw [pcOff _ absent] at positive
    exact Nat.lt_irrefl 0 positive
  have recipsCard : (proposerKeys.image UInt64.toNat).card ≤ proposers := by
    have card := Finset.card_image_le (s := proposerKeys) (f := UInt64.toNat)
    have blocksBound : proposerKeys.card ≤ blocksZ := propCard.trans (by split <;> omega)
    simp only [proposers, altair, ↓reduceIte]
    simp only [blocksZ] at blocksBound
    omega
  -- The validators slashed on the branch of `y` are among those that `P` can slash.
  have farE : e.toNat < FAR_FUTURE_EPOCH.toNat := by
    have farNat : FAR_FUTURE_EPOCH.toNat = 18446744073709551615 := rfl
    omega
  have wbLe : (∑ v ∈ slashedNow, effectiveZ v.toNat) / pZ.WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤
      whistleblower := by
    apply Nat.div_le_div_right
    have inR : ∀ v ∈ slashedNow, v.toNat < r.validators.data.size := by
      intro v member
      obtain ⟨-, -, vR, readR, -⟩ := slashedFacts v member
      exact (Array.getElem?_eq_some_iff.mp readR).1
    calc ∑ v ∈ slashedNow, effectiveZ v.toNat = ∑ v ∈ slashedNow, effective v.toNat := by
          refine Finset.sum_congr rfl fun v member => ?_
          simp only [effectiveZ, stateZ]
          rw [show balanceAt zs v.toNat = effectiveAt ⟨F, zs⟩ v.toNat from rfl,
            effZR _ (inR v member), ← effPR _ (inR v member)]
      _ = ∑ i ∈ slashedNow.image UInt64.toNat, effective i :=
          (Finset.sum_image fun a _ b _ same => UInt64.toNat_inj.mp same).symm
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset
          intro i member
          obtain ⟨v, vMem, rfl⟩ := Finset.mem_image.mp member
          obtain ⟨-, -, vR, readR, activated, live⟩ := slashedFacts v vMem
          have insideR := (Array.getElem?_eq_some_iff.mp readR).1
          obtain ⟨wq, readQ, stepQ⟩ := wdP _ vR readR
          obtain ⟨later, readLater, life⟩ := tailP.registryLifecycle.validators _ vR readR
          rw [readQ, Option.some.injEq] at readLater
          subst later
          have activatedNat := UInt64.le_iff_toNat_le.mp activated
          rw [he] at activatedNat
          have activationSame : wq.activationEpoch = vR.activationEpoch :=
            life.activationEpoch (fun far => by
              rw [far] at activatedNat
              omega)
          have wdLater : e < wq.withdrawableEpoch := by
            rw [he] at live
            by_cases exited : vR.exitEpoch = FAR_FUTURE_EPOCH
            · have activeR : isActiveAt r e v.toNat = true := by
                apply isActiveAt_eq_true_iff.mpr
                refine ⟨vR, readR, ?_⟩
                simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq]
                refine ⟨by rw [← he]; exact activated, ?_⟩
                rw [exited]
                exact UInt64.lt_iff_toNat_lt.mpr farE
              rw [← activeP e fixedNow] at activeR
              obtain ⟨w', read', active'⟩ := isActiveAt_eq_true_iff.mp activeR
              rw [readQ, Option.some.injEq] at read'
              subst w'
              simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active'
              exact UInt64.lt_of_lt_of_le active'.2
                (invP.exitsOrdered wq (Array.mem_of_getElem? readQ))
            · exact UInt64.lt_of_lt_of_le live (stepQ.2 exited).2.1
          simp only [Finset.mem_filter, positions, Finset.mem_range, validator, state, readQ,
            Option.any_some, Bool.and_eq_true, decide_eq_true_eq, epoch, epochP]
          refine ⟨Nat.lt_of_lt_of_le insideR growsP, ?_, wdLater⟩
          rw [activationSame, ← he]
          exact activated
  -- The proposer credits of the upcoming validators are among those of the credited keys.
  have pcSum : ∑ i ∈ positions with upcoming i, pc (UInt64.ofNat i) ≤
      ∑ v ∈ creditedKeys, pc v := by
    rw [← Finset.sum_image (f := pc) (fun a member b member' same => by
      have ia := toIdx a (insideU a (Finset.mem_filter.mp member).2)
      have ib := toIdx b (insideU b (Finset.mem_filter.mp member').2)
      rw [← ia, ← ib, same])]
    apply Finset.sum_le_sum_of_ne_zero
    intro v _ nonzero
    rw [credSplit]
    apply Finset.mem_union_left
    by_contra absent
    exact nonzero (pcOff v absent)
  -- The transfers of the upcoming validators.
  have transferLe : ∑ i ∈ positions with upcoming i,
      (pc (UInt64.ofNat i) + (pd i + cs i)) ≤ transfers := by
    simp only [Finset.sum_add_distrib]
    have pcBound := pcSum.trans pcSlashed
    rw [recentZeq, syncProposerZeq] at pcBound
    have := wbLe
    simp only [transfers, proposerCredit]
    omega
  -- Put the rises together.
  have eachSum : ∀ i ∈ positions.filter (fun i => upcoming i = true), i ∉ (∅ : Finset ℕ) →
      effectiveAt y i - effective i ≤ cross i +
        (if i ∈ (positions.filter (fun i => upcoming i = true)).filter
            (fun i => 0 < pc (UInt64.ofNat i) + (pd i + cs i))
          then preset.upwardBand else 0) +
        (if i ∈ debitedKeys.image UInt64.toNat then preset.upwardBand + creditMax else 0) +
        (pc (UInt64.ofNat i) + (pd i + cs i)) := by
    intro i memberU _
    obtain ⟨member, up⟩ := Finset.mem_filter.mp memberU
    have idx := toIdx i (insideU i up)
    obtain ⟨-, offBound, onBound⟩ := each i member up
    by_cases debitedI : UInt64.ofNat i ∈ debitedKeys
    · have inD : i ∈ debitedKeys.image UInt64.toNat := Finset.mem_image.mpr ⟨_, debitedI, idx⟩
      have creditLe : credit i ≤ creditMax := by
        have := Finset.le_sup (f := fun i => if upcoming i = true then credit i else 0) member
        simp only [up, ↓reduceIte] at this
        exact this
      have := onBound debitedI
      simp only [inD, ↓reduceIte]
      split <;> omega
    · have := offBound debitedI
      by_cases zero : pc (UInt64.ofNat i) + (pd i + cs i) = 0
      · simp only [zero, Nat.add_zero, ↓reduceIte] at this
        split <;> split <;> omega
      · have inA : i ∈ (positions.filter (fun i => upcoming i = true)).filter
            (fun i => 0 < pc (UInt64.ofNat i) + (pd i + cs i)) :=
          Finset.mem_filter.mpr ⟨memberU, Nat.pos_of_ne_zero zero⟩
        simp only [zero, ↓reduceIte, inA] at this ⊢
        split <;> omega
  have sumBound := rise_sum (capMax := capMax) eachSum (fun _ _ absent => absurd absent nofun)
  -- The recipients of transfers and the debited validators.
  have cardA : (positions.filter (fun i => upcoming i = true) ∩
      (positions.filter (fun i => upcoming i = true)).filter
        (fun i => 0 < pc (UInt64.ofNat i) + (pd i + cs i))).card ≤ recipients := by
    have sub : positions.filter (fun i => upcoming i = true) ∩
        (positions.filter (fun i => upcoming i = true)).filter
          (fun i => 0 < pc (UInt64.ofNat i) + (pd i + cs i)) ⊆
        proposerKeys.image UInt64.toNat ∪ pdKeys ∪ csKeys := by
      intro i member
      obtain ⟨memberU, memberA⟩ := Finset.mem_inter.mp member
      obtain ⟨member', up⟩ := Finset.mem_filter.mp memberU
      have positive := (Finset.mem_filter.mp memberA).2
      simp only [Finset.mem_union]
      by_cases first : 0 < pc (UInt64.ofNat i)
      · exact .inl (.inl (Finset.mem_image.mpr ⟨_, inKeys i first, toIdx i (insideU i up)⟩))
      · by_cases second : 0 < pd i
        · left; right
          by_contra absent
          rw [pdOff i absent] at second
          exact Nat.lt_irrefl 0 second
        · right
          by_contra absent
          rw [csOff i absent] at positive
          omega
    refine (Finset.card_le_card sub).trans ?_
    have union := Finset.card_union_le (proposerKeys.image UInt64.toNat ∪ pdKeys) csKeys
    have union' := Finset.card_union_le (proposerKeys.image UInt64.toNat) pdKeys
    simp only [recipients, depositRecipients, electraF, ↓reduceIte]
    omega
  have cardD : (positions.filter (fun i => upcoming i = true) ∩
      debitedKeys.image UInt64.toNat).card ≤ debited :=
    (Finset.card_le_card Finset.inter_subset_right).trans (Finset.card_image_le.trans debitedCard)
  refine le_min ?_ ?_
  · exact Finset.sum_le_sum fun i memberU =>
      (each i (Finset.mem_filter.mp memberU).1 (Finset.mem_filter.mp memberU).2).1
  · refine sumBound.trans ?_
    rw [crossingEq]
    have one := Nat.mul_le_mul_right preset.upwardBand cardA
    have two := Nat.mul_le_mul_right preset.upwardBand cardD
    have three := Nat.mul_le_mul_right creditMax cardD
    simp only [Finset.inter_empty, Finset.card_empty, Nat.zero_mul, Nat.add_zero]
    rw [Nat.mul_add, Nat.add_mul]
    omega

end EthLib.Consensus
