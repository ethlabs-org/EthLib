module

public import EthLib.Consensus.Proofs.Transition.Trace
public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
public import EthLib.Consensus.Proofs.Transition.Genesis

/-!
# Pending consolidation sources

Every pending source remains in the validator registry along a run before Gloas.

Electra starts an empty queue, requests append existing indices, and processing drops a prefix.
-/

@[expose] public section
namespace EthLib.Consensus
open Base
variable {preset : Preset} {config : Config} {checks : SignatureChecks}

theorem processPendingDeposits_pendingConsolidations {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f}
    (ok : processPendingDeposits config checks s electra = .ok t) :
    t.pendingConsolidations = s.pendingConsolidations := by
  have deposit {a b : BeaconState preset f} {d : PendingDeposit}
      (ok : applyPendingDeposit config checks a d = .ok b) :
      b.pendingConsolidations = a.pendingConsolidations := by
    unfold applyPendingDeposit at ok
    split at ok
    · split at ok
      · cases ok; rfl
      simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · unfold addValidatorToRegistry at ok
        split at ok
        · simp only [addValidatorToRegistryAltair, bind_ok_iff, liftAccessor_ok,
            pure, Except.pure, Except.ok.injEq] at ok
          obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := ok
          rfl
        · split at ok <;> cases ok
          rfl
      · cases ok; rfl
    · simp only [liftAccessor_ok, bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      obtain ⟨_, set⟩ := increaseBalance_ok ok
      obtain ⟨_, rfl⟩ := setBalance_ok set
      rfl
  have pass {stop : PendingDeposit → Bool} {nextEpoch : Epoch} {available : Gwei} :
      ∀ {entries : List PendingDeposit} {a : BeaconState preset f} {processed : Gwei}
        {count : Nat} {postponed : Array PendingDeposit} {result},
        passPendingDeposits config checks stop nextEpoch available a processed count
          postponed entries = .ok result →
          result.1.state.pendingConsolidations = a.pendingConsolidations := by
    intro entries
    induction entries with
    | nil => intro a processed count postponed result ok; cases ok; rfl
    | cons d rest ih =>
      intro a processed count postponed result ok
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
        exact (ih ‹_›).trans (deposit credited)
      split at ok
      · split at ok
        · cases ok
        cases ok
        exact ih ‹_›
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
      exact (ih ‹_›).trans (deposit credited)
  unfold processPendingDeposits at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals exact pass ‹_›

private def PendingSources {f : Fork} (s : BeaconState preset f) : Prop :=
  ∀ electra : .pectra ≤ f, ∀ entry ∈ (s.pendingConsolidations electra).data.toList,
    entry.sourceIndex.toNat < s.validators.data.size

private def SamePendingQueue {f : Fork} (s t : BeaconState preset f) : Prop :=
  t.pendingConsolidations = s.pendingConsolidations

private theorem SamePendingQueue.trans {f : Fork} {s t u : BeaconState preset f}
    (one : SamePendingQueue s t) (two : SamePendingQueue t u) : SamePendingQueue s u :=
  Eq.trans two one

private theorem SamePendingQueue.fold {f : Fork} {s t : BeaconState preset f} {α ε : Type}
    {step : BeaconState preset f → α → Except ε (BeaconState preset f)} {xs : List α}
    (kept : ∀ a item b, step a item = .ok b → SamePendingQueue a b)
    (ok : xs.foldlM step s = .ok t) : SamePendingQueue s t :=
  foldlM_ok_invariant (SamePendingQueue s)
    (fun _ _ _ prior computed => prior.trans (kept _ _ _ computed)) rfl ok

private theorem SamePendingQueue.setValidatorAt {f : Fork} {s t : BeaconState preset f}
    {i : Nat} {v : Validator} (ok : s.setValidatorAt i v = .ok t) : SamePendingQueue s t := by
  obtain ⟨_, rfl⟩ := setValidatorAt_ok ok
  rfl

private theorem SamePendingQueue.setValidator {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} {v : Validator} (ok : s.setValidator i v = .ok t) :
    SamePendingQueue s t :=
  setValidatorAt (by rwa [← setValidator_eq_setValidatorAt])

private theorem SamePendingQueue.increase {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} {amount : Gwei} (ok : increaseBalance s i amount = .ok t) :
    SamePendingQueue s t := by
  obtain ⟨_, set⟩ := increaseBalance_ok ok
  obtain ⟨_, rfl⟩ := setBalance_ok set
  rfl

private theorem SamePendingQueue.decrease {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} {amount : Gwei} (ok : decreaseBalance s i amount = .ok t) :
    SamePendingQueue s t := by
  obtain ⟨_, rfl⟩ := decreaseBalance_eq_ok_iff.mp ok
  rfl

private theorem SamePendingQueue.exit {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} (ok : initiateValidatorExit config s i = .ok t) :
    SamePendingQueue s t := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok ok
  · rfl
  · obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
    have kept := setValidator set
    exact kept

private theorem SamePendingQueue.rewards {f : Fork} {s t : BeaconState preset f}
    (ok : processRewardsAndPenalties config s = .ok t) : SamePendingQueue s t := by
  have all {a b : BeaconState preset f} {deltas : Array Gwei × Array Gwei}
      (ok : applyAllDeltas a deltas = .ok b) : SamePendingQueue a b := by
    apply fold (fun _ _ _ ok => ?_) ok
    simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, raised, lowered⟩ := ok
    exact (increase raised).trans (decrease lowered)
  unfold processRewardsAndPenalties at ok
  split at ok
  · cases ok; rfl
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, _, _, applied⟩ := ok
    exact fold (fun _ _ _ => all) applied
  · obtain ⟨_, _, applied⟩ := bind_ok_iff.mp ok
    exact all applied

private theorem SamePendingQueue.registry {f : Fork} {s t : BeaconState preset f}
    (ok : processRegistryUpdates config s = .ok t) : SamePendingQueue s t := by
  have entry {a b : BeaconState preset f} {i : Nat}
      (ok : updateRegistryEntry config a i = .ok b) : SamePendingQueue a b := by
    simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, _, marked, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, exited⟩ := ok
      exact (setValidatorAt marked).trans (exit exited)
    · cases ok; exact setValidatorAt marked
  have electra {a b : BeaconState preset f} {i : Nat} {epoch : Epoch}
      (ok : updateRegistryEntryElectra config epoch a i = .ok b) : SamePendingQueue a b := by
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, set⟩ := ok
      exact setValidatorAt set
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, exited⟩ := ok
      exact exit exited
    split at ok
    · exact setValidatorAt (liftAccessor_ok.mp ok)
    · cases ok; rfl
  unfold processRegistryUpdates at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact fold (fun _ _ _ => electra) ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, updated, activated⟩ := ok
  apply (fold (fun _ _ _ => entry) updated).trans
  apply fold (fun _ _ _ ok => ?_) activated
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, set⟩ := ok
  exact setValidator set

private theorem SamePendingQueue.slashings {f : Fork} {s t : BeaconState preset f}
    (ok : processSlashings s = .ok t) : SamePendingQueue s t := by
  unfold processSlashings at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, ok⟩ := ok
  split at ok
  · obtain ⟨_, _, applied⟩ := bind_ok_iff.mp ok
    refine fold (fun _ _ _ ok => ?_) applied
    simp only [applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · obtain ⟨_, _, ok⟩ := bind_ok_iff.mp ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, _, _, lowered⟩ := ok
        exact decrease lowered
      · cases ok; rfl
    · cases ok; rfl
  · refine fold (fun _ _ _ ok => ?_) ok
    simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · obtain ⟨_, _, ok⟩ := bind_ok_iff.mp ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, _, _, _, _, lowered⟩ := ok
        exact decrease lowered
      · cases ok; rfl
    · cases ok; rfl

private theorem SamePendingQueue.effectiveUpdates {f : Fork} {s t : BeaconState preset f}
    (ok : processEffectiveBalanceUpdates s = .ok t) : SamePendingQueue s t := by
  apply fold (fun _ _ _ ok => ?_) ok
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, set⟩ := ok
  exact setValidatorAt set

private theorem SamePendingQueue.inactivity {f : Fork} {s t : BeaconState preset f}
    {altair : .altair ≤ f} (ok : processInactivityUpdates config s altair = .ok t) :
    SamePendingQueue s t := by
  unfold processInactivityUpdates at ok
  split at ok
  · cases ok; rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    rfl

private theorem SamePendingQueue.justification {f : Fork} {s t : BeaconState preset f}
    (ok : processJustificationAndFinalization s = .ok t) : SamePendingQueue s t := by
  obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok ok
  · rfl
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    unfold SamePendingQueue
    rw [← rest]

private theorem SamePendingQueue.eth1Reset {f : Fork} {s t : BeaconState preset f}
    {before : f < .hegota} (ok : processEth1DataReset before s = .ok t) :
    SamePendingQueue s t := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok <;> cases ok <;> rfl

private theorem PendingSources.kept {f : Fork} {s t : BeaconState preset f}
    (holds : PendingSources s) (queue : SamePendingQueue s t)
    (grows : s.validators.data.size ≤ t.validators.data.size) : PendingSources t := by
  intro electra entry mem
  change t.pendingConsolidations = s.pendingConsolidations at queue
  rw [queue] at mem
  exact Nat.lt_of_lt_of_le (holds electra entry mem) grows

private theorem PendingSources.consolidations {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} (holds : PendingSources s)
    (ok : processPendingConsolidations s electra = .ok t) : PendingSources t := by
  obtain ⟨result, _, _, queue⟩ := processPendingConsolidations_pass ok
  intro electra entry mem
  rw [queue] at mem
  rw [(processPendingConsolidations_kept ok).1]
  exact holds electra entry (List.mem_of_mem_drop mem)

private theorem PendingSources.pending {f : Fork} {s t : BeaconState preset f}
    (holds : PendingSources s) (ok : processPendingBalances config checks s = .ok t) :
    PendingSources t := by
  unfold processPendingBalances at ok
  split at ok
  · obtain ⟨_, deposited, consolidated⟩ := bind_ok_iff.mp ok
    exact (holds.kept (processPendingDeposits_pendingConsolidations deposited)
      (registryLifecycle_processPendingDeposits deposited).size_le).consolidations consolidated
  · cases ok; exact holds

private theorem PendingSources.queue {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (holds : PendingSources s)
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    PendingSources t := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at ok
  obtain ⟨⟨churned, epoch⟩, churnOk, _, _, written, set, pending, appended, final⟩ := ok
  cases final
  have data := appendWithinLimit_data appended
  have size := (sameSizes_setValidator set).1
  have bound : sourceIndex.toNat < churned.validators.data.size := (setValidator_ok set).1
  have churnQueue : churned.pendingConsolidations = s.pendingConsolidations := by
    simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churnOk
    obtain ⟨_, _, _, _, _, _, final⟩ := churnOk
    cases final
    rfl
  have churnSize := (computeConsolidationEpochAndUpdateChurn_earliest churnOk).2.1
  have kept := SamePendingQueue.setValidator set
  change written.pendingConsolidations = churned.pendingConsolidations at kept
  intro witness entry mem
  change entry ∈ pending.data.toList at mem
  rw [data, Array.toList_push, List.mem_append, List.mem_singleton] at mem
  change entry.sourceIndex.toNat < written.validators.data.size
  rw [size]
  rcases mem with previous | rfl
  · rw [kept, churnQueue] at previous
    rw [churnSize]
    exact holds electra entry previous
  · exact bound

private theorem SamePendingQueue.compounding {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {index : ValidatorIndex}
    (ok : switchToCompoundingValidator s electra index = .ok t) : SamePendingQueue s t := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, _, middle, set, queued⟩ := ok
  apply (setValidator set).trans
  simp only [queueExcessActiveBalance, bind_ok_iff] at queued
  obtain ⟨_, _, queued⟩ := queued
  split at queued
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
    obtain ⟨_, _, _, _, _, set, rfl⟩ := queued
    obtain ⟨_, rfl⟩ := setBalance_ok set
    rfl
  · cases queued; rfl

private theorem PendingSources.request {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : ConsolidationRequest} (holds : PendingSources s)
    (ok : processConsolidationRequest config s electra request = .ok t) : PendingSources t := by
  have size := (sameSizes_processConsolidationRequest ok).1
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact holds)
    | exact holds.kept (SamePendingQueue.compounding (liftAccessor_ok.mp ok)) (by omega)
    | exact holds.queue ok

theorem processJustificationAndFinalization_pendingConsolidations
    {f : Fork} {s t : BeaconState preset f}
    (ok : processJustificationAndFinalization s = .ok t) :
    t.pendingConsolidations = s.pendingConsolidations := SamePendingQueue.justification ok

theorem processInactivityUpdates_pendingConsolidations
    {f : Fork} {s t : BeaconState preset f} {altair : .altair ≤ f}
    (ok : processInactivityUpdates config s altair = .ok t) :
    t.pendingConsolidations = s.pendingConsolidations := SamePendingQueue.inactivity ok

theorem processRewardsAndPenalties_pendingConsolidations
    {f : Fork} {s t : BeaconState preset f}
    (ok : processRewardsAndPenalties config s = .ok t) :
    t.pendingConsolidations = s.pendingConsolidations := SamePendingQueue.rewards ok

theorem processRegistryUpdates_pendingConsolidations
    {f : Fork} {s t : BeaconState preset f}
    (ok : processRegistryUpdates config s = .ok t) :
    t.pendingConsolidations = s.pendingConsolidations := SamePendingQueue.registry ok

theorem processSlashings_pendingConsolidations {f : Fork} {s t : BeaconState preset f}
    (ok : processSlashings s = .ok t) :
    t.pendingConsolidations = s.pendingConsolidations := SamePendingQueue.slashings ok

theorem processEth1DataReset_pendingConsolidations
    {f : Fork} {s t : BeaconState preset f} {before : f < .hegota}
    (ok : processEth1DataReset before s = .ok t) :
    t.pendingConsolidations = s.pendingConsolidations := SamePendingQueue.eth1Reset ok

variable {fork : Fork} {state after : BeaconState preset fork}
  {engine : ExecutionEngine preset fork}

namespace SamePendingQueue

private theorem refl (s : BeaconState preset fork) : SamePendingQueue s s := rfl

private theorem slash {i : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config state i whistleblower = .ok after) :
    SamePendingQueue state after := by
  obtain ⟨_, _, _, marked, _, _, slashings, _, _, _, _, last, exited, read, _, set,
    _, _, _, lowered, _, _, raised, paid, rfl⟩ := slashValidator_ok ok
  have first := (exit exited).trans (setValidator set)
  have second : SamePendingQueue marked last :=
    (show SamePendingQueue marked { marked with slashings } from rfl).trans
      ((decrease lowered).trans ((increase raised).trans (increase paid)))
  apply (first.trans second).trans
  split <;> rfl

private theorem proposer {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks state slashing = .ok after) :
    SamePendingQueue state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact slash slashed

private theorem slashIf {step next : BeaconState preset fork × Bool} {index : ValidatorIndex}
    (ok : slashIfSlashable config step index = .ok next) : SamePendingQueue step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact slash slashed
  · cases ok; rfl

private theorem attester {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks state slashing = .ok after) :
    SamePendingQueue state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  exact foldlM_ok_invariant (fun step : BeaconState preset fork × Bool =>
    SamePendingQueue state step.1)
    (fun _ _ _ prior ok => prior.trans (slashIf ok))
    (show SamePendingQueue state (state, false).1 from rfl) folded

private theorem voluntary {signed : SignedVoluntaryExit}
    (ok : processVoluntaryExit config checks state signed = .ok after) :
    SamePendingQueue state after := by
  unfold processVoluntaryExit at ok
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
  exact exit exited

private theorem bls {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks state signed = .ok after) :
    SamePendingQueue state after := by
  obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact setValidator set

private theorem deposit {before : fork < .hegota} {deposit : Deposit}
    (electra : .pectra ≤ fork)
    (ok : processDeposit config checks before state deposit = .ok after) :
    SamePendingQueue state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok ok
  unfold applyDeposit at applied
  simp only [dite_eq_left electra] at applied
  unfold applyDepositElectra at applied
  split at applied
  · simp only [bind_ok_iff] at applied
    obtain ⟨_, _, applied⟩ := applied
    split at applied
    · simp only [bind_ok_iff, liftAccessor_ok] at applied
      obtain ⟨_, added, pushed⟩ := applied
      obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
      unfold addValidatorToRegistry at added
      split at added
      · simp only [addValidatorToRegistryAltair, bind_ok_iff, liftAccessor_ok,
          pure, Except.pure, Except.ok.injEq] at added
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := added
        rfl
      · split at added <;> cases added
        rfl
    · cases applied; rfl
  · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp applied)
    rfl

private theorem depositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (ok : processDepositRequest state electra request = .ok after) :
    SamePendingQueue state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  rfl

private theorem partialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (ok : requestPartialWithdrawal config state electra index validator amount owed = .ok after) :
    SamePendingQueue state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churned
    obtain ⟨_, _, _, _, _, _, final⟩ := churned
    cases final; rfl
  · cases ok; rfl

private theorem withdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config state electra request = .ok after) :
    SamePendingQueue state after := by
  unfold processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; rfl)
    | exact exit (liftAccessor_ok.mp ok)
    | exact partialWithdrawal ok

private theorem attestation {attestation : Attestation preset fork} {parentSlot : Slot}
    (electra : .pectra ≤ fork)
    (ok : processAttestation config checks state parentSlot attestation = .ok after) :
    SamePendingQueue state after := by
  unfold processAttestation at ok
  rw [dite_eq_left (show .altair ≤ fork from Nat.le_trans (by decide) electra)] at ok
  unfold processAttestationAltair at ok
  simp only [bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, raised, raisedOk, final⟩ := ok
  have last : SamePendingQueue raised after := by
    split at final
    · rw [recordPaymentWeight_eq final]; rfl
    · cases final; rfl
  have flagged : ∀ (current : Bool) (participation : EpochParticipation preset fork),
      SamePendingQueue state (setEpochParticipation state current participation) := by
    intro current participation
    unfold setEpochParticipation
    split <;> rfl
  exact (flagged _ _).trans ((increase raisedOk).trans last)

private theorem withdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (early : fork < .glamsterdam)
    (ok : processWithdrawals state capella payload = .ok after) :
    SamePendingQueue state after := by
  unfold processWithdrawals at ok
  rw [dite_eq_right (show ¬ .glamsterdam ≤ fork from Nat.not_le_of_lt early)] at ok
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, applied⟩ := ok
  unfold applyExpectedWithdrawals at applied
  simp only [bind_ok_iff] at applied
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := applied
  have one : SamePendingQueue state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact fold (fun _ _ _ ok => by
      unfold applyWithdrawal at ok
      split at ok
      · simp only [bind_ok_iff] at ok
        obtain ⟨_, _, set⟩ := ok
        obtain ⟨_, rfl⟩ := setBuilder_ok set
        rfl
      · exact decrease ok) appliedOk
  have two : SamePendingQueue applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      rfl
    · cases indexedOk; rfl
  simp only [dite_eq_right (show ¬ .glamsterdam ≤ fork from Nat.not_le_of_lt early),
    pure, Except.pure, Except.ok.injEq] at sweptOk
  subst finished
  have lastKept : SamePendingQueue indexed after := by
    split at last <;>
    unfold updateNextWithdrawalValidatorIndex at last
    all_goals
      simp only [bind_ok_iff] at last
      obtain ⟨_, _, last⟩ := last
      split at last
      · cases last
      · cases last; rfl
  exact one.trans (two.trans lastKept)

private theorem blockExecution {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (early : fork < .glamsterdam)
    (ok : processBlockExecution config checks engine state body bellatrix = .ok after) :
    SamePendingQueue state after := by
  unfold processBlockExecution at ok
  rw [dite_eq_right (show ¬ .glamsterdam ≤ fork from Nat.not_le_of_lt early)] at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, paid⟩ := ok
    apply (withdrawals early withdrawn).trans
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok paid
    rfl
  · dsimp only at ok
    split at ok
    · obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
      rfl
    · cases ok; rfl

private theorem syncAggregate {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (ok : processSyncAggregate config checks state altair aggregate = .ok after) :
    SamePendingQueue state after := by
  unfold processSyncAggregate at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := ok
  rw [← Array.foldlM_toList] at folded
  exact fold (fun _ _ _ ok => by
    unfold applySyncReward at ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, raised, _, _, paid⟩ := ok
      exact (increase raised).trans (increase paid)
    · exact decrease (liftAccessor_ok.mp ok)) folded

end SamePendingQueue

namespace PendingSources

private theorem fold {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)} {xs : List α}
    (kept : ∀ a item b, PendingSources a → step a item = .ok b → PendingSources b)
    (holds : PendingSources state) (ok : xs.foldlM step state = .ok after) :
    PendingSources after := foldlM_ok_invariant PendingSources kept holds ok

private theorem executionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (holds : PendingSources state)
    (ok : processExecutionRequests config state body electra = .ok after) :
    PendingSources after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
  have first := fold (fun _ _ _ h ok => h.kept (SamePendingQueue.depositRequest ok)
    (registryLifecycle_processDepositRequest ok).size_le) holds deposits
  have second := fold (fun _ _ _ h ok => h.kept (SamePendingQueue.withdrawalRequest ok)
    (registryLifecycle_processWithdrawalRequest ok).size_le) first withdrawals
  exact fold (fun _ _ _ h ok => h.request ok) second consolidations

private theorem operations {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (early : fork < .glamsterdam) (electra : .pectra ≤ fork) (holds : PendingSources state)
    (ok : processOperations config checks state body parentSlot = .ok after) :
    PendingSources after := by
  unfold processOperations at ok
  rw [dite_eq_right (show ¬ .glamsterdam ≤ fork from Nat.not_le_of_lt early)] at ok
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, _, _, _, _, proposers, _, attesters, _, attested, _, deposits, exited,
    exits, changed, changes, requests⟩ := ok
  have p := fold (fun _ _ _ h ok => h.kept (SamePendingQueue.proposer ok)
    (registryLifecycle_processProposerSlashing ok).size_le) holds proposers
  have a := fold (fun _ _ _ h ok => h.kept (SamePendingQueue.attester ok)
    (registryLifecycle_processAttesterSlashing ok).size_le) p attesters
  have att := fold (fun _ _ _ h ok => h.kept (SamePendingQueue.attestation electra ok)
    (registryLifecycle_processAttestation ok).size_le) a attested
  have d := fold (fun _ _ _ h ok => h.kept (SamePendingQueue.deposit electra ok)
    (registryLifecycle_processDeposit ok).size_le) att deposits
  have e := fold (fun _ _ _ h ok => h.kept (SamePendingQueue.voluntary ok)
    (registryLifecycle_processVoluntaryExit ok).size_le) d exits
  have c : PendingSources changed := by
    unfold processBlsToExecutionChanges at changes
    split at changes
    · rw [← Array.foldlM_toList] at changes
      exact fold (fun _ _ _ h ok => h.kept (SamePendingQueue.bls ok)
        (registryLifecycle_processBlsToExecutionChange ok).size_le) e changes
    · cases changes; exact e
  rw [dite_eq_left electra] at requests
  exact c.executionRequests requests

private theorem block (early : fork < .glamsterdam) (holds : PendingSources state)
    {block : BeaconBlock preset fork}
    (ok : processBlock config checks engine state block = .ok after) : PendingSources after := by
  by_cases electra : .pectra ≤ fork
  · unfold processBlock at ok
    rw [dite_eq_left (show .altair ≤ fork from Nat.le_trans (by decide) electra)] at ok
    unfold processBlockAltair at ok
    simp only [bind_ok_iff] at ok
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, operated, operatedOk, synced⟩ := ok
    rw [dite_eq_right (show ¬ .glamsterdam ≤ fork from Nat.not_le_of_lt early)] at paidOk
    cases paidOk
    have h : PendingSources headed := by
      obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
      exact holds
    have e : PendingSources executed := by
      split at executedOk
      · exact h.kept (SamePendingQueue.blockExecution early executedOk)
          (registryLifecycle_processBlockExecution executedOk).size_le
      · cases executedOk; exact h
    have r : PendingSources revealed := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealedOk
      exact e
    have v : PendingSources voted := by
      split at votedOk
      · obtain ⟨_, _, rest⟩ := processEth1Data_eq votedOk
        have queue : SamePendingQueue revealed voted := by
          unfold SamePendingQueue; rw [← rest]
        exact r.kept queue (registryLifecycle_processEth1Data votedOk).size_le
      · cases votedOk; exact r
    exact (operations early electra v operatedOk).kept (SamePendingQueue.syncAggregate synced)
      (registryLifecycle_processSyncAggregate synced).size_le
  · intro witness
    exact False.elim (electra witness)

private theorem epoch (early : fork < .glamsterdam) (holds : PendingSources state)
    (ok : processEpoch config checks state = .ok after) : PendingSources after := by
  by_cases electra : .pectra ≤ fork
  · unfold processEpoch at ok
    rw [dite_eq_left (show .altair ≤ fork from Nat.le_trans (by decide) electra)] at ok
    unfold processEpochAltair at ok
    simp only [bind_ok_iff] at ok
    obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
      registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk, balanced,
      balancedOk, cleared, clearedOk, mixed, mixedOk, ok⟩ := ok
    have j := holds.kept (SamePendingQueue.justification justifiedOk)
      (registryLifecycle_processJustificationAndFinalization justifiedOk).size_le
    have i := j.kept (SamePendingQueue.inactivity scoredOk)
      (registryLifecycle_processInactivityUpdates scoredOk).size_le
    have r := i.kept (SamePendingQueue.rewards rewardedOk)
      (registryLifecycle_processRewardsAndPenalties rewardedOk).size_le
    have reg := r.kept (SamePendingQueue.registry registeredOk)
      (registryLifecycle_processRegistryUpdates registeredOk).size_le
    have sl := reg.kept (SamePendingQueue.slashings slashedOk)
      (registryLifecycle_processSlashings slashedOk).size_le
    have re : PendingSources reset := by
      split at resetOk
      · exact sl.kept (SamePendingQueue.eth1Reset resetOk)
          (registryLifecycle_processEth1DataReset resetOk).size_le
      · cases resetOk; exact sl
    have pe := re.pending pendingOk
    rw [dite_eq_right (show ¬ .glamsterdam ≤ fork from Nat.not_le_of_lt early)] at paidOk
    cases paidOk
    have b := pe.kept (SamePendingQueue.effectiveUpdates balancedOk)
      (registryLifecycle_processEffectiveBalanceUpdates balancedOk).size_le
    have c : PendingSources cleared := by
      obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
      exact b
    have m : PendingSources mixed := by
      obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
      exact c
    rw [dite_eq_left (show .shapella ≤ fork from Nat.le_trans (by decide) electra)] at ok
    simp only [bind_ok_iff] at ok
    obtain ⟨rooted, roots, synced, sync, looked, look, window⟩ := ok
    have root : PendingSources rooted := by
      unfold processHistoricalSummariesUpdate at roots
      simp only [bind, Except.bind, pure, Except.pure] at roots
      repeat' (split at roots <;> try cases roots)
      all_goals exact m
    have sy : PendingSources synced := by
      unfold processSyncCommitteeUpdates at sync
      simp only [bind, Except.bind, pure, Except.pure] at sync
      repeat' (split at sync <;> try cases sync)
      all_goals exact root
    have lo : PendingSources looked := by
      split at look
      · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
          Except.ok.injEq] at look
        obtain ⟨_, _, _, _, rfl⟩ := look
        exact sy
      · cases look; exact sy
    rw [dite_eq_right (show ¬ .glamsterdam ≤ fork from Nat.not_le_of_lt early)] at window
    cases window; exact lo
  · intro witness
    exact False.elim (electra witness)

private theorem advance (early : fork < .glamsterdam) (holds : PendingSources state)
    (ok : advanceSlot config checks state = .ok after) : PendingSources after := by
  obtain ⟨_, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have first : PendingSources cached := by rw [cachedEq]; exact holds
  have second : PendingSources epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact epoch early first epochedOk
    · cases epochedOk; exact first
  exact second

private theorem upgrade {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (holds : PendingSources pre.state)
    (ok : upgradeNext config checks pre = .ok post)
    (early : post.val.fork < .glamsterdam) : PendingSources post.val.state := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, upgraded, rfl⟩ := ok
    intro electra
    exact False.elim (Nat.not_le_of_lt (show Fork.altair < .pectra from by decide) electra)
  · subst ok
    intro electra
    exact False.elim (Nat.not_le_of_lt (show Fork.bellatrix < .pectra from by decide) electra)
  · subst ok
    intro electra
    exact False.elim (Nat.not_le_of_lt (show Fork.shapella < .pectra from by decide) electra)
  · subst ok
    intro electra
    exact False.elim (Nat.not_le_of_lt (show Fork.dencun < .pectra from by decide) electra)
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, _, _, _, _, _, _, _, _, queued, compounded⟩ := upgraded
    have kept := SamePendingQueue.fold (fun _ _ _ ok => by
      simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
        Except.ok.injEq] at ok
      obtain ⟨_, _, _, _, _, _, b, balance, _, set, rfl⟩ := ok
      obtain ⟨_, rfl⟩ := setBalance_ok balance
      have same := SamePendingQueue.setValidator set
      exact same) queued
    have kept' := SamePendingQueue.fold (fun _ _ _ ok => by
      unfold queueCompoundingExcess at ok
      split at ok
      · split at ok
        · simp only [liftAccessor_ok, queueExcessActiveBalance, bind_ok_iff] at ok
          obtain ⟨_, _, ok⟩ := ok
          split at ok
          · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
            obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
            obtain ⟨_, rfl⟩ := setBalance_ok set
            rfl
          · cases ok; rfl
        · cases ok; rfl
      · cases ok; rfl) compounded
    have queue := kept.trans kept'
    intro electra entry mem
    unfold SamePendingQueue at queue
    rw [queue] at mem
    simp [carryFields, show ¬ Fork.pectra ≤ .dencun from by decide] at mem
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
    obtain ⟨_, _, rfl⟩ := upgraded
    intro electra entry mem
    exact holds (show Fork.pectra ≤ .pectra from Nat.le_refl _) entry
      (by simpa [carryFields, carryList] using mem)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.lt_irrefl _ early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.not_le_of_lt early (show Fork.glamsterdam ≤ .hegota from by decide))

private theorem step {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (early : y.fork < .glamsterdam)
    (holds : PendingSources x.state) : PendingSources y.state := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    have forkLe := processUpgrades_fork_le upgrades
    have earlier : x.fork < .glamsterdam := Nat.lt_of_le_of_lt forkLe early
    have initial := advance earlier holds slotOk
    have rest := processUpgrades_induction
      (property := fun post => post.fork < .glamsterdam → PendingSources post.state)
      (fun {pre post} h ok early => upgrade (h (Nat.lt_trans post.property early)) ok early)
      (fun _ => initial) upgrades
    exact rest early
  | block engine signed due ok => exact block early holds (applySignedBlock_ok ok).2.1

end PendingSources

theorem Run.pendingConsolidation_sources {g x : ForkedBeaconState preset}
    (run : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : x.fork < .glamsterdam) (electra : .pectra ≤ x.fork) :
    ∀ c ∈ (x.state.pendingConsolidations electra).data.toList,
      c.sourceIndex.toNat < x.state.validators.data.size := by
  have holds : PendingSources x.state := by
    clear electra
    induction run with
    | nil =>
      obtain ⟨_, _, _, ok⟩ := genesis
      have before := (initializeBeaconStateFromEth1_invariant ok).1
      intro electra
      exact False.elim (Nat.not_le_of_lt (Nat.lt_trans before (by decide)) electra)
    | snoc pre step ih =>
      exact PendingSources.step step early
        (ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early))
  exact holds electra

end EthLib.Consensus
