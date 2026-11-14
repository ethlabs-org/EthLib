module

public import EthLib.Consensus.Proofs.DirectSafety.DepartureQueue
public import EthLib.Consensus.Proofs.Transition.PendingPartialsKept
import all EthLib.Consensus.Proofs.Transition.PendingPartialsKept

/-!
# The partial-withdrawal ledger

Payments consume entries from the front of the queue.

Each consumed entry pays at most its amount, and only after its withdrawable epoch.

The ledger distinguishes equal entries by position, so an entry cannot pay twice.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

private theorem getPendingPartialWithdrawals_loop_ledger {fork : Fork}
    {state : BeaconState preset fork} {prior : Array Withdrawal} {epoch : Epoch} {limit : Nat} :
    ∀ (queue : List PendingPartialWithdrawal) (withdrawals : Array Withdrawal)
      (next : WithdrawalIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    getPendingPartialWithdrawals.loop state prior epoch limit queue withdrawals next processed =
      .ok result →
    ∃ (count : ℕ) (pay : ℕ → ℕ), result.2.2 = processed + count ∧ count ≤ queue.length ∧
      (∀ k, count ≤ k → pay k = 0) ∧
      (∀ k < count, ∃ w, queue[k]? = some w ∧ pay k ≤ w.amount.toNat ∧
        (0 < pay k → w.withdrawableEpoch ≤ epoch)) ∧
      ∀ v, ((result.1.toList.filter (·.validatorIndex = v)).map (·.amount.toNat)).sum =
        ((withdrawals.toList.filter (·.validatorIndex = v)).map (·.amount.toNat)).sum +
          ∑ k ∈ Finset.range count,
            if queue[k]?.map (·.validatorIndex) = some v then pay k else 0
  | [], _, _, _, _, computed => by
    simp only [getPendingPartialWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨0, fun _ => 0, rfl, Nat.zero_le _, fun _ _ => rfl,
      fun _ small => absurd small (by omega), fun _ => by simp⟩
  | pending :: rest, withdrawals, next, processed, _, computed => by
    simp only [getPendingPartialWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact ⟨0, fun _ => 0, rfl, Nat.zero_le _, fun _ _ => rfl,
        fun _ small => absurd small (by omega), fun _ => by simp⟩
    rename_i ready
    have due : pending.withdrawableEpoch ≤ epoch := by
      simp only [not_or, Nat.not_le] at ready
      exact UInt64.not_lt.mp ready.1
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, left, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨⟨appended, following⟩, appendedOk, loopOk⟩ := computed
      simp only [appendWithdrawal, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at appendedOk
      obtain ⟨_, _, rfl, rfl⟩ := appendedOk
      obtain ⟨count, pay, counted, bounded, beyond, entries, sums⟩ :=
        getPendingPartialWithdrawals_loop_ledger rest _ _ _ loopOk
      refine ⟨count + 1, fun k => k.casesOn
        (min (left - preset.MIN_ACTIVATION_BALANCE) pending.amount).toNat pay,
        by omega, by simp only [List.length_cons]; omega, ?_, ?_, ?_⟩
      · intro k large
        cases k with
        | zero => omega
        | succ k => exact beyond k (by omega)
      · intro k small
        cases k with
        | zero => exact ⟨pending, rfl, UInt64.le_iff_toNat_le.mp Std.min_le_right, fun _ => due⟩
        | succ k => exact entries k (by omega)
      · intro v
        rw [sums v, Finset.sum_range_succ']
        by_cases named : pending.validatorIndex = v
        · simp [named, Array.toList_push, List.filter_append]
          omega
        · simp [named, Array.toList_push, List.filter_append]
    · obtain ⟨count, pay, counted, bounded, beyond, entries, sums⟩ :=
        getPendingPartialWithdrawals_loop_ledger rest _ _ _ computed
      refine ⟨count + 1, fun k => k.casesOn 0 pay, by omega,
        by simp only [List.length_cons]; omega, ?_, ?_, ?_⟩
      · intro k large
        cases k with
        | zero => rfl
        | succ k => exact beyond k (by omega)
      · intro k small
        cases k with
        | zero => exact ⟨pending, rfl, Nat.zero_le _, fun positive => absurd positive (by simp)⟩
        | succ k => exact entries k (by omega)
      · intro v
        rw [sums v, Finset.sum_range_succ']
        simp

private theorem getPendingPartialWithdrawals_ledger {fork : Fork}
    {state : BeaconState preset fork} {electra : .pectra ≤ fork} {start : WithdrawalIndex}
    {prior partials : Array Withdrawal} {next : WithdrawalIndex} {count : ℕ}
    (computed : getPendingPartialWithdrawals state electra start prior =
      .ok (partials, next, count)) :
    ∃ pay : ℕ → ℕ, count ≤ (state.pendingPartialWithdrawals electra).data.toList.length ∧
      (∀ k, count ≤ k → pay k = 0) ∧
      (∀ k < count, ∃ w, (state.pendingPartialWithdrawals electra).data.toList[k]? = some w ∧
        pay k ≤ w.amount.toNat ∧ (0 < pay k → w.withdrawableEpoch ≤ getCurrentEpoch state)) ∧
      ∀ v, ((partials.toList.filter (·.validatorIndex = v)).map (·.amount.toNat)).sum =
        ∑ k ∈ (Finset.range count).filter (fun k =>
          (state.pendingPartialWithdrawals electra).data.toList[k]?.map (·.validatorIndex) =
            some v), pay k := by
  unfold getPendingPartialWithdrawals at computed
  simp only [bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, _, _, loopOk⟩ := computed
  obtain ⟨found, pay, counted, bounded, beyond, entries, sums⟩ :=
    getPendingPartialWithdrawals_loop_ledger _ _ _ _ loopOk
  simp only [Nat.zero_add] at counted
  subst counted
  refine ⟨pay, bounded, beyond, entries, fun v => ?_⟩
  rw [sums v, Finset.sum_filter]
  simp

private theorem withdrawals_pendingPartials {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {capella : .shapella ≤ fork} {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (ok : processWithdrawals s capella payload = .ok t) :
    ∃ (partials : Array Withdrawal) (next : WithdrawalIndex) (count : ℕ),
      getPendingPartialWithdrawals s electra (s.nextWithdrawalIndex capella) #[] =
        .ok (partials, next, count) ∧
      (t.pendingPartialWithdrawals electra).data.toList =
        (s.pendingPartialWithdrawals electra).data.toList.drop count := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [processWithdrawals, notGloas, ↓reduceDIte, bind_ok_iff, ensure_ok_iff,
    liftAccessor_ok] at ok
  obtain ⟨expected, expectedOk, _, _, applied⟩ := ok
  unfold getExpectedWithdrawals at expectedOk
  simp only [notGloas, electra, ↓reduceDIte, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at expectedOk
  obtain ⟨_, rfl, ⟨partials, next, count⟩, partialsOk, _, rfl, _, _, rfl⟩ := expectedOk
  refine ⟨partials, next, count, partialsOk, ?_⟩
  simp only [applyExpectedWithdrawals, notGloas, electra, ↓reduceDIte, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq, exists_eq_left'] at applied
  obtain ⟨withdrawn, paid, indexed, moved, swept⟩ := applied
  have paidQueue :
      withdrawn.pendingPartialWithdrawals electra = s.pendingPartialWithdrawals electra := by
    unfold applyWithdrawals at paid
    rw [← Array.foldlM_toList] at paid
    refine foldlM_ok_invariant
      (fun t => t.pendingPartialWithdrawals electra = s.pendingPartialWithdrawals electra)
      ?_ rfl paid
    intro a withdrawal b kept stepped
    simp only [applyWithdrawal, notGloas, false_and, ↓reduceDIte] at stepped
    exact (partialsSame_decreaseBalance stepped electra).trans kept
  have movedQueue :
      indexed.pendingPartialWithdrawals electra = withdrawn.pendingPartialWithdrawals electra := by
    unfold updateNextWithdrawalIndex at moved
    split at moved
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at moved
      obtain ⟨_, _, rfl⟩ := moved
      rfl
    · cases moved; rfl
  simp only [updateNextWithdrawalValidatorIndex, bind_ok_iff] at swept
  obtain ⟨_, _, swept⟩ := swept
  split at swept
  · cases swept
  · cases swept
    simp only [updatePendingPartialWithdrawals, Array.toList_extract, List.extract_eq_take_drop,
      movedQueue, paidQueue]
    exact List.take_of_length_le (by simp)

private def QueueAppend {fork : Fork} (s t : BeaconState preset fork) : Prop :=
  ∀ electra : .pectra ≤ fork, ∃ added : List PendingPartialWithdrawal,
    (t.pendingPartialWithdrawals electra).data.toList =
      (s.pendingPartialWithdrawals electra).data.toList ++ added ∧
    ∀ w ∈ added, getCurrentEpoch s < w.withdrawableEpoch

private theorem QueueAppend.of_same {fork : Fork} {s t : BeaconState preset fork}
    (same : PartialsSame s t) : QueueAppend s t := fun electra =>
  ⟨[], by rw [same electra, List.append_nil], by simp⟩

private theorem QueueAppend.trans {fork : Fork} {s t u : BeaconState preset fork}
    (one : QueueAppend s t) (two : QueueAppend t u)
    (epoch : getCurrentEpoch s ≤ getCurrentEpoch t) :
    QueueAppend s u := by
  intro electra
  obtain ⟨a, first, lateA⟩ := one electra
  obtain ⟨b, second, lateB⟩ := two electra
  refine ⟨a ++ b, by rw [second, first, List.append_assoc], ?_⟩
  intro w member
  rcases List.mem_append.mp member with member | member
  · exact lateA w member
  · exact UInt64.lt_of_le_of_lt epoch (lateB w member)

private theorem QueueAppend.foldlM {fork : Fork} {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (appends : ∀ s a t, step s a = .ok t → QueueAppend s t)
    (slots : ∀ s a t, step s a = .ok t → t.slot = s.slot)
    {items : List α} {s t : BeaconState preset fork}
    (ok : items.foldlM step s = .ok t) : QueueAppend s t := by
  have both := foldlM_ok_invariant
    (fun t => QueueAppend s t ∧ t.slot = s.slot)
    (fun a item b prior ok =>
      ⟨prior.1.trans (appends a item b ok) (by
          simp only [getCurrentEpoch, prior.2]; exact UInt64.le_refl _),
        (slots a item b ok).trans prior.2⟩)
    ⟨.of_same (PartialsSame.refl s), rfl⟩ ok
  exact both.1

private theorem partialWithdrawal_queueAppend {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : ValidatorIndex} {v : Validator} {amount owed : Gwei}
    (ok : requestPartialWithdrawal config s electra index v amount owed = .ok t) :
    QueueAppend s t := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨balance, _, kept, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨⟨queued, epoch⟩, called, withdrawable, delayed, pending, appended, rfl⟩ := ok
    have queue : queued.pendingPartialWithdrawals electra =
        s.pendingPartialWithdrawals electra := by
      unfold computeExitEpochAndUpdateChurn at called
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at called
      obtain ⟨_, _, _, _, _, _, rfl, _⟩ := called
      rfl
    have late : getCurrentEpoch s < withdrawable := by
      obtain ⟨first, firstOk⟩ : ∃ first,
          computeActivationExitEpoch preset (getCurrentEpoch s) = .ok first := by
        unfold computeExitEpochAndUpdateChurn at called
        simp only [bind_ok_iff] at called
        obtain ⟨first, firstOk, _⟩ := called
        exact ⟨first, by simpa only [liftArith, mapError_ok_iff] using firstOk⟩
      have placed := UInt64.le_iff_toNat_le.mp
        (computeExitEpochAndUpdateChurn_first firstOk called).1
      have starts := (computeActivationExitEpoch_ok_iff.mp firstOk).2
      have sum := (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp delayed)).2
      dsimp only at sum
      simp only [UInt64.lt_iff_toNat_lt]
      omega
    intro electra'
    refine ⟨[⟨index, min (balance - kept) amount, withdrawable⟩], ?_, ?_⟩
    · simp only [appendWithinLimit_data appended, Array.toList_push, queue]
    · intro w member
      obtain rfl := List.mem_singleton.mp member
      exact late
  · cases ok
    exact .of_same (PartialsSame.refl s)

private theorem withdrawalRequest_queueAppend {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) : QueueAppend s t := by
  rcases withdrawalRequest_cases ok with same | ⟨index, exited⟩ | ⟨index, v, owed, withdrawn⟩
  · subst t
    exact .of_same (PartialsSame.refl s)
  · exact .of_same (partialsSame_initiateValidatorExit exited)
  · exact partialWithdrawal_queueAppend withdrawn

private theorem slashValidator_partialsSame {fork : Fork} {s t : BeaconState preset fork}
    (early : fork < .glamsterdam) {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config s index whistleblower = .ok t) : PartialsSame s t := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, exitedOk, _, _, markedOk, _, _, _,
    lowered, _, _, raised, final, done⟩ := slashValidator_ok ok
  simp only [show ¬ .glamsterdam ≤ fork from Nat.not_le_of_lt early, ↓reduceDIte] at done
  subst done
  intro electra
  rw [partialsSame_increaseBalance final electra, partialsSame_increaseBalance raised electra,
    partialsSame_decreaseBalance lowered electra,
    ← partialsSame_initiateValidatorExit exitedOk electra]
  obtain ⟨_, rfl⟩ := setValidator_ok markedOk
  rfl

private theorem proposerSlashing_partialsSame {fork : Fork} {s t : BeaconState preset fork}
    (early : fork < .glamsterdam) {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t) : PartialsSame s t := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact slashValidator_partialsSame early slashed

private theorem attesterSlashing_partialsSame {fork : Fork} {s t : BeaconState preset fork}
    (early : fork < .glamsterdam) {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks s slashing = .ok t) : PartialsSame s t := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨folded, flag⟩, foldedOk, ok⟩ := ok
  simp only [pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  refine foldlM_ok_invariant (fun step => PartialsSame s step.1) ?_
    (PartialsSame.refl s) foldedOk
  intro ⟨state, _⟩ index next kept stepped
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at stepped
  obtain ⟨_, _, stepped⟩ := stepped
  split at stepped
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at stepped
    obtain ⟨_, slashed, rfl⟩ := stepped
    exact kept.trans (slashValidator_partialsSame early slashed)
  · cases stepped; exact kept

private theorem attestation_partialsSame {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {parentSlot : Slot} {attestation : Attestation preset fork}
    (ok : processAttestation config checks s parentSlot attestation = .ok t) :
    PartialsSame s t := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [processAttestation, altair, ↓reduceDIte] at ok
  unfold processAttestationAltair at ok
  simp only [bind_ok_iff, liftAccessor_ok, notGloas, ↓reduceDIte,
    pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, raised, rfl⟩ := ok
  intro electra
  rw [partialsSame_increaseBalance raised electra]
  unfold setEpochParticipation
  split <;> rfl

private theorem deposit_partialsSame {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {before : fork < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) : PartialsSame s t := by
  obtain ⟨_, _, _, _, credited⟩ := processDeposit_ok ok
  simp only [applyDeposit, electra, ↓reduceDIte] at credited
  unfold applyDepositElectra at credited
  split at credited
  · simp only [bind_ok_iff] at credited
    obtain ⟨_, _, credited⟩ := credited
    split at credited
    · simp only [bind_ok_iff, liftAccessor_ok] at credited
      obtain ⟨_, added, queued⟩ := credited
      obtain ⟨_, rfl⟩ := addPendingDeposit_eq queued
      intro e
      exact partialsSame_addValidatorToRegistry added e
    · cases credited; exact PartialsSame.refl _
  · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp credited)
    exact PartialsSame.refl _

private theorem credentials_partialsSame {fork : Fork} {s t : BeaconState preset fork}
    {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) : PartialsSame s t := by
  obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact partialsSame_setValidator set

private theorem consolidationRequest_partialsSame {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t) : PartialsSame s t := by
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact PartialsSame.refl _)
    | cases ok
    | (intro e; simp only [switchToCompoundingValidator, queueExcessActiveBalance, bind_ok_iff,
        liftAccessor_ok] at ok
       obtain ⟨_, _, _, set, _, _, queued⟩ := ok
       obtain ⟨_, rfl⟩ := setValidator_ok set
       split at queued
       · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
         obtain ⟨_, _, _, _, _, set, rfl⟩ := queued
         exact partialsSame_setBalance set e
       · cases queued; rfl)
    | (intro e
       simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
         Except.ok.injEq] at ok
       obtain ⟨⟨_, _⟩, scheduled, _, _, _, set, _, _, rfl⟩ := ok
       obtain ⟨_, rfl⟩ := setValidator_ok set
       simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
         Except.ok.injEq, Prod.mk.injEq] at scheduled
       obtain ⟨_, _, _, _, ⟨_, _⟩, _, rfl, _⟩ := scheduled
       rfl)

private theorem executionRequests_queueAppend {fork : Fork} {s t : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (ok : processExecutionRequests config s body electra = .ok t) : QueueAppend s t := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨deposited, deposits, withdrawn, withdrawals, consolidations⟩ := ok
  have first : PartialsSame s deposited := by
    refine PartialsSame.foldlM (fun a request b called => ?_) deposits
    obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp called)
    intro e
    unfold recordDepositRequestsStart
    split <;> (try split) <;> rfl
  have second := QueueAppend.foldlM
    (fun _ _ _ called => withdrawalRequest_queueAppend called)
    (fun _ _ _ called => (frame_processWithdrawalRequest called).slot) withdrawals
  have third := PartialsSame.foldlM
    (fun _ _ _ called => consolidationRequest_partialsSame called) consolidations
  have slot := (BlockFrame.foldlM
    (fun _ _ _ called => frame_processDepositRequest called) deposits).slot
  have withdrawnSlot := (BlockFrame.foldlM
    (fun _ _ _ called => frame_processWithdrawalRequest called) withdrawals).slot
  exact ((QueueAppend.of_same first).trans second (by
    simp only [getCurrentEpoch, slot]; exact UInt64.le_refl _)).trans
    (.of_same third) (by
      simp only [getCurrentEpoch, withdrawnSlot, slot]; exact UInt64.le_refl _)

private theorem operations_queueAppend {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (ok : processOperations config checks s body parentSlot = .ok t) : QueueAppend s t := by
  let step := fun a b : BeaconState preset fork => QueueAppend a b ∧ b.slot = a.slot
  have same {a b : BeaconState preset fork} (kept : PartialsSame a b) (slot : b.slot = a.slot) :
      step a b := ⟨.of_same kept, slot⟩
  have chain {a b c : BeaconState preset fork} (one : step a b) (two : step b c) :
      step a c := ⟨one.1.trans two.1 (by
        simp only [getCurrentEpoch, one.2]; exact UInt64.le_refl _), two.2.trans one.2⟩
  obtain ⟨proposed, slashed, attested, proposers, slashings, attestations, rest⟩ :=
    processOperations_folds_of step (fun a => same (.refl a) rfl) chain
      (fun called => same (deposit_partialsSame electra called) (frame_processDeposit called).slot)
      (fun called => same (partialsSame_initiateValidatorExit
        (processVoluntaryExit_initiates called)) (frame_processVoluntaryExit called).slot)
      (fun called => same (credentials_partialsSame called)
        (frame_processBlsToExecutionChange called).slot)
      (fun called => ⟨executionRequests_queueAppend called,
        (frame_processExecutionRequests called).slot⟩)
      (fun {a b} gloas _ => False.elim ((Nat.not_le_of_lt early) gloas)) ok
  have first := PartialsSame.foldlM
    (fun _ _ _ called => proposerSlashing_partialsSame early called) proposers
  have second := PartialsSame.foldlM
    (fun _ _ _ called => attesterSlashing_partialsSame early called) slashings
  have third := PartialsSame.foldlM
    (fun _ _ _ called => attestation_partialsSame electra early called) attestations
  exact (chain (same (first.trans (second.trans third))
    (((Frame.foldlM (fun _ _ _ called => frame_processAttestation called) attestations).slot).trans
      (((BlockFrame.foldlM (fun _ _ _ called => frame_processAttesterSlashing called)
        slashings).slot).trans
        (BlockFrame.foldlM (fun _ _ _ called => frame_processProposerSlashing called)
          proposers).slot))) rest).1

private theorem block_partialLedger {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    (ok : processBlock config checks engine s block = .ok t) :
    ∃ (headed : BeaconState preset fork) (partials : Array Withdrawal) (next : WithdrawalIndex)
      (count : ℕ) (new : List PendingPartialWithdrawal),
      processBlockHeader s block = .ok headed ∧
      getPendingPartialWithdrawals headed electra
        (headed.nextWithdrawalIndex (Nat.le_trans (by decide) electra)) #[] =
          .ok (partials, next, count) ∧
      (t.pendingPartialWithdrawals electra).data.toList =
        (s.pendingPartialWithdrawals electra).data.toList.drop count ++ new ∧
      ∀ w ∈ new, getCurrentEpoch s < w.withdrawableEpoch := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) electra
  have capella : .shapella ≤ fork := Nat.le_trans (by decide) electra
  have before : fork < .hegota := Nat.lt_trans early (by decide)
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  obtain ⟨voted, operated, started, operatedOk, -, synced⟩ := processBlock_operationsInput ok
  have slot := (frame_operationsInput started).slot
  obtain ⟨parented, headed, executed, revealed, paid, headedOk, executedOk, revealedOk,
    votedOk⟩ := started
  simp only [notGloas, bellatrix, before, altair, ↓reduceDIte, pure, Except.pure,
    Except.ok.injEq] at paid executedOk votedOk synced
  subst paid
  obtain ⟨partials, next, count, partialsOk, executedQueue⟩ :
      ∃ (partials : Array Withdrawal) (next : WithdrawalIndex) (count : ℕ),
        getPendingPartialWithdrawals headed electra (headed.nextWithdrawalIndex capella) #[] =
          .ok (partials, next, count) ∧
        (executed.pendingPartialWithdrawals electra).data.toList =
          (headed.pendingPartialWithdrawals electra).data.toList.drop count := by
    simp only [processBlockExecution, notGloas, capella, ↓reduceDIte, bind_ok_iff] at executedOk
    obtain ⟨withdrawn, withdrawnOk, payload⟩ := executedOk
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok payload
    simpa only using withdrawals_pendingPartials electra early withdrawnOk
  have voteQueue := congrArg (fun state => state.pendingPartialWithdrawals electra)
    (processEth1Data_eq votedOk).2.2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealedOk
  have headQueue : (voted.pendingPartialWithdrawals electra).data.toList =
      (s.pendingPartialWithdrawals electra).data.toList.drop count := by
    rw [voteQueue]
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
    exact executedQueue
  obtain ⟨new, queue, late⟩ := operations_queueAppend electra early operatedOk electra
  obtain ⟨_, syncedEq⟩ := processSyncAggregate_eq synced
  refine ⟨headed, partials, next, count, new, headedOk, partialsOk, ?_, ?_⟩
  · rw [syncedEq]
    exact queue.trans (congrArg (· ++ new) headQueue)
  · simpa only [getCurrentEpoch, slot] using late

private theorem upgrades_partials {s t : ForkedBeaconState preset}
    (electra : .pectra ≤ s.fork) (early : t.fork < .glamsterdam)
    (ok : processUpgrades config checks s = .ok t) (targetElectra : .pectra ≤ t.fork) :
    (t.state.pendingPartialWithdrawals targetElectra).data.toList =
      (s.state.pendingPartialWithdrawals electra).data.toList := by
  fun_induction processUpgrades config checks s generalizing t with
  | case1 s due ih =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
    have nextElectra := Nat.le_trans electra (Nat.le_of_lt next.property)
    have nextEarly := Nat.lt_of_le_of_lt (processUpgrades_fork_le rest) early
    rw [ih next nextElectra early rest targetElectra]
    obtain ⟨fork, state⟩ := s
    have sourceEarly := Nat.lt_trans next.property nextEarly
    have forkCases : fork = .pectra ∨ fork = .fusaka := by
      change Fork.pectra ≤ fork at electra
      change fork < Fork.glamsterdam at sourceEarly
      cases fork <;> simp_all (config := { decide := true })
      all_goals cases nextOk
    rcases forkCases with rfl | rfl
    · simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at nextOk
      obtain ⟨_, upgraded, rfl⟩ := nextOk
      simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
      obtain ⟨_, _, rfl⟩ := upgraded
      rfl
    · simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at nextOk
      obtain ⟨_, _, rfl⟩ := nextOk
      exact False.elim (Nat.lt_irrefl _ nextEarly)
  | case2 s notDue => cases ok; rfl

private theorem step_partialLedger {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (targetElectra : .pectra ≤ y.fork) :
    ∃ (count : ℕ) (new : List PendingPartialWithdrawal) (pay : ℕ → ℕ),
      count ≤ (x.state.pendingPartialWithdrawals electra).data.toList.length ∧
      (y.state.pendingPartialWithdrawals targetElectra).data.toList =
        (x.state.pendingPartialWithdrawals electra).data.toList.drop count ++ new ∧
      (∀ w ∈ new, ∃ (f : Fork) (before after : BeaconState preset f)
        (engine : ExecutionEngine preset f) (signed : SignedBeaconBlock preset f)
        (due : upgradeDue config ⟨f, before⟩ = false)
        (applied : applySignedBlock config checks engine before signed true = .ok after),
        (Run.nil.snoc step).Contains (.block engine signed due applied) ∧
        getCurrentEpoch before = getCurrentEpoch x.state ∧
        getCurrentEpoch before < w.withdrawableEpoch) ∧
      (∀ k, count ≤ k → pay k = 0) ∧
      (∀ k < count, ∃ w, (x.state.pendingPartialWithdrawals electra).data.toList[k]? = some w ∧
        pay k ≤ w.amount.toNat ∧ (0 < pay k → w.withdrawableEpoch ≤ getCurrentEpoch x.state)) ∧
      ∀ v, step.queuePaid v = ∑ k ∈ (Finset.range count).filter (fun k =>
        (x.state.pendingPartialWithdrawals electra).data.toList[k]?.map (·.validatorIndex) =
          some v), pay k := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
    refine ⟨0, [], fun _ => 0, Nat.zero_le _, ?_, by simp, fun _ _ => rfl,
      fun _ small => absurd small (by omega), fun _ => by simp [Step.queuePaid]⟩
    rw [upgrades_partials (s := ⟨x.fork, advanced⟩) electra early upgraded targetElectra,
      List.drop_zero, List.append_nil]
    exact congrArg (fun queue => queue.data.toList)
      (advanceSlot_pendingPartialWithdrawals electra advancedOk)
  | block engine signed due ok =>
    obtain ⟨headed, partials, next, count, new, headedOk, partialsOk, queue, late⟩ :=
      block_partialLedger electra early (applySignedBlock_ok ok).2.1
    obtain ⟨pay, bounded, beyond, entries, sums⟩ := getPendingPartialWithdrawals_ledger partialsOk
    have paid : ∀ v, (Step.block engine signed due ok).queuePaid v =
        ((partials.toList.filter (·.validatorIndex = v)).map (·.amount.toNat)).sum := by
      intro v
      simp only [Step.queuePaid, show Fork.pectra ≤ _ ∧ _ < Fork.glamsterdam from
        ⟨electra, early⟩, headedOk, partialsOk, bind, Except.bind, pure, Except.pure,
        Except.toOption, Option.getD_some, and_self, dite_true]
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
    refine ⟨count, new, pay, bounded, queue, ?_, beyond, entries,
      fun v => (paid v).trans (sums v)⟩
    intro w member
    exact ⟨_, _, _, engine, signed, due, ok, .last _ _, rfl, late w member⟩

private theorem run_partialLedger {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (targetElectra : .pectra ≤ y.fork) :
    ∃ (appended : List (PendingPartialWithdrawal × Epoch)) (consumed : ℕ) (paid : ℕ → ℕ),
      let ledger := (x.state.pendingPartialWithdrawals electra).data.toList ++ appended.map (·.1)
      consumed ≤ ledger.length ∧
      (y.state.pendingPartialWithdrawals targetElectra).data.toList = ledger.drop consumed ∧
      (∀ a ∈ appended, ∃ (f : Fork) (before after : BeaconState preset f)
        (engine : ExecutionEngine preset f) (signed : SignedBeaconBlock preset f)
        (due : upgradeDue config ⟨f, before⟩ = false)
        (applied : applySignedBlock config checks engine before signed true = .ok after),
        tail.Contains (.block engine signed due applied) ∧ getCurrentEpoch before = a.2 ∧
        a.2 < a.1.withdrawableEpoch) ∧
      (∀ j, consumed ≤ j → paid j = 0) ∧
      (∀ j < consumed, ∃ w, ledger[j]? = some w ∧ paid j ≤ w.amount.toNat ∧
        (0 < paid j → w.withdrawableEpoch ≤ getCurrentEpoch y.state)) ∧
      ∀ v, tail.queuePaid v = ∑ j ∈ (Finset.range consumed).filter
        (fun j => ledger[j]?.map (·.validatorIndex) = some v), paid j := by
  induction tail with
  | nil =>
    refine ⟨[], 0, fun _ => 0, ?_⟩
    simp [Run.queuePaid]
  | @snoc middle last pre step ih =>
    have middleElectra := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
    obtain ⟨appended, consumed, paid, bounded, queue, charged, beyond, entries, sums⟩ :=
      ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early) middleElectra
    obtain ⟨count, new, pay, counted, stepQueue, stepCharged, stepBeyond, stepEntries,
      stepSums⟩ := step_partialLedger step middleElectra early targetElectra
    have stepped := currentEpoch_le_of_chainSteps (.single step.chainStep)
    generalize ledgerDef : (x.state.pendingPartialWithdrawals electra).data.toList ++
      appended.map (·.1) = ledger at bounded queue entries sums
    have middleLength : (middle.state.pendingPartialWithdrawals middleElectra).data.toList.length =
        ledger.length - consumed := by rw [queue, List.length_drop]
    have within : consumed + count ≤ ledger.length := by omega
    refine ⟨appended ++ new.map (·, getCurrentEpoch middle.state), consumed + count,
      fun j => if j < consumed then paid j else pay (j - consumed), ?_⟩
    have extended : (x.state.pendingPartialWithdrawals electra).data.toList ++
        (appended ++ new.map (·, getCurrentEpoch middle.state)).map (·.1) = ledger ++ new := by
      rw [← ledgerDef]
      simp [Function.comp_def]
    have prefixAt : ∀ j < ledger.length, (ledger ++ new)[j]? = ledger[j]? :=
      fun j small => List.getElem?_append_left small
    intro ledger'
    simp only [ledger', extended]
    refine ⟨by simp only [List.length_append]; omega, ?_, ?_, ?_, ?_, ?_⟩
    · rw [stepQueue, queue, List.drop_drop, List.drop_append_of_le_length within]
    · intro a member
      rcases List.mem_append.mp member with member | member
      · obtain ⟨f, before, after, engine, signed, due, applied, contained, epoch, late⟩ :=
          charged a member
        exact ⟨f, before, after, engine, signed, due, applied,
          .earlier contained step, epoch, late⟩
      · obtain ⟨w, added, rfl⟩ := List.mem_map.mp member
        obtain ⟨f, before, after, engine, signed, due, applied, contained, epoch, late⟩ :=
          stepCharged w added
        refine ⟨f, before, after, engine, signed, due, applied, ?_, epoch, epoch ▸ late⟩
        exact (Run.contains_append pre (Run.nil.snoc step) _).mpr (.inr contained)
    · intro j large
      have notOld : ¬ j < consumed := by omega
      simp only [notOld, ↓reduceIte]
      exact stepBeyond _ (by omega)
    · intro j small
      by_cases old : j < consumed
      · obtain ⟨w, found, bound, due⟩ := entries j old
        refine ⟨w, (prefixAt j (by omega)).trans found, by simpa [old] using bound, ?_⟩
        intro positive
        simp only [old, ↓reduceIte] at positive
        exact UInt64.le_trans (due positive) stepped
      · obtain ⟨w, found, bound, due⟩ := stepEntries (j - consumed) (by omega)
        refine ⟨w, ?_, by simpa [old] using bound, ?_⟩
        · rw [prefixAt j (by omega), ← found, queue, List.getElem?_drop]
          congr 1
          omega
        · intro positive
          simp only [old, ↓reduceIte] at positive
          exact UInt64.le_trans (due positive) stepped
    · intro v
      simp only [Run.queuePaid, sums v, stepSums v, Finset.sum_filter, Finset.sum_range_add]
      congr 1
      · refine Finset.sum_congr rfl fun j member => ?_
        have small := Finset.mem_range.mp member
        simp [small, prefixAt j (by omega)]
      · refine Finset.sum_congr rfl fun k member => ?_
        have small := Finset.mem_range.mp member
        rw [prefixAt (consumed + k) (by omega), queue, List.getElem?_drop]
        simp

private theorem sum_filter_map_eq_sum_range {α : Type} (p : α → Bool) (f : α → ℕ) :
    ∀ l : List α, ((l.filter p).map f).sum =
      ∑ j ∈ Finset.range l.length, ((l[j]?.filter p).map f).getD 0
  | [] => by simp
  | a :: l => by
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
      ← sum_filter_map_eq_sum_range p f l]
    cases passes : p a
    · simp [passes, Option.filter_some]
    · simp [passes, Option.filter_some]
      omega

/-- A run within one epoch pays only the due entries of its starting partial-withdrawal queue. -/
theorem queuePaid_le_ancestorPartials {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (targetElectra : .pectra ≤ y.fork) {epoch : Epoch}
    (blocks : ∀ {f : Fork} {before after : BeaconState preset f}
      {engine : ExecutionEngine preset f} {signed : SignedBeaconBlock preset f}
      {due : upgradeDue config ⟨f, before⟩ = false}
      {applied : applySignedBlock config checks engine before signed true = .ok after},
      tail.Contains (.block engine signed due applied) → epoch ≤ getCurrentEpoch before)
    (ended : getCurrentEpoch y.state ≤ epoch) (v : ValidatorIndex) :
    tail.queuePaid v ≤
      (((x.state.pendingPartialWithdrawals electra).data.toList.filter fun w =>
        w.validatorIndex.toNat = v.toNat ∧ w.withdrawableEpoch ≤ epoch).map
          (·.amount.toNat)).sum := by
  obtain ⟨appended, consumed, paid, -, -, charged, -, entries, sums⟩ :=
    run_partialLedger tail electra early targetElectra
  generalize queueDef : (x.state.pendingPartialWithdrawals electra).data.toList = queue at *
  let due (j : ℕ) := ((queue[j]?.filter fun w =>
    w.validatorIndex.toNat = v.toNat ∧ w.withdrawableEpoch ≤ epoch).map (·.amount.toNat)).getD 0
  have bound : ∀ j ∈ Finset.range consumed,
      (if (queue ++ appended.map (·.1))[j]?.map (·.validatorIndex) = some v then paid j else 0) ≤
        if j < queue.length then due j else 0 := by
    intro j member
    obtain ⟨w, found, cap, paidDue⟩ := entries j (Finset.mem_range.mp member)
    by_cases positive : 0 < paid j
    swap
    · have zero : paid j = 0 := by omega
      simp [zero]
    have withdrawable := UInt64.le_trans (paidDue positive) ended
    by_cases old : j < queue.length
    · have read : queue[j]? = some w := by rwa [List.getElem?_append_left old] at found
      simp only [found, read, Option.map_some, Option.some.injEq, old, ↓reduceIte, due,
        Option.filter_some]
      by_cases named : w.validatorIndex = v
      · simp [named, withdrawable, cap]
      · simp [named]
    · exfalso
      rw [List.getElem?_append_right (by omega), List.getElem?_map] at found
      obtain ⟨a, appendedAt, rfl⟩ := Option.map_eq_some_iff.mp found
      obtain ⟨_, _, _, _, _, _, _, contained, blockEpoch, late⟩ :=
        charged a (List.mem_of_getElem? appendedAt)
      have paidBy := UInt64.le_iff_toNat_le.mp withdrawable
      have starts := UInt64.le_iff_toNat_le.mp (blockEpoch ▸ blocks contained)
      have later := UInt64.lt_iff_toNat_lt.mp late
      omega
  rw [sums v, Finset.sum_filter, sum_filter_map_eq_sum_range]
  calc _ ≤ ∑ j ∈ Finset.range consumed, if j < queue.length then due j else 0 :=
      Finset.sum_le_sum bound
    _ ≤ ∑ j ∈ Finset.range queue.length, due j := by
      rw [← Finset.sum_filter]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (by intro j member; exact Finset.mem_range.mpr (Finset.mem_filter.mp member).2)
        (by intros; exact Nat.zero_le _)

end EthLib.Consensus.DirectSafety
