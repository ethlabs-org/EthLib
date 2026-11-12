module

public import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
import all EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
import all EthLib.Consensus.Proofs.Transition.BalanceSources

/-!
# Gloas accounting rates and parent replay

The three churn rates follow [EIP-8061], Churn computations.

Exit churn has a minimum and no cap.

Activation churn caps the rounded exit rate with its own configuration field.

Consolidation churn has neither a minimum nor a cap.

The parent replay follows [EIP-7732], Beacon chain changes, State transition.

Builder requests follow [EIP-8282], Consensus layer processing.

[EIP-8061]: https://eips.ethereum.org/EIPS/eip-8061#churn-computations
[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#state-transition
[EIP-8282]: https://eips.ethereum.org/EIPS/eip-8282#consensus-layer-processing
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- Exit churn rounds down after applying its minimum, without an activation cap. -/
def gloasExitRate (preset : Preset) (config : Config) (total : Gwei) : Nat :=
  (roundToIncrement preset (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
    (total / config.CHURN_LIMIT_QUOTIENT_GLOAS))).toNat

def gloasActivationRate (preset : Preset) (config : Config) (total : Gwei) : Nat :=
  min config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS.toNat
    (gloasExitRate preset config total)

def gloasConsolidationRate (preset : Preset) (config : Config) (total : Gwei) : Nat :=
  (roundToIncrement preset (total / config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT)).toNat

theorem gloas_exit_rate {fork : Fork} (s : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) {total churn : Gwei}
    (active : getTotalActiveBalance s = .ok total)
    (ok : exitChurnLimit config s = .ok churn) :
    churn.toNat = gloasExitRate preset config total := by
  simp only [exitChurnLimit, gloas, ↓reduceIte, getExitChurnLimit, active, bind, Except.bind,
    pure, Except.pure, Except.ok.injEq] at ok
  subst churn
  rfl

theorem gloas_activation_rate {fork : Fork} (s : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) {total churn : Gwei}
    (active : getTotalActiveBalance s = .ok total)
    (ok : depositChurnLimit config s = .ok churn) :
    churn.toNat = gloasActivationRate preset config total := by
  simp only [depositChurnLimit, gloas, ↓reduceIte, getActivationChurnLimit,
    getExitChurnLimit, active, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at ok
  subst churn
  simp [gloasActivationRate, gloasExitRate, Uint64.toNat_min]

theorem gloas_consolidation_rate {fork : Fork} (s : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) {total churn : Gwei}
    (active : getTotalActiveBalance s = .ok total)
    (ok : getConsolidationChurnLimit config s = .ok churn) :
    churn.toNat = gloasConsolidationRate preset config total := by
  simp only [getConsolidationChurnLimit, gloas, ↓reduceIte, active, bind, Except.bind,
    pure, Except.pure, Except.ok.injEq] at ok
  subst churn
  rfl

/-- A window that crosses Gloas must allow either cap, without equating configuration fields. -/
def gloasDepositWindow (config : Config) (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  (if electra : .pectra ≤ x.fork then (x.state.depositBalanceToConsume electra).toNat else 0) +
    driftHorizon x high *
      (if .glamsterdam ≤ x.fork then config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS.toNat
       else max config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat
         config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS.toNat)

/-- EIP-7732, Beacon chain changes: replay requests where the parent payload applies them.

Only consolidation requests can debit validator balances in this pass.

Builder requests update their separate registry, as EIP-8282 specifies. -/
def gloasParentRequestsReplay {fork : Fork} (gloas : .glamsterdam ≤ fork)
    (requests : ExecutionRequests preset fork) (pre : BalanceReplay preset fork) :
    Except TransitionError (BalanceReplay preset fork) := do
  let electra : .pectra ≤ fork := Nat.le_trans (by decide) gloas
  let pre ← carryBalance (fun s => requests.deposits.data.foldlM
    (processDepositRequest · electra ·) s) pre
  let pre ← carryBalance (fun s => requests.withdrawals.data.foldlM
    (processWithdrawalRequest config · electra ·) s) pre
  let pre ← requests.consolidations.data.toList.foldlM (fun pre request =>
    recordBalance .excess (fun s => pure (0,
      match findValidatorByPubkey s request.sourcePubkey with
      | none => 0
      | some i => actualBalanceAt ⟨fork, s⟩ i.val - preset.MIN_ACTIVATION_BALANCE.toNat))
      (processConsolidationRequest config · electra request) pre) pre
  let pre ← carryBalance (fun s => (requests.builderDeposits gloas).data.foldlM
    (processBuilderDepositRequest config checks · gloas ·) s) pre
  carryBalance (fun s => (requests.builderExits gloas).data.foldlM
    (processBuilderExitRequest config · gloas ·) s) pre

theorem gloasParentRequestsReplay_result {fork : Fork} (gloas : .glamsterdam ≤ fork)
    (requests : ExecutionRequests preset fork) (s t : BeaconState preset fork)
    (ok : processParentRequests config checks s gloas requests = .ok t)
    (events : List (BalanceEvent preset)) :
    ∃ recorded, gloasParentRequestsReplay (config := config) (checks := checks)
      gloas requests (s, events) = .ok (t, recorded) := by
  simp only [processParentRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨deposited, deposits, withdrawn, withdrawals, consolidated, consolidations,
    built, builders, exits⟩ := ok
  obtain ⟨recorded, replayed⟩ := replay_fold_result
    (processConsolidationRequest config · (Nat.le_trans (by decide) gloas) ·)
    (fun pre request => recordBalance .excess (fun site => pure (0,
      match findValidatorByPubkey site request.sourcePubkey with
      | none => 0
      | some i => actualBalanceAt ⟨fork, site⟩ i.val - preset.MIN_ACTIVATION_BALANCE.toNat))
      (processConsolidationRequest config · (Nat.le_trans (by decide) gloas) request) pre)
    (fun _ _ _ step events => recordBalance_result step ⟨_, rfl⟩ _ events)
    _ withdrawn consolidated consolidations events
  refine ⟨recorded, ?_⟩
  unfold gloasParentRequestsReplay
  simp only [bind_ok_iff]
  -- Only the consolidation fold appends events; the other folds carry them unchanged.
  refine ⟨(deposited, events), ?_, (withdrawn, events), ?_,
    (consolidated, recorded), replayed, (built, recorded), ?_, ?_⟩
  all_goals
    apply carryBalance_result
    simpa only [← Array.foldlM_toList] using (by assumption)

/-- EIP-7732: parent requests preserve balance lengths and the recorded event bounds. -/
theorem gloas_parent_requests_bounded {fork : Fork} (gloas : .glamsterdam ≤ fork)
    (requests : ExecutionRequests preset fork) (pre post : BalanceReplay preset fork)
    (matched : BalancesMatch pre.1)
    (bounded : ∀ event ∈ pre.2,
      event.credits ≤ event.creditLimit ∧ event.debits ≤ event.debitLimit)
    (ok : gloasParentRequestsReplay (config := config) (checks := checks)
      gloas requests pre = .ok post) :
    BalancesMatch post.1 ∧ ∀ event ∈ post.2,
      event.credits ≤ event.creditLimit ∧ event.debits ≤ event.debitLimit := by
  unfold gloasParentRequestsReplay at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨deposited, deposits, withdrawn, withdrawals, consolidated, consolidations,
    built, builders, exits⟩ := ok
  have depositedBound := carryBalance_bounded _ (fun _ _ ok h =>
    foldlM_ok_invariant BalancesMatch
      (fun _ _ _ h ok => (frame_processDepositRequest ok).balancesMatch h) h
      (by simpa only [← Array.foldlM_toList] using ok)) ⟨matched, bounded⟩ deposits
  have withdrawnBound := carryBalance_bounded _ (fun _ _ ok h =>
    foldlM_ok_invariant BalancesMatch
      (fun _ _ _ h ok => (frame_processWithdrawalRequest ok).balancesMatch h) h
      (by simpa only [← Array.foldlM_toList] using ok)) depositedBound withdrawals
  -- Only consolidations append events, using the existing excess-balance debit bound.
  have consolidatedBound : ReplayBounded consolidated := by
    apply foldlM_ok_invariant ReplayBounded ?_ withdrawnBound consolidations
    intro pre request post initial ok
    apply recordBalance_matched _ _ _ (fun _ _ ok =>
      balancesMatch_of_sameSizes (sameSizes_processConsolidationRequest ok)) ?_ initial ok
    intro s t credit debit _ limits action
    cases limits
    exact consolidation_request_bounds (Nat.le_trans (by decide) gloas) request action
  have builtBound := carryBalance_bounded _ (fun _ _ ok h =>
    foldlM_ok_invariant BalancesMatch
      (fun _ _ _ h ok => (frame_processBuilderDepositRequest ok).balancesMatch h) h
      (by simpa only [← Array.foldlM_toList] using ok)) consolidatedBound builders
  exact carryBalance_bounded _ (fun _ _ ok h =>
    foldlM_ok_invariant BalancesMatch
      (fun _ _ _ h ok => (frame_processBuilderExitRequest ok).balancesMatch h) h
      (by simpa only [← Array.foldlM_toList] using ok)) builtBound exits

/-- Replay the full parent's requests between payment settlement and availability marking. -/
def gloasParentPayloadReplay {fork : Fork} (gloas : .glamsterdam ≤ fork)
    (body : BeaconBlockBody preset fork) (pre : BalanceReplay preset fork) :
    Except TransitionError (BalanceReplay preset fork) := do
  let bid := (body.signedExecutionPayloadBid gloas).message
  let parentBid := pre.1.latestExecutionPayloadBid gloas
  let parentSlot := pre.1.latestBlockHeader.slot
  let requests := body.parentExecutionRequests gloas
  if bid.parentBlockHash ≠ parentBid.blockHash then
    ensure (requests.isEmpty gloas) .parentRequestsNotEmpty
    return pre
  let root ← liftSsz (Serialization.Ssz.SszType.hashTreeRoot requests)
  ensure (root = parentBid.executionRequestsRoot) .wrongParentRequestsRoot
  checkCount requests.withdrawals.data.size preset.MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD
  checkCount requests.consolidations.data.size preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD
  checkCount (requests.builderDeposits gloas).data.size
    preset.MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD
  checkCount (requests.builderExits gloas).data.size preset.MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD
  let pre ← carryBalance (settleParentPayment · gloas) pre
  let pre ← gloasParentRequestsReplay (config := config) (checks := checks) gloas requests pre
  let bits ← liftAccessor
    (writeCircular (pre.1.executionPayloadAvailability gloas).bits parentSlot true)
  return ({ pre.1 with
    executionPayloadAvailability := fun _ => ⟨bits⟩
    latestBlockHash := fun _ => parentBid.blockHash }, pre.2)

theorem gloasParentPayloadReplay_result {fork : Fork} (gloas : .glamsterdam ≤ fork)
    (body : BeaconBlockBody preset fork) (s t : BeaconState preset fork)
    (ok : processParentExecutionPayload config checks s gloas body = .ok t)
    (events : List (BalanceEvent preset)) :
    ∃ recorded, gloasParentPayloadReplay (config := config) (checks := checks)
      gloas body (s, events) = .ok (t, recorded) := by
  unfold processParentExecutionPayload at ok
  unfold gloasParentPayloadReplay
  dsimp only at ok ⊢
  -- Empty parents retain both the state and the accumulated events.
  split at ok <;> rename_i full
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, checked, rfl⟩ := ok
    exact ⟨events, by simp [full, checked, bind, Except.bind, pure, Except.pure]⟩
  · simp only [full, ↓reduceIte, applyParentExecutionPayload, bind_ok_iff,
      pure, Except.pure, Except.ok.injEq] at ok ⊢
    obtain ⟨root, rootOk, _, rootEq, _, wCount, _, cCount, _, bCount, _, eCount,
      settled, settledOk, requested, requestedOk, bits, bitsOk, rfl⟩ := ok
    -- Replay the requests at the settled state, before marking parent availability.
    obtain ⟨recorded, replayed⟩ :=
      gloasParentRequestsReplay_result gloas _ settled requested requestedOk events
    exact ⟨recorded, root, rootOk, _, rootEq, _, wCount, _, cCount, _, bCount, _, eCount,
      (settled, events), carryBalance_result settledOk events,
      (requested, recorded), replayed, bits, bitsOk, rfl⟩

/-- EIP-7732: parent payload processing preserves the recorded validator balance bounds. -/
theorem gloas_parent_payload_bounded {fork : Fork} (gloas : .glamsterdam ≤ fork)
    (body : BeaconBlockBody preset fork) (pre post : BalanceReplay preset fork)
    (matched : BalancesMatch pre.1)
    (bounded : ∀ event ∈ pre.2,
      event.credits ≤ event.creditLimit ∧ event.debits ≤ event.debitLimit)
    (ok : gloasParentPayloadReplay (config := config) (checks := checks)
      gloas body pre = .ok post) :
    BalancesMatch post.1 ∧ ∀ event ∈ post.2,
      event.credits ≤ event.creditLimit ∧ event.debits ≤ event.debitLimit := by
  unfold gloasParentPayloadReplay at ok
  dsimp only at ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, rfl⟩ := ok
    exact ⟨matched, bounded⟩
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, settled, settledOk,
      requested, requestedOk, _, _, rfl⟩ := ok
    have settledBound := carryBalance_bounded _
      (fun _ _ ok => (frame_settleParentPayment ok).balancesMatch)
      ⟨matched, bounded⟩ settledOk
    -- Availability and block-hash writes leave validator data and recorded events unchanged.
    exact gloas_parent_requests_bounded gloas _ settled requested
      settledBound.1 settledBound.2 requestedOk

/-- EIP-7732, State transition: builder payments do not change validator balances.

The effective-balance pass reads the state after builder payments settle.

The payload-committee window at the end also keeps validator balances. -/
theorem epochBalanceReplay_result_gloas {fork : Fork} (s t : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) (ok : processEpoch config checks s = .ok t) :
    ∃ middle paid updated events,
      epochBalanceReplay (config := config) (checks := checks) s = .ok (middle, events) ∧
      processBuilderPendingPayments middle gloas = .ok paid ∧
      processEffectiveBalanceUpdates paid = .ok updated ∧
      paid.validators = middle.validators ∧ paid.balances = middle.balances ∧
      updated.validators = t.validators ∧ middle.balances = t.balances := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) gloas
  have capella : .shapella ≤ fork := Nat.le_trans (by decide) gloas
  have fulu : .fusaka ≤ fork := Nat.le_trans (by decide) gloas
  simp only [processEpoch, altair, ↓reduceDIte,
    processEpochAltair_eq_epochBeforePayments_bind, gloas, capella, fulu,
    ↓reduceDIte, bind_ok_iff] at ok
  obtain ⟨middle, middleOk, paid, paidOk, updated, updatedOk, cleared, clearedOk,
    mixed, mixedOk, historical, historyOk, synced, syncedOk, looked, lookedOk, windowOk⟩ := ok
  obtain ⟨events, replay⟩ := epochBalanceReplay_before middleOk
  have paymentKept : paid.validators = middle.validators ∧
      paid.balances = middle.balances := by
    simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff,
      pure, Except.pure, Except.ok.injEq] at paidOk
    obtain ⟨_, _, rfl⟩ := paidOk
    exact ⟨rfl, rfl⟩
  -- Reuse the unchanged epoch tail up to proposer lookahead.
  have tail : looked.validators = updated.validators ∧ looked.balances = updated.balances :=
    epochTail_kept (by
      simp only [altair, capella, fulu, ↓reduceDIte, bind_ok_iff]
      exact ⟨cleared, clearedOk, mixed, mixedOk, historical, historyOk,
        synced, syncedOk, lookedOk⟩)
  have window : t.validators = looked.validators ∧ t.balances = looked.balances := by
    simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at windowOk
    obtain ⟨_, _, _, _, rfl⟩ := windowOk
    exact ⟨rfl, rfl⟩
  exact ⟨middle, paid, updated, events, replay, liftAccessor_ok.mp paidOk, updatedOk,
    paymentKept.1, paymentKept.2, (window.1.trans tail.1).symm,
    (window.2.trans (tail.2.trans
      ((effectiveUpdates_balances updatedOk).trans paymentKept.2))).symm⟩

/-- EIP-7732, State transition: withdrawals run only when the parent is full.

The bound includes builder withdrawals, so it can overestimate validator debits. -/
def gloasWithdrawalLimits {fork : Fork} (gloas : .glamsterdam ≤ fork)
    (s : BeaconState preset fork) : Except TransitionError (Nat × Nat) := do
  if isParentBlockFull s gloas then
    return (0, ((← getExpectedWithdrawals s (Nat.le_trans (by decide) gloas)).withdrawals.toList.map
      fun w => w.amount.toNat).sum)
  else return (0, 0)

theorem gloasWithdrawalLimits_result {fork : Fork} (gloas : .glamsterdam ≤ fork)
    (s t : BeaconState preset fork)
    (ok : processWithdrawals s (Nat.le_trans (by decide) gloas)
      (fun before => absurd gloas (Nat.not_le_of_lt before)) = .ok t) :
    ∃ limits, gloasWithdrawalLimits gloas s = .ok limits := by
  simp only [processWithdrawals, gloas, ↓reduceDIte] at ok
  unfold gloasWithdrawalLimits
  split at ok <;> rename_i full
  · simp only [bind_ok_iff] at ok
    obtain ⟨expected, expectedOk, _⟩ := ok
    refine ⟨(0, (expected.withdrawals.toList.map fun w => w.amount.toNat).sum), ?_⟩
    simp [full, expectedOk, bind, Except.bind, pure, Except.pure]
  · exact ⟨(0, 0), by simp [full, pure, Except.pure]⟩

/-- Gloas operations retain their validation order and record validator rewards and slashings. -/
def gloasOperationsReplay {fork : Fork} (gloas : .glamsterdam ≤ fork)
    (before : fork < .hegota) (body : BeaconBlockBody preset fork) (parent : Slot)
    (pre : BalanceReplay preset fork) : Except TransitionError (BalanceReplay preset fork) := do
  ensure ((body.deposits before).data.size = 0)
    (.wrongDepositCount (body.deposits before).data.size 0)
  let changes := (body.blsToExecutionChanges (Nat.le_trans (by decide) gloas)).data
  let payloadAttestations := (body.payloadAttestations gloas).data
  checkCount body.proposerSlashings.data.size preset.MAX_PROPOSER_SLASHINGS
  checkCount body.attesterSlashings.data.size preset.MAX_ATTESTER_SLASHINGS_ELECTRA
  checkCount body.attestations.data.size preset.MAX_ATTESTATIONS_ELECTRA
  checkCount body.voluntaryExits.data.size preset.MAX_VOLUNTARY_EXITS
  checkCount changes.size preset.MAX_BLS_TO_EXECUTION_CHANGES
  checkCount payloadAttestations.size preset.MAX_PAYLOAD_ATTESTATIONS
  let pre ← body.proposerSlashings.data.toList.foldlM (fun pre sl =>
    recordBalance .slashings (slashingLimits [sl.signedHeader1.message.proposerIndex])
      (processProposerSlashing config checks · sl) pre) pre
  let pre ← body.attesterSlashings.data.toList.foldlM (fun pre sl =>
    recordBalance .slashings (slashingLimits (slashingIndices sl))
      (processAttesterSlashing config checks · sl) pre) pre
  let pre ← body.attestations.data.toList.foldlM (fun pre att =>
    recordBalance .rewards (fun site => do return (← attestationCredit site att parent, 0))
      (processAttestation config checks · parent att) pre) pre
  let pre ← carryBalance (fun s => body.voluntaryExits.data.foldlM
    (processVoluntaryExit config checks) s) pre
  let pre ← carryBalance (fun s => changes.foldlM
    (processBlsToExecutionChange config checks) s) pre
  carryBalance (fun s => payloadAttestations.foldlM
    (processPayloadAttestation config checks · gloas ·) s) pre

theorem gloasOperationsReplay_result {fork : Fork} (gloas : .glamsterdam ≤ fork)
    (before : fork < .hegota) (body : BeaconBlockBody preset fork) (parent : Slot)
    (s t : BeaconState preset fork)
    (ok : processOperationsGloas config checks s body gloas parent = .ok t)
    (events : List (BalanceEvent preset)) :
    ∃ recorded, gloasOperationsReplay (config := config) (checks := checks)
      gloas before body parent (s, events) = .ok (t, recorded) := by
  simp only [processOperationsGloas, before, ↓reduceDIte, bind_ok_iff,
    ← Array.foldlM_toList] at ok
  obtain ⟨_, noDeposits, _, pCount, _, aCount, _, attCount, _, exitCount, _, changeCount,
    _, payloadCount, proposed, proposedOk, slashed, slashedOk, attested, attestedOk,
    exited, exitedOk, changed, changedOk, payloadOk⟩ := ok
  obtain ⟨proposedEvents, proposedReplay⟩ := replay_fold_result
    (processProposerSlashing config checks)
    (fun pre sl => recordBalance .slashings
      (slashingLimits [sl.signedHeader1.message.proposerIndex])
      (processProposerSlashing config checks · sl) pre)
    (fun _ _ _ step events => recordBalance_result step (proposerLimits_result step) _ events)
    _ s proposed proposedOk events
  obtain ⟨slashedEvents, slashedReplay⟩ := replay_fold_result
    (processAttesterSlashing config checks)
    (fun pre sl => recordBalance .slashings (slashingLimits (slashingIndices sl))
      (processAttesterSlashing config checks · sl) pre)
    (fun _ _ _ step events => recordBalance_result step (attesterLimits_result step) _ events)
    _ proposed slashed slashedOk proposedEvents
  obtain ⟨attestedEvents, attestedReplay⟩ := replay_fold_result
    (processAttestation config checks · parent ·)
    (fun pre att => recordBalance .rewards (fun site => do
      return (← attestationCredit site att parent, 0))
      (processAttestation config checks · parent att) pre)
    (fun _ _ _ step events => recordBalance_result step (by
      obtain ⟨credit, computed⟩ := attestationCredit_result step
      exact ⟨(credit, 0), by rw [computed]; rfl⟩) _ events)
    _ slashed attested attestedOk slashedEvents
  -- The remaining operations leave the event list unchanged.
  refine ⟨attestedEvents, ?_⟩
  simp only [gloasOperationsReplay, bind_ok_iff]
  refine ⟨_, noDeposits, _, pCount, _, aCount, _, attCount, _, exitCount, _, changeCount,
    _, payloadCount, (proposed, proposedEvents), proposedReplay,
    (slashed, slashedEvents), slashedReplay, (attested, attestedEvents), attestedReplay,
    (exited, attestedEvents), ?_, (changed, attestedEvents), ?_, ?_⟩
  all_goals
    apply carryBalance_result
    simpa only [← Array.foldlM_toList] using (by assumption)

/-- EIP-7732, State transition: the parent payload precedes the header and withdrawals. -/
def gloasBlockBalanceReplay {fork : Fork} (gloas : .glamsterdam ≤ fork)
    (before : fork < .hegota) (s : BeaconState preset fork) (block : BeaconBlock preset fork) :
    Except TransitionError (BalanceReplay preset fork) := do
  let pre ← gloasParentPayloadReplay (config := config) (checks := checks) gloas block.body (s, [])
  let pre ← carryBalance (processBlockHeader · block) pre
  let pre ← recordBalance .withdrawals (gloasWithdrawalLimits gloas)
    (fun site => processWithdrawals site (Nat.le_trans (by decide) gloas)
      (fun early => absurd gloas (Nat.not_le_of_lt early))) pre
  let pre ← carryBalance (fun site => processExecutionPayloadBid config checks site gloas
    (block.body.signedExecutionPayloadBid gloas)) pre
  let pre ← carryBalance (processRandao config checks · block.body) pre
  let pre ← carryBalance (processEth1Data before · block.body) pre
  let pre ← gloasOperationsReplay (config := config) (checks := checks)
    gloas before block.body s.latestBlockHeader.slot pre
  let altair : .altair ≤ fork := Nat.le_trans (by decide) gloas
  recordBalance .sync (fun site => do
    let reward ← syncParticipantReward site
    let proposer ← liftAccessor (liftArith do
      Uint64.divChecked (← Uint64.mulChecked reward PROPOSER_WEIGHT)
        (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT))
    return (preset.SYNC_COMMITTEE_SIZE.toNat * (reward.toNat + proposer.toNat),
      preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat))
    (processSyncAggregate config checks · altair (block.body.syncAggregate altair)) pre

theorem gloasBlockBalanceReplay_result {fork : Fork} (gloas : .glamsterdam ≤ fork)
    (before : fork < .hegota) (engine : ExecutionEngine preset fork)
    (s t : BeaconState preset fork) (block : BeaconBlock preset fork)
    (ok : processBlock config checks engine s block = .ok t) :
    ∃ events, gloasBlockBalanceReplay (config := config) (checks := checks)
      gloas before s block = .ok (t, events) := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) gloas
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) gloas
  simp only [processBlock, altair, ↓reduceDIte, processBlockAltair, gloas, bellatrix,
    before, ↓reduceDIte, processBlockExecution, processOperations, bind_ok_iff] at ok
  obtain ⟨parent, parentOk, headed, headerOk, executed, ⟨withdrawn, withdrawalOk, bidOk⟩,
    revealed, randaoOk, voted, voteOk, operated, operationsOk, syncOk⟩ := ok
  obtain ⟨parentEvents, parentReplay⟩ :=
    gloasParentPayloadReplay_result gloas block.body s parent parentOk []
  obtain ⟨withdrawalEvents, withdrawalReplay⟩ := recordBalance_result
    (action := fun site => processWithdrawals site (Nat.le_trans (by decide) gloas)
      (fun early => absurd gloas (Nat.not_le_of_lt early))) withdrawalOk
    (gloasWithdrawalLimits_result gloas headed withdrawn withdrawalOk) .withdrawals parentEvents
  obtain ⟨operationEvents, operationReplay⟩ :=
    gloasOperationsReplay_result gloas before block.body s.latestBlockHeader.slot
      voted operated operationsOk withdrawalEvents
  obtain ⟨reward, proposer, rewardOk, proposerOk⟩ := syncLimits_result syncOk
  have limits : ∃ limit, (do
      let reward ← syncParticipantReward operated
      let proposer ← liftAccessor (liftArith do
        Uint64.divChecked (← Uint64.mulChecked reward PROPOSER_WEIGHT)
          (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT))
      pure (preset.SYNC_COMMITTEE_SIZE.toNat * (reward.toNat + proposer.toNat),
        preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat)) =
        (Except.ok limit : Except TransitionError (Nat × Nat)) := by
    simp only [bind, Except.bind] at proposerOk
    simp only [rewardOk, proposerOk, bind, Except.bind, pure, Except.pure]
    exact ⟨_, rfl⟩
  obtain ⟨events, syncReplay⟩ := recordBalance_result
    (action := fun site =>
      processSyncAggregate config checks site altair (block.body.syncAggregate altair))
    (limits := fun site => do
      let reward ← syncParticipantReward site
      let proposer ← liftAccessor (liftArith do
        Uint64.divChecked (← Uint64.mulChecked reward PROPOSER_WEIGHT)
          (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT))
      return (preset.SYNC_COMMITTEE_SIZE.toNat * (reward.toNat + proposer.toNat),
        preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat))
    syncOk limits .sync operationEvents
  refine ⟨events, ?_⟩
  simp only [gloasBlockBalanceReplay, bind_ok_iff]
  exact ⟨(parent, parentEvents), parentReplay,
    (headed, parentEvents), carryBalance_result headerOk parentEvents,
    (withdrawn, withdrawalEvents), withdrawalReplay,
    (executed, withdrawalEvents), carryBalance_result bidOk withdrawalEvents,
    (revealed, withdrawalEvents), carryBalance_result randaoOk withdrawalEvents,
    (voted, withdrawalEvents), carryBalance_result voteOk withdrawalEvents,
    (operated, operationEvents), operationReplay, syncReplay⟩

/-- Extend block event recording to Gloas without changing the pre-Gloas entry point. -/
def _root_.EthLib.Consensus.Step.balanceEventsGloas {x y : ForkedBeaconState preset}
    (step : Step config checks x y) : Except TransitionError (List (BalanceEvent preset)) :=
  match step with
  | .block _ signed _ _ => do
    if gloas : .glamsterdam ≤ x.fork then
      if before : x.fork < .hegota then
        return (← gloasBlockBalanceReplay (config := config) (checks := checks)
          gloas before x.state signed.message).2
      else throw (.accessor (.forkNotYetSpecified x.fork))
    else step.balanceEvents
  | .slot _ => step.balanceEvents

theorem _root_.EthLib.Consensus.Step.balanceEventsGloas_eq {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (early : x.fork < .glamsterdam) :
    step.balanceEventsGloas = step.balanceEvents := by
  cases step with
  | slot _ => rfl
  | block _ _ _ _ =>
    simp only [Step.balanceEventsGloas]
    split
    · rename_i gloas
      exact False.elim (Nat.not_le_of_lt early gloas)
    · rfl

/-- Replay succeeds through Gloas; the event bounds are a separate obligation. -/
theorem _root_.EthLib.Consensus.Step.balanceEventsGloas_result
    {x y : ForkedBeaconState preset} (step : Step config checks x y)
    (before : y.fork < .hegota) : ∃ events, step.balanceEventsGloas = .ok events := by
  have startBefore := Nat.lt_of_le_of_lt step.chainStep.fork_le before
  cases step with
  | @block fork s t engine signed due ok =>
    have bound : fork < .hegota := before
    by_cases gloas : .glamsterdam ≤ fork
    · obtain ⟨events, replay⟩ := gloasBlockBalanceReplay_result gloas startBefore engine
        s t signed.message (applySignedBlock_ok ok).2.1
      exact ⟨events, by simp [Step.balanceEventsGloas, gloas, bound, replay,
        bind, Except.bind, pure, Except.pure]⟩
    · have early : fork < .glamsterdam := Nat.lt_of_not_le gloas
      obtain ⟨events, replay⟩ := blockBalanceReplay_result _ _ early
        engine signed.message (applySignedBlock_ok ok).2.1
      exact ⟨events, by simp [Step.balanceEventsGloas, Step.balanceEvents, gloas,
        early, replay, bind, Except.bind, pure, Except.pure]⟩
  | slot ok =>
    obtain ⟨advanced, advanceOk, upgrades⟩ := bind_ok_iff.mp ok
    obtain ⟨crossings, crossingOk, _⟩ := upgradeBalanceReplay_bounded upgrades
    have advanceCopy := advanceOk
    simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at advanceCopy
    obtain ⟨next, nextOk, cached, cachedOk, epoched, epochOk, _⟩ := advanceCopy
    by_cases last : next % preset.SLOTS_PER_EPOCH = 0
    · simp only [epochIfLast, last, ↓reduceIte] at epochOk
      have recorded : ∃ middle events,
          epochBalanceReplay (config := config) (checks := checks) cached =
            .ok (middle, events) := by
        by_cases gloas : .glamsterdam ≤ x.fork
        · obtain ⟨middle, _, _, events, replay, _⟩ :=
            epochBalanceReplay_result_gloas cached epoched gloas epochOk
          exact ⟨middle, events, replay⟩
        · obtain ⟨middle, _, events, replay, _⟩ :=
            epochBalanceReplay_result cached epoched (Nat.lt_of_not_le gloas) epochOk
          exact ⟨middle, events, replay⟩
      obtain ⟨middle, events, replay⟩ := recorded
      exact ⟨events ++ crossings, by
        simp [Step.balanceEventsGloas, Step.balanceEvents, cachedOk, nextOk, last, replay,
          advanceOk, crossingOk, pure, Except.pure, bind, Except.bind]⟩
    · exact ⟨crossings, by
        simp [Step.balanceEventsGloas, Step.balanceEvents, cachedOk, nextOk, last,
          advanceOk, crossingOk, pure, Except.pure, bind, Except.bind]⟩

/-- Use the existing interval selection rule with Gloas-capable step replay. -/
def _root_.EthLib.Consensus.Run.balanceEventsGloas {x : ForkedBeaconState preset} (high : Nat) :
    {y : ForkedBeaconState preset} → Run config checks x y →
      Except TransitionError (List (BalanceEvent preset))
  | _, .nil => pure []
  | _, .snoc (middle := m) pre step => do
    let prior ← pre.balanceEventsGloas high
    if (getCurrentEpoch m.state).toNat ≤ high + 1 then
      return prior ++ (← step.balanceEventsGloas)
    else return prior

theorem _root_.EthLib.Consensus.Run.balanceEventsGloas_eq {x y : ForkedBeaconState preset}
    (run : Run config checks x y) (early : y.fork < .glamsterdam) (high : Nat) :
    run.balanceEventsGloas high = run.balanceEvents high := by
  induction run with
  | nil => rfl
  | snoc pre step ih =>
    have before := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    simp only [Run.balanceEventsGloas, Run.balanceEvents, ih before,
      step.balanceEventsGloas_eq before]

theorem _root_.EthLib.Consensus.Run.balanceEventsGloas_result {x y : ForkedBeaconState preset}
    (run : Run config checks x y) (before : y.fork < .hegota) (high : Nat) :
    ∃ events, run.balanceEventsGloas high = .ok events := by
  induction run with
  | nil => exact ⟨[], rfl⟩
  | snoc pre step ih =>
    obtain ⟨prior, priorOk⟩ := ih (Nat.lt_of_le_of_lt step.chainStep.fork_le before)
    obtain ⟨added, addedOk⟩ := step.balanceEventsGloas_result before
    simp only [Run.balanceEventsGloas, priorOk, bind, Except.bind]
    split
    · exact ⟨prior ++ added, by simp [addedOk, pure, Except.pure]⟩
    · exact ⟨prior, rfl⟩

/-- Builder withdrawals cannot increase the validator debit beyond the full withdrawal sum. -/
theorem gloas_withdrawal_bounds {fork : Fork} (gloas : .glamsterdam ≤ fork)
    (s t : BeaconState preset fork)
    (ok : processWithdrawals s (Nat.le_trans (by decide) gloas)
      (fun before => absurd gloas (Nat.not_le_of_lt before)) = .ok t) :
    ∃ debit, gloasWithdrawalLimits gloas s = .ok (0, debit) ∧
      balanceCredits s t = 0 ∧ balanceDebits s t ≤ debit := by
  simp only [processWithdrawals, gloas, ↓reduceDIte] at ok
  split at ok <;> rename_i full
  · obtain ⟨expected, expectedOk, applied⟩ := bind_ok_iff.mp ok
    obtain ⟨u, withdrawn, balances, _⟩ :=
      applyExpectedWithdrawals_balances (liftAccessor_ok.mp applied)
    have bounds := withdrawal_debit_bound s u expected.withdrawals withdrawn
    refine ⟨(expected.withdrawals.toList.map fun w => w.amount.toNat).sum, ?_, ?_, ?_⟩
    · simp [gloasWithdrawalLimits, full, expectedOk, bind, Except.bind, pure, Except.pure]
    · simpa only [balanceCredits, actualBalanceAt, balances] using bounds.1
    · simpa only [balanceDebits, actualBalanceAt, balances] using bounds.2
  · cases ok
    exact ⟨0, by simp [gloasWithdrawalLimits, full, pure, Except.pure],
      by simp [balanceCredits], by simp [balanceDebits]⟩

/-- EIP-7732: weighing builder payments leaves the validator proposer credit unchanged. -/
theorem attestation_proposer_bound_gloas {fork : Fork} (s t : BeaconState preset fork)
    (att : Attestation preset fork) (parent : Slot) (gloas : .glamsterdam ≤ fork)
    (ok : processAttestation config checks s parent att = .ok t) :
    ∃ credit, attestationCredit s att parent = .ok credit ∧
      balanceDebits s t = 0 ∧ balanceCredits s t ≤ credit := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) gloas
  simp only [processAttestation, altair, ↓reduceDIte, processAttestationAltair,
    bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, earned, earnedOk, _, _, _, _, _, _, total,
    totalOk, attesters, attestersOk, pair, flagsOk, proposer, _, u, raised, final⟩ := ok
  simp only [gloas, ↓reduceDIte] at final
  -- The Gloas suffix updates builder payments, not validator balances.
  have paidBalances : t.balances = u.balances := by rw [recordPaymentWeight_eq final]
  refine ⟨(pair.2 /
    ((WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR / PROPOSER_WEIGHT)).toNat,
    ?_, ?_⟩
  · simp only [attestationCredit, altair, ↓reduceDIte, liftAccessor, earnedOk, totalOk,
      attestersOk, Except.mapError, bind, Except.bind, flagsOk]
    rfl
  · have bounds := credits_increase raised
    have kept : (setEpochParticipation s
        (att.data.target.epoch == getCurrentEpoch s) pair.1).balances = s.balances := by
      unfold setEpochParticipation
      split <;> rfl
    simpa only [balanceCredits, balanceDebits, actualBalanceAt, paidBalances, kept]
      using And.intro bounds.2 bounds.1.le

/-- EIP-7732, State transition: Gloas operations preserve the recorded balance bounds. -/
theorem gloas_operations_bounded {fork : Fork} (gloas : .glamsterdam ≤ fork)
    (before : fork < .hegota) (body : BeaconBlockBody preset fork) (parent : Slot)
    (pre post : BalanceReplay preset fork) (matched : BalancesMatch pre.1)
    (bounded : ∀ event ∈ pre.2,
      event.credits ≤ event.creditLimit ∧ event.debits ≤ event.debitLimit)
    (ok : gloasOperationsReplay (config := config) (checks := checks)
      gloas before body parent pre = .ok post) :
    BalancesMatch post.1 ∧ ∀ event ∈ post.2,
      event.credits ≤ event.creditLimit ∧ event.debits ≤ event.debitLimit := by
  have proposer {pre post : BalanceReplay preset fork} (sl : ProposerSlashing)
      (initial : ReplayBounded pre)
      (ok : recordBalance .slashings (slashingLimits [sl.signedHeader1.message.proposerIndex])
        (processProposerSlashing config checks · sl) pre = .ok post) : ReplayBounded post := by
    apply recordBalance_matched _ _ _
      (fun _ _ ok => (frame_processProposerSlashing ok).balancesMatch) _ initial ok
    intro s t credit debit _ limits action
    obtain ⟨credit', debit', limits', bounds⟩ := proposer_slashing_bounds sl action
    cases Except.ok.inj (limits.symm.trans limits')
    exact bounds
  have attester {pre post : BalanceReplay preset fork} (sl : AttesterSlashing preset fork)
      (initial : ReplayBounded pre)
      (ok : recordBalance .slashings (slashingLimits (slashingIndices sl))
        (processAttesterSlashing config checks · sl) pre = .ok post) : ReplayBounded post := by
    apply recordBalance_matched _ _ _
      (fun _ _ ok => (frame_processAttesterSlashing ok).balancesMatch) _ initial ok
    intro s t credit debit _ limits action
    obtain ⟨credit', debit', limits', bounds⟩ := attester_slashing_bounds sl action
    cases Except.ok.inj (limits.symm.trans limits')
    exact bounds
  have attestation {pre post : BalanceReplay preset fork} (att : Attestation preset fork)
      (initial : ReplayBounded pre)
      (ok : recordBalance .rewards (fun site => do
          return (← attestationCredit site att parent, 0))
        (processAttestation config checks · parent att) pre = .ok post) : ReplayBounded post := by
    apply recordBalance_matched _ _ _
      (fun _ _ ok => (frame_processAttestation ok).balancesMatch) _ initial ok
    intro site t credit debit _ limits action
    obtain ⟨credit', limits', debits, credits⟩ :=
      attestation_proposer_bound_gloas site t att parent gloas action
    simp only [limits', bind, Except.bind, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at limits
    rcases limits with ⟨rfl, rfl⟩
    exact ⟨credits, debits.le⟩
  simp only [gloasOperationsReplay, bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _,
    proposed, proposedOk, slashed, slashedOk, attested, attestedOk,
    exited, exitedOk, changed, changedOk, paid⟩ := ok
  -- Each recorded operation preserves both the state invariant and all event bounds.
  have proposedBound := foldlM_ok_invariant ReplayBounded
    (fun _ sl _ h ok => proposer sl h ok) ⟨matched, bounded⟩ proposedOk
  have slashedBound := foldlM_ok_invariant ReplayBounded
    (fun _ sl _ h ok => attester sl h ok) proposedBound slashedOk
  have attestedBound := foldlM_ok_invariant ReplayBounded
    (fun _ att _ h ok => attestation att h ok) slashedBound attestedOk
  -- Carry passes leave events unchanged, so only balance/registry matching remains.
  have exitedBound := carryBalance_bounded _ (fun _ _ ok h =>
    foldlM_ok_invariant BalancesMatch
      (fun _ _ _ h ok => (frame_processVoluntaryExit ok).balancesMatch h) h
      (by simpa only [← Array.foldlM_toList] using ok)) attestedBound exitedOk
  have changedBound := carryBalance_bounded _ (fun _ _ ok h =>
    foldlM_ok_invariant BalancesMatch
      (fun _ _ _ h ok => (frame_processBlsToExecutionChange ok).balancesMatch h) h
      (by simpa only [← Array.foldlM_toList] using ok)) exitedBound changedOk
  exact carryBalance_bounded _ (fun _ _ ok h =>
    foldlM_ok_invariant BalancesMatch
      (fun _ _ _ h ok => processPayloadAttestation_eq ok ▸ h) h
      (by simpa only [← Array.foldlM_toList] using ok)) changedBound paid

end EthLib.Consensus.DirectSafety
