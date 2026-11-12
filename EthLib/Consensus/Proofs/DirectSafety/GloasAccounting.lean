module

public import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
import all EthLib.Consensus.Proofs.DirectSafety.IntervalFunding

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

end EthLib.Consensus.DirectSafety
