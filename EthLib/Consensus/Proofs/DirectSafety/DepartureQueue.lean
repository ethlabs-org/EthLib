module

public import EthLib.Consensus.Proofs.DirectSafety.ChurnBounds
public import EthLib.Consensus.Proofs.Transition.Requests

-- Reuse the operation-level activity and effective-balance preservation proofs.
import all EthLib.Consensus.Proofs.Transition.ActiveKept
import all EthLib.Consensus.Proofs.Transition.BalanceDrift

/-!
# Departure queue accounting

A queue call records its assigned epoch as well as the balance that it spends.

Partial withdrawals spend exit capacity without assigning a validator's exit.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base

/-- One successful balance-queue call, including the queue before and after it. -/
structure DepartureQueueCall where
  earliest : Epoch
  available : Gwei
  first : Epoch
  rate : Gwei
  amount : Gwei
  epoch : Epoch
  left : Gwei
  computed : churnQueue earliest first rate available amount = .ok (epoch, left)

/-- The capacity still usable through a fixed last epoch. -/
def departureQueuePotential (high cap : Nat) (epoch : Epoch) (left : Gwei) : Nat :=
  if epoch.toNat ≤ high then left.toNat + (high - epoch.toNat) * cap else 0

/-- A call cannot move the open queue epoch backwards. -/
theorem DepartureQueueCall.epoch_mono (call : DepartureQueueCall) :
    call.earliest.toNat ≤ call.epoch.toNat := by
  have placed := UInt64.le_iff_toNat_le.mp (churnQueue_spend call.computed).1
  rw [Base.Uint64.toNat_max] at placed
  omega

/-- Spending beyond the horizon counts nothing and leaves no usable capacity inside it. -/
theorem DepartureQueueCall.window_spend (call : DepartureQueueCall) (high cap : Nat)
    (rateBound : call.rate.toNat ≤ cap) :
    (if call.epoch.toNat ≤ high then call.amount.toNat else 0) +
      departureQueuePotential high cap call.epoch call.left ≤
        departureQueuePotential high cap call.earliest call.available := by
  have ordered := call.epoch_mono
  by_cases inside : call.epoch.toNat ≤ high
  · have before : call.earliest.toNat ≤ high := by omega
    obtain ⟨_, spent⟩ := churnQueue_window_le cap [(call.first, call.rate, call.amount)]
      call.earliest call.available call.epoch call.left
      (by intro c member; simpa using List.mem_singleton.mp member ▸ rateBound)
      (by simpa using call.computed)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at spent
    simp only [departureQueuePotential, inside, before, ↓reduceIte]
    have distance : high - call.earliest.toNat =
        (call.epoch.toNat - call.earliest.toNat) + (high - call.epoch.toNat) := by omega
    rw [distance, Nat.add_mul]
    omega
  · simp only [departureQueuePotential, inside, ↓reduceIte, Nat.zero_add]
    exact Nat.zero_le _

/-- A concrete sequence uses each call's output queue as the next call's input queue. -/
inductive DepartureQueueTrace : Epoch → Gwei → List DepartureQueueCall → Epoch → Gwei → Prop
  | nil (epoch : Epoch) (left : Gwei) : DepartureQueueTrace epoch left [] epoch left
  | cons (call : DepartureQueueCall) {rest : List DepartureQueueCall} {epoch : Epoch}
      {left : Gwei} (tail : DepartureQueueTrace call.epoch call.left rest epoch left) :
      DepartureQueueTrace call.earliest call.available (call :: rest) epoch left

/-- Filtering calls by completion epoch preserves the queue budget through that epoch. -/
theorem DepartureQueueTrace.window_le {earliest epoch : Epoch} {available left : Gwei}
    {calls : List DepartureQueueCall}
    (trace : DepartureQueueTrace earliest available calls epoch left) (high cap : Nat)
    (rates : ∀ call ∈ calls, call.rate.toNat ≤ cap) :
    ((calls.filter fun call => call.epoch.toNat ≤ high).map fun call => call.amount.toNat).sum +
      departureQueuePotential high cap epoch left ≤
        departureQueuePotential high cap earliest available := by
  induction trace with
  | nil => simp
  | cons call tail ih =>
    have step := call.window_spend high cap (rates call (by simp))
    have rest := ih (fun c member => rates c (List.mem_cons_of_mem _ member))
    by_cases inside : call.epoch.toNat ≤ high
    · simp only [List.filter_cons, decide_eq_true inside, ↓reduceIte,
        List.map_cons, List.sum_cons]
      rw [ite_eq_left inside] at step
      omega
    · simp only [List.filter_cons, decide_eq_false inside, Bool.false_eq_true, ↓reduceIte]
      rw [ite_eq_right inside] at step
      omega

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- An exit scheduling operation supplies a call with exactly its input and output queues. -/
theorem exitQueueCall_of_computed {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {amount : Gwei} {epoch : Epoch}
    (ok : computeExitEpochAndUpdateChurn config s electra amount = .ok (t, epoch)) :
    ∃ call : DepartureQueueCall,
      call.earliest = s.earliestExitEpoch electra ∧
      call.available = s.exitBalanceToConsume electra ∧
      call.amount = amount ∧ call.epoch = epoch ∧
      call.left = t.exitBalanceToConsume electra ∧
      exitChurnLimit config s = .ok call.rate := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, liftArith,
    mapError_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ok
  obtain ⟨first, _, rate, rateOk, ⟨placed, left⟩, queued, rfl, rfl⟩ := ok
  exact ⟨⟨_, _, first, rate, amount, placed, left, queued⟩,
    rfl, rfl, rfl, rfl, rfl, rateOk⟩

/-- A consolidation scheduling operation supplies its exact balance-queue call. -/
theorem consolidationQueueCall_of_computed {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {amount : Gwei} {epoch : Epoch}
    (ok : computeConsolidationEpochAndUpdateChurn config s electra amount = .ok (t, epoch)) :
    ∃ call : DepartureQueueCall,
      call.earliest = s.earliestConsolidationEpoch electra ∧
      call.available = s.consolidationBalanceToConsume electra ∧
      call.amount = amount ∧ call.epoch = epoch ∧
      call.left = t.consolidationBalanceToConsume electra ∧
      getConsolidationChurnLimit config s = .ok call.rate := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, liftArith,
    mapError_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ok
  obtain ⟨first, _, rate, rateOk, ⟨placed, left⟩, queued, rfl, rfl⟩ := ok
  exact ⟨⟨_, _, first, rate, amount, placed, left, queued⟩,
    rfl, rfl, rfl, rfl, rfl, rateOk⟩

/-- Successful consolidation requests record the input to their balance-queue call.

Credential switches and ignored requests do not call that queue. -/
def consolidationRequestCalls {fork : Fork} (config : Config)
    (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (request : ConsolidationRequest) : Except TransitionError Bool := do
  if request.sourcePubkey == request.targetPubkey then return false
  if (state.pendingConsolidations electra).data.size ==
      preset.PENDING_CONSOLIDATIONS_LIMIT.toNat then return false
  if (← liftAccessor (getConsolidationChurnLimit config state)) ≤ preset.MIN_ACTIVATION_BALANCE
    then return false
  let some sourcePosition := findValidatorByPubkey state request.sourcePubkey | return false
  let some targetPosition := findValidatorByPubkey state request.targetPubkey | return false
  let sourceIndex ← liftAccessor (liftArith (Uint64.ofNatChecked sourcePosition.val))
  let targetIndex ← liftAccessor (liftArith (Uint64.ofNatChecked targetPosition.val))
  let source := state.validators.data[sourcePosition]
  let target := state.validators.data[targetPosition]
  unless hasExecutionWithdrawalCredential source &&
      credentialAddress source.withdrawalCredentials == request.sourceAddress do return false
  unless hasCompoundingWithdrawalCredential target do return false
  let epoch := getCurrentEpoch state
  unless isActiveValidator source epoch && isActiveValidator target epoch do return false
  unless source.exitEpoch == FAR_FUTURE_EPOCH && target.exitEpoch == FAR_FUTURE_EPOCH do
    return false
  let eligible ←
    liftAccessor (liftArith
      (Uint64.addChecked source.activationEpoch config.SHARD_COMMITTEE_PERIOD))
  if epoch < eligible then return false
  if 0 < (← liftAccessor (getPendingBalanceToWithdraw state electra sourceIndex)) then
    return false
  let _ ← queueConsolidation config state electra sourceIndex source targetIndex
  return true

def consolidationRequestSites {fork : Fork} (config : Config)
    (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (request : ConsolidationRequest) :
    Except TransitionError (List (ForkedBeaconState preset)) := do
  return if ← consolidationRequestCalls config state electra request then [⟨fork, state⟩] else []

/-- A successful request always has a successful classification of its churn call. -/
private theorem consolidationRequestCalls_result {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t) :
    ∃ called, consolidationRequestCalls config s electra request = .ok called := by
  unfold processConsolidationRequest at ok
  unfold consolidationRequestCalls
  split at ok
  · rename_i same
    simp only [same, ↓reduceIte, pure, Except.pure]
    exact ⟨false, rfl⟩
  · rename_i different
    simp only [different]
    repeat' first
      | (split at ok)
      | (simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok)
      | (obtain ⟨value, computed, ok⟩ := ok)
    all_goals simp_all only [bind, Except.bind, pure, Except.pure, ↓reduceIte]
    all_goals first | exact ⟨false, rfl⟩ | exact ⟨true, rfl⟩

/-- Replay requests in order, retaining each actual consolidation queue input. -/
def consolidationRequestsSites {fork : Fork} (config : Config) (electra : .pectra ≤ fork)
    (state : BeaconState preset fork) : List ConsolidationRequest →
      Except TransitionError (BeaconState preset fork × List (ForkedBeaconState preset))
  | [] => pure (state, [])
  | request :: rest => do
    let sites ← consolidationRequestSites config state electra request
    let next ← processConsolidationRequest config state electra request
    let (last, later) ← consolidationRequestsSites config electra next rest
    return (last, sites ++ later)

private theorem consolidationRequestsSites_result {fork : Fork}
    {electra : .pectra ≤ fork} {s t : BeaconState preset fork}
    {requests : List ConsolidationRequest}
    (ok : requests.foldlM (processConsolidationRequest config · electra ·) s = .ok t) :
    ∃ sites, consolidationRequestsSites config electra s requests = .ok (t, sites) := by
  induction requests generalizing s with
  | nil => cases ok; exact ⟨[], rfl⟩
  | cons request rest ih =>
    obtain ⟨next, stepped, remaining⟩ := bind_ok_iff.mp ok
    obtain ⟨called, classified⟩ := consolidationRequestCalls_result stepped
    obtain ⟨sites, replayed⟩ := ih remaining
    refine ⟨(if called then [⟨fork, s⟩] else []) ++ sites, ?_⟩
    simp only [consolidationRequestsSites, consolidationRequestSites, classified, stepped,
      replayed, bind, Except.bind, pure, Except.pure]

/-- The block prefix reaches execution requests before any consolidation queue call. -/
def blockConsolidationSites {fork : Fork} (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) :
    Except TransitionError (List (ForkedBeaconState preset)) := do
  if electra : .pectra ≤ fork ∧ fork < .glamsterdam then
    have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) electra.1
    have before : fork < .hegota := Nat.lt_trans electra.2 (by decide)
    let parentSlot := state.latestBlockHeader.slot
    let state ← processBlockHeader state block
    let state ← processBlockExecution config checks engine state block.body bellatrix
    let state ← processRandao config checks state block.body
    let state ← processEth1Data before state block.body
    let expected ← expectedDepositCount state before
    let deposits := (block.body.deposits before).data
    ensure (deposits.size = expected) (.wrongDepositCount deposits.size expected)
    let state ← block.body.proposerSlashings.data.foldlM
      (processProposerSlashing config checks) state
    let state ← block.body.attesterSlashings.data.foldlM
      (processAttesterSlashing config checks) state
    let state ← block.body.attestations.data.foldlM
      (processAttestation config checks · parentSlot ·) state
    let state ← deposits.foldlM (processDeposit config checks before) state
    let state ← block.body.voluntaryExits.data.foldlM (processVoluntaryExit config checks) state
    let state ← processBlsToExecutionChanges config checks state block.body
    let requests := block.body.executionRequests electra
    let state ← requests.deposits.data.foldlM (processDepositRequest · electra.1 ·) state
    let state ← requests.withdrawals.data.foldlM
      (processWithdrawalRequest config · electra.1 ·) state
    return (← consolidationRequestsSites config electra.1 state
      requests.consolidations.data.toList).2
  else return []

/-- Successful block processing cannot lose its consolidation sites through a replay error. -/
theorem blockConsolidationSites_result {fork : Fork}
    {engine : ExecutionEngine preset fork} {s t : BeaconState preset fork}
    {block : BeaconBlock preset fork}
    (ok : processBlock config checks engine s block = .ok t) :
    ∃ sites, blockConsolidationSites config checks engine s block = .ok sites := by
  by_cases electra : .pectra ≤ fork ∧ fork < .glamsterdam
  · have altair : .altair ≤ fork := Nat.le_trans (by decide) electra.1
    have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) electra.1
    have before : fork < .hegota := Nat.lt_trans electra.2 (by decide)
    have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt electra.2
    simp only [processBlock, processBlockAltair, altair, bellatrix, before, notGloas,
      ↓reduceDIte, pure_bind, bind_ok_iff] at ok
    obtain ⟨headed, headedOk, executed, executedOk, revealed, revealedOk, voted, votedOk,
      operated, operatedOk, _⟩ := ok
    simp only [processOperations, notGloas, electra.1, ↓reduceDIte,
      bind_ok_iff, ensure_ok_iff] at operatedOk
    obtain ⟨expected, expectedOk, _, count, proposed, proposedOk, attested, attestedOk,
      votedAtt, votedAttOk, deposited, depositedOk, exited, exitedOk, changed, changedOk,
      requestsOk⟩ := operatedOk
    simp only [processExecutionRequests, bind_ok_iff] at requestsOk
    obtain ⟨requested, requestedOk, withdrawn, withdrawnOk, consolidated⟩ := requestsOk
    obtain ⟨sites, replayed⟩ := consolidationRequestsSites_result
      (by simpa only [← Array.foldlM_toList] using consolidated)
    have ensured : ensure ((block.body.deposits before).data.size = expected)
        (TransitionError.wrongDepositCount (block.body.deposits before).data.size expected) =
          .ok () := ensure_ok_iff.mpr count
    refine ⟨sites, ?_⟩
    rw [blockConsolidationSites, dite_eq_left electra]
    simp only [headedOk, executedOk,
      revealedOk, votedOk, expectedOk, ensured, proposedOk, attestedOk,
      votedAttOk, depositedOk, exitedOk, changedOk, requestedOk, withdrawnOk,
      replayed, pure, Except.pure, bind, Except.bind]
  · exact ⟨[], by simp only [blockConsolidationSites, electra, ↓reduceDIte]; rfl⟩

def _root_.EthLib.Consensus.Step.consolidationSites {x y : ForkedBeaconState preset}
    (step : Step config checks x y) : List (ForkedBeaconState preset) :=
  match step with
  | .slot _ => []
  | .block engine signed _ _ =>
    ((blockConsolidationSites config checks engine x.state signed.message).toOption).getD []

def _root_.EthLib.Consensus.Run.consolidationSites {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → List (ForkedBeaconState preset)
  | _, .nil => []
  | _, .snoc pre step => pre.consolidationSites ++ step.consolidationSites

private structure SitePrefix {fork : Fork} (s t : BeaconState preset fork) : Prop where
  identity : RegistryIdentity s t
  active : ActiveStep s t
  effective : EffectiveKept s t

private theorem SitePrefix.refl {fork : Fork} (s : BeaconState preset fork) : SitePrefix s s :=
  ⟨.refl _, .refl _, effectiveKept_refl _⟩

private theorem SitePrefix.trans {fork : Fork} {s t u : BeaconState preset fork}
    (one : SitePrefix s t) (two : SitePrefix t u) : SitePrefix s u :=
  ⟨one.identity.trans two.identity, one.active.trans two.active,
    effectiveKept_trans one.effective two.effective
      (by simpa [validatorKeys] using one.identity.kept.length_le)⟩

private theorem SitePrefix.fold {fork : Fork} {α : Type}
    {action : BeaconState preset fork → α → Except TransitionError (BeaconState preset fork)}
    (kept : ∀ s a t, action s a = .ok t → SitePrefix s t)
    {s t : BeaconState preset fork} {items : List α}
    (ok : items.foldlM action s = .ok t) : SitePrefix s t :=
  foldlM_ok_invariant (SitePrefix s)
    (fun _ _ _ previous computed => previous.trans (kept _ _ _ computed)) (.refl s) ok

private theorem SitePrefix.weight {fork : Fork} {s t : BeaconState preset fork}
    (kept : SitePrefix s t) (unique : uniqueKeys s)
    (bound : t.validators.data.size < 2 ^ 64) :
    Quorum.weight (effectiveWeight t) (activeKeys t) =
      Quorum.weight (effectiveWeight s) (activeKeys s) := by
  classical
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by
    simp only [getCurrentEpoch, kept.active.1]
  have indices : getActiveValidatorIndices t (getCurrentEpoch t) =
      getActiveValidatorIndices s (getCurrentEpoch s) := by
    rw [epoch]
    exact kept.active.2.getActiveValidatorIndices_eq (getCurrentEpoch_le_activityFixedEpoch s)
  have grows : s.validators.data.size ≤ t.validators.data.size := by
    simpa [validatorKeys] using kept.identity.kept.length_le
  have inside (u : BeaconState preset fork) (_small : u.validators.data.size < 2 ^ 64)
      (i : ValidatorIndex) (member : i ∈ getActiveValidatorIndices u (getCurrentEpoch u)) :
      i.toNat < u.validators.data.size := by
    simp only [getActiveValidatorIndices, List.mem_filterMap, List.mem_zipIdx_iff_getElem?,
      Prod.exists] at member
    obtain ⟨v, index, found, chosen⟩ := member
    split at chosen
    · cases Option.some.inj chosen
      have inside := (List.getElem?_eq_some_iff.mp found).1
      simp only [Array.length_toList] at inside
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) inside
    · cases chosen
  rw [activeKeys, keys_weight t _ (kept.identity.unique unique) (inside t bound),
    activeKeys, keys_weight s _ unique (inside s (Nat.lt_of_le_of_lt grows bound)), indices]
  apply Finset.sum_congr rfl
  intro i member
  exact kept.effective i.toNat (inside s (Nat.lt_of_le_of_lt grows bound) i
    (List.mem_toFinset.mp member))

private theorem consolidationRequestSites_input {fork : Fork} {s : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : ConsolidationRequest}
    {sites : List (ForkedBeaconState preset)}
    (ok : consolidationRequestSites config s electra request = .ok sites)
    (site : ForkedBeaconState preset) (member : site ∈ sites) : site = ⟨fork, s⟩ := by
  simp only [consolidationRequestSites, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨called, _, rfl⟩ := ok
  cases called with
  | false => simp at member
  | true => simpa using member

private theorem consolidationRequestsSites_prefix {fork : Fork}
    {electra : .pectra ≤ fork} {s t : BeaconState preset fork}
    {sites : List (ForkedBeaconState preset)} {requests : List ConsolidationRequest}
    (ok : consolidationRequestsSites config electra s requests = .ok (t, sites))
    (site : ForkedBeaconState preset) (member : site ∈ sites) :
    ∃ u : BeaconState preset fork, site = ⟨fork, u⟩ ∧ SitePrefix s u := by
  induction requests generalizing s sites with
  | nil => cases ok; simp at member
  | cons request rest ih =>
    simp only [consolidationRequestsSites, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨here, recorded, next, stepped, ⟨last, later⟩, replayed, rfl, rfl⟩ := ok
    rcases List.mem_append.mp member with first | tail
    · exact ⟨s, consolidationRequestSites_input recorded site first, .refl s⟩
    · obtain ⟨u, same, kept⟩ := ih replayed tail
      exact ⟨u, same, (SitePrefix.mk (RegistryIdentity.processConsolidationRequest stepped)
        (stepKeeps_processConsolidationRequest stepped).2
        (effectiveKept_consolidationRequest stepped)).trans kept⟩

private theorem blockConsolidationSites_prefix {fork : Fork}
    {engine : ExecutionEngine preset fork} {s : BeaconState preset fork}
    {block : BeaconBlock preset fork} {sites : List (ForkedBeaconState preset)}
    (ok : blockConsolidationSites config checks engine s block = .ok sites)
    (site : ForkedBeaconState preset) (member : site ∈ sites) :
    ∃ u : BeaconState preset fork, site = ⟨fork, u⟩ ∧ SitePrefix s u := by
  unfold blockConsolidationSites at ok
  split at ok
  · rename_i electra
    simp only [bind_ok_iff, ensure_ok_iff, pure, Except.pure, Except.ok.injEq,
      ← Array.foldlM_toList] at ok
    obtain ⟨headed, headedOk, executed, executedOk, revealed, revealedOk, voted, votedOk,
      expected, expectedOk, _, count, proposed, proposedOk, attested, attestedOk,
      votedAtt, votedAttOk, deposited, depositedOk, exited, exitedOk, changed, changedOk,
      requested, requestedOk, withdrawn, withdrawnOk, ⟨last, recorded⟩, replayed, rfl⟩ := ok
    have head : SitePrefix s headed := by
      refine ⟨RegistryIdentity.processBlockHeader headedOk,
        (stepKeeps_processBlockHeader headedOk).2, ?_⟩
      obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
      exact effectiveKept_refl _
    have execution : SitePrefix headed executed := by
      refine ⟨RegistryIdentity.processBlockExecution executedOk,
        (stepKeeps_processBlockExecution executedOk).2, ?_⟩
      have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt electra.2
      have capella : .shapella ≤ fork := Nat.le_trans (by decide) electra.1
      simp only [processBlockExecution, notGloas, capella, ↓reduceDIte,
        bind_ok_iff] at executedOk
      obtain ⟨middle, withdrawn, payload⟩ := executedOk
      obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok payload
      simpa only [EffectiveKept, effectiveAt] using effectiveKept_withdrawals withdrawn
    have randao : SitePrefix executed revealed := by
      refine ⟨RegistryIdentity.processRandao revealedOk,
        (stepKeeps_processRandao revealedOk).2, ?_⟩
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealedOk
      exact effectiveKept_refl _
    have vote : SitePrefix revealed voted := by
      refine ⟨RegistryIdentity.processEth1Data votedOk,
        (stepKeeps_processEth1Data votedOk).2, ?_⟩
      obtain ⟨_, _, rest⟩ := processEth1Data_eq votedOk
      exact effectiveKept_data (congrArg (·.validators.data) rest)
    have proposers : SitePrefix voted proposed := SitePrefix.fold
      (fun _ _ _ h => ⟨RegistryIdentity.processProposerSlashing h,
        (stepKeeps_processProposerSlashing h).2, effectiveKept_proposerSlashing h⟩) proposedOk
    have attesters : SitePrefix proposed attested := SitePrefix.fold
      (fun _ _ _ h => ⟨RegistryIdentity.processAttesterSlashing h,
        (stepKeeps_processAttesterSlashing h).2, effectiveKept_attesterSlashing h⟩) attestedOk
    have attestations : SitePrefix attested votedAtt := SitePrefix.fold
      (fun _ _ _ h => ⟨RegistryIdentity.processAttestation h,
        (stepKeeps_processAttestation h).2,
        effectiveKept_data (by rw [(processAttestation_registry h).1])⟩) votedAttOk
    have deposits : SitePrefix votedAtt deposited := SitePrefix.fold
      (fun _ _ _ h => ⟨RegistryIdentity.processDeposit h,
        (stepKeeps_processDeposit h).2, effectiveKept_processDeposit h⟩) depositedOk
    have exits : SitePrefix deposited exited := SitePrefix.fold
      (fun _ _ _ h => ⟨RegistryIdentity.processVoluntaryExit h,
        (stepKeeps_processVoluntaryExit h).2, effectiveKept_voluntaryExit h⟩) exitedOk
    have changes : SitePrefix exited changed := by
      unfold processBlsToExecutionChanges at changedOk
      split at changedOk
      · rw [← Array.foldlM_toList] at changedOk
        exact SitePrefix.fold (fun _ _ _ h => ⟨RegistryIdentity.processBlsToExecutionChange h,
          (stepKeeps_processBlsToExecutionChange h).2, effectiveKept_blsChange h⟩) changedOk
      · cases changedOk; exact .refl _
    have requests : SitePrefix changed requested := SitePrefix.fold
      (fun _ _ _ h => ⟨RegistryIdentity.processDepositRequest h,
        (stepKeeps_processDepositRequest h).2, effectiveKept_depositRequest h⟩) requestedOk
    have withdrawals : SitePrefix requested withdrawn := SitePrefix.fold
      (fun _ _ _ h => ⟨RegistryIdentity.processWithdrawalRequest h,
        (stepKeeps_processWithdrawalRequest h).2, effectiveKept_withdrawalRequest h⟩) withdrawnOk
    obtain ⟨u, same, kept⟩ := consolidationRequestsSites_prefix replayed site member
    exact ⟨u, same, head.trans (execution.trans (randao.trans (vote.trans (proposers.trans
      (attesters.trans (attestations.trans (deposits.trans (exits.trans (changes.trans
        (requests.trans (withdrawals.trans kept)))))))))))⟩
  · cases ok; simp at member

theorem consolidationSites_provenance {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (early : y.fork < .glamsterdam)
    (site : ForkedBeaconState preset) (member : site ∈ tail.consolidationSites) :
    ∃ a b, ∃ pre : Run config checks x a, ∃ step : Step config checks a b,
      ∃ post : Run config checks b y,
        (pre.snoc step).append post = tail ∧
        site.fork = a.fork ∧
        getCurrentEpoch site.state = getCurrentEpoch a.state ∧
        Quorum.weight (effectiveWeight site.state) (activeKeys site.state) ≤
          Quorum.weight (effectiveWeight a.state) (activeKeys a.state) := by
  have _ := parameters
  have _ := caps
  induction tail with
  | nil => simp [Run.consolidationSites] at member
  | @snoc middle last pre step ih =>
    rcases List.mem_append.mp member with previous | current
    · obtain ⟨a, b, before, selected, after, same, fork, epoch, weight⟩ :=
        ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early) previous
      exact ⟨a, b, before, selected, after.snoc step,
        congrArg (fun run => run.snoc step) same, fork, epoch, weight⟩
    · refine ⟨middle, last, pre, step, .nil, rfl, ?_⟩
      cases step with
      | slot ok => simp [Step.consolidationSites] at current
      | @block fork before after engine signed due applied =>
        unfold Step.consolidationSites at current
        cases replay : blockConsolidationSites config checks engine before signed.message with
        | error err => simp [replay, Except.toOption] at current
        | ok sites =>
          simp only [replay, Except.toOption, Option.getD_some] at current
          obtain ⟨u, rfl, kept⟩ := blockConsolidationSites_prefix replay site current
          refine ⟨rfl, ?_, Nat.le_of_eq (kept.weight
            ((shared.append pre).unique (genesis_unique genesis)) ?_)⟩
          · simp only [getCurrentEpoch, kept.active.1]
          · exact Nat.lt_of_le_of_lt (u.validators.bound early) (UInt64.toNat_lt _)

end EthLib.Consensus.DirectSafety
