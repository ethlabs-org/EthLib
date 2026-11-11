module

public import EthLib.Consensus.Proofs.Transition.BalanceSources
public import EthLib.Consensus.Proofs.DirectSafety.ChurnBounds

/-!
# Source bounds over a selected execution interval

The replay below executes the concrete transition passes and records their inputs and results.

It records positive changes per validator, so transfers cannot cancel losses or gains elsewhere.

No caller supplies the amount of a source or an accounting cap.

The source bounds retain the initial queues, scores and balances needed by arbitrary intervals.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Classical

noncomputable section

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

inductive BalanceSource where
  | rewards | penalties | inactivity | slashings | deposits | consolidations
  | withdrawals | sync | excess | crossing
  deriving DecidableEq

structure BalanceEvent (preset : Preset) where
  source : BalanceSource
  before : ForkedBeaconState preset
  after : ForkedBeaconState preset
  creditLimit : Nat
  debitLimit : Nat

def BalanceEvent.credits (event : BalanceEvent preset) : Nat :=
  ∑ i ∈ Finset.range event.after.state.balances.data.size,
    (actualBalanceAt event.after i - actualBalanceAt event.before i)

def BalanceEvent.debits (event : BalanceEvent preset) : Nat :=
  ∑ i ∈ Finset.range event.before.state.balances.data.size,
    (actualBalanceAt event.before i - actualBalanceAt event.after i)

abbrev BalanceReplay (preset : Preset) (fork : Fork) :=
  BeaconState preset fork × List (BalanceEvent preset)

/-- Replay a pass and charge its protocol-computed limits, not its observed balance difference. -/
def recordBalance {fork : Fork} (source : BalanceSource)
    (limits : BeaconState preset fork → Except TransitionError (Nat × Nat))
    (action : BeaconState preset fork → Except TransitionError (BeaconState preset fork))
    (pre : BalanceReplay preset fork) : Except TransitionError (BalanceReplay preset fork) := do
  let (credit, debit) ← limits pre.1
  let post ← action pre.1
  return (post, pre.2 ++ [⟨source, ⟨fork, pre.1⟩, ⟨fork, post⟩, credit, debit⟩])

def carryBalance {fork : Fork}
    (action : BeaconState preset fork → Except TransitionError (BeaconState preset fork))
    (pre : BalanceReplay preset fork) : Except TransitionError (BalanceReplay preset fork) := do
  return (← action pre.1, pre.2)

/-- Separate the reward and penalty updates even when the concrete pass interleaves them. -/
def replayDeltas {fork : Fork} (penaltySource : BalanceSource)
    (deltas : Array Gwei × Array Gwei) (pre : BalanceReplay preset fork) :
    Except TransitionError (BalanceReplay preset fork) :=
  (List.range pre.1.validators.data.size).foldlM (fun pre i => do
    let index ← liftAccessor (liftArith (Uint64.ofNatChecked i))
    let reward := deltas.1.getD i 0
    let penalty := deltas.2.getD i 0
    let pre ← recordBalance .rewards (fun _ => pure (reward.toNat, 0))
      (fun s => liftAccessor (increaseBalance s index reward)) pre
    recordBalance penaltySource (fun _ => pure (0, penalty.toNat))
      (fun s => liftAccessor (decreaseBalance s index penalty)) pre) pre

def replayRewards {fork : Fork} (pre : BalanceReplay preset fork) :
    Except TransitionError (BalanceReplay preset fork) := do
  if getCurrentEpoch pre.1 = GENESIS_EPOCH then return pre
  let ordinary ← rewardPasses pre.1
  let inactivity ← getInactivityPenaltyDeltas config pre.1
  if .altair ≤ fork then
    let pre ← ordinary.foldlM (fun pre deltas => replayDeltas .penalties deltas pre) pre
    replayDeltas .inactivity inactivity pre
  else
    -- Phase 0 combines arrays first; splitting their saturating debits has the same endpoint.
    let rewards ← (List.range pre.1.validators.data.size).mapM fun i =>
      liftAccessor (liftArith (Uint64.ofNatChecked
        ((ordinary.map fun p => (p.1.getD i 0).toNat).sum)))
    let pre ← replayDeltas .penalties (rewards.toArray, #[]) pre
    let pre ← ordinary.foldlM (fun pre p => replayDeltas .penalties (#[], p.2) pre) pre
    replayDeltas .inactivity (#[], inactivity.2) pre

/-- The replay ends after the last balance-changing epoch pass, before effective-balance updates. -/
def epochBalanceReplay {fork : Fork} (s : BeaconState preset fork) :
    Except TransitionError (BalanceReplay preset fork) := do
  let pre ← carryBalance processJustificationAndFinalization (s, [])
  let pre ← if altair : .altair ≤ fork then
      carryBalance (processInactivityUpdates config · altair) pre else pure pre
  let pre ← replayRewards (config := config) pre
  let pre ← carryBalance (processRegistryUpdates config) pre
  let pre ← recordBalance .slashings
    (fun s => return (0, ← delayedSlashingLimit s))
    processSlashings pre
  let pre ← if before : fork < .hegota then
      carryBalance (processEth1DataReset before) pre else pure pre
  if electra : .pectra ≤ fork then
    let deposited ← processPendingDeposits config checks pre.1 electra
    let events := pre.2 ++ [⟨.deposits, ⟨fork, pre.1⟩, ⟨fork, deposited⟩,
      consumedDeposits pre.1 deposited electra, 0⟩]
    let consolidated ← processPendingConsolidations deposited electra
    let moved := consumedConsolidations deposited consolidated electra
    return (consolidated, events ++
      [⟨.consolidations, ⟨fork, deposited⟩, ⟨fork, consolidated⟩, moved, moved⟩])
  else pure pre

def slashingLimits {fork : Fork} (indices : List ValidatorIndex) (s : BeaconState preset fork) :
    Except TransitionError (Nat × Nat) := do
  let validators ← liftAccessor (indices.mapM (getValidator s))
  let p := EthLib.Consensus.parameters preset fork
  return ((validators.map fun v => v.effectiveBalance.toNat /
      p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat).sum,
    (validators.map fun v => v.effectiveBalance.toNat / p.MIN_SLASHING_PENALTY_QUOTIENT.toNat).sum)

/-- Pre-Gloas block replay, with limits read at the actual site of each operation. -/
def blockBalanceReplay {fork : Fork} (early : fork < .glamsterdam)
    (engine : ExecutionEngine preset fork) (s : BeaconState preset fork)
    (block : BeaconBlock preset fork) : Except TransitionError (BalanceReplay preset fork) := do
  let before := Nat.lt_trans early (by decide : Fork.glamsterdam < .hegota)
  let pre ← carryBalance (processBlockHeader · block) (s, [])
  let pre ← if bellatrix : .bellatrix ≤ fork then
      recordBalance .withdrawals (fun s => do
        if capella : .shapella ≤ fork then
          return (0, ((← getExpectedWithdrawals s capella).withdrawals.toList.map
            fun w => w.amount.toNat).sum)
        else return (0, 0))
        (processBlockExecution config checks engine · block.body bellatrix) pre
    else pure pre
  let pre ← carryBalance (processRandao config checks · block.body) pre
  let pre ← carryBalance (processEth1Data before · block.body) pre
  let expected ← expectedDepositCount pre.1 before
  let deposits := (block.body.deposits before).data
  ensure (deposits.size = expected) (.wrongDepositCount deposits.size expected)
  let pre ← block.body.proposerSlashings.data.toList.foldlM (fun pre sl =>
    recordBalance .slashings (slashingLimits [sl.signedHeader1.message.proposerIndex])
      (processProposerSlashing config checks · sl) pre) pre
  let pre ← block.body.attesterSlashings.data.toList.foldlM (fun pre sl =>
    recordBalance .slashings (slashingLimits (slashingIndices sl))
      (processAttesterSlashing config checks · sl) pre) pre
  let pre ← block.body.attestations.data.toList.foldlM (fun pre att =>
    recordBalance .rewards (fun site => do
      return (← attestationCredit site att s.latestBlockHeader.slot, 0))
      (processAttestation config checks · s.latestBlockHeader.slot att) pre) pre
  let pre ← (block.body.deposits before).data.toList.foldlM (fun pre dep =>
    recordBalance .deposits (fun _ => pure (if fork < .pectra then dep.data.amount.toNat else 0, 0))
      (processDeposit config checks before · dep) pre) pre
  let pre ← carryBalance (fun s => block.body.voluntaryExits.data.foldlM
    (processVoluntaryExit config checks) s) pre
  let pre ← carryBalance (processBlsToExecutionChanges config checks · block.body) pre
  let pre ← if electra : .pectra ≤ fork then do
      let requests := block.body.executionRequests ⟨electra, early⟩
      let pre ← carryBalance (fun s => requests.deposits.data.foldlM
        (processDepositRequest · electra ·) s) pre
      let pre ← carryBalance (fun s => requests.withdrawals.data.foldlM
        (processWithdrawalRequest config · electra ·) s) pre
      requests.consolidations.data.toList.foldlM (fun pre request =>
        recordBalance .excess (fun s => pure (0,
          match findValidatorByPubkey s request.sourcePubkey with
          | none => 0
          | some i => actualBalanceAt ⟨fork, s⟩ i.val - preset.MIN_ACTIVATION_BALANCE.toNat))
          (processConsolidationRequest config · electra request) pre) pre
    else pure pre
  if altair : .altair ≤ fork then
    recordBalance .sync (fun s => do
      let reward ← syncParticipantReward s
      let proposer ← liftAccessor (liftArith do
        Uint64.divChecked (← Uint64.mulChecked reward PROPOSER_WEIGHT)
          (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT))
      return (preset.SYNC_COMMITTEE_SIZE.toNat * (reward.toNat + proposer.toNat),
        preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat))
      (processSyncAggregate config checks · altair (block.body.syncAggregate altair)) pre
  else pure pre

/-- The instrumented reward pass has the same endpoint as the real reward pass. -/
theorem replayRewards_result {fork : Fork} (s t : BeaconState preset fork)
    (events : List (BalanceEvent preset))
    (ok : processRewardsAndPenalties config s = .ok t) :
    ∃ recorded, replayRewards (config := config) (s, events) = .ok (t, recorded) := by
  sorry

/-- The remaining epoch passes keep balances; the replay endpoint is the effective-update input. -/
theorem epochBalanceReplay_result {fork : Fork} (s t : BeaconState preset fork)
    (early : fork < .glamsterdam) (ok : processEpoch config checks s = .ok t) :
    ∃ middle updated events,
      epochBalanceReplay (config := config) (checks := checks) s = .ok (middle, events) ∧
      processEffectiveBalanceUpdates middle = .ok updated ∧
      updated.validators = t.validators ∧ middle.balances = t.balances := by
  sorry

/-- Every real pre-Gloas block has the exact endpoint of the instrumented passes. -/
theorem blockBalanceReplay_result {fork : Fork} (s t : BeaconState preset fork)
    (early : fork < .glamsterdam) (engine : ExecutionEngine preset fork)
    (block : BeaconBlock preset fork)
    (ok : processBlock config checks engine s block = .ok t) :
    ∃ events, blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok (t, events) := by
  sorry

def upgradeBalanceReplay (s : ForkedBeaconState preset) :
    Except TransitionError (List (BalanceEvent preset)) := do
  if upgradeDue config s then
    let next ← upgradeNext config checks s
    let rest ← upgradeBalanceReplay next.val
    if s.fork = .dencun then
      if electra : .pectra ≤ next.val.fork then
        let queued := ((next.val.state.pendingDeposits electra).data.toList.map
          fun d => d.amount.toNat).sum
        return ⟨.crossing, s, next.val, 0, queued⟩ :: rest
      else return rest
    else return rest
  else return []
termination_by Fork.hegota.ctorIdx + 1 - s.fork.ctorIdx
decreasing_by
  have later : s.fork.ctorIdx < next.val.fork.ctorIdx := next.property
  have last : next.val.fork.ctorIdx ≤ Fork.hegota.ctorIdx := by cases next.val.fork <;> decide
  omega

def _root_.EthLib.Consensus.Step.balanceEvents {x y : ForkedBeaconState preset}
    (step : Step config checks x y) :
    Except TransitionError (List (BalanceEvent preset)) :=
  match step with
  | .block engine signed _ _ => do
    if early : x.fork < .glamsterdam then
      return (← blockBalanceReplay (config := config) (checks := checks)
        early engine x.state signed.message).2
    else throw (.accessor (.forkNotYetSpecified x.fork))
  | .slot _ => do
    let cached ← processSlot x.state
    let next ← liftAccessor (liftArith (Uint64.addChecked x.state.slot 1))
    let events ← if next % preset.SLOTS_PER_EPOCH = 0 then
        return (← epochBalanceReplay (config := config) (checks := checks) cached).2
      else pure []
    let advanced ← advanceSlot config checks x.state
    return events ++
      (← upgradeBalanceReplay (config := config) (checks := checks) ⟨x.fork, advanced⟩)

/-- Start at this run's first state and include tests with target epoch at most `high`. -/
def _root_.EthLib.Consensus.Run.balanceEvents {x : ForkedBeaconState preset} (high : Nat) :
    {y : ForkedBeaconState preset} → Run config checks x y →
      Except TransitionError (List (BalanceEvent preset))
  | _, .nil => pure []
  | _, .snoc (middle := m) pre step => do
    let prior ← pre.balanceEvents high
    if (getCurrentEpoch m.state).toNat ≤ high + 1 then
      return prior ++ (← step.balanceEvents)
    else return prior

/-- Filtering by the same horizon preserves the selected prefix's events. -/
theorem _root_.EthLib.Consensus.Run.balanceEvents_prefix {x m y : ForkedBeaconState preset}
    (pre : Run config checks x m) (tail : Run config checks m y) (high : Nat)
    (events : List (BalanceEvent preset))
    (ok : (pre.append tail).balanceEvents high = .ok events) :
    ∃ before, pre.balanceEvents high = .ok before ∧ before <+: events := by
  induction tail generalizing events with
  | nil => exact ⟨events, ok, List.prefix_refl _⟩
  | snoc tail step ih =>
    simp only [Run.append, Run.balanceEvents, bind_ok_iff] at ok
    obtain ⟨prior, priorOk, remaining⟩ := ok
    obtain ⟨before, beforeOk, initial⟩ := ih prior priorOk
    refine ⟨before, beforeOk, ?_⟩
    split at remaining
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at remaining
      obtain ⟨added, _, rfl⟩ := remaining
      exact initial.trans (List.prefix_append _ _)
    · cases remaining
      exact initial

def sourceTotal (events : List (BalanceEvent preset)) (source : BalanceSource)
    (amount : BalanceEvent preset → Nat) : Nat :=
  ((events.filter fun e => e.source == source).map amount).sum

/-- Every source is bounded separately, with no freely supplied credit or debit cap. -/
theorem source_bounds_over_interval {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (alignedCaps : MaxEffectiveBalancesAligned preset)
    (early : y.fork < .glamsterdam) (high : Nat) :
    ∃ events, tail.balanceEvents high = .ok events ∧
      ∀ source : BalanceSource,
        sourceTotal events source BalanceEvent.credits ≤ sourceTotal events source (·.creditLimit) ∧
        sourceTotal events source BalanceEvent.debits ≤
          sourceTotal events source (·.debitLimit) := by
  sorry

/-- The replay covers all positive balance changes of the selected steps, not just net issuance. -/
theorem balance_path_covered {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    (∑ i ∈ Finset.range y.state.validators.data.size, pathCredits i tail.balancePath) ≤
      (events.map (·.creditLimit)).sum ∧
    (∑ i ∈ Finset.range y.state.validators.data.size, pathDebits i tail.balancePath) ≤
      (events.map (·.debitLimit)).sum := by
  sorry

def initialExcess (x : ForkedBeaconState preset) : Nat :=
  ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
    actualBalanceAt x i.toNat - effectiveAt x i.toNat).sum

/-- Count future activations and previous-epoch voters, not validators that exited long ago. -/
def activationCarry (x : ForkedBeaconState preset) : Nat :=
  (x.state.validators.data.toList.zipIdx.map fun (v, i) =>
    if isActiveValidator v (getCurrentEpoch x.state) then 0
    else if isActiveValidator v (getPreviousEpoch x.state) ||
        getCurrentEpoch x.state < v.activationEpoch then max (effectiveAt x i) (actualBalanceAt x i)
    else 0).sum

def scheduledExitCarry (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  (x.state.validators.data.toList.filter fun v =>
    isActiveValidator v (getCurrentEpoch x.state) && v.exitEpoch != FAR_FUTURE_EPOCH &&
      v.exitEpoch.toNat ≤ high + 1).foldl
      (fun total v => total + v.effectiveBalance.toNat) 0

def queueCarry (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  if electra : .pectra ≤ x.fork then
    (if (x.state.earliestExitEpoch electra).toNat ≤ high + 1 then
      (x.state.exitBalanceToConsume electra).toNat else 0) +
    (if (x.state.earliestConsolidationEpoch electra).toNat ≤ high + 1 then
      (x.state.consolidationBalanceToConsume electra).toNat else 0)
  else 0

/-- Pre-Gloas consolidation churn is the whole balance churn less the activation/exit cap. -/
def consolidationRate (stake : Nat) : Nat :=
  max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
    (max preset.EFFECTIVE_BALANCE_INCREMENT.toNat stake / config.CHURN_LIMIT_QUOTIENT.toNat) -
      config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat

/-- Includes both epoch tests that can justify a target at high. -/
def driftHorizon (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  high + 2 - (getCurrentEpoch x.state).toNat

/-- New registry entries come from block deposits or the bounded pending-deposit pass. -/
def registryWindow (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  x.state.validators.data.size + driftHorizon x high *
    (preset.SLOTS_PER_EPOCH.toNat * preset.MAX_DEPOSITS.toNat +
      preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat)

/-- Electra deposit churn includes active top-ups, but not credits to already withdrawn keys. -/
def depositWindow (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  (if electra : .pectra ≤ x.fork then (x.state.depositBalanceToConsume electra).toNat else 0) +
    driftHorizon x high * config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat

/-- Funding that can still support active stake, including queued consolidation sources.

The maximum retains effective stake above actual balance without counting all registry entries. -/
def fundedStake (x : ForkedBeaconState preset) : Nat :=
  (x.state.validators.data.toList.zipIdx.map fun (v, i) =>
    let pending := if electra : .pectra ≤ x.fork then
      (x.state.pendingConsolidations electra).data.any (fun c => c.sourceIndex.toNat == i)
      else false
    if isActiveValidator v (getCurrentEpoch x.state) ||
        getCurrentEpoch x.state < v.activationEpoch || pending then
      max (effectiveAt x i) (actualBalanceAt x i)
    else 0).sum

/-- Retain withdrawn-source credits until queue chronology excludes them on reachable runs.

Those exception credits do not consume deposit churn and must remain explicit. -/
def withdrawnConsolidationCredit (event : BalanceEvent preset) : Nat :=
  if electra : .pectra ≤ event.before.fork then
    (event.before.state.validators.data.toList.zipIdx.map fun (v, i) =>
      if v.withdrawableEpoch.toNat ≤ (getCurrentEpoch event.before.state).toNat &&
          (event.before.state.pendingConsolidations electra).data.any
            (fun c => c.sourceIndex.toNat == i) then
        actualBalanceAt event.after i - actualBalanceAt event.before i
      else 0).sum
  else 0

/-- Consolidations move existing funding; deposits have churn and a withdrawn-source exception. -/
def fundingCredit (event : BalanceEvent preset) : Nat :=
  match event.source with
  | .consolidations => 0
  | .deposits => withdrawnConsolidationCredit event
  | _ => event.creditLimit

/-- Electra active stake is funded initially, by deposit churn, or by non-transfer credits.

Before Electra this retains the registry envelope until a count-churn funding proof is supplied. -/
def activeStakeWindow (x : ForkedBeaconState preset) (high : Nat)
    (events : List (BalanceEvent preset)) : Nat :=
  if .pectra ≤ x.fork ∧ 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat then
    fundedStake x + depositWindow (config := config) x high + (events.map fundingCredit).sum
  else registryWindow x high * preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat

/-- The post-Electra funding envelope bounds active stake without a registry-wide effective cap.

The bound retains withdrawn-source credits rather than assuming pending-source chronology. -/
theorem active_stake_le_window {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (withdrawalDelay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    Quorum.weight (effectiveWeight y.state) (activeKeys y.state) ≤
      activeStakeWindow (config := config) x high events := by
  sorry

def exitWindow (x : ForkedBeaconState preset) (high : Nat)
    (events : List (BalanceEvent preset)) : Nat :=
  scheduledExitCarry x high + queueCarry x high +
    driftHorizon x high *
      ((if x.fork < .pectra then max 1 (cohortCap config (registryWindow x high)) *
        preset.MAX_EFFECTIVE_BALANCE.toNat else 0) +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        consolidationRate (preset := preset) (config := config)
          (activeStakeWindow (config := config) x high events))

/-- Before Electra activations spend count churn; afterwards funding spends deposit churn.

Already funded inactive validators remain a carry-in because Electra activation has no count cap. -/
def activationWindow (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  activationCarry x + depositWindow (config := config) x high +
    (if x.fork < .pectra then driftHorizon x high * cohortCap config (registryWindow x high) *
      preset.MAX_EFFECTIVE_BALANCE.toNat else 0)

/-- Electra deposits use depositWindow; pre-Electra active top-ups remain here.

Across Electra, pre-upgrade funding can bypass later deposit churn, so retain all such credits. -/
def residualCredit (x : ForkedBeaconState preset) (high : Nat)
    (event : BalanceEvent preset) : Nat :=
  match event.source with
  | .deposits => if .pectra ≤ event.before.fork then 0 else
      if high + 1 < config.ELECTRA_FORK_EPOCH.toNat then
        ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
          actualBalanceAt event.after i.toNat - actualBalanceAt event.before i.toNat).sum
      else event.creditLimit
  | _ => event.creditLimit

/-- Per-reference-key non-slashing debits count while the key remains in the recent support. -/
def referenceDebit (i : Nat) (event : BalanceEvent preset) : Nat :=
  if event.source == .slashings then 0 else
    match event.before.state.validators.data[i]? with
    | none => 0
    | some v => if isActiveValidator v (getCurrentEpoch event.before.state) ||
        isActiveValidator v (getPreviousEpoch event.before.state) then
        actualBalanceAt event.before i - actualBalanceAt event.after i
      else 0

/-- Rounding is charged only to a key with initial slack or an actual non-slashing debit.

An aligned effective balance cannot fall below its starting value without such a deficit. -/
def lossCorrection (x : ForkedBeaconState preset) (events : List (BalanceEvent preset)) : Nat :=
  ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
    match x.state.validators.data[i.toNat]? with
    | none => 0
    | some v => if v.slashed then 0 else
      let deficit := effectiveAt x i.toNat - actualBalanceAt x i.toNat +
        (events.map (referenceDebit i.toNat)).sum
      if deficit = 0 then 0 else deficit + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1).sum

/-- No rounding allowance is needed when each unslashed reference key has no deficit. -/
theorem lossCorrection_eq_zero (x : ForkedBeaconState preset)
    (events : List (BalanceEvent preset))
    (funded : ∀ i ∈ getActiveValidatorIndices x.state (getCurrentEpoch x.state),
      ∀ v, x.state.validators.data[i.toNat]? = some v → v.slashed = false →
        effectiveAt x i.toNat ≤ actualBalanceAt x i.toNat)
    (noDebits : ∀ i ∈ getActiveValidatorIndices x.state (getCurrentEpoch x.state),
      (events.map (referenceDebit i.toNat)).sum = 0) : lossCorrection x events = 0 := by
  unfold lossCorrection
  apply List.sum_eq_zero
  intro value member
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp member
  cases found : x.state.validators.data[i.toNat]? with
  | none => simp
  | some v =>
    cases slashed : v.slashed with
    | true => simp [slashed]
    | false =>
      have balance := funded i hi v found slashed
      simp [slashed, Nat.sub_eq_zero_of_le balance, noDebits i hi]

private theorem registry_fold_bound {fork : Fork} {α : Type}
    {action : BeaconState preset fork → α → Except TransitionError (BeaconState preset fork)}
    (bound : ∀ s a t, action s a = .ok t →
      t.validators.data.size ≤ s.validators.data.size + 1)
    {items : List α} {s t : BeaconState preset fork}
    (ok : items.foldlM action s = .ok t) :
    t.validators.data.size ≤ s.validators.data.size + items.length := by
  induction items generalizing s with
  | nil => cases ok; simp
  | cons a rest ih =>
    simp only [List.foldlM_cons, bind_ok_iff] at ok
    obtain ⟨middle, first, last⟩ := ok
    have one := bound s a middle first
    have remaining := ih last
    simp only [List.length_cons]
    omega

private theorem registry_pending_bound {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork}
    (ok : processPendingDeposits config checks s electra = .ok t) :
    t.validators.data.size ≤ s.validators.data.size +
      preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  -- Applied deposits form a sublist of the bounded prefix read by this pass.
  obtain ⟨read, rest, applied, postponed, next, pending, carried,
    _, _, cap, subset, _, _, folded, rfl⟩ := processPendingDeposits_applied ok
  have growth := registry_fold_bound
    (fun _ _ _ h => (applyPendingDeposit_validators_size_le_and_mem h).1) folded
  have count := subset.length_le
  dsimp only
  omega

private theorem registry_deposit_bound {fork : Fork} {s t : BeaconState preset fork}
    {before : fork < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) :
    t.validators.data.size ≤ s.validators.data.size + 1 := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok ok
  unfold applyDeposit at applied
  split at applied
  · unfold applyDepositElectra at applied
    split at applied
    · simp only [bind_ok_iff] at applied
      obtain ⟨_, _, applied⟩ := applied
      split at applied
      · simp only [bind_ok_iff, liftAccessor_ok] at applied
        obtain ⟨_, added, pushed⟩ := applied
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
        rw [addValidatorToRegistry_validators_eq_push added]
        simp
      · cases applied; exact Nat.le_succ _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp applied)
      exact Nat.le_succ _
  · exact (applyPendingDeposit_validators_size_le_and_mem applied).1

private theorem registry_fold_size {fork : Fork} {α : Type}
    {action : BeaconState preset fork → α → Except TransitionError (BeaconState preset fork)}
    (keeps : ∀ s a t, action s a = .ok t → t.validators.data.size = s.validators.data.size)
    {items : List α} {s t : BeaconState preset fork}
    (ok : items.foldlM action s = .ok t) : t.validators.data.size = s.validators.data.size :=
  foldlM_ok_invariant (fun t => t.validators.data.size = s.validators.data.size)
    (fun _ _ _ prior ok => (keeps _ _ _ ok).trans prior) rfl ok

private theorem registry_operations_bound {fork : Fork} {s t : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {parentSlot : Slot} (early : fork < .glamsterdam)
    (ok : processOperations config checks s body parentSlot = .ok t) :
    t.validators.data.size ≤ s.validators.data.size + preset.MAX_DEPOSITS.toNat := by
  have notGloas : ¬ Fork.glamsterdam ≤ fork := fun h => Nat.not_le.mpr early h
  simp only [processOperations, notGloas, ↓reduceDIte,
    bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, _, _, _, a, proposers, b, attesters, c, attestations, d, deposits,
    e, exits, f, changes, requests⟩ := ok
  have sa := registry_fold_size (fun _ _ _ h => (sameSizes_processProposerSlashing h).1) proposers
  have sb := registry_fold_size (fun _ _ _ h => (sameSizes_processAttesterSlashing h).1) attesters
  have sc := registry_fold_size (fun _ _ _ h => (sameSizes_processAttestation h).1) attestations
  have sd := registry_fold_bound (fun _ _ _ h => registry_deposit_bound h) deposits
  have se := registry_fold_size (fun _ _ _ h => (sameSizes_processVoluntaryExit h).1) exits
  have sf : f.validators.data.size = e.validators.data.size := by
    unfold processBlsToExecutionChanges at changes
    split at changes
    · rw [← Array.foldlM_toList] at changes
      exact registry_fold_size (fun _ _ _ h => (sameSizes_processBlsToExecutionChange h).1) changes
    · cases changes; rfl
  have st : t.validators.data.size = f.validators.data.size := by
    split at requests
    · exact (sameSizes_processExecutionRequests requests).1
    · cases requests; rfl
  have cap := (body.deposits (Nat.lt_trans early (by decide))).bound early
  simp only [Array.length_toList] at sd
  omega

private theorem registry_execution_size {fork : Fork} {s t : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {engine : ExecutionEngine preset fork}
    {bellatrix : .bellatrix ≤ fork} (early : fork < .glamsterdam)
    (ok : processBlockExecution config checks engine s body bellatrix = .ok t) :
    t.validators.data.size = s.validators.data.size := by
  have notGloas : ¬ Fork.glamsterdam ≤ fork := fun h => Nat.not_le.mpr early h
  unfold processBlockExecution at ok
  simp only [notGloas, ↓reduceDIte] at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨withdrawn, wit, payload⟩ := ok
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok payload
    exact (sameSizes_processWithdrawals wit).1
  · split at ok
    · obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
      rfl
    · cases ok; rfl

private theorem registry_block_bound {fork : Fork} {s t : BeaconState preset fork}
    {block : BeaconBlock preset fork} {engine : ExecutionEngine preset fork}
    (early : fork < .glamsterdam)
    (ok : processBlock config checks engine s block = .ok t) :
    t.validators.data.size ≤ s.validators.data.size + preset.MAX_DEPOSITS.toNat := by
  have notGloas : ¬ Fork.glamsterdam ≤ fork := fun h => Nat.not_le.mpr early h
  unfold processBlock at ok
  split at ok
  · simp only [processBlockAltair, notGloas, ↓reduceDIte, pure_bind,
      bind_ok_iff] at ok
    obtain ⟨a, header, b, execution, c, randao, d, eth1, e, operations, sync⟩ := ok
    have ha := (sameSizes_processBlockHeader header).1
    have hb : b.validators.data.size = a.validators.data.size := by
      split at execution
      · exact registry_execution_size early execution
      · cases execution; rfl
    have hc := (sameSizes_processRandao randao).1
    have hd : d.validators.data.size = c.validators.data.size := by
      split at eth1
      · exact (sameSizes_processEth1Data eth1).1
      · cases eth1; rfl
    have he := registry_operations_bound early operations
    have ht : t.validators.data.size = e.validators.data.size := by
      unfold processSyncAggregate at sync
      simp only [bind_ok_iff] at sync
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := sync
      rw [← Array.foldlM_toList] at folded
      apply registry_fold_size (fun _ _ _ h => ?_) folded
      unfold applySyncReward at h
      split at h
      · simp only [bind_ok_iff, liftAccessor_ok] at h
        obtain ⟨_, raised, _, _, paid⟩ := h
        exact (sameSizes_increaseBalance paid).1.trans (sameSizes_increaseBalance raised).1
      · exact (sameSizes_decreaseBalance (liftAccessor_ok.mp h)).1
    omega
  · simp only [bind_ok_iff] at ok
    obtain ⟨a, header, b, randao, c, eth1, operations⟩ := ok
    have ha := (sameSizes_processBlockHeader header).1
    have hb := (sameSizes_processRandao randao).1
    have hc := (sameSizes_processEth1Data eth1).1
    have ht := registry_operations_bound early operations
    omega

private theorem registry_history_size {fork : Fork} {s t : BeaconState preset fork}
    (ok : processHistoricalRootsUpdate s = .ok t) :
    t.validators.data.size = s.validators.data.size := by
  unfold processHistoricalRootsUpdate at ok
  split at ok
  · cases ok
  simp only [bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    rfl
  · cases ok; rfl

private theorem registry_summary_size {fork : Fork} {s t : BeaconState preset fork}
    {capella : .shapella ≤ fork}
    (ok : processHistoricalSummariesUpdate s capella = .ok t) :
    t.validators.data.size = s.validators.data.size := by
  unfold processHistoricalSummariesUpdate at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals rfl

private theorem registry_reset_size {fork : Fork} {s t : BeaconState preset fork}
    {before : fork < .hegota} (ok : processEth1DataReset before s = .ok t) :
    t.validators.data.size = s.validators.data.size := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok <;> cases ok <;> rfl

private theorem registry_epoch_tail_size {fork : Fork} {altair : .altair ≤ fork}
    {rooted synced looked after : BeaconState preset fork}
    (sync : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair) altair =
      .ok synced)
    (look : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (window : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) :
    after.validators.data.size = rooted.validators.data.size := by
  have hs : synced.validators.data.size = rooted.validators.data.size := by
    unfold processSyncCommitteeUpdates at sync
    simp only [bind, Except.bind, pure, Except.pure] at sync
    repeat' (split at sync <;> try cases sync)
    all_goals rfl
  have hl : looked.validators.data.size = synced.validators.data.size := by
    split at look
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at look
      obtain ⟨_, _, _, _, rfl⟩ := look
      rfl
    · cases look; rfl
  have hw : after.validators.data.size = looked.validators.data.size := by
    split at window
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at window
      obtain ⟨_, _, _, _, rfl⟩ := window
      rfl
    · cases window; rfl
  exact hw.trans (hl.trans hs)

private theorem registry_epoch_bound {fork : Fork} {s t : BeaconState preset fork}
    (early : fork < .glamsterdam) (ok : processEpoch config checks s = .ok t) :
    t.validators.data.size ≤ s.validators.data.size +
      preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  have notGloas : ¬ Fork.glamsterdam ≤ fork := fun h => Nat.not_le.mpr early h
  unfold processEpoch at ok
  split at ok
  · simp only [processEpochAltair, notGloas, ↓reduceDIte, pure_bind, bind_ok_iff] at ok
    obtain ⟨a, justified, b, scored, c, rewarded, d, registered, e, slashed, f, reset,
      g, pending, h, balanced, i, cleared, j, mixed, rest⟩ := ok
    have ha := (sameSizes_processJustificationAndFinalization justified).1
    have hb : b.validators.data.size = a.validators.data.size := by
      unfold processInactivityUpdates at scored
      split at scored
      · cases scored; rfl
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at scored
        obtain ⟨_, _, _, _, rfl⟩ := scored
        rfl
    have hc := (processRewardsAndPenalties_sameSizes rewarded).1
    have hd := (sameSizes_processRegistryUpdates registered).1
    have he := (sameSizes_processSlashings slashed).1
    have hf : f.validators.data.size = e.validators.data.size := by
      split at reset
      · exact registry_reset_size reset
      · cases reset; rfl
    -- Only the pending-deposit pass can append validators during an epoch transition.
    have hg : g.validators.data.size ≤ f.validators.data.size +
        preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
      unfold processPendingBalances at pending
      split at pending
      · simp only [bind_ok_iff] at pending
        obtain ⟨deposited, dep, con⟩ := pending
        rw [(processPendingConsolidations_kept con).1]
        exact registry_pending_bound dep
      · cases pending; omega
    have hh := (sameSizes_processEffectiveBalanceUpdates balanced).1
    obtain ⟨_, _, _, _, hi⟩ := processSlashingsReset_eq cleared
    obtain ⟨_, _, _, _, _, _, hj⟩ := processRandaoMixesReset_eq mixed
    have ht : t.validators.data.size = j.validators.data.size := by
      split at rest <;> simp only [bind_ok_iff] at rest <;>
        obtain ⟨rooted, history, synced, sync, looked, look, window⟩ := rest
      · exact (registry_epoch_tail_size sync look (by simpa only [notGloas, ↓reduceDIte]
          using window)).trans (registry_summary_size history)
      · exact (registry_epoch_tail_size sync look (by simpa only [notGloas, ↓reduceDIte]
          using window)).trans (registry_history_size history)
    rw [hj, hi] at ht
    dsimp only at ht
    omega
  · simp only [bind_ok_iff] at ok
    obtain ⟨a, justified, b, rewarded, c, registered, d, slashed, e, reset, f, balanced,
      g, cleared, h, mixed, i, history, rotated⟩ := ok
    have ha := (sameSizes_processJustificationAndFinalization justified).1
    have hb := (processRewardsAndPenalties_sameSizes rewarded).1
    have hc := (sameSizes_processRegistryUpdates registered).1
    have hd := (sameSizes_processSlashings slashed).1
    have he := registry_reset_size reset
    have hf := (sameSizes_processEffectiveBalanceUpdates balanced).1
    obtain ⟨_, _, _, _, hg⟩ := processSlashingsReset_eq cleared
    obtain ⟨_, _, _, _, _, _, hh⟩ := processRandaoMixesReset_eq mixed
    have hi := registry_history_size history
    have ht : t.validators.data.size = i.validators.data.size := by
      unfold processParticipationRecordUpdates at rotated
      split at rotated
      · cases rotated
      · cases rotated; rfl
    rw [hh, hg] at hi
    dsimp only at hi
    omega

private theorem registry_upgrade_size {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (ok : upgradeNext config checks s = .ok t) :
    t.val.state.validators.data.size = s.state.validators.data.size := by
  obtain ⟨fork, state⟩ := s
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact congrArg Array.size (upgradeToAltair_spec upgraded).1
  · subst ok; rfl
  · subst ok; rfl
  · subst ok; rfl
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact (upgradeToElectra_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact congrArg Array.size (upgradeToFulu_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact congrArg Array.size (upgradeToGloas_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    rfl

private theorem registry_upgrades_size {s t : ForkedBeaconState preset}
    (ok : processUpgrades config checks s = .ok t) :
    t.state.validators.data.size = s.state.validators.data.size :=
  processUpgrades_induction
    (property := fun t => t.state.validators.data.size = s.state.validators.data.size)
    (fun prior ok => (registry_upgrade_size ok).trans prior) rfl ok

private theorem registry_slot_bound {s t : ForkedBeaconState preset}
    (early : t.fork < .glamsterdam)
    (ok : advanceSlotAcross config checks s = .ok t) :
    t.state.slot.toNat = s.state.slot.toNat + 1 ∧
      t.state.validators.data.size ≤ s.state.validators.data.size +
        ((getCurrentEpoch t.state).toNat - (getCurrentEpoch s.state).toNat) *
          preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  simp only [advanceSlotAcross, bind_ok_iff] at ok
  obtain ⟨advanced, slot, upgrades⟩ := ok
  have size := registry_upgrades_size upgrades
  have slotEq := processUpgrades_slot upgrades
  have forward := processUpgrades_fork_le upgrades
  have oldEarly : s.fork < .glamsterdam := Nat.lt_of_le_of_lt forward early
  obtain ⟨next, cached, epoched, nextOk, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok slot
  obtain ⟨_, _, _, _, cacheEq⟩ := processSlot_ok cachedOk
  have cacheSize : cached.validators.data.size = s.state.validators.data.size := by rw [cacheEq]
  have cacheSlot := processSlot_slot cachedOk
  have nextSlot : t.state.slot.toNat = s.state.slot.toNat + 1 := by
    rw [slotEq]
    exact nextOk
  refine ⟨nextSlot, ?_⟩
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    -- Charge the pending-deposit cap only when this slot crosses an epoch boundary.
    have epochs := nextSlot_epoch_of_boundary nextOk boundary
    have growth := registry_epoch_bound oldEarly epochedOk
    have diff : (getCurrentEpoch t.state).toNat - (getCurrentEpoch s.state).toNat = 1 := by
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, slotEq]
      dsimp only
      omega
    rw [diff, one_mul, size]
    dsimp only
    omega
  · cases epochedOk
    rw [size]
    dsimp only
    omega

private theorem registry_operations_header {fork : Fork} {s t : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {parentSlot : Slot} (early : fork < .glamsterdam)
    (ok : processOperations config checks s body parentSlot = .ok t) :
    t.latestBlockHeader = s.latestBlockHeader := by
  have foldHeader {α : Type} {f : BeaconState preset fork → α → Except TransitionError _}
      (keeps : ∀ s x t, f s x = .ok t → t.latestBlockHeader = s.latestBlockHeader)
      {s t : BeaconState preset fork} {xs : List α} (h : xs.foldlM f s = .ok t) :
      t.latestBlockHeader = s.latestBlockHeader :=
    foldlM_ok_invariant (fun t => t.latestBlockHeader = s.latestBlockHeader)
      (fun _ _ _ before ok => (keeps _ _ _ ok).trans before) rfl h
  have notGloas : ¬ Fork.glamsterdam ≤ fork := fun h => Nat.not_le.mpr early h
  simp only [processOperations, notGloas, ↓reduceDIte, bind_ok_iff, ensure_ok_iff,
    ← Array.foldlM_toList] at ok
  obtain ⟨_, _, _, _, _, proposers, _, attesters, _, attestations, _, deposits, exited,
    exits, changed, changes, requests⟩ := ok
  have changesKept : changed.latestBlockHeader = exited.latestBlockHeader := by
    unfold processBlsToExecutionChanges at changes
    split at changes
    · rw [← Array.foldlM_toList] at changes
      exact foldHeader (fun _ _ _ h =>
        (payloadInputs_processBlsToExecutionChange h).latestBlockHeader) changes
    · cases changes; rfl
  have requestsKept : t.latestBlockHeader = changed.latestBlockHeader := by
    split at requests
    · simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at requests
      obtain ⟨_, dep, _, wit, con⟩ := requests
      exact (foldHeader (fun _ _ _ h =>
        (payloadInputs_processConsolidationRequest h).latestBlockHeader) con).trans <|
        (foldHeader (fun _ _ _ h =>
          (payloadInputs_processWithdrawalRequest h).latestBlockHeader) wit).trans <|
        foldHeader (fun _ _ _ h => (payloadInputs_processDepositRequest h).latestBlockHeader) dep
    · cases requests; rfl
  exact requestsKept.trans <| changesKept.trans <|
    (foldHeader (fun _ _ _ h => (payloadInputs_processVoluntaryExit h).latestBlockHeader)
      exits).trans <|
    (foldHeader (fun _ _ _ h => by
      obtain ⟨_, _, _, _, applied⟩ := processDeposit_ok h
      exact (frame_applyDeposit applied).latestBlockHeader) deposits).trans <|
    (foldHeader (fun _ _ _ h => (payloadInputs_processAttestation h).latestBlockHeader)
      attestations).trans <|
    (foldHeader (fun _ _ _ h => (payloadInputs_processAttesterSlashing h).latestBlockHeader)
      attesters).trans <|
    foldHeader (fun _ _ _ h => (payloadInputs_processProposerSlashing h).latestBlockHeader)
      proposers

private theorem registry_execution_header {fork : Fork} {s t : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork} (early : fork < .glamsterdam)
    (ok : processBlockExecution config checks engine s body bellatrix = .ok t) :
    t.latestBlockHeader = s.latestBlockHeader := by
  have notGloas : ¬ Fork.glamsterdam ≤ fork := fun h => Nat.not_le.mpr early h
  unfold processBlockExecution at ok
  simp only [notGloas, ↓reduceDIte] at ok
  split at ok
  · obtain ⟨_, withdrawn, executed⟩ := bind_ok_iff.mp ok
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok executed
    exact (payloadInputs_processWithdrawals withdrawn).latestBlockHeader
  · split at ok
    · obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
      rfl
    · cases ok; rfl

private theorem registry_block_header {fork : Fork} {s t : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    (early : fork < .glamsterdam)
    (ok : processBlock config checks engine s block = .ok t) :
    t.latestBlockHeader.slot = s.slot ∧ s.latestBlockHeader.slot < s.slot := by
  obtain ⟨headed, headerOk⟩ := processBlock_header_of_lt_gloas early ok
  have checked := processBlockHeader_checks headerOk
  refine ⟨?_, checked.1 ▸ checked.2.1⟩
  suffices t.latestBlockHeader.slot = block.slot by exact this.trans checked.1
  have notGloas : ¬ Fork.glamsterdam ≤ fork := fun h => Nat.not_le.mpr early h
  unfold processBlock at ok
  split at ok
  · simp only [processBlockAltair, notGloas, ↓reduceDIte, pure_bind, bind_ok_iff] at ok
    obtain ⟨headed, headedOk, executed, executedOk, revealed, revealedOk, voted, votedOk,
      operated, operatedOk, synced⟩ := ok
    have executedKept : executed.latestBlockHeader = headed.latestBlockHeader := by
      split at executedOk
      · exact registry_execution_header early executedOk
      · cases executedOk; rfl
    have votedKept : voted.latestBlockHeader = revealed.latestBlockHeader := by
      split at votedOk
      · exact (payloadInputs_processEth1Data votedOk).latestBlockHeader
      · cases votedOk; rfl
    obtain ⟨_, _, eq⟩ := processBlockHeader_eq headedOk
    rw [(payloadInputs_processSyncAggregate synced).latestBlockHeader,
      registry_operations_header early operatedOk, votedKept,
      (payloadInputs_processRandao revealedOk).latestBlockHeader, executedKept, eq]
  · simp only [bind_ok_iff] at ok
    obtain ⟨headed, headedOk, revealed, revealedOk, voted, votedOk, operatedOk⟩ := ok
    obtain ⟨_, _, eq⟩ := processBlockHeader_eq headedOk
    rw [registry_operations_header early operatedOk,
      (payloadInputs_processEth1Data votedOk).latestBlockHeader,
      (payloadInputs_processRandao revealedOk).latestBlockHeader, eq]

-- An unused block slot retains its allowance until a successful header consumes it.
private def registry_block_allowance (s : ForkedBeaconState preset) : Nat :=
  if s.state.latestBlockHeader.slot < s.state.slot then preset.MAX_DEPOSITS.toNat else 0

private theorem registry_run_bound {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) :
    x.state.slot.toNat ≤ y.state.slot.toNat ∧
      y.state.validators.data.size + registry_block_allowance y ≤
        x.state.validators.data.size +
          (y.state.slot.toNat + 1 - x.state.slot.toNat) * preset.MAX_DEPOSITS.toNat +
          ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) *
            preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  induction tail with
  | nil =>
    constructor
    · exact Nat.le_refl _
    · simp only [Nat.add_sub_cancel_left, Nat.sub_self, Nat.zero_mul, Nat.add_zero, one_mul]
      unfold registry_block_allowance
      split <;> omega
  | @snoc middle last pre step ih =>
    have beforeEarly : middle.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt step.chainStep.fork_le early
    obtain ⟨slotsBefore, bound⟩ := ih beforeEarly
    have epochsBefore : (getCurrentEpoch x.state).toNat ≤
        (getCurrentEpoch middle.state).toNat := by
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
      exact Nat.div_le_div_right slotsBefore
    cases step with
    | slot ok =>
      obtain ⟨slot, growth⟩ := registry_slot_bound early ok
      have epochsAfter : (getCurrentEpoch middle.state).toNat ≤
          (getCurrentEpoch last.state).toNat := by
        rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
        exact Nat.div_le_div_right (by omega)
      have epochAdd : (getCurrentEpoch last.state).toNat - (getCurrentEpoch x.state).toNat =
          ((getCurrentEpoch middle.state).toNat - (getCurrentEpoch x.state).toNat) +
          ((getCurrentEpoch last.state).toNat - (getCurrentEpoch middle.state).toNat) := by omega
      have slotAdd : last.state.slot.toNat + 1 - x.state.slot.toNat =
          (middle.state.slot.toNat + 1 - x.state.slot.toNat) + 1 := by omega
      -- Advancing a slot supplies at most one fresh block allowance, even across upgrades.
      have allowance : registry_block_allowance last ≤ preset.MAX_DEPOSITS.toNat := by
        unfold registry_block_allowance
        split <;> omega
      constructor
      · omega
      · rw [slotAdd, epochAdd, Nat.add_mul, Nat.add_mul, one_mul]
        omega
    | @block fork before after engine signed due ok =>
      have processed := (applySignedBlock_ok ok).2.1
      have slot := (frame_processBlock processed).slot
      have header := registry_block_header early processed
      have growth := registry_block_bound early processed
      -- A successful block consumes the allowance and forbids another block at this slot.
      have used : ¬ after.latestBlockHeader.slot < after.slot := by
        rw [header.1, slot]
        exact UInt64.lt_irrefl _
      have oldAllowance : registry_block_allowance ⟨fork, before⟩ =
          preset.MAX_DEPOSITS.toNat := by simp only [registry_block_allowance, header.2, ↓reduceIte]
      have newAllowance : registry_block_allowance ⟨fork, after⟩ = 0 := by
        simp only [registry_block_allowance, used, ↓reduceIte]
      have epoch : getCurrentEpoch after = getCurrentEpoch before := by
        simp only [getCurrentEpoch, slot]
      simp only [oldAllowance] at bound
      simp only [newAllowance, Nat.add_zero, slot, epoch]
      exact ⟨slotsBefore, by omega⟩

/-- The registry envelope is independent of the endpoint, including a mid-epoch start. -/
theorem registry_le_window {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) :
    y.state.validators.data.size ≤ registryWindow x high := by
  obtain ⟨slots, bound⟩ := registry_run_bound tail early
  have epochs : (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch y.state).toNat := by
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
    exact Nat.div_le_div_right slots
  have epochCount : (getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat ≤
      driftHorizon x high := by unfold driftHorizon; omega
  have lastSlot : y.state.slot.toNat < (high + 2) * preset.SLOTS_PER_EPOCH.toNat := by
    rw [getCurrentEpoch_toNat] at endEpoch
    apply (Nat.div_lt_iff_lt_mul positive).mp
    omega
  have firstSlot : (getCurrentEpoch x.state).toNat * preset.SLOTS_PER_EPOCH.toNat ≤
      x.state.slot.toNat := by
    rw [getCurrentEpoch_toNat]
    exact Nat.div_mul_le_self _ _
  -- Include the initial slot: the run can start before that slot's block has arrived.
  have slotCount : y.state.slot.toNat + 1 - x.state.slot.toNat ≤
      driftHorizon x high * preset.SLOTS_PER_EPOCH.toNat := by
    unfold driftHorizon
    rw [Nat.sub_mul]
    omega
  have deposits := Nat.mul_le_mul_right preset.MAX_DEPOSITS.toNat slotCount
  have pending := Nat.mul_le_mul_right preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat epochCount
  unfold registryWindow
  rw [Nat.mul_add, ← Nat.mul_assoc]
  omega

/-- Bound exits and retained-key losses, omitting keys with slashing evidence.

The source envelope can charge a pre-exit deficit as well as the later departure.

The exact referenceLoss does not double-count that key. -/
theorem nonaccountable_losses_over_interval {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    referenceLoss x y ≤
      exitWindow (config := config) x high events + lossCorrection x events := by
  sorry

/-- Funding churn bounds Electra deposits that can contribute to recent voting stake.

Withdrawn-key exceptions do not reactivate an exited validator and contribute no such stake. -/
theorem gains_and_activations_over_interval {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (withdrawalDelay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    referenceGain x y ≤
      activationWindow (config := config) x high + initialExcess x +
        (events.map (residualCredit (config := config) x high)).sum := by
  sorry

/-- A conservative source envelope, separate from the exact observed-state drift.

The boundary term is supplied by boundaryWindow, not by the cumulative exit envelope.

Queue, registry and rounding bounds still need tighter transition proofs. -/
def sourceDrift (x : ForkedBeaconState preset) (high boundary : Nat)
    (events : List (BalanceEvent preset)) : Nat :=
  2 * (exitWindow (config := config) x high events + lossCorrection x events) +
    activationWindow (config := config) x high + initialExcess x +
    (events.map (residualCredit (config := config) x high)).sum + 2 * boundary

/-- Extending a replay prefix and its boundary budget cannot shrink the source envelope. -/
theorem sourceDrift_le_of_prefix (x : ForkedBeaconState preset) (high : Nat)
    {before after : List (BalanceEvent preset)} (initial : before <+: after)
    {first last : Nat} (boundary : first ≤ last) :
    sourceDrift (config := config) x high first before ≤
      sourceDrift (config := config) x high last after := by
  have sums (f : BalanceEvent preset → Nat) : (before.map f).sum ≤ (after.map f).sum := by
    obtain ⟨rest, rfl⟩ := initial
    simp only [List.map_append, List.sum_append]
    omega
  have loss : lossCorrection x before ≤ lossCorrection x after := by
    apply List.sum_le_sum
    intro i _
    cases found : x.state.validators.data[i.toNat]? with
    | none => simp
    | some v =>
      cases slashed : v.slashed with
      | true => simp [slashed]
      | false =>
        simp only [slashed, Bool.false_eq_true, ↓reduceIte]
        have monotone := sums (referenceDebit i.toNat)
        split <;> split <;> omega
  have active : activeStakeWindow (config := config) x high before ≤
      activeStakeWindow (config := config) x high after := by
    unfold activeStakeWindow
    split
    · have monotone := sums fundingCredit
      omega
    · exact Nat.le_refl _
  have rates : consolidationRate (preset := preset) (config := config)
      (activeStakeWindow (config := config) x high before) ≤
      consolidationRate (preset := preset) (config := config)
        (activeStakeWindow (config := config) x high after) :=
    Nat.sub_le_sub_right (max_le_max_left _
      (Nat.div_le_div_right (max_le_max_left _ active))) _
  have exits : exitWindow (config := config) x high before ≤
      exitWindow (config := config) x high after := by
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_left rates _)) _
  have credits := sums (residualCredit (config := config) x high)
  unfold sourceDrift
  omega

/-- The source envelope is a derived upper bound, not the definition of the safety loss. -/
theorem derivedDrift_le_sources {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (withdrawalDelay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (early : y.fork < .glamsterdam) (high : Nat)
    (startEpoch : (getCurrentEpoch x.state).toNat ≤ high + 1) :
    ∃ events, tail.balanceEvents high = .ok events ∧
      derivedDrift high tail ≤
        sourceDrift (config := config) x high (boundaryWindow high tail) events := by
  obtain ⟨events, replayed, bounds⟩ :=
    source_bounds_over_interval shared tail genesis parameters caps aligned early high
  clear bounds
  refine ⟨events, replayed, ?_⟩
  have atState {y : ForkedBeaconState preset} (run : Run config checks x y)
      (early : y.fork < .glamsterdam)
      (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
      (events : List (BalanceEvent preset)) (replayed : run.balanceEvents high = .ok events) :
      stateDrift x y ≤ sourceDrift (config := config) x high (boundaryStake y) events := by
    have losses := nonaccountable_losses_over_interval shared run genesis parameters caps
      aligned early high within events replayed
    have gains := gains_and_activations_over_interval shared run genesis parameters caps
      aligned withdrawalDelay early high within events replayed
    unfold stateDrift sourceDrift
    omega
  induction tail generalizing events with
  | nil => exact atState .nil early startEpoch events replayed
  | @snoc middle last pre step ih =>
    have beforeFork : middle.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt step.chainStep.fork_le early
    obtain ⟨prior, priorOk, initial⟩ := pre.balanceEvents_prefix
      (Run.nil.snoc step) high events replayed
    have before := ih beforeFork prior priorOk
    have budget := sourceDrift_le_of_prefix (config := config) x high initial
      (first := boundaryWindow high pre) (last := boundaryWindow high (pre.snoc step))
      (by simp only [boundaryWindow]; split <;> omega)
    have past := Nat.le_trans before budget
    simp only [derivedDrift, boundaryWindow]
    split
    · rename_i within
      simp only [boundaryWindow, within, ↓reduceIte] at past
      have current := atState (pre.snoc step) early within events replayed
      have enlarged := sourceDrift_le_of_prefix (config := config) x high
        (List.prefix_refl events) (Nat.le_max_right (boundaryWindow high pre) (boundaryStake last))
      exact max_le past (current.trans enlarged)
    · rename_i beyond
      simpa only [boundaryWindow, beyond, ↓reduceIte] using past

/-- Cache-preserving epoch calls inherit the exact budget of their selected prefix. -/
theorem quorum_drift_from_run {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (withdrawalDelay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (early : y.fork < .glamsterdam) (low high : Nat)
    (starts : x.state.slot.toNat ≤ low * preset.SLOTS_PER_EPOCH.toNat)
    (call : QuorumCall (shared.append tail))
    (lower : low ≤ call.target.epoch.toNat) (upper : call.target.epoch.toNat ≤ high) :
    ∃ loss gain outside,
        (∑ k ∈ (activeKeys x.state).filter (fun k => ¬ (shared.append tail).SlashingEvidence k),
          (effectiveWeight x.state k - Quorum.supported (recentKeys call.cached)
            (effectiveWeight call.cached) k)) ≤ loss ∧
        (∑ k ∈ recentKeys call.cached, (effectiveWeight call.cached k -
          Quorum.supported (activeKeys x.state)
            (effectiveWeight x.state) k)) ≤ gain ∧
        Quorum.weight (effectiveWeight call.cached)
          (recentKeys call.cached \ activeKeys call.cached) ≤ outside ∧
        2 * loss + gain + 2 * outside ≤ derivedDrift high tail := by
  classical
  have _ := caps
  have _ := aligned
  have _ := withdrawalDelay
  have member := call_after_reference shared tail parameters low starts call lower
  obtain ⟨pre, post, split⟩ := tail.contains_split (.slot call.advanced) member
  let before := call.before
  have cachedSlot := (frame_processSlot call.cachedOk).slot
  obtain ⟨_, _, _, _, validators, _⟩ := call.toEpochCall.selected_prefix
  have epochBound : (getCurrentEpoch before.state).toNat ≤ high + 1 := by
    have target : (getCurrentEpoch call.cached).toNat ≤ call.target.epoch.toNat + 1 := by
      rw [call.targetEpoch]
      cases call.current <;> simp [getPreviousEpoch_toNat]
      omega
    have epoch : getCurrentEpoch call.cached = getCurrentEpoch before.state := by
      simp only [getCurrentEpoch, cachedSlot, before]
    rw [epoch] at target
    omega
  have observed {z : ForkedBeaconState preset} (run : Run config checks x z)
      (bounded : (getCurrentEpoch z.state).toNat ≤ high + 1) :
      stateDrift x z ≤ derivedDrift high run := by
    cases run with
    | nil => exact Nat.le_refl _
    | snoc pre step => simp only [derivedDrift, ite_eq_left bounded]; exact Nat.le_max_right _ _
  have monotone {u v : ForkedBeaconState preset} (run : Run config checks x u)
      (rest : Run config checks u v) :
      derivedDrift high run ≤ derivedDrift high (run.append rest) := by
    induction rest with
    | nil => exact Nat.le_refl _
    | snoc rest step ih =>
      simp only [Run.append, derivedDrift]
      split
      · exact ih.trans (Nat.le_max_left _ _)
      · exact ih
  have budget : stateDrift x before ≤ derivedDrift high tail := by
    rw [split]
    apply (observed pre epochBound).trans
    apply le_trans (b := derivedDrift high (pre.snoc (.slot call.advanced)))
    · simp only [derivedDrift]
      split
      · exact Nat.le_max_left _ _
      · exact Nat.le_refl _
    · exact monotone _ post
  have evidence (k) (h : (shared.append pre).SlashingEvidence k) :
      (shared.append tail).SlashingEvidence k := by
    obtain ⟨u, v, step, inside, slashed⟩ := h
    refine ⟨u, v, step, ?_, slashed⟩
    rcases (shared.contains_append pre step).mp inside with inside | inside
    · exact (shared.contains_append tail step).mpr (.inl inside)
    · apply (shared.contains_append tail step).mpr
      right
      rw [split]
      exact ((pre.snoc (.slot call.advanced)).contains_append post step).mpr
        (.inl (.earlier inside _))
  have earlyBefore : before.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps
      ((Run.nil.snoc (.slot call.advanced)).append post).chainSteps) early
  have lossBound : (∑ k ∈ (activeKeys x.state).filter
      (fun k => ¬ (shared.append tail).SlashingEvidence k),
      (effectiveWeight x.state k - Quorum.supported (recentKeys before.state)
        (effectiveWeight before.state) k)) ≤ referenceLoss x before := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      obtain ⟨active, absent⟩ := Finset.mem_filter.mp hk
      refine Finset.mem_filter.mpr ⟨active, ?_⟩
      rintro ⟨v, found, key, slashed⟩
      exact absent (evidence k (key ▸
        (shared.append pre).slashed_evidence genesis earlyBefore v found slashed))
    · intros; exact Nat.zero_le _
  refine ⟨referenceLoss x before, referenceGain x before, boundaryStake before, ?_, ?_, ?_,
    budget⟩
  all_goals
    have weight : effectiveWeight call.cached = effectiveWeight before.state := by
      funext k
      simp only [effectiveWeight, validators, before]
    have active : activeKeys call.cached = activeKeys before.state := by
      simp only [activeKeys, keysAt, getActiveValidatorIndices, getCurrentEpoch,
        validators, cachedSlot, before]
      rfl
    have recent : recentKeys call.cached = recentKeys before.state := by
      simp only [recentKeys, active, keysAt, getActiveValidatorIndices, getPreviousEpoch,
        getCurrentEpoch, validators, cachedSlot, before]
      rfl
  · simpa only [weight, recent] using lossBound
  · exact (congrArg₂ (fun s w => ∑ k ∈ s,
        (w k - Quorum.supported (activeKeys x.state) (effectiveWeight x.state) k))
        recent weight).le
  · exact (congrArg₂ (fun w s => Quorum.weight w s) weight
      (congrArg₂ (· \ ·) recent active)).le

end

end EthLib.Consensus.DirectSafety
