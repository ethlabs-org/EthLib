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

/-- The registry envelope is independent of the endpoint, including a mid-epoch start. -/
theorem registry_le_window {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) :
    y.state.validators.data.size ≤ registryWindow x high := by
  sorry

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
  sorry

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
