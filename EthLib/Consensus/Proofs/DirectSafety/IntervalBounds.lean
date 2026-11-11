module

public import EthLib.Consensus.Proofs.DirectSafety.SourceBounds

/-!
# Source bounds over a selected execution interval

The replay below executes the concrete transition passes and records their inputs and results.

It records positive changes per validator, so transfers cannot cancel losses or gains elsewhere.

No caller supplies the amount of a source or an accounting cap.

The source bounds retain the initial queues, scores and balances needed by arbitrary intervals.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base

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
    (balanceAt event.after i - balanceAt event.before i)

def BalanceEvent.debits (event : BalanceEvent preset) : Nat :=
  ∑ i ∈ Finset.range event.before.state.balances.data.size,
    (balanceAt event.before i - balanceAt event.after i)

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

def consolidationLimit {fork : Fork} (s : BeaconState preset fork)
    (electra : .pectra ≤ fork) : Nat :=
  ((s.pendingConsolidations electra).data.toList.map fun c =>
    effectiveAt ⟨fork, s⟩ c.sourceIndex.toNat).sum

def pendingDepositLimit {fork : Fork} (s : BeaconState preset fork) (electra : .pectra ≤ fork) :
    Except TransitionError Nat := do
  let churn ← liftAccessor (depositChurnLimit config s)
  let next ← liftAccessor (liftArith (Uint64.addChecked (getCurrentEpoch s) 1))
  let exceptions := (s.pendingDeposits electra).data.toList.filter fun d =>
    Option.getD ((depositTargetStatus s next d.pubkey).toOption.map Prod.snd) false
  return (s.depositBalanceToConsume electra).toNat + churn.toNat +
    (exceptions.map fun d => d.amount.toNat).sum

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
    let pre ← recordBalance .deposits
      (fun s => return (← pendingDepositLimit (config := config) s electra, 0))
      (processPendingDeposits config checks · electra) pre
    recordBalance .consolidations
      (fun s => pure (consolidationLimit s electra, consolidationLimit s electra))
      (processPendingConsolidations · electra) pre
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
          | some i => balanceAt ⟨fork, s⟩ i.val - preset.MIN_ACTIVATION_BALANCE.toNat))
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

def initialSlack (x : ForkedBeaconState preset) : Nat :=
  ∑ i ∈ Finset.range x.state.validators.data.size, (effectiveAt x i - balanceAt x i)

def initialExcess (x : ForkedBeaconState preset) : Nat :=
  ∑ i ∈ Finset.range x.state.validators.data.size, (balanceAt x i - effectiveAt x i)

/-- Includes already eligible and already scheduled activations, not only fresh deposits. -/
def activationCarry (x : ForkedBeaconState preset) : Nat :=
  (x.state.validators.data.toList.zipIdx.map fun (v, i) =>
    if isActiveValidator v (getCurrentEpoch x.state) then 0
    else max (effectiveAt x i) (balanceAt x i)).sum

def scheduledExitCarry (x : ForkedBeaconState preset) : Nat :=
  (x.state.validators.data.toList.filter fun v =>
    isActiveValidator v (getCurrentEpoch x.state) && v.exitEpoch != FAR_FUTURE_EPOCH).foldl
      (fun total v => total + v.effectiveBalance.toNat) 0

def queueCarry (x : ForkedBeaconState preset) : Nat :=
  if electra : .pectra ≤ x.fork then
    (x.state.exitBalanceToConsume electra).toNat +
      (x.state.consolidationBalanceToConsume electra).toNat
  else 0

/-- A configuration-derived upper rate for consolidation churn, using the endpoint registry size. -/
def consolidationRate (size : Nat) : Nat :=
  max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
    (max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (size * preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat) / config.CHURN_LIMIT_QUOTIENT.toNat)

def exitWindow (x y : ForkedBeaconState preset) (high : Nat) : Nat :=
  scheduledExitCarry x + queueCarry x +
    (high + 2 - (getCurrentEpoch x.state).toNat) *
      ((if x.fork < .pectra then max 1 (cohortCap config y.state.validators.data.size) *
        preset.MAX_EFFECTIVE_BALANCE.toNat else 0) +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        consolidationRate (preset := preset) (config := config) y.state.validators.data.size)

def lossCorrection (x : ForkedBeaconState preset) (events : List (BalanceEvent preset)) : Nat :=
  initialSlack x + (events.map (·.debitLimit)).sum +
    x.state.validators.data.size * (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1)

/-- Exit charges can be smaller than reference stake because penalties occurred before charging. -/
theorem exits_over_interval {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    leaving x y ≤ exitWindow (config := config) x y high + lossCorrection x events := by
  sorry

/-- Activation growth uses initial inactive funds or concrete credits, including top-ups. -/
theorem activations_and_joining_growth_over_interval {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    Quorum.weight (effectiveWeight y.state) (recentKeys y.state \ activeKeys x.state) ≤
      activationCarry x + (events.map (·.creditLimit)).sum := by
  sorry

theorem gains_over_interval {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    gaining x y ≤ initialExcess x + (events.map (·.creditLimit)).sum := by
  sorry

theorem losses_and_hysteresis_over_interval {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    losing x y ≤ lossCorrection x events := by
  sorry

/-- No cap hypothesis: every term is a common-state field, a protocol rate, or a replayed input. -/
def derivedDrift (x y : ForkedBeaconState preset) (high : Nat)
    (events : List (BalanceEvent preset)) : Nat :=
  2 * (exitWindow (config := config) x y high + 2 * lossCorrection x events) +
    3 * (activationCarry x + initialExcess x + 2 * (events.map (·.creditLimit)).sum)

theorem quorum_drift_from_sources {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (early : y.fork < .glamsterdam) (low high : Nat)
    (starts : x.state.slot.toNat ≤ low * preset.SLOTS_PER_EPOCH.toNat)
    (call : QuorumCall (shared.append tail))
    (lower : low ≤ call.target.epoch.toNat) (upper : call.target.epoch.toNat ≤ high) :
    ∃ events, tail.balanceEvents high = .ok events ∧
      ∃ loss gain,
        Quorum.weight (effectiveWeight x.state) (activeKeys x.state) ≤
          Quorum.weight (effectiveWeight call.cached) (activeKeys call.cached) + loss ∧
        (∑ k ∈ recentKeys call.cached, (effectiveWeight call.cached k -
          Quorum.supported (activeKeys x.state) (effectiveWeight x.state) k)) ≤ gain ∧
        2 * loss + 3 * gain ≤ derivedDrift (config := config) x y high events := by
  sorry

end EthLib.Consensus.DirectSafety
