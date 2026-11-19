module

import all EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumReserve
import EthLib.Consensus.Proofs.Transition.BalanceDrift
import EthLib.Consensus.Proofs.Transition.FfgJustification
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.SlashedExit
import EthLib.Consensus.Proofs.Transition.SlashedPersistence
import EthLib.Consensus.Proofs.Transition.EpochReads
import EthLib.Consensus.Proofs.Transition.PendingConsolidations
import EthLib.Consensus.Proofs.Transition.Committees
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Penalties
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Contracts.Ledger
import EthLib.Consensus.Proofs.Transition.EpochPending
import EthLib.Consensus.Proofs.Transition.Operations
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Reserved.Operations
import EthLib.Consensus.Proofs.Transition.Block
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Whistleblower
import EthLib.Consensus.Proofs.DirectSafety.BalanceSources
import EthLib.Consensus.Proofs.Mutators
import EthLib.Consensus.Proofs.Transition.Trace
import Mathlib.Data.Nat.Notation
import EthLib.Consensus.Proofs.Transition.EpochUpdates
import EthLib.Consensus.Proofs.Transition.ForkBoundary
import EthLib.Consensus.Proofs.Transition.StateTransition
import EthLib.Consensus.Proofs.Transition.BalanceCappedWithdrawals
import EthLib.Consensus.Proofs.Transition.BranchLedger
import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Assembly
import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.ValidatorCaps
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Bound
import EthLib.Consensus.Proofs.Transition.Totality.Supply
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Ceiling

/-!
SCRATCH BASE for D-1 (not for merge): the summation of `pinReserve` at spec rev 2.5.3.
The per-term lemmas are `sorry` stubs, one owner each; `pinDrift_le_of_stubs` is closed from them.
Statements are frozen: a prover fills only its own stubs' bodies, with private helpers right above them.
It reads PinDriftBound's private lemmas by `import all` (a scratch-only waiver).
At the merge its content moves into PinDriftBound, every helper private, and this file is deleted.
-/

namespace EthLib.Consensus.Models.Network
namespace PinSum

open Base Uint64 Models DirectSafety

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- The terms of `pinReserve`, by name. -/
structure PinTerms (preset : Preset) where
  quorum : ℕ
  exiting : ℕ
  queues : ℕ
  queueDep : ℕ
  queueExit : ℕ
  exitingRise : ℕ
  exitingCredits : ℕ
  queueRise : ℕ
  reserveW : ℕ
  flagged : ℕ
  seatShortfall : ℕ
  consolidationsX : ℕ
  exitedR : ℕ
  depth : ℕ
  syncProposer : ℕ
  proposerCredit : ℕ
  exitingBands : ℕ
  pendingR : ℕ
  creditGain : ℕ
  gainHigh : Bool
  pendingRB : ℕ → Bool
  credits : ℕ
  branchR : ℕ
  late : ℕ
  syncSeats : ℕ
  rise : ℕ → ℕ
  fall : ℕ → ℕ
  positions : Finset ℕ
  current : ℕ → Bool
  joining : ℕ
  joinRise : ℕ
  exitingB : ℕ → Bool
  lateB : ℕ → Bool
  exitedRB : ℕ → Bool
  slashedR : ℕ
  slashedRB : ℕ → Bool
  tight : Bool
  queueKeys : ℕ
  queueWindow : ℕ
  gainRateMax : ℕ
  exitFloor : ℕ
  lowKeys : ℕ
  lowB : ℕ → Bool
  lowEB : ℕ → ℕ
  newKeySeats : ℕ
  newKeySlack : ℕ
  newKeyFloor : ℕ

/-- `pinReserve` as the sum of its named terms, with the code's weights. -/
def PinTerms.total (t : PinTerms preset) : ℕ :=
  t.quorum + (3 * t.exiting + t.queues + t.credits + t.branchR + t.late +
    t.syncSeats + (∑ i ∈ t.positions with t.current i = true, t.rise i) + t.joinRise +
    3 * (∑ i ∈ t.positions with t.current i = true, t.fall i) +
    3 * t.exitingRise + t.exitingCredits + t.exitingBands + t.queueRise + t.reserveW + t.flagged +
    t.seatShortfall + (33 * t.consolidationsX + 9) / 10 + t.exitedR + t.pendingR + t.creditGain)

/-- A verbatim copy of `pinReserve`'s lets (spec rev 2.5.3), returning the named terms. -/
def pinTerms (config : Config) (state ancestor finalizedState : BeaconState preset fork) :
    PinTerms preset :=
  let epoch := getCurrentEpoch state
  let inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  let slots := preset.SLOTS_PER_EPOCH.toNat
  let p := parameters preset fork
  let positions := Finset.range state.validators.data.size
  let validator (i : ℕ) := state.validators.data[i]?
  let effective (i : ℕ) := balanceAt state i
  let actual (i : ℕ) := ((state.balances.data[i]?).map (·.toNat)).getD 0
  let current (i : ℕ) := isActiveAt state epoch i
  let before (i : ℕ) := isActiveAt state (getPreviousEpoch state) i
  let upcoming (i : ℕ) := isActiveAt state (epoch + 1) i
  let slashed (i : ℕ) := ((validator i).map (·.slashed)).getD false
  let cap (i : ℕ) :=
    ((validator i).map fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat).getD 0
  let capMax := preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
  let finalized := ancestor.finalizedCheckpoint.epoch.toNat
  let depth := epoch.toNat + 2 - finalized
  let tight := decide (depth ≤ 1 + preset.MAX_SEED_LOOKAHEAD.toNat)
  let recentSlashing (i : ℕ) := (validator i).any fun v =>
    decide (finalized + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤ v.withdrawableEpoch.toNat)
  let exiting := ∑ i ∈ positions with (before i || current i) = true ∧
      (slashed i = false ∨ recentSlashing i = true) ∧
      ((validator i).map fun v => decide (v.exitEpoch.toNat ≤ epoch.toNat + 1)).getD false = true,
    effective i
  let totalGwei := (getTotalActiveBalance state).toOption.getD 0
  let total := totalGwei.toNat
  -- The rates are read at a quarter of the call's total.
  --
  -- A counting state that keeps that much has a base reward per increment at most twice this one.
  let quarter := if 18 * inc ≤ total then totalGwei / 4
    else preset.EFFECTIVE_BALANCE_INCREMENT / 5
  let perIncrement := ((getBaseRewardPerIncrement preset quarter).toOption.getD 0).toNat
  let base (i : ℕ) := effective i / inc * perIncrement
  let depositChurn := config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat
  -- The exit and consolidation churns are bounded at three halves of the call's total.
  --
  -- A counting state on another branch can spend churn at a total up to that much.
  --
  -- They follow `exitChurnLimit` and `getConsolidationChurnLimit` on natural numbers.
  --
  -- They do not model the error branch of those reads.
  --
  -- `wide` is a natural-number bound on another branch's total, not a copy of a read.
  --
  -- It holds within the band of totals that the producer of the pin premise assumes.
  let wide := 3 * total / 2
  let round (amount : ℕ) := amount - amount % inc
  let balanceChurn := round (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
    (wide / config.CHURN_LIMIT_QUOTIENT.toNat))
  let activationExitChurn :=
    min config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat balanceChurn
  let exitChurn := if .glamsterdam ≤ fork then
      round (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
        (wide / config.CHURN_LIMIT_QUOTIENT_GLOAS.toNat))
    else activationExitChurn
  let consolidationChurn := if .glamsterdam ≤ fork then
      round (wide / config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT.toNat)
    else balanceChurn - activationExitChurn
  let consolidationCarry := max (if electra : .pectra ≤ fork then
      (finalizedState.consolidationBalanceToConsume electra).toNat else 0) consolidationChurn
  let exitCarry := max capMax depositChurn
  let depthFin := epoch.toNat + 2 - (getCurrentEpoch finalizedState).toNat
  let depositCarry := if electra : .pectra ≤ fork then
      (finalizedState.depositBalanceToConsume electra).toNat else 0
  let queueDep := 3 * (depthFin * depositChurn + depositCarry)
  let queueExit := if tight then 0 else
    3 * (depth * (exitChurn + consolidationChurn) + exitCarry + consolidationCarry)
  let queues := queueDep + queueExit
  -- A sync seat's reward is bounded by its envelope at three halves of the call's total.
  --
  -- The integer reward is not monotone in the total, and the envelope is.
  --
  -- `div_mul_div_sqrt_le` bounds the reward of any total up to that much by it.
  let syncEnvelope := preset.BASE_REWARD_FACTOR.toNat * (Nat.sqrt (3 * total / 2) + 2) *
    SYNC_REWARD_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat / slots / preset.SYNC_COMMITTEE_SIZE.toNat
  -- The inactivity score is read at the finalized block's state, with depth from its epoch.
  --
  -- That state lies on every branch, and a score rises by at most the bias per epoch on any.
  --
  -- So this bounds the score of a counting state, whose score can rise while the call's falls.
  let scoreFin (i : ℕ) := if altair : .altair ≤ fork then
      (((finalizedState.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0
  -- Sync-seat penalties are charged in aggregate, by the sync-seat terms, not per key.
  let leakAt (eb : ℕ) (i : ℕ) := 2 * (eb / inc * perIncrement) +
    eb * (scoreFin i + depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
      (config.INACTIVITY_SCORE_BIAS.toNat * p.INACTIVITY_PENALTY_QUOTIENT.toNat)
  let partialsR (i : ℕ) := if electra : .pectra ≤ fork then
      (((state.pendingPartialWithdrawals electra).data.toList.filter fun w =>
        w.validatorIndex.toNat = i ∧ w.withdrawableEpoch.toNat ≤ epoch.toNat + 1).map
          (·.amount.toNat)).sum
    else 0
  let partialsX (i : ℕ) := if electra : .pectra ≤ fork then
      (((finalizedState.pendingPartialWithdrawals electra).data.toList.filter fun w =>
        w.validatorIndex.toNat = i ∧ w.withdrawableEpoch.toNat ≤ epoch.toNat + 1).map
          (·.amount.toNat)).sum
    else 0
  -- The rates are read at a computed envelope of the key's effective balance on any branch.
  --
  -- That is at least its effective balance here and at the finalized block's state.
  --
  -- A key can rise by its leak at the cap and its partials, then by a band, up to its cap.
  let finEB (i : ℕ) := balanceAt finalizedState i
  let ebUp (i : ℕ) :=
    let top := actual i + depthFin * leakAt (cap i) i + (partialsX i - partialsR i) +
      preset.downwardBand + inc - 1
    max (max (effective i) (finEB i)) (min (cap i) (top - top % inc))
  let leak (i : ℕ) := leakAt (ebUp i) i
  let gainRate (i : ℕ) := ebUp i / inc * perIncrement *
    (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat
  -- A partial due by the next epoch was queued at least `partialDelay` epochs before it.
  --
  -- Within that depth it predates finality and sits in the queue of the finalized block's state.
  let partialDelay := config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  let partialsDue (i : ℕ) := max (partialsX i) (partialsR i)
  -- Deeper than `partialDelay` from the finalized block's state, a key can fall to nothing.
  --
  -- A partial requested after that state can then be paid on a branch and sit in no queue read
  -- here, so its whole balance is charged.
  let actualFin (i : ℕ) := ((finalizedState.balances.data[i]?).map (·.toNat)).getD 0
  let fall (i : ℕ) := if depthFin ≤ partialDelay then
      let low := min (actualFin i) (cap i) - (depthFin * (leak i + gainRate i) + partialsDue i)
      let floorC := if ebUp i ≤ low + preset.downwardBand then finEB i
        else min (finEB i) (low - low % inc)
      effective i - floorC
    else effective i
  -- Gains compound across the window, so the rise reads the gain at eleven tenths, rounded up.
  let gainScaled (i : ℕ) := (11 * gainRate i + 9) / 10
  let capFor (i : ℕ) :=
    if depth * gainScaled i < inc ∧ 11 * depth * gainRate i < ebUp i then cap i else capMax
  let rise (i : ℕ) :=
    let high := actual i + depthFin * (gainScaled i + leak i) + (partialsX i - partialsR i)
    -- Deeper than `partialDelay`, the call's branch can pay partials that neither queue holds.
    --
    -- So the rise is the key's whole headroom.
    --
    -- It is too once eleven times the gain over the depth reaches that bound on the key's balance.
    if depthFin ≤ partialDelay then
      if 11 * depth * gainRate i ≥ ebUp i then capFor i - effective i
      else
        let kept := high + preset.downwardBand
        min (capFor i) (min (kept - kept % inc) (max (finEB i) (high - high % inc))) - effective i
    else capFor i - effective i
  -- This follows `syncProposerReward` on natural numbers, at the envelope.
  --
  -- It is a bound on the reward, not a read.
  let syncProposer := slots * preset.SYNC_COMMITTEE_SIZE.toNat *
    (syncEnvelope * PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat))
  let proposerCredit :=
    (∑ i ∈ positions with (before i || current i || upcoming i) = true, base i) +
    syncProposer
  -- The slashable keys of the window that the quorum reserve's whistleblower term leaves out.
  --
  -- Those are keys active from the next epoch, or withdrawable after the finalized epoch.
  --
  -- With that term, the allowance covers one slashing credit of each key, and the rises.
  let whistleblowerExtra := ((∑ i ∈ positions with (validator i).any (fun v =>
      v.activationEpoch.toNat = epoch.toNat + 1 ||
        (decide (finalized < v.withdrawableEpoch.toNat) &&
          decide (v.withdrawableEpoch.toNat ≤ epoch.toNat))), effective i) +
      ∑ i ∈ positions with current i = true, rise i) /
    p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  -- Slashings on the call's branch after the finalized epoch, which the other branch can lack.
  --
  -- A slashing sets the withdrawable epoch at least `EPOCHS_PER_SLASHINGS_VECTOR` later.
  let whistleblowerR := (∑ i ∈ positions with slashed i = true ∧ recentSlashing i = true,
      effective i) / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  let slashedR := (positions.filter fun i => slashed i = true ∧ recentSlashing i = true).card
  let gainRateMax := capMax / inc * perIncrement *
    (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat
  let late := if tight then 0 else
    ∑ i ∈ positions with (validator i).any (fun v =>
      decide (v.activationEligibilityEpoch.toNat ≤ epoch.toNat) &&
        decide (finalized + preset.MAX_SEED_LOOKAHEAD.toNat < v.activationEpoch.toNat)),
      (3 * effective i + rise i)
  let period := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat
  -- Every seat of every sync committee in the window counts, at the seat's envelope.
  --
  -- The window can include the call's previous period, which its state does not store.
  --
  -- Both branches can credit and debit those seats, so they count twice.
  let syncSeats := 3 * (2 * depth * slots * preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope)
  let due := if electra : .pectra ≤ fork then
      (state.pendingConsolidations electra).data.toList.filter fun c =>
        ((validator c.sourceIndex.toNat).map fun v =>
          v.slashed || decide (v.withdrawableEpoch ≤ epoch + 1)).getD false
    else []
  let depositRecipients := preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat
  let creditedKeys := depth * slots + (depth / period + 2) * preset.SYNC_COMMITTEE_SIZE.toNat +
    depth * depositRecipients + due.length
  -- The credits are scaled by eleven tenths, rounded up, for the gains they compound.
  --
  -- The band of each credited key is not scaled.
  let credits :=
    (11 * (depth * proposerCredit + depositCarry + depthFin * depositChurn +
      whistleblowerExtra) + 9) / 10 +
      creditedKeys * preset.upwardBand
  -- Each key the call's branch credits or debits can move by a rounding step and a band.
  --
  -- The keys are the window's proposers and deposit recipients.
  --
  -- They also hold the sync seats of each period from the finalized epoch to the next epoch.
  --
  -- Each period crossing adds one more set of seats.
  let roundedKeys := depth * slots + depth * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat +
    preset.SYNC_COMMITTEE_SIZE.toNat *
      (((epoch.toNat + 1) / period - finalized / period + 1) + depth / period)
  -- The rounding is weighted 3 exactly once, by the `3 *` of this branch term.
  let branchR := 3 * (whistleblowerR + inc * slashedR + depth * proposerCredit +
    (inc + preset.downwardBand - 1) * roundedKeys)
  -- A key previous-epoch-only in a counting state weighs three times there, at its balance there.
  --
  -- `exiting` reads it here, so its rise since the split also weighs three times.
  --
  -- That rise is its gains, the call's branch's penalties and the other branch's credits.
  --
  -- A credit raises an effective balance by at most itself plus the upward band.
  let exitingRise := ∑ i ∈ positions with (before i || current i) = true ∧
      (slashed i = false ∨ recentSlashing i = true) ∧
      ((validator i).map fun v => decide (v.exitEpoch.toNat ≤ epoch.toNat + 1)).getD false = true,
    rise i
  -- An exiting key can still be credited as a proposer or as the target of a due consolidation.
  --
  -- `credits` charges those credits once at eleven tenths and their bands once.
  --
  -- These charge them twice more, also at eleven tenths, rounded up.
  let exitingCredits := (22 * (depth * proposerCredit) + 9) / 10
  -- A lower bound on a key's effective balance on another branch, up to the counting state.
  --
  -- It starts at the finalized block's state, which lies on every branch, and at most this one's.
  --
  -- Leak over the depth from there, partials, the band and one increment of rounding are drops.
  --
  -- A partial in that state's own epoch can be paid before it, but leaves the activation balance.
  let drop (i : ℕ) := depthFin * leak i + preset.downwardBand + inc
  let lowEB (i : ℕ) := min (min (effective i) (finEB i) - partialsDue i)
    preset.MIN_ACTIVATION_BALANCE.toNat - drop i
  -- A key can exit on the other branch with an effective balance below the ejection balance.
  --
  -- Such a key uses little churn, so each one whose `lowEB` falls below that bound is counted.
  --
  -- Every key not yet withdrawable after the finalized epoch counts.
  --
  -- Its exit here is not its exit there.
  --
  -- A key not active by this epoch here, or created on the other branch, activates there only
  -- with at least the activation balance, which it keeps until then.
  --
  -- No lemma here proves yet that it keeps at least `newKeyFloor` from its activation, less its
  -- own sync-seat debits and pending partial payments.
  let newKeyFloor := 2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
    preset.MAX_EFFECTIVE_BALANCE.toNat / p.MIN_SLASHING_PENALTY_QUOTIENT.toNat -
      preset.downwardBand - inc
  let exitFloor := max 1 (min (config.EJECTION_BALANCE.toNat - inc) newKeyFloor)
  let newKeySlack := newKeyFloor - exitFloor
  let lowKeys := (positions.filter fun i =>
    (validator i).any (fun v => decide (finalized < v.withdrawableEpoch.toNat) &&
      decide (v.activationEpoch.toNat ≤ epoch.toNat)) ∧
      lowEB i < newKeyFloor).card
  -- Outside the tight window, keys can start to exit on the other branch.
  --
  -- The queues admit at most this many keys at the ejection balance less an increment each.
  --
  -- The `+ 2` counts one key at each end of the window that the churn covers only in part.
  --
  -- `lowKeys` adds every key whose effective balance can fall below that.
  --
  -- After an exit starts, the key's proposer and due-consolidation credits are in `exitingCredits`.
  --
  -- Its whistleblower credits are in `reserveW`, `flagged` and the drift's slashed keys.
  let newKeySeats := depthFin * slots * preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope /
    max 1 newKeySlack
  let queueKeys := (depth * (exitChurn + consolidationChurn) + exitCarry + consolidationCarry) /
    exitFloor + 2 + lowKeys + newKeySeats
  -- The largest gain rate of one key, its gain rate at the largest effective balance.
  let exitingCount := (positions.filter fun i => (before i || current i) = true ∧
      (slashed i = false ∨ recentSlashing i = true) ∧
      ((validator i).map fun v =>
        decide (v.exitEpoch.toNat ≤ epoch.toNat + 1)).getD false = true).card
  let exitingBands := 2 * (exitingCount + queueKeys) * preset.upwardBand
  let queueRise := if tight then 0 else
    3 * queueKeys * (preset.upwardBand + depth * gainRateMax)
  -- A key slashed on another branch credits its whistleblower, the block's proposer.
  --
  -- A key still active there is meant to pay three times that reward from its own balance.
  --
  -- A key that has exited there by then has no such balance in the count, so it is charged here.
  --
  -- Those are the keys whose exit the call reads.
  --
  -- Outside the tight window, they include the keys that the queues let exit on the other branch.
  let exitedSlashable := ∑ i ∈ positions with slashed i = false ∧
      ((validator i).map fun v => decide (v.exitEpoch.toNat ≤ epoch.toNat + 1)).getD false = true ∧
      (validator i).any (fun v => decide (finalized < v.withdrawableEpoch.toNat)),
    (effective i + rise i)
  let reserveW := 3 * (exitedSlashable + (if tight then 0 else
      depth * (exitChurn + consolidationChurn) + exitCarry + consolidationCarry +
        queueKeys * (preset.upwardBand + depth * gainRateMax))) /
    p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  -- A key active there is meant to pay for its reward unless its effective balance can be low.
  --
  -- `lowEB` bounds that balance from below, before the slashing penalty and sync-seat debits.
  --
  -- A key that fails the test is charged its reward three times.
  let slashable (i : ℕ) := slashed i = false ∧ (validator i).any (fun v =>
    decide (v.activationEpoch.toNat ≤ epoch.toNat + 1) &&
      decide (finalized < v.withdrawableEpoch.toNat))
  -- The reward is read at `ebUp`.
  let flagged := ∑ i ∈ positions with slashable i ∧
      2 * (lowEB i - ebUp i / p.MIN_SLASHING_PENALTY_QUOTIENT.toNat) <
        3 * (ebUp i / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat),
    3 * (ebUp i / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat)
  -- No key's sync-seat debits are bounded from what the call reads, so they are charged together.
  --
  -- Twice the debits of every seat in the window covers what they take from the test.
  let seatShortfall := 2 * (depth * slots * preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope)
  let consolidationsX := if depthFin ≤ partialDelay then
      (if electra : .pectra ≤ fork then
        ((((finalizedState.pendingConsolidations electra).data.toList.filterMap fun c =>
          finalizedState.validators.data[c.sourceIndex.toNat]?).filter fun v =>
            !v.slashed && decide (v.withdrawableEpoch.toNat ≤ epoch.toNat + 1)).map fun v =>
              (withdrawalMaxEffectiveBalance preset fork v).toNat).sum
      else 0)
    else 0
  let exitedR := ∑ i ∈ positions with (validator i).any (fun v =>
      decide (finalized + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ v.exitEpoch.toNat) &&
        decide (v.exitEpoch.toNat + 1 ≤ epoch.toNat)),
    (effective i + rise i)
  let consolidationGain := consolidationsX / inc * perIncrement *
    (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat
  let otherCredits := 3 * (2 * ((∑ i ∈ positions, ebUp i) +
        depthFin * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat * capMax +
        consolidationsX + depth * proposerCredit +
        depth * slots * preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope) /
          p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
      depth * slots * preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope + depth * syncProposer)
  let otherGain := otherCredits / inc * perIncrement *
    (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat
  let creditGain := if 11 * depth * gainRateMax < capMax
    then (33 * depth * consolidationGain + 11 * depth * otherGain + 9) / 10
    else depthFin * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat * capMax
  let pendingR := if tight then 0 else
    ∑ i ∈ positions with (validator i).any (fun v =>
      decide (epoch.toNat < v.activationEligibilityEpoch.toNat) &&
        v.activationEpoch == FAR_FUTURE_EPOCH), (effective i + rise i)
  { quorum := quorumReserve config state ancestor, exiting, queues, queueDep, queueExit, credits,
    branchR, late, syncSeats, rise, fall, positions, current, exitingRise, exitingCredits,
    queueRise, reserveW, flagged, seatShortfall, consolidationsX, exitedR, depth, syncProposer,
    proposerCredit, exitingBands, pendingR, creditGain,
    gainHigh := !decide (11 * depth * gainRateMax < capMax),
    pendingRB := fun i => (validator i).any (fun v =>
      decide (epoch.toNat < v.activationEligibilityEpoch.toNat) &&
        v.activationEpoch == FAR_FUTURE_EPOCH),
    joining := ∑ i ∈ positions with current i = false ∧ upcoming i = true, effective i,
    joinRise := ∑ i ∈ positions with current i = false ∧ upcoming i = true, rise i,
    exitingB := fun i => decide ((before i || current i) = true ∧
      (slashed i = false ∨ recentSlashing i = true) ∧
      ((validator i).map fun v => decide (v.exitEpoch.toNat ≤ epoch.toNat + 1)).getD false = true),
    lateB := fun i => (validator i).any (fun v =>
      decide (v.activationEligibilityEpoch.toNat ≤ epoch.toNat) &&
        decide (finalized + preset.MAX_SEED_LOOKAHEAD.toNat < v.activationEpoch.toNat)),
    exitedRB := fun i => (validator i).any (fun v =>
      decide (finalized + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ v.exitEpoch.toNat) &&
        decide (v.exitEpoch.toNat + 1 ≤ epoch.toNat)),
    slashedR,
    slashedRB := fun i => decide (slashed i = true ∧ recentSlashing i = true),
    tight, queueKeys,
    queueWindow := depth * (exitChurn + consolidationChurn) + exitCarry + consolidationCarry,
    gainRateMax, exitFloor, lowKeys,
    lowB := fun i => decide ((validator i).any (fun v =>
      decide (finalized < v.withdrawableEpoch.toNat) &&
        decide (v.activationEpoch.toNat ≤ epoch.toNat)) ∧ lowEB i < newKeyFloor),
    lowEB, newKeySeats, newKeySlack, newKeyFloor }
/-- The copy is faithful: the named terms sum to `pinReserve`. -/
theorem pinReserve_eq_total (config : Config) (state ancestor finalizedState : BeaconState preset fork) :
    pinReserve config state ancestor finalizedState =
      (pinTerms config state ancestor finalizedState).total := rfl

/-- `exitedRB` is the filter of `exitedR`: the keys whose exit started on this branch after the split.-/
theorem exitedR_eq (config : Config) (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).exitedR =
      ∑ i ∈ (pinTerms config state ancestor finalizedState).positions with
        (pinTerms config state ancestor finalizedState).exitedRB i = true,
        (balanceAt state i + (pinTerms config state ancestor finalizedState).rise i) := rfl

/-- `slashedRB` is the filter of `slashedR`.

They are the keys slashed on this branch after the finalized epoch. -/
theorem slashedR_eq (config : Config) (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).slashedR =
      ((pinTerms config state ancestor finalizedState).positions.filter fun i =>
        (pinTerms config state ancestor finalizedState).slashedRB i = true).card := rfl

/-- The copy splits `queues` into its deposit part and its exit and consolidation part. -/
theorem queues_split (config : Config) (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).queues =
      (pinTerms config state ancestor finalizedState).queueDep +
        (pinTerms config state ancestor finalizedState).queueExit := rfl

/-- `queueRise` charges each key the queues let exit, at a band and the largest gain rate. -/
theorem queueRise_unfold (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).queueRise =
      if (pinTerms config state ancestor finalizedState).tight then 0 else
        3 * (pinTerms config state ancestor finalizedState).queueKeys *
          (preset.upwardBand + (pinTerms config state ancestor finalizedState).depth *
            (pinTerms config state ancestor finalizedState).gainRateMax) := rfl

/-- `queueKeys` counts the window's churn by `exitFloor`, the ends, the low keys and new keys. -/
theorem queueKeys_unfold (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).queueKeys =
      (pinTerms config state ancestor finalizedState).queueWindow /
          (pinTerms config state ancestor finalizedState).exitFloor + 2 +
        (pinTerms config state ancestor finalizedState).lowKeys +
        (pinTerms config state ancestor finalizedState).newKeySeats := rfl

/-- `lowB` is the filter of `lowKeys`. -/
theorem lowKeys_eq (config : Config) (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).lowKeys =
      ((pinTerms config state ancestor finalizedState).positions.filter fun i =>
        (pinTerms config state ancestor finalizedState).lowB i = true).card := rfl

/-! ## D-1's setting -/

/-- D-1's setting, as D-2 supplies it (the call's own-epoch runs are left out: they feed
`quorumReserve`, which this check uses only for `joining`). -/
structure Setting (config : Config) (checks : SignatureChecks) (g : ForkedBeaconState preset)
    (split fin pulled anc counted : BeaconState preset fork) (V : Finset ValidatorIndex) : Prop where
  genesis : Genesis config checks g
  toFin : Nonempty (Run config checks g ⟨fork, fin⟩)
  fromFin : Nonempty (Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
  toPulled : Nonempty (Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
  toCounted : Nonempty (Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
  early : fork < .glamsterdam
  fulu : .fusaka ≤ fork
  bands : preset.IncrementWithinUpwardBand
  caps : CapOrder preset
  window : preset.SeedLookaheadAtLeastThree
  parameters : DirectSafety.Parameters preset
  aligned : MaxEffectiveBalancesAligned preset
  twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat
  delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  shallow : (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat ≤
    config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  pulledTotal : ∃ t, getTotalActiveBalance pulled = .ok t
  room : 2 ^ 32 ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat
  below : preset.downwardBand < preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  guard : DirectSafety.Apriori.aprioriGuardAt config ⟨fork, fin⟩ (getCurrentEpoch pulled).toNat
  finalized : anc.finalizedCheckpoint.epoch ≤ getCurrentEpoch split
  called : getCurrentEpoch split ≤ getCurrentEpoch pulled
  later : getCurrentEpoch pulled ≤ getCurrentEpoch counted
  near : (getCurrentEpoch counted).toNat ≤ (getCurrentEpoch pulled).toNat + 1
  voting : ∀ v ∈ V, v ∈ activeVoters pulled ∧ (slashedFlagAt counted v.toNat).getD false = false

/-! ## Flows of the two branches -/

/-- The credit that one balance event gives to the key at position `i`.

This is `keyCredit` of the exiting-credit lemmas, verbatim. -/
def keyCredit (i : ℕ) (e : BalanceEvent preset) : ℕ :=
  actualBalanceAt e.after i - actualBalanceAt e.before i

/-- The deposits applied to the key on R's branch, over the replayed events of the run from the
split. -/
def credDepR (events : List (BalanceEvent preset)) (v : ℕ) : ℕ :=
  ((events.filter (·.source = .deposits)).map (keyCredit v)).sum

/-- The consolidation credits to the key over the replayed events of a run.

It is the quantity that `Run.consolidation_credits_le_X_targets` bounds, summed over targets. -/
def consAmt (events : List (BalanceEvent preset)) (v : ℕ) : ℕ :=
  ((events.filter (·.source = .consolidations)).map (keyCredit v)).sum

/-! ### The C-side credits of a key, read from the run (prover D)

They are read from the run itself, as E's `riseQ` is.

A block step's `.rewards` events are its proposer's credits.

A slot step's `.rewards` events are the epoch's flag rewards, so a slot step counts only the sources
named below.

Sync events are in `syncF` with the seats. -/

/-- The credits to the key in one step, from the sources that count at that kind of step. -/
def stepCredit (blockP slotP : BalanceSource → Bool) (v : ℕ) {x y : ForkedBeaconState preset}
    (step : Step config checks x y) : ℕ :=
  let events := step.balanceEvents.toOption.getD []
  match step with
  | .slot _ => ((events.filter (slotP ·.source)).map (keyCredit v)).sum
  | .block .. => ((events.filter (blockP ·.source)).map (keyCredit v)).sum

/-- The credits to the key over a run, and the number of block steps that credit it.

The steps count from the one whose start epoch is at most `high + 1`, as in `Run.balanceEvents`. -/
def creditScan (blockP slotP : BalanceSource → Bool) (v high : ℕ) {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → ℕ × ℕ
  | _, .nil => (0, 0)
  | _, .snoc (middle := m) pre step =>
    let before := creditScan blockP slotP v high pre
    if (getCurrentEpoch m.state).toNat ≤ high + 1 then
      let credit := stepCredit blockP slotP v step
      (before.1 + credit, before.2 + match step with
        | .block .. => if 0 < credit then 1 else 0
        | .slot _ => 0)
    else before

/-- The net credits to the key in the block steps of a run.

A block step counts the rise of the key's balance across the whole step.

A credit that the same step takes back counts for nothing.

The steps count from the one whose start epoch is at most `high + 1`, as in `Run.balanceEvents`. -/
def netScan (v high : ℕ) {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → ℕ
  | _, .nil => 0
  | y, .snoc (middle := m) pre step =>
    if (getCurrentEpoch m.state).toNat ≤ high + 1 then
      netScan v high pre + match step with
        | .block .. => actualBalanceAt y v - actualBalanceAt m v
        | .slot _ => 0
    else netScan v high pre

/-- Proposer and due-consolidation credits to the key on C's branch since the split.

The rounding slack of a credited key is `bandC`, once for each key.

The consolidation bands are not here: `bud_consolidations` charges them. -/
def propC {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high v : ℕ) : ℕ :=
  (creditScan (fun s => decide (s = .rewards ∨ s = .consolidations))
    (fun s => decide (s = .consolidations)) v high tail).1

/-- Proposer credits to the key on C's branch since the split, without the consolidation credits.

A credited stake compounds by at most a tenth, which the stubs charge as `propN / 10`.

The consolidation credits are under `consolidationsX`, so their compounding is not charged here. -/
def propN {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high v : ℕ) : ℕ :=
  (creditScan (fun s => decide (s = .rewards)) (fun _ => false) v high tail).1

/-- Proposer and deposit credits to the key on C's branch since the split.

They are `credC` without its consolidation credits.

A credited stake compounds by at most a tenth, which the stubs charge as `credN / 10`.

The tenth is rounded down, so that the tenths of several keys add up to at most the tenth of their sum. -/
def credN {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high v : ℕ) : ℕ :=
  (creditScan (fun s => decide (s = .rewards)) (fun s => decide (s = .deposits)) v high tail).1

/-- Non-attestation credits to the key on C's branch since the split, whistleblower and sync credits
excluded: proposer, deposits applied and consolidations.

The rounding slack of a credited key is `bandC`, once for each key. -/
def credC {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high v : ℕ) : ℕ :=
  (creditScan (fun s => decide (s = .rewards ∨ s = .consolidations))
    (fun s => decide (s = .consolidations ∨ s = .deposits)) v high tail).1

/-- The block credits to the key on R's branch since the split: proposer and whistleblower credits.

A slot step's credits are not here: `fall` reads the epoch rewards at its gain rate.

A key that gains in a block step or by a deposit moves by one more rounding step.

The band comes with the step.

A block step that nets the key no credit cannot push its effective balance up.

That step is `inc + downwardBand - 1`, the one that `branchR` charges for each of its keys. -/
def credR {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high v : ℕ) : ℕ :=
  (creditScan (fun s => decide (s ≠ .deposits ∧ s ≠ .sync ∧ s ≠ .consolidations))
    (fun _ => false) v high tail).1 +
    if netScan v high tail = 0 ∧ (creditScan (fun _ => false) (fun s => decide (s = .deposits))
        v high tail).1 = 0 then 0
    else preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1

/-- Whistleblower credits to the key on C's branch since the split.

A whistleblower credit lands in the block of the proposer's own slot.

The rounding slack of a credited key is `bandC`, once for each key.

A slot step records only debits for a slashing. -/
def whistC {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high v : ℕ) : ℕ :=
  (creditScan (fun s => decide (s = .slashings)) (fun _ => false) v high tail).1

/-- The entries of X's queue of pending consolidations that name a target in `T` and apply by
`high + 1`.

It is the set of `Run.consolidation_credits_le_X_targets`, counted instead of summed. -/
def dueAt (X : BeaconState preset fork) (high : ℕ) (T : Finset ValidatorIndex) : ℕ :=
  if electra : .pectra ≤ fork then
    ((((X.pendingConsolidations electra).data.toList.filter fun c =>
        decide (c.targetIndex ∈ T)).filterMap fun c =>
      X.validators.data[c.sourceIndex.toNat]?).filter fun v =>
        !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)).length
  else 0

/-- The debit that one balance event takes from the key at position `i`. -/
def keyDebit (i : ℕ) (e : BalanceEvent preset) : ℕ :=
  actualBalanceAt e.before i - actualBalanceAt e.after i

/-- The sync-seat movement of the key over the replayed events of one run.

It is the key's credits and debits of the sync aggregates: a seat's debit, a seat's reward, and the
proposer's share of it.

The caller adds it over the two runs from the split, since both branches credit and debit seats. -/
def syncF (events : List (BalanceEvent preset)) (v : ℕ) : ℕ :=
  ((events.filter (·.source = .sync)).map (keyCredit v)).sum +
    ((events.filter (·.source = .sync)).map (keyDebit v)).sum

/-- One increment for a key slashed on R's branch after the finalized epoch.

The initial penalty is at most one increment, and `branchR` charges `inc` for each such key. -/
def slashR (t : PinTerms preset) (i : ℕ) : ℕ :=
  if t.slashedRB i = true then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0

/-- The rounding slack of a key with any C-side credit, once for each key.

The credits are those of a block step that nets the key a rise, and an applied deposit.

A proposer reward, a whistleblower reward and a sync reward are block credits.

A consolidation credit is not here: `bud_consolidations` charges its band for each entry.

`credits` charges `upwardBand` for each credited key. -/
def bandC {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high v : ℕ) : ℕ :=
  if 0 < netScan v high tail +
      (creditScan (fun _ => false) (fun s => decide (s = .deposits)) v high tail).1 then
    preset.upwardBand else 0

/-- The rounding slack of a key whose balance on R's branch took a sync debit that `high` omits.

It is the step of `credR`, one increment and the downward band less one.

`branchR` charges that step for each of its keys. -/
def bandR (events : List (BalanceEvent preset)) (v : ℕ) : ℕ :=
  if 0 < ((events.filter (·.source = .sync)).map (keyDebit v)).sum then
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1 else 0

/-- The key's effective balance when its exit starts on a run, or 0.

It is the amount of the key's departure charge, which reads the effective balance at the exit call.

A key has a charge only if its exit was not assigned at the run's start.

Only a charge whose exit epoch is at most the run's last epoch counts. -/
def exitQ {x y : ForkedBeaconState preset} (tail : Run config checks x y) (v : ℕ) : ℕ :=
  ((tail.departureCharges.find? fun c =>
      c.index == v && decide (c.epoch ≤ (getCurrentEpoch y.state).toNat)).map (·.amount)).getD 0

/-- The epoch-pass reward credits to the key in one step.

A slot step's events are those of its epoch pass and its upgrades, so its `.rewards` events are the
epoch's rewards. A block step has none counted: its proposer credits are charged elsewhere. -/
def epochRewards (v : ℕ) {x y : ForkedBeaconState preset} (step : Step config checks x y) : ℕ :=
  match step with
  | .slot ok =>
    ((((Step.slot (config := config) (checks := checks) ok).balanceEvents.toOption.getD []).filter
      (·.source = .rewards)).map (keyCredit v)).sum
  | .block .. => 0

/-- Whether a run has the key's departure charge, and the epoch rewards of the steps after it.

The steps count from the one whose start epoch is at most `high + 1`, as in `Run.balanceEvents`. -/
def riseScan (v high : ℕ) {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → Bool × ℕ
  | _, .nil => (false, 0)
  | _, .snoc (middle := m) pre step =>
    let before := riseScan v high pre
    (before.1 || step.departureCharges.any (·.index == v),
      if before.1 = true ∧ (getCurrentEpoch m.state).toNat ≤ high + 1 then
        before.2 + epochRewards v step
      else before.2)

/-- The key's rise on a run after its exit starts there.

It is one upward band for the rise of the effective balance beyond the key's epoch rewards, plus
those rewards over the slot steps that come after the step with its departure charge.

It is 0 for a key whose exit does not start on the run. -/
def riseQ {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high v : ℕ) : ℕ :=
  if (riseScan v high tail).1 = true then preset.upwardBand + (riseScan v high tail).2 else 0

/-! ### The keys that a run credits -/

/-- The net credits to a key in the block steps of a run, after one more step. -/
private theorem netScan_snoc (v high : ℕ) {x m y : ForkedBeaconState preset}
    (pre : Run config checks x m) (step : Step config checks m y) :
    netScan v high (pre.snoc step) =
      if (getCurrentEpoch m.state).toNat ≤ high + 1 then
        netScan v high pre + (match step with
          | .block .. => actualBalanceAt y v - actualBalanceAt m v
          | .slot _ => 0)
      else netScan v high pre := rfl

/-- The net credits to a key in the block steps of a run add over `append`. -/
private theorem netScan_append (v high : ℕ) {x m y : ForkedBeaconState preset}
    (pre : Run config checks x m) (post : Run config checks m y) :
    netScan v high (pre.append post) = netScan v high pre + netScan v high post := by
  induction post with
  | nil => rfl
  | snoc post step ih =>
    change netScan v high ((pre.append post).snoc step) = _
    rw [netScan_snoc, netScan_snoc, ih]
    split <;> omega

/-- A key keeps its public key at its position along a run. -/
private theorem key_persists {x y : ForkedBeaconState preset} (run : Run config checks x y)
    {i : ℕ} {w : Validator} (found : x.state.validators.data[i]? = some w) :
    ∃ w', y.state.validators.data[i]? = some w' ∧ w'.pubkey = w.pubkey :=
  validators_getElem?_of_validatorKeys_prefix
    (validatorKeys_prefix_and_distinct_of_chainSteps run.chainSteps).1 found

/-- A block step that raises the balance of a key has the key among its proposers or sync seats. -/
private theorem block_credit_keys {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) {f : Fork} {s t : BeaconState preset f}
    (engine : ExecutionEngine preset f) (signed : SignedBeaconBlock preset f)
    (due : upgradeDue config ⟨f, s⟩ = false)
    (ok : applySignedBlock config checks engine s signed true = .ok t)
    (shared : Run config checks g ⟨f, s⟩) (fulu : .fusaka ≤ f) (early : f < .glamsterdam) :
    ∃ K : Finset ℕ, K.card ≤ 1 ∧ ∀ i : ℕ,
      actualBalanceAt (⟨f, s⟩ : ForkedBeaconState preset) i <
        actualBalanceAt (⟨f, t⟩ : ForkedBeaconState preset) i →
      i ∈ K ∨ ∃ altair : .altair ≤ f, 0 < syncSeats t altair i := by
  classical
  have invariant := (run_justified_separated shared genesis).1
  have processed := (applySignedBlock_ok ok).2.1
  have same : getCurrentEpoch (⟨f, t⟩ : ForkedBeaconState preset).state =
      getCurrentEpoch (⟨f, s⟩ : ForkedBeaconState preset).state := by
    simp only [getCurrentEpoch, processBlock_slot processed]
  obtain ⟨-, creditedKeys, pc, deposit, -, creditedCard, -, rise, zeroOff, electraZero, -⟩ :=
    (Run.nil.snoc (Step.block engine signed due ok) :
        Run config checks (⟨f, s⟩ : ForkedBeaconState preset) ⟨f, t⟩).balanceCorrections_of_same_epoch
      early fulu same invariant.balancesMatch invariant.exitsOrdered
  have blocksOne : (Run.nil.snoc (Step.block engine signed due ok) :
      Run config checks (⟨f, s⟩ : ForkedBeaconState preset) ⟨f, t⟩).blockCount = 1 := rfl
  have electra : .pectra ≤ f := Nat.le_trans (by decide) fulu
  have altair : .altair ≤ f := Nat.le_trans (by decide) electra
  have hegota : f < .hegota := Nat.lt_trans early (by decide)
  have matchedT : BalancesMatch t :=
    (frame_processBlock processed).balancesMatch invariant.balancesMatch
  have limit := t.registryWithinLimit_of_lt early
  have creditedLe : creditedKeys.card ≤ 1 := by
    refine creditedCard.trans ?_
    simp [blocksOne, electra, hegota]
    have atMost : ∀ (P : Prop) (d : Decidable P), (@ite ℕ P d 0 1) ≤ 1 := fun P d => by
      cases d with
      | isTrue _ => exact Nat.zero_le _
      | isFalse _ => exact Nat.le_refl _
    exact atMost _ _
  refine ⟨creditedKeys.image UInt64.toNat, Finset.card_image_le.trans creditedLe,
    fun i increased => ?_⟩
  have inside : i < t.balances.data.size := by
    by_contra outside
    have missing : actualBalanceAt (⟨f, t⟩ : ForkedBeaconState preset) i = 0 := by
      simp [actualBalanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt outside)]
    omega
  have below : i < 2 ^ 64 := by
    have sizes := matchedT
    unfold BalancesMatch at sizes
    have registry : i < t.validators.data.size := by omega
    unfold BeaconState.RegistryWithinLimit at limit
    have bound := preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
    omega
  obtain ⟨v, hv⟩ : ∃ v : ValidatorIndex, v.toNat = i :=
    ⟨UInt64.ofNat i, UInt64.toNat_ofNat_of_lt' below⟩
  have bound := rise v
  rw [hv] at bound
  have zero := electraZero electra v
  by_cases member : v ∈ creditedKeys
  · exact .inl (Finset.mem_image.mpr ⟨v, member, hv⟩)
  · obtain ⟨pcZero, -⟩ := zeroOff v member
    refine .inr ⟨altair, ?_⟩
    by_contra none
    have seats : syncSeats t altair i = 0 := Nat.eq_zero_of_not_pos none
    dsimp only at bound
    simp [altair, seats, blocksOne] at bound
    omega

/-- The keys credited in the block steps of a run inside one period of sync committees.

A key credited by a block is a proposer, at most one for each block, or it holds a seat of the
committee that the run starts with. -/
private theorem credited_piece {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) {x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (r : Run config checks x y)
    (fulu : .fusaka ≤ x.fork) (altair : .altair ≤ x.fork) (early : y.fork < .glamsterdam)
    (high : ℕ)
    (same : (getCurrentEpoch y.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
      (getCurrentEpoch x.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) :
    ∃ B : Finset ℕ, B.card ≤ r.blockCount ∧ ∀ i, 0 < netScan i high r →
      i ∈ B ∨ ∃ w, y.state.validators.data[i]? = some w ∧
        w.pubkey ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList := by
  classical
  induction r with
  | nil => exact ⟨∅, by simp, fun i pos => (Nat.lt_irrefl 0 pos).elim⟩
  | @snoc u l pre step ih =>
    have uEarly : u.fork < .glamsterdam := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have low := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
    have up := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
    have uSame : (getCurrentEpoch u.state).toNat /
        max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
          (getCurrentEpoch x.state).toNat /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat := by
      have above := Nat.div_le_div_right
        (c := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) up
      have under := Nat.div_le_div_right
        (c := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) low
      omega
    obtain ⟨B, cardB, hB⟩ := ih uEarly uSame
    have carry : ∀ (i : ℕ) (w : Validator), u.state.validators.data[i]? = some w →
        w.pubkey ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList →
          ∃ w', l.state.validators.data[i]? = some w' ∧
            w'.pubkey ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList := by
      intro i w found mem
      obtain ⟨w', found', same'⟩ := key_persists (Run.nil.snoc step) found
      exact ⟨w', found', same' ▸ mem⟩
    cases step with
    | slot ok =>
      refine ⟨B, cardB, fun i pos => ?_⟩
      rw [netScan_snoc] at pos
      have prior : 0 < netScan i high pre := by
        split at pos
        · simpa using pos
        · exact pos
      rcases hB i prior with member | ⟨w, found, mem⟩
      · exact .inl member
      · exact .inr (carry i w found mem)
    | @block f s t engine signed due ok =>
      have fulu' : .fusaka ≤ f := Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
      obtain ⟨K, cardK, hK⟩ := block_credit_keys genesis engine signed due ok (shared.append pre)
        fulu' uEarly
      refine ⟨B ∪ K, ?_, fun i pos => ?_⟩
      · exact (Finset.card_union_le _ _).trans (Nat.add_le_add cardB cardK)
      · rw [netScan_snoc] at pos
        have either : 0 < netScan i high pre ∨
            actualBalanceAt (⟨f, s⟩ : ForkedBeaconState preset) i <
              actualBalanceAt (⟨f, t⟩ : ForkedBeaconState preset) i := by
          split at pos
          · simp only [] at pos
            omega
          · exact .inl pos
        rcases either with prior | risen
        · rcases hB i prior with member | ⟨w, found, mem⟩
          · exact .inl (Finset.mem_union_left _ member)
          · exact .inr (carry i w found mem)
        · rcases hK i risen with member | ⟨altair', seats⟩
          · exact .inl (Finset.mem_union_right _ member)
          · unfold syncSeats at seats
            obtain ⟨key, hkey⟩ := List.length_pos_iff_exists_mem.mp seats
            obtain ⟨keyMem, test⟩ := List.mem_filter.mp hkey
            obtain ⟨w, hv⟩ : ∃ w, t.validators.data[i]? = some w := by
              cases found : t.validators.data[i]? with
              | none =>
                rw [found] at test
                simp at test
              | some w => exact ⟨w, rfl⟩
            rw [hv] at test
            simp only [Option.any_some, beq_iff_eq] at test
            have committee := (Run.snoc pre (Step.block engine signed due ok)
                ).currentSyncCommittee_eq_of_same_period early same altair' altair
            refine .inr ⟨w, hv, ?_⟩
            rw [test, ← committee]
            exact keyMem


/-- The positions that hold a key of a committee are at most the size of the committee. -/
private theorem seat_positions {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) {x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (r : Run config checks x y) (altair : .altair ≤ x.fork) :
    ∃ S : Finset ℕ, S.card ≤ preset.SYNC_COMMITTEE_SIZE.toNat ∧ ∀ (i : ℕ) (w : Validator),
      y.state.validators.data[i]? = some w →
        w.pubkey ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList → i ∈ S := by
  classical
  have distinct := (shared.append r).pubkeysDistinct genesis
  let L := (x.state.currentSyncCommittee altair).value.pubkeys.toList
  refine ⟨(Finset.range y.state.validators.data.size).filter fun i =>
      ∃ w, y.state.validators.data[i]? = some w ∧ w.pubkey ∈ L, ?_, ?_⟩
  · have mapped : ((Finset.range y.state.validators.data.size).filter fun i =>
        ∃ w, y.state.validators.data[i]? = some w ∧ w.pubkey ∈ L).card ≤ L.toFinset.card := by
      refine Finset.card_le_card_of_injOn (keyAt y.state) (fun i member => ?_)
        (fun i mi j mj eq => ?_)
      · obtain ⟨w, found, mem⟩ := (Finset.mem_filter.mp member).2
        simp only [keyAt, found, Option.map_some, Option.getD_some]
        exact List.mem_toFinset.mpr mem
      · obtain ⟨w, found, -⟩ := (Finset.mem_filter.mp mi).2
        obtain ⟨w', found', -⟩ := (Finset.mem_filter.mp mj).2
        simp only [keyAt, found, found', Option.map_some, Option.getD_some] at eq
        exact distinct.index_eq found found' eq
    exact mapped.trans ((List.toFinset_card_le L).trans (by simp [L]))
  · intro i w found mem
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1,
      w, found, mem⟩

/-- A later epoch of a period is in the same period or the next one. -/
private theorem succ_div_le (a c : ℕ) : (a + 1) / c ≤ a / c + 1 := by
  rcases Nat.eq_zero_or_pos c with zero | positive
  · subst zero
    simp
  · apply Nat.div_le_of_le_mul
    have := Nat.lt_mul_div_succ a positive
    omega

/-- The keys credited in the block steps of a run, counted by the periods that it touches. -/
private theorem credited_pieces {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) {y : ForkedBeaconState preset}
    (early : y.fork < .glamsterdam) (high : ℕ) :
    ∀ (n : ℕ) {x : ForkedBeaconState preset}, Run config checks g x →
      ∀ (r : Run config checks x y), .fusaka ≤ x.fork →
    (getCurrentEpoch y.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
      (getCurrentEpoch x.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + n →
    ∃ B S : Finset ℕ, B.card ≤ r.blockCount ∧
      S.card ≤ preset.SYNC_COMMITTEE_SIZE.toNat * (n + 1) ∧
      ∀ i, 0 < netScan i high r → i ∈ B ∨ i ∈ S := by
  classical
  intro n
  induction n with
  | zero =>
    intro x shared r fulu count
    have electra : .pectra ≤ x.fork := Nat.le_trans (by decide) fulu
    have altair : .altair ≤ x.fork := Nat.le_trans (by decide) electra
    obtain ⟨B, cardB, hB⟩ := credited_piece genesis shared r fulu altair early high
      (by simpa using count)
    obtain ⟨S, cardS, hS⟩ := seat_positions genesis shared r altair
    refine ⟨B, S, cardB, by simpa using cardS, fun i pos => ?_⟩
    rcases hB i pos with member | ⟨w, found, mem⟩
    · exact .inl member
    · exact .inr (hS i w found mem)
  | succ n ih =>
    intro x shared r fulu count
    have electra : .pectra ≤ x.fork := Nat.le_trans (by decide) fulu
    have altair : .altair ≤ x.fork := Nat.le_trans (by decide) electra
    obtain ⟨m, v, pre, step, post, split, hm, hv⟩ := PinSplit.Run.split_at_flip r
      (fun z => (getCurrentEpoch x.state).toNat /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat <
        (getCurrentEpoch z.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
      (Nat.lt_irrefl _) (by omega)
    have low := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
    have up := PinSplit.ChainStep.epoch_le_succ step.chainStep
    have mSame : (getCurrentEpoch m.state).toNat /
        max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
          (getCurrentEpoch x.state).toNat /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat := by
      have under := Nat.div_le_div_right
        (c := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) low
      omega
    have vNext : (getCurrentEpoch v.state).toNat /
        max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
          (getCurrentEpoch x.state).toNat /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 1 := by
      have above := Nat.div_le_div_right
        (c := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) up
      have step' := succ_div_le (getCurrentEpoch m.state).toNat
        (max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
      omega
    have mEarly : m.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (Nat.le_trans step.chainStep.fork_le
        (fork_le_of_chainSteps post.chainSteps)) early
    have vFulu : .fusaka ≤ v.fork :=
      Nat.le_trans fulu (fork_le_of_chainSteps (pre.snoc step).chainSteps)
    obtain ⟨B₁, cardB₁, hB₁⟩ := credited_piece genesis shared pre fulu altair mEarly high
      (by simpa using mSame)
    obtain ⟨S₁, cardS₁, hS₁⟩ := seat_positions genesis shared pre altair
    obtain ⟨B₂, S₂, cardB₂, cardS₂, hB₂⟩ := ih (x := v) (shared.append (pre.snoc step)) post vFulu
      (by omega)
    -- The step leaves an epoch, so it is a slot step: a block step keeps its epoch.
    have slotStep : ∃ ok, step = Step.slot ok := by
      cases step with
      | slot ok => exact ⟨ok, rfl⟩
      | @block f before after engine signed due ok =>
        exfalso
        have same := processBlock_slot (applySignedBlock_ok ok).2.1
        have e : (getCurrentEpoch after).toNat = (getCurrentEpoch before).toNat := by
          simp only [getCurrentEpoch, same]
        have hm' : ¬ (getCurrentEpoch x.state).toNat /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat <
              (getCurrentEpoch before).toNat /
                max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat := hm
        have hv' : (getCurrentEpoch x.state).toNat /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat <
              (getCurrentEpoch after).toNat /
                max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat := hv
        rw [e] at hv'
        exact hm' hv'
    obtain ⟨ok, rfl⟩ := slotStep
    subst split
    refine ⟨B₁ ∪ B₂, S₁ ∪ S₂, ?_, ?_, fun i pos => ?_⟩
    · rw [Run.blockCount_append]
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add cardB₁ cardB₂)
    · refine (Finset.card_union_le _ _).trans ?_
      calc _ ≤ preset.SYNC_COMMITTEE_SIZE.toNat +
            preset.SYNC_COMMITTEE_SIZE.toNat * (n + 1) := Nat.add_le_add cardS₁ cardS₂
        _ = _ := by ring
    · rw [netScan_append] at pos
      by_cases first : 0 < netScan i high (pre.snoc (Step.slot ok))
      · have prior : 0 < netScan i high pre := by
          rw [netScan_snoc] at first
          split at first
          · simpa using first
          · exact first
        rcases hB₁ i prior with member | ⟨w, found, mem⟩
        · exact .inl (Finset.mem_union_left _ member)
        · exact .inr (Finset.mem_union_left _ (hS₁ i w found mem))
      · have later : 0 < netScan i high post := by omega
        rcases hB₂ i later with member | member
        · exact .inl (Finset.mem_union_right _ member)
        · exact .inr (Finset.mem_union_right _ member)

/-- The credits that a scan reads from a run, after one more step. -/
private theorem creditScan_snoc_fst (blockP slotP : BalanceSource → Bool) (v high : ℕ)
    {x m y : ForkedBeaconState preset} (pre : Run config checks x m)
    (step : Step config checks m y) :
    (creditScan blockP slotP v high (pre.snoc step)).1 =
      if (getCurrentEpoch m.state).toNat ≤ high + 1 then
        (creditScan blockP slotP v high pre).1 + stepCredit blockP slotP v step
      else (creditScan blockP slotP v high pre).1 := by
  change (if (getCurrentEpoch m.state).toNat ≤ high + 1 then
      ((creditScan blockP slotP v high pre).1 + stepCredit blockP slotP v step, _)
    else creditScan blockP slotP v high pre).1 = _
  split_ifs <;> rfl

/-- A list of at most one element has equal members. -/
private theorem list_eq_of_length_le_one {α : Type} {L : List α} (short : L.length ≤ 1) {a b : α}
    (ha : a ∈ L) (hb : b ∈ L) : a = b := by
  cases L with
  | nil => simp at ha
  | cons c rest =>
    cases rest with
    | nil =>
      rw [List.mem_singleton] at ha hb
      rw [ha, hb]
    | cons d rest => exact absurd short (by simp)

/-- The keys that a run credits by a pending-deposit pass.

An epoch pass applies at most `MAX_PENDING_DEPOSITS_PER_EPOCH` deposits, in one slot step.

So the keys are at most that many for each epoch that the run leaves. -/
private theorem credited_deposits {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) {x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (r : Run config checks x y) (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) (high : ℕ) :
    ∃ D : Finset ℕ, D.card ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
        ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) ∧
      ∀ i, 0 < (creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high r).1 →
        i ∈ D := by
  classical
  induction r with
  | nil => exact ⟨∅, by simp, fun i pos => (Nat.lt_irrefl 0 pos).elim⟩
  | @snoc u l pre step ih =>
    have uEarly : u.fork < .glamsterdam := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    obtain ⟨D, cardD, hD⟩ := ih uEarly
    have low := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
    have up := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
    -- A step that records no deposit credit leaves the set as it is.
    have keep : ∀ i, (0 < (creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high
        (pre.snoc step)).1 → 0 < (creditScan (fun _ => false)
          (fun s => decide (s = .deposits)) i high pre).1 ∨
        0 < stepCredit (fun _ => false) (fun s => decide (s = .deposits)) i step) := by
      intro i pos
      rw [creditScan_snoc_fst] at pos
      split at pos
      · omega
      · exact .inl pos
    cases step with
    | block engine signed due ok =>
      refine ⟨D, ?_, fun i pos => ?_⟩
      · exact cardD.trans (Nat.mul_le_mul_left _ (by omega))
      · rcases keep i pos with prior | here
        · exact hD i prior
        · exfalso
          have zero : stepCredit (fun _ => false) (fun s => decide (s = .deposits)) i
              (Step.block engine signed due ok : Step config checks _ _) = 0 := by
            show ((((Step.block (config := config) (checks := checks) engine signed due
              ok).balanceEvents.toOption.getD []).filter ((fun _ => false) ·.source)).map
                (keyCredit i)).sum = 0
            rw [List.filter_eq_nil_iff.mpr (fun a _ => by simp)]
            rfl
          omega
    | slot across =>
      obtain ⟨events, eventsOk⟩ :=
        (Step.slot across : Step config checks u l).balanceEvents_ok early
      by_cases any : ∃ e ∈ events, e.source = .deposits
      · obtain ⟨sites, ends, single⟩ :=
          DirectSafety.Apriori.Internal.Step.slot_deposit_site (shared.append pre) genesis across
          early delay eventsOk
        have epochNext := ends any
        obtain ⟨e0, mem0, dep0⟩ := any
        obtain ⟨electra, a, b, matched, deposited, before0, after0⟩ := sites e0 mem0 dep0
        obtain ⟨-, -, rises⟩ := pending_deposit_rises a b matched electra deposited
        refine ⟨D ∪ (Finset.range b.balances.data.size).filter fun i =>
            actualBalanceAt (⟨u.fork, a⟩ : ForkedBeaconState preset) i <
              actualBalanceAt (⟨u.fork, b⟩ : ForkedBeaconState preset) i, ?_, fun i pos => ?_⟩
        · refine (Finset.card_union_le _ _).trans ?_
          have grown := Nat.mul_le_mul_left preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat
            (show (getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat + 1 ≤
              (getCurrentEpoch l.state).toNat - (getCurrentEpoch x.state).toNat by omega)
          rw [Nat.mul_add, Nat.mul_one] at grown
          omega
        · rcases keep i pos with prior | here
          · exact Finset.mem_union_left _ (hD i prior)
          · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ?_)
            have mono : ∃ e ∈ events, e.source = .deposits ∧ 0 < keyCredit i e := by
              by_contra none
              push_neg at none
              have zero : stepCredit (fun _ => false) (fun s => decide (s = .deposits)) i
                  (Step.slot across : Step config checks u l) = 0 := by
                show (((((Step.slot (config := config) (checks := checks)
                  across).balanceEvents.toOption.getD []).filter
                    ((fun s => decide (s = .deposits)) ·.source))).map (keyCredit i)).sum = 0
                simp only [eventsOk, Except.toOption, Option.getD_some]
                exact List.sum_eq_zero fun _ member => by
                  obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
                  obtain ⟨mem, test⟩ := List.mem_filter.mp inside
                  have := none e mem (by simpa using test)
                  omega
              omega
            obtain ⟨e, mem, dep, positive⟩ := mono
            -- A slot step records one deposit event, so it is the one that the site names.
            have same : e = e0 := list_eq_of_length_le_one single
              (List.mem_filter.mpr ⟨mem, by simpa using dep⟩)
              (List.mem_filter.mpr ⟨mem0, by simpa using dep0⟩)
            subst same
            unfold keyCredit at positive
            rw [before0, after0] at positive
            refine ⟨?_, ?_⟩
            · by_contra outside
              have outside' : ¬ i < b.balances.data.size := fun h =>
                outside (Finset.mem_range.mpr h)
              have missing : actualBalanceAt (⟨u.fork, b⟩ : ForkedBeaconState preset) i = 0 := by
                simp [actualBalanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt outside')]
              omega
            · omega
      · refine ⟨D, ?_, fun i pos => ?_⟩
        · exact cardD.trans (Nat.mul_le_mul_left _ (by omega))
        · rcases keep i pos with prior | here
          · exact hD i prior
          · exfalso
            have zero : stepCredit (fun _ => false) (fun s => decide (s = .deposits)) i
                (Step.slot across : Step config checks u l) = 0 := by
              show (((((Step.slot (config := config) (checks := checks)
                across).balanceEvents.toOption.getD []).filter
                  ((fun s => decide (s = .deposits)) ·.source))).map (keyCredit i)).sum = 0
              simp only [eventsOk, Except.toOption, Option.getD_some]
              exact List.sum_eq_zero fun _ member => by
                obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
                obtain ⟨mem, test⟩ := List.mem_filter.mp inside
                exact absurd ⟨e, mem, by simpa using test⟩ any
            omega

/-- The keys that a run from the split credits.

They are at most its proposers, its seat holders and its deposit recipients.

A key counts if a block step of the run nets it a rise, or an epoch pass applies a deposit to it.

A block step has one proposer, and an epoch has at most one block for each slot.

The seat holders are those of one sync committee for each period that the run touches.

An epoch pass applies at most `MAX_PENDING_DEPOSITS_PER_EPOCH` deposits. -/
private theorem credited_keys_le (h : Setting config checks g split fin pulled anc counted V)
    {x : BeaconState preset fork} (tail : Run config checks ⟨fork, split⟩ ⟨fork, x⟩) (high : ℕ) :
    ((Finset.range x.validators.data.size).filter fun i =>
        0 < netScan i high tail +
          (creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high tail).1).card ≤
      ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat + 1) *
          (preset.SLOTS_PER_EPOCH.toNat + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) +
        preset.SYNC_COMMITTEE_SIZE.toNat *
          ((getCurrentEpoch x).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
            (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat +
              1) := by
  classical
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have shared : Run config checks g ⟨fork, split⟩ := toFin.append fromFin
  have slots := h.twoSlots
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by omega
  have low : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch x).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  have periodLe := Nat.div_le_div_right
    (c := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) low
  have periods : (getCurrentEpoch x).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
      (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat +
        ((getCurrentEpoch x).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
          (getCurrentEpoch split).toNat /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) := by omega
  obtain ⟨B, S, cardB, cardS, hBS⟩ := credited_pieces h.genesis (y := ⟨fork, x⟩) h.early high
    ((getCurrentEpoch x).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
      (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
    shared tail h.fulu periods
  obtain ⟨D, cardD, hD⟩ := credited_deposits h.genesis shared tail h.early h.delay high
  have cardD' : D.card ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
      ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat) := cardD
  have subset : ((Finset.range x.validators.data.size).filter fun i =>
        0 < netScan i high tail +
          (creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high tail).1) ⊆
      B ∪ S ∪ D := fun i member => by
    have pos := (Finset.mem_filter.mp member).2
    by_cases net : 0 < netScan i high tail
    · rcases hBS i net with inB | inS
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ inB)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ inS)
    · exact Finset.mem_union_right _ (hD i (by omega))
  -- The blocks of the run are at most one for each slot of its epochs.
  have blocks : tail.blockCount ≤
      ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat + 1) *
        preset.SLOTS_PER_EPOCH.toNat := by
    have start : (getCurrentEpoch split).toNat * preset.SLOTS_PER_EPOCH.toNat ≤
        split.slot.toNat := by
      rw [getCurrentEpoch_toNat]
      exact Nat.div_mul_le_self _ _
    have finish : x.slot.toNat <
        ((getCurrentEpoch x).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
      rw [getCurrentEpoch_toNat]
      exact lt_of_lt_of_eq (Nat.lt_mul_div_succ _ positive) (Nat.mul_comm _ _)
    have last : x.slot.toNat ≤
        ((getCurrentEpoch x).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat - 1 := by omega
    have count := tail.blocks_le_slots (a := (getCurrentEpoch split).toNat *
      preset.SLOTS_PER_EPOCH.toNat) (b := ((getCurrentEpoch x).toNat + 1) *
        preset.SLOTS_PER_EPOCH.toNat - 1) start last
    have gap := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat
      (show (getCurrentEpoch split).toNat + 1 ≤ (getCurrentEpoch x).toNat + 1 by omega)
    rw [Nat.add_mul, Nat.one_mul] at gap
    have shape : ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat + 1) *
        preset.SLOTS_PER_EPOCH.toNat = ((getCurrentEpoch x).toNat + 1) *
          preset.SLOTS_PER_EPOCH.toNat - (getCurrentEpoch split).toNat *
            preset.SLOTS_PER_EPOCH.toNat := by
      rw [← Nat.sub_mul]
      congr 1
      omega
    rw [shape]
    omega
  have total := (Finset.card_le_card subset).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have expand : ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat + 1) *
      (preset.SLOTS_PER_EPOCH.toNat + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) =
        ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat + 1) *
          preset.SLOTS_PER_EPOCH.toNat + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
            ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat) +
              preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by ring
  omega

/-! ## The classes of keys and their costs -/

section Costs
variable (pulled counted : BeaconState preset fork) (V : Finset ValidatorIndex)

def AC := activeVoters counted
def AR := activeVoters pulled
def Q := quorumVoters counted
def U := Q counted ∪ AC counted ∪ AR pulled
def eC (v : ValidatorIndex) : ℕ := balanceAt counted v.toNat
def eR (v : ValidatorIndex) : ℕ := balanceAt pulled v.toNat

/-- V keys active in C: twice their fall. -/
def cV1 : ℤ := ∑ v ∈ U pulled counted,
  if v ∈ V ∧ v ∈ AC counted then (eR pulled v : ℤ) - eC counted v else 0
/-- V keys not active in C: twice their stake at R. -/
def cV2 : ℤ := ∑ v ∈ U pulled counted, if v ∈ V ∧ v ∉ AC counted then (eR pulled v : ℤ) else 0
/-- (K4 pulled counted V), other keys active in both and counted in C: once their rise. -/
def cN : ℤ := ∑ v ∈ U pulled counted,
  if v ∈ AC counted ∧ v ∈ AR pulled ∧ v ∈ Q counted ∧ v ∉ V then
    (eC counted v : ℤ) - eR pulled v else 0
/-- (K5 counted V), other keys previous-epoch-only in C: three times their stake at C. -/
def cP : ℤ := ∑ v ∈ U pulled counted,
  if v ∈ Q counted ∧ v ∉ AC counted ∧ v ∉ V then (eC counted v : ℤ) else 0
/-- (K6 pulled counted), keys counted in C and not active at R: once their stake at C. -/
def cJ : ℤ := ∑ v ∈ U pulled counted,
  if v ∈ AC counted ∧ v ∈ Q counted ∧ v ∉ AR pulled then (eC counted v : ℤ) else 0

/-- K7, keys active at C and outside its quorum (slashed at C): minus twice their stake at C, and
minus their stake at R if active there. -/
def cK7 : ℤ := ∑ v ∈ U pulled counted,
  if v ∈ AC counted ∧ v ∉ Q counted then
    -(2 * (eC counted v : ℤ)) - (if v ∈ AR pulled then (eR pulled v : ℤ) else 0) else 0
/-- cS, other keys active at R, not at C and outside C's quorum: minus their stake at R. -/
def cS : ℤ := ∑ v ∈ U pulled counted,
  if v ∈ AR pulled ∧ v ∉ AC counted ∧ v ∉ Q counted ∧ v ∉ V then -(eR pulled v : ℤ) else 0
def VN : Finset ValidatorIndex := V.filter (· ∉ AC counted)
def K4 : Finset ValidatorIndex := (AC counted).filter fun v => v ∈ AR pulled ∧ v ∈ Q counted ∧ v ∉ V
def K5 : Finset ValidatorIndex := (Q counted).filter fun v => v ∉ AC counted ∧ v ∉ V
def K6 : Finset ValidatorIndex := (AC counted).filter fun v => v ∈ Q counted ∧ v ∉ AR pulled

end Costs

/-! ## Sums over validator indices, read at positions -/

/-- A sum over validator indices is at most the sum over a set of positions that holds them all.

An index is read at its position, `toNat` is injective, and the terms are natural numbers. -/
private theorem sum_toNat_le {S : Finset ValidatorIndex} {P : Finset ℕ} (f : ℕ → ℕ)
    (inside : ∀ v ∈ S, v.toNat ∈ P) : ∑ v ∈ S, f v.toNat ≤ ∑ i ∈ P, f i := by
  classical
  refine Finset.sum_le_sum_of_injOn (fun v : ValidatorIndex => v.toNat)
    (fun a _ b _ same => UInt64.toNat_inj.mp same) ?_ (fun _ _ => le_rfl)
    (fun _ _ _ => Nat.zero_le _)
  intro i hi
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
  exact inside v hv

/-- A position that holds a validator and meets a test is among the positions that meet it. -/
private theorem mem_positions_filter (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) {i : ℕ} {w : Validator}
    (found : state.validators.data[i]? = some w) {p : ℕ → Prop} [DecidablePred p] (test : p i) :
    i ∈ (pinTerms config state ancestor finalizedState).positions.filter p :=
  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1, test⟩

/-- A flag read from the validator at a position can hold only where the position holds one.

The flag is the `any` of the validator, or its `map` read with a default of `false`. -/
private theorem validator_of_flag {state : BeaconState preset fork} {i : ℕ} {f : Validator → Bool}
    (flag : (state.validators.data[i]?).any f = true ∨
      ((state.validators.data[i]?).map f).getD false = true) :
    ∃ w, state.validators.data[i]? = some w := by
  cases found : state.validators.data[i]? with
  | none =>
    rw [found] at flag
    simp at flag
  | some w => exact ⟨w, rfl⟩

/-- A voter active at the epoch of a state holds a validator there that is active at that epoch. -/
private theorem active_of_activeVoters (early : fork < .glamsterdam)
    {s : BeaconState preset fork} {v : ValidatorIndex} (member : v ∈ activeVoters s) :
    ∃ w, s.validators.data[v.toNat]? = some w ∧
      isActiveValidator w (getCurrentEpoch s) = true := by
  have listed : v ∈ getActiveValidatorIndices s (getCurrentEpoch s) := by
    simpa [activeVoters] using member
  exact (mem_getActiveValidatorIndices (s.validators.bound early)).mp listed

/-! ## Per-term stubs -/

section Stubs
variable {g : ForkedBeaconState preset} {split fin pulled anc counted : BeaconState preset fork}
  {V : Finset ValidatorIndex}


/-- A key active at C's epoch is activated by then at R, when that epoch is within the lookahead.

Activity up to the seed lookahead after the split is the same on both branches. -/
private theorem activation_le_of_active {g : ForkedBeaconState preset}
    {split fin pulled anc counted : BeaconState preset fork} {V : Finset ValidatorIndex}
    (h : Setting config checks g split fin pulled anc counted V)
    (bound : (getCurrentEpoch counted).toNat ≤
      anc.finalizedCheckpoint.epoch.toNat + preset.MAX_SEED_LOOKAHEAD.toNat)
    {v : ValidatorIndex} (member : v ∈ AC counted) {w : Validator}
    (found : pulled.validators.data[v.toNat]? = some w) :
    w.activationEpoch.toNat ≤ (getCurrentEpoch counted).toNat := by
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  obtain ⟨u, foundU, activeU⟩ := active_of_activeVoters h.early member
  obtain ⟨rp⟩ := h.toPulled
  obtain ⟨rc⟩ := h.toCounted
  have fixed : getCurrentEpoch counted ≤ activityFixedEpoch split := by
    rw [UInt64.le_iff_toNat_le, activityFixedEpoch_toNat]
    have := (getCurrentEpoch counted).toNat_lt
    omega
  have kc := activeKept_of_chainSteps rc.chainSteps (getCurrentEpoch counted) fixed v.toNat
  have kp := activeKept_of_chainSteps rp.chainSteps (getCurrentEpoch counted) fixed v.toNat
  have activeAtC : isActiveAt counted (getCurrentEpoch counted) v.toNat = true :=
    isActiveAt_eq_true_iff.mpr ⟨u, foundU, activeU⟩
  have activeAtR : isActiveAt pulled (getCurrentEpoch counted) v.toNat = true := by
    rw [kp, ← kc]
    exact activeAtC
  obtain ⟨w', found', active⟩ := isActiveAt_eq_true_iff.mp activeAtR
  rw [found] at found'
  cases found'
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
  exact UInt64.le_iff_toNat_le.mp active.1

/-- Glue: an unslashed V key active in C counts in C's quorum. -/
theorem glue_quorum (h : Setting config checks g split fin pulled anc counted V) :
    ∀ v ∈ V, v ∈ AC counted → v ∈ Q counted := by
  intro v member active
  have unslashed := (h.voting v member).2
  have listed : v ∈ getActiveValidatorIndices counted (getCurrentEpoch counted) := by
    simpa [AC, activeVoters] using active
  have inside := lt_size_of_mem_getActiveValidatorIndices listed
  have found : counted.validators.data[v.toNat]? = some counted.validators.data[v.toNat] :=
    Array.getElem?_eq_getElem inside
  have flag : ((counted.validators.data[v.toNat]?).map (·.slashed)).getD true = false := by
    simpa [slashedFlagAt, found] using unslashed
  simp only [Q, quorumVoters, Finset.mem_filter, List.mem_toFinset, List.mem_append]
  exact ⟨.inl listed, flag⟩

/-- D-5/D-6 (fall, V): the fall of V keys, and the stake of V keys that left C's active set. -/
theorem stub_V (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    cV1 pulled counted V + cV2 pulled counted V ≤
      ((∑ v ∈ V, (pinTerms config pulled anc fin).fall v.toNat) + (∑ v ∈ V, credR tail high v.toNat) +
        (∑ v ∈ V, (syncF events v.toNat + syncF eventsC v.toNat)) + (∑ v ∈ V, credDepR events v.toNat) +
        (∑ v ∈ V, consAmt events v.toNat) + preset.upwardBand * dueAt fin high V +
        (∑ v ∈ (VN counted V), exitQ tailC v.toNat) +
        (∑ v ∈ (VN counted V) with (pinTerms config pulled anc fin).exitingB v.toNat = true, eR pulled v) +
        (∑ v ∈ (VN counted V) with (pinTerms config pulled anc fin).lateB v.toNat = true, eR pulled v) : ℕ) := sorry

/-- The per-key core of the rise.

A key of R's registry rises from R to C by at most its rise term.

It also rises by the credits and slacks that `rise` does not read.

The slacks are one increment for a slashing on R's branch.

They are one rounding step for a credit on C's branch or a sync debit on R's.

A credit on C's branch also compounds by a tenth of its amount, without its consolidation credits. -/
private theorem key_core (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (i : ℕ) (inside : i < pulled.validators.data.size) :
    balanceAt counted i ≤ balanceAt pulled i + (pinTerms config pulled anc fin).rise i +
      (credC tailC highC i + credN tailC highC i / 10) + whistC tailC highC i +
      (syncF events i + syncF eventsC i) + slashR (pinTerms config pulled anc fin) i +
      bandC tailC highC i + bandR events i :=
  sorry

/-- D-7 (rise): other keys active in both. -/
theorem stub_N (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    cN pulled counted V ≤ ((∑ v ∈ (K4 pulled counted V), ((pinTerms config pulled anc fin).rise v.toNat +
      (credC tailC highC v.toNat + credN tailC highC v.toNat / 10) + whistC tailC highC v.toNat + (syncF events v.toNat + syncF eventsC v.toNat) +
      slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
      bandR events v.toNat)) : ℕ) := sorry

/-- D-4 (+ D-8 exits): other keys previous-epoch-only in C. A key whose exit R reads is at its
balance at R plus its rise; any other one is at its balance when its exit starts on C's branch,
plus its rise after that. Both add C's proposer credits and sync seats. -/
theorem stub_P (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    cP pulled counted V ≤ ((∑ v ∈ (K5 counted V) with (pinTerms config pulled anc fin).exitingB v.toNat = true,
        (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ (K5 counted V) with (pinTerms config pulled anc fin).exitingB v.toNat = false,
        (exitQ tailC v.toNat + riseQ tailC highC v.toNat)) +
      (∑ v ∈ (K5 counted V), ((propC tailC highC v.toNat + propN tailC highC v.toNat / 10) +
        whistC tailC highC v.toNat +
        (syncF events v.toNat + syncF eventsC v.toNat) +
        slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
        bandR events v.toNat)) : ℕ) := sorry

/-- D-8 (activations): keys counted in C and not active at R.

A key whose exit started on R's branch after the split is inactive at R and active in C (L10).

Its stake in C is at most its stake at R and its rise.

So is the stake of a key whose exit R reads, which `exiting` and `exitingRise` charge. -/
theorem stub_J (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    cJ pulled counted ≤ (((pinTerms config pulled anc fin).joining +
      (pinTerms config pulled anc fin).joinRise + (∑ v ∈ (K6 pulled counted) with (pinTerms config pulled anc fin).lateB v.toNat = true,
        (3 * eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ (K6 pulled counted) with (pinTerms config pulled anc fin).exitedRB v.toNat = true,
        (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ (K6 pulled counted) with (pinTerms config pulled anc fin).exitingB v.toNat = true,
        (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ (K6 pulled counted), ((credC tailC highC v.toNat + credN tailC highC v.toNat / 10) +
        whistC tailC highC v.toNat)) +
      (∑ v ∈ (K6 pulled counted), (syncF events v.toNat + syncF eventsC v.toNat)) +
      (∑ v ∈ (K6 pulled counted),
        (slashR (pinTerms config pulled anc fin) v.toNat + bandC tailC highC v.toNat +
          bandR events v.toNat)) +
      (∑ v ∈ (K6 pulled counted) with (pinTerms config pulled anc fin).pendingRB v.toNat = true,
        (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (if (pinTerms config pulled anc fin).gainHigh then (pinTerms config pulled anc fin).creditGain
        else 0)) : ℕ) := sorry

/-- K5 bands: the two bands beyond `credits`' one of each credited K5 key, weight 3.

Split by `exitingB`: the keys whose exit R reads and those the queues let exit on C. -/
theorem bud_exitingBands (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1) :
    2 * (∑ v ∈ (K5 counted V), bandC tailC highC v.toNat) ≤
      (pinTerms config pulled anc fin).exitingBands := sorry

/-- K6 keys of R's registry that are not yet eligible at R: their stake at R and their rise. -/
theorem bud_pendingR (h : Setting config checks g split fin pulled anc counted V) :
    (∑ v ∈ (K6 pulled counted) with (pinTerms config pulled anc fin).pendingRB v.toNat = true,
      (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) ≤
        (pinTerms config pulled anc fin).pendingR := sorry

/-- D-4: the keys whose exit R reads. -/
theorem bud_exiting :
    (∑ v ∈ (VN counted V) with (pinTerms config pulled anc fin).exitingB v.toNat = true, eR pulled v) +
      (∑ v ∈ (K5 counted V) with (pinTerms config pulled anc fin).exitingB v.toNat = true, eR pulled v) +
      (∑ v ∈ (K6 pulled counted) with (pinTerms config pulled anc fin).exitingB v.toNat = true,
        eR pulled v) ≤ (pinTerms config pulled anc fin).exiting := sorry

/-- Late activations, weight 3 for V keys and for new keys. -/
theorem bud_late (h : Setting config checks g split fin pulled anc counted V) :
    3 * (∑ v ∈ (VN counted V) with (pinTerms config pulled anc fin).lateB v.toNat = true, eR pulled v) +
      (∑ v ∈ (K6 pulled counted) with (pinTerms config pulled anc fin).lateB v.toNat = true,
        (3 * eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) ≤ (pinTerms config pulled anc fin).late := sorry

/-- D-8 (queues): exits and consolidations initiated on C's branch (none in the tight window). -/
theorem bud_queues (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) :
    3 * ((∑ v ∈ (VN counted V), exitQ tailC v.toNat) +
      (∑ v ∈ (K5 counted V) with (pinTerms config pulled anc fin).exitingB v.toNat = false, exitQ tailC v.toNat)) ≤
      (pinTerms config pulled anc fin).queueExit := sorry

/-- D-8 (deposit queue): deposits applied on R's branch to V keys, weight 3. -/
theorem bud_deposits (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    3 * (∑ v ∈ V, credDepR events v.toNat) ≤ (pinTerms config pulled anc fin).queueDep := sorry

/-- K5 (`queueRise`): the rise of exiting keys after their exit starts on C's branch. -/
theorem bud_queueRise (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1) :
    3 * (∑ v ∈ (K5 counted V) with (pinTerms config pulled anc fin).exitingB v.toNat = false, riseQ tailC highC v.toNat) ≤
      (pinTerms config pulled anc fin).queueRise := sorry

/-- K5 (`exitingRise`): the keys whose exit R reads. -/
theorem bud_exitingRise (h : Setting config checks g split fin pulled anc counted V) :
    (∑ v ∈ (K5 counted V) with (pinTerms config pulled anc fin).exitingB v.toNat = true, (pinTerms config pulled anc fin).rise v.toNat) +
      (∑ v ∈ (K6 pulled counted) with (pinTerms config pulled anc fin).exitingB v.toNat = true,
        (pinTerms config pulled anc fin).rise v.toNat) ≤
      (pinTerms config pulled anc fin).exitingRise := sorry

/-- K5 (`exitingCredits` with `credits`): C's proposer credits to K5 keys, weight 3.

The consolidation amounts are not here: `bud_consolidations` charges them, so they are added to the
bound.

The `syncProposer` part of the bound is not here: `bud_sync` uses it.

The bound is scaled by ten, to take the eleven tenths and the rounding of `exitingCredits`.

The compounding of the credits, a tenth of each key's amount rounded down, is in the bound.

The two further bands of each credited K5 key are in `bud_exitingBands`. -/
theorem bud_exitingCredits (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    10 * (2 * ((∑ v ∈ (K5 counted V), propC tailC highC v.toNat) +
      (∑ v ∈ (K5 counted V), propN tailC highC v.toNat / 10))) +
        22 * ((pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).syncProposer) ≤
      10 * (pinTerms config pulled anc fin).exitingCredits +
        20 * (∑ v ∈ (K5 counted V), consAmt eventsC v.toNat) := sorry

/-- D-7 (credits): C's non-attestation credits to keys counted once.

The consolidation amounts are not here either: `bud_consolidations` charges them.

The `syncProposer` part of `credits` is not here: `bud_sync` uses it.

The bound is scaled by ten, to take the eleven tenths and the rounding of `credits`.

The compounding of the credits, a tenth of each key's amount rounded down, is in the bound.

The rounding slacks of the credited keys of `K4` and `K5` are paid by `creditedKeys`. -/
theorem bud_credits (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    10 * ((∑ v ∈ (K4 pulled counted V), credC tailC highC v.toNat) +
      (∑ v ∈ (K6 pulled counted), credC tailC highC v.toNat) +
      (∑ v ∈ (K5 counted V), propC tailC highC v.toNat) +
      (∑ v ∈ (K4 pulled counted V), credN tailC highC v.toNat / 10) +
      (∑ v ∈ (K6 pulled counted), credN tailC highC v.toNat / 10) +
      (∑ v ∈ (K5 counted V), propN tailC highC v.toNat / 10) +
      (∑ v ∈ (K4 pulled counted V), bandC tailC highC v.toNat) +
      (∑ v ∈ (K5 counted V), bandC tailC highC v.toNat) +
      (∑ v ∈ (K6 pulled counted), bandC tailC highC v.toNat)) +
        11 * ((pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).syncProposer) ≤
      10 * (pinTerms config pulled anc fin).credits +
        10 * ((∑ v ∈ (K4 pulled counted V), consAmt eventsC v.toNat) +
          (∑ v ∈ (K6 pulled counted), consAmt eventsC v.toNat) +
          (∑ v ∈ (K5 counted V), consAmt eventsC v.toNat)) :=
  sorry

/-- The consolidation credits of C's branch, charged to `consolidationsX` (the S9 ruling).

The run from the finalized block's state X to C's state has the run from the split as its tail.

`Run.consolidation_credits_le_X_targets` bounds the credits to a set of targets by the caps at X of
the due entries of X's queue that name them, over the whole run from X.

The run to R's state bounds the credits to V the same way.

The sets `V`, `K4`, `K5` and `K6` are disjoint, so the sum over their union is at most the caps of X's
queue: `consolidationsX`, as `high ≤` the epoch of the call and X is within the withdrawal delay.

A key of `V` or `K5` weighs three, and the others one.

Each applied entry also adds one upward band to its target's rise, so the left side has `upwardBand`
for each due entry of X's queue.

An entry is charged its cap at X, which is at least `MAX_EFFECTIVE_BALANCE`, so three bands are at
most three tenths of it.

The bound `3.3 · X ≤ (33 · X + 9) / 10` is the charge of `consolidationsX` in `pinReserve`.

Deeper than the withdrawal delay `consolidationsX` is 0, so `shallow` is a premise here. -/
theorem bud_consolidations (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (highLeR : high ≤ (getCurrentEpoch pulled).toNat)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (highLe : highC ≤ (getCurrentEpoch pulled).toNat)
    (shallow : (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat ≤
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (band : 10 * preset.upwardBand ≤ preset.MAX_EFFECTIVE_BALANCE.toNat) :
    ((∑ v ∈ (K4 pulled counted V), consAmt eventsC v.toNat) +
      (∑ v ∈ (K6 pulled counted), consAmt eventsC v.toNat) +
      3 * (∑ v ∈ (K5 counted V), consAmt eventsC v.toNat) +
      3 * (∑ v ∈ V, consAmt events v.toNat)) +
      preset.upwardBand * (dueAt fin highC (K4 pulled counted V) +
        dueAt fin highC (K6 pulled counted) + 3 * dueAt fin highC (K5 counted V) +
        3 * dueAt fin high V) ≤
        (33 * (pinTerms config pulled anc fin).consolidationsX + 9) / 10 := sorry

/-- L10: the keys whose exit started on R's branch after the split, in `K6`. -/
theorem bud_exitedR :
    (∑ v ∈ (K6 pulled counted) with (pinTerms config pulled anc fin).exitedRB v.toNat = true,
      (eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) ≤
        (pinTerms config pulled anc fin).exitedR := sorry

/-- Selecting more events can only add to the sum of a nonnegative function. -/
private theorem sum_filter_mono {α : Type} (l : List α) (p q : α → Bool) (f : α → ℕ)
    (h : ∀ a, p a = true → q a = true) :
    ((l.filter p).map f).sum ≤ ((l.filter q).map f).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    by_cases hp : p a = true
    · have hq := h a hp
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos hq]
      simp only [List.map_cons, List.sum_cons]
      omega
    · by_cases hq : q a = true
      · rw [List.filter_cons_of_neg hp, List.filter_cons_of_pos hq]
        simp only [List.map_cons, List.sum_cons]
        omega
      · rw [List.filter_cons_of_neg hp, List.filter_cons_of_neg hq]
        exact ih

/-- The credits of a run to a key, read as a scan, add over `append`. -/
private theorem creditScan_append (blockP slotP : BalanceSource → Bool) (v high : ℕ)
    {x m y : ForkedBeaconState preset} (pre : Run config checks x m)
    (post : Run config checks m y) :
    (creditScan blockP slotP v high (pre.append post)).1 =
      (creditScan blockP slotP v high pre).1 + (creditScan blockP slotP v high post).1 := by
  induction post with
  | nil => rfl
  | snoc post step ih =>
    change (creditScan blockP slotP v high ((pre.append post).snoc step)).1 = _
    rw [creditScan_snoc_fst, creditScan_snoc_fst]
    split
    · omega
    · exact ih

/-- A step's scanned credit is at most the matching credits of its events. -/
private theorem stepCredit_le (blockP slotP : BalanceSource → Bool) (v : ℕ)
    {x y : ForkedBeaconState preset} (step : Step config checks x y)
    {added : List (BalanceEvent preset)} (addedOk : step.balanceEvents = .ok added) :
    stepCredit blockP slotP v step ≤
      ((added.filter fun e => blockP e.source || slotP e.source).map (keyCredit v)).sum := by
  cases step with
  | slot ok =>
    show ((((Step.slot (config := config) (checks := checks) ok).balanceEvents.toOption.getD
      []).filter (slotP ·.source)).map (keyCredit v)).sum ≤ _
    rw [addedOk]
    exact sum_filter_mono added _ _ _ fun a ha => by
      simp only [Bool.or_eq_true]
      exact Or.inr ha
  | block engine signed due ok =>
    show ((((Step.block engine signed due ok : Step config checks _ _).balanceEvents.toOption.getD
      []).filter (blockP ·.source)).map (keyCredit v)).sum ≤ _
    rw [addedOk]
    exact sum_filter_mono added _ _ _ fun a ha => by
      simp only [Bool.or_eq_true]
      exact Or.inl ha

/-- The credits that a scan reads from a run are at most the matching credits of its events. -/
private theorem creditScan_le_events (blockP slotP : BalanceSource → Bool) (v high : ℕ)
    {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    (creditScan blockP slotP v high tail).1 ≤
      ((events.filter fun e => blockP e.source || slotP e.source).map (keyCredit v)).sum := by
  induction tail generalizing events with
  | nil => exact Nat.zero_le _
  | @snoc m l pre step ih =>
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    have before := ih priorOk
    rw [creditScan_snoc_fst]
    split at rest
    · rename_i within
      split
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
        obtain ⟨added, addedOk, rfl⟩ := rest
        simp only [List.filter_append, List.map_append, List.sum_append]
        have credit := stepCredit_le blockP slotP v step addedOk
        omega
      · rename_i outside
        exact absurd within outside
    · rename_i outside
      split
      · rename_i within
        exact absurd within outside
      · cases rest
        exact before

/-- The credits to some keys at one event add up to at most the credits of the event.

A key beyond the balance array has no credit. -/
private theorem sum_keyCredit_le_credits (S : Finset ValidatorIndex) (e : BalanceEvent preset) :
    ∑ v ∈ S, keyCredit v.toNat e ≤ e.credits := by
  classical
  have trim : ∑ v ∈ S.filter (fun v => v.toNat < e.after.state.balances.data.size),
      keyCredit v.toNat e = ∑ v ∈ S, keyCredit v.toNat e := by
    refine Finset.sum_filter_of_ne fun v _ nonzero => ?_
    by_contra outside
    apply nonzero
    have missing : actualBalanceAt e.after v.toNat = 0 := by
      simp [actualBalanceAt, Array.getElem?_eq_none (not_lt.mp outside)]
    simp [keyCredit, missing]
  rw [← trim]
  exact sum_toNat_le (fun i => actualBalanceAt e.after i - actualBalanceAt e.before i)
    (fun v member => Finset.mem_range.mpr (Finset.mem_filter.mp member).2)

/-- The credits to one key at one event are at most the credits of the event. -/
private theorem keyCredit_le_credits (i : ℕ) (e : BalanceEvent preset) :
    keyCredit i e ≤ e.credits := by
  by_cases inside : i < e.after.state.balances.data.size
  · exact Finset.single_le_sum (f := fun j => actualBalanceAt e.after j - actualBalanceAt e.before j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr inside)
  · have missing : actualBalanceAt e.after i = 0 := by
      simp [actualBalanceAt, Array.getElem?_eq_none (not_lt.mp inside)]
    simp [keyCredit, missing]

/-- If every selected item is also selected by one of two tests, or adds nothing, then the sum over
the first test is at most the two sums over the others. -/
private theorem sum_filter_split {α : Type} (l : List α) (p q r : α → Bool) (f : α → ℕ)
    (h : ∀ a ∈ l, p a = true → q a = true ∨ r a = true ∨ f a = 0) :
    ((l.filter p).map f).sum ≤ ((l.filter q).map f).sum + ((l.filter r).map f).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    have tail := ih fun b member => h b (List.mem_cons_of_mem _ member)
    by_cases hp : p a = true
    · rcases h a List.mem_cons_self hp with hq | hr | hz
      · by_cases hr : r a = true
        · rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos hq, List.filter_cons_of_pos hr]
          simp only [List.map_cons, List.sum_cons]
          omega
        · rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos hq, List.filter_cons_of_neg hr]
          simp only [List.map_cons, List.sum_cons]
          omega
      · by_cases hq : q a = true
        · rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos hq, List.filter_cons_of_pos hr]
          simp only [List.map_cons, List.sum_cons]
          omega
        · rw [List.filter_cons_of_pos hp, List.filter_cons_of_neg hq, List.filter_cons_of_pos hr]
          simp only [List.map_cons, List.sum_cons]
          omega
      · rw [List.filter_cons_of_pos hp]
        simp only [List.map_cons, List.sum_cons, hz]
        by_cases hq : q a = true <;> by_cases hr : r a = true
        · rw [List.filter_cons_of_pos hq, List.filter_cons_of_pos hr]
          simp only [List.map_cons, List.sum_cons]
          omega
        · rw [List.filter_cons_of_pos hq, List.filter_cons_of_neg hr]
          simp only [List.map_cons, List.sum_cons]
          omega
        · rw [List.filter_cons_of_neg hq, List.filter_cons_of_pos hr]
          simp only [List.map_cons, List.sum_cons]
          omega
        · rw [List.filter_cons_of_neg hq, List.filter_cons_of_neg hr]
          omega
    · rw [List.filter_cons_of_neg hp]
      by_cases hq : q a = true <;> by_cases hr : r a = true
      · rw [List.filter_cons_of_pos hq, List.filter_cons_of_pos hr]
        simp only [List.map_cons, List.sum_cons]
        omega
      · rw [List.filter_cons_of_pos hq, List.filter_cons_of_neg hr]
        simp only [List.map_cons, List.sum_cons]
        omega
      · rw [List.filter_cons_of_neg hq, List.filter_cons_of_pos hr]
        simp only [List.map_cons, List.sum_cons]
        omega
      · rw [List.filter_cons_of_neg hq, List.filter_cons_of_neg hr]
        exact tail

/-- A step's block credits from one source test are at most those from two others, with the slot
credits left out, when each of its events that the first test selects is selected by one of the
others or credits the key nothing. -/
private theorem stepCredit_split (p q r : BalanceSource → Bool) (v : ℕ)
    {x y : ForkedBeaconState preset} (step : Step config checks x y)
    {added : List (BalanceEvent preset)} (addedOk : step.balanceEvents = .ok added)
    (h : ∀ e ∈ added, p e.source = true →
      q e.source = true ∨ r e.source = true ∨ keyCredit v e = 0) :
    stepCredit p (fun _ => false) v step ≤
      stepCredit q (fun _ => false) v step + stepCredit r (fun _ => false) v step := by
  cases step with
  | slot ok =>
    show ((((Step.slot (config := config) (checks := checks) ok).balanceEvents.toOption.getD
      []).filter ((fun _ => false) ·.source)).map (keyCredit v)).sum ≤
        ((((Step.slot (config := config) (checks := checks) ok).balanceEvents.toOption.getD
      []).filter ((fun _ => false) ·.source)).map (keyCredit v)).sum +
        ((((Step.slot (config := config) (checks := checks) ok).balanceEvents.toOption.getD
      []).filter ((fun _ => false) ·.source)).map (keyCredit v)).sum
    omega
  | block engine signed due ok =>
    show ((((Step.block engine signed due ok : Step config checks _ _).balanceEvents.toOption.getD
      []).filter (p ·.source)).map (keyCredit v)).sum ≤
        ((((Step.block engine signed due ok : Step config checks _ _).balanceEvents.toOption.getD
      []).filter (q ·.source)).map (keyCredit v)).sum +
        ((((Step.block engine signed due ok : Step config checks _ _).balanceEvents.toOption.getD
      []).filter (r ·.source)).map (keyCredit v)).sum
    rw [addedOk]
    exact sum_filter_split added (p ·.source) (q ·.source) (r ·.source) (keyCredit v) h

/-- The block credits of a run from one source test are at most those from two others, when every
event of the run that the first test selects is selected by one of the others or credits the key
nothing. -/
private theorem creditScan_split (p q r : BalanceSource → Bool) (v high : ℕ)
    {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (h : ∀ e ∈ events, p e.source = true →
      q e.source = true ∨ r e.source = true ∨ keyCredit v e = 0) :
    (creditScan p (fun _ => false) v high tail).1 ≤
      (creditScan q (fun _ => false) v high tail).1 +
        (creditScan r (fun _ => false) v high tail).1 := by
  induction tail generalizing events with
  | nil => exact Nat.zero_le _
  | @snoc m l pre step ih =>
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    rw [creditScan_snoc_fst, creditScan_snoc_fst, creditScan_snoc_fst]
    split at rest
    · rename_i within
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
      obtain ⟨added, addedOk, rfl⟩ := rest
      have before := ih priorOk fun e member => h e (List.mem_append_left _ member)
      have credit := stepCredit_split p q r v step addedOk fun e member =>
        h e (List.mem_append_right _ member)
      simp only [within, ↓reduceIte]
      omega
    · rename_i outside
      cases rest
      have before := ih priorOk h
      simp only [outside, ↓reduceIte]
      exact before

/-- The per-epoch base rewards of the keys recent at `pulled`, at a quarter of its total.

It is the sum inside `proposerCredit` of `pinTerms`, without the sync part. -/
private def baseSum (pulled : BeaconState preset fork) : ℕ :=
  let inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  let epoch := getCurrentEpoch pulled
  let totalGwei := (getTotalActiveBalance pulled).toOption.getD 0
  let quarter := max preset.EFFECTIVE_BALANCE_INCREMENT (totalGwei / 4)
  let perIncrement := ((getBaseRewardPerIncrement preset quarter).toOption.getD 0).toNat
  ∑ i ∈ Finset.range pulled.validators.data.size with
      (isActiveAt pulled (getPreviousEpoch pulled) i || isActiveAt pulled epoch i ||
        isActiveAt pulled (epoch + 1) i) = true,
    balanceAt pulled i / inc * perIncrement

/-- A total with a successful read of the reward per increment lets any positive total read it. -/
private theorem perIncrement_ok_of {a b pa : Gwei}
    (ok : getBaseRewardPerIncrement preset a = .ok pa) (positive : 0 < b.toNat) :
    ∃ pb, getBaseRewardPerIncrement preset b = .ok pb := by
  have unfolded := ok
  simp only [getBaseRewardPerIncrement, liftArith, mapError_ok_iff, bind_ok_iff] at unfolded
  obtain ⟨scaled, scaledOk, -⟩ := unfolded
  have fits := (mulChecked_ok_iff.mp scaledOk).1
  have root := toNat_integerSquareroot b
  have nonzero : integerSquareroot b ≠ 0 := fun zero => by
    rw [zero, UInt64.toNat_zero] at root
    have := Nat.sqrt_pos.mpr positive
    omega
  refine ⟨preset.EFFECTIVE_BALANCE_INCREMENT * preset.BASE_REWARD_FACTOR /
    integerSquareroot b, ?_⟩
  simp only [getBaseRewardPerIncrement, liftArith, mulChecked_of_lt fits, bind, Except.bind,
    divChecked, nonzero, ite_false, Except.mapError]

/-- The base rewards of the recent keys are at least the reward per increment of the quarter
total times the active increments. -/
private theorem baseSum_ge {pulled : BeaconState preset fork} (early : fork < .glamsterdam)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (aligned : EffectiveBalancesAligned pulled) {per : Gwei}
    (perOk : getBaseRewardPerIncrement preset
      (max preset.EFFECTIVE_BALANCE_INCREMENT
        (((getTotalActiveBalance pulled).toOption.getD 0) / 4)) = .ok per) :
    per.toNat * ((∑ v ∈ activeVoters pulled, balanceAt pulled v.toNat) /
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤ baseSum pulled := by
  classical
  have sumEq : (∑ v ∈ activeVoters pulled, balanceAt pulled v.toNat) =
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        ∑ v ∈ activeVoters pulled, balanceAt pulled v.toNat /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ =>
      (Nat.mul_div_cancel' (dvd_balanceAt_of_aligned aligned dvd_rfl v.toNat)).symm
  rw [sumEq, Nat.mul_div_cancel_left _ incPos, Finset.mul_sum]
  unfold baseSum
  dsimp only
  rw [perOk]
  simp only [Except.toOption, Option.getD_some]
  have swap : ∑ v ∈ activeVoters pulled, per.toNat *
      (balanceAt pulled v.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) =
      ∑ v ∈ activeVoters pulled, balanceAt pulled v.toNat /
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat * per.toNat :=
    Finset.sum_congr rfl fun _ _ => Nat.mul_comm _ _
  rw [swap]
  refine sum_toNat_le (fun i => balanceAt pulled i / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
    per.toNat) fun v member => ?_
  obtain ⟨w, found, active⟩ := active_of_activeVoters early member
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1, ?_⟩
  have current := isActiveAt_eq_true_iff.mpr ⟨w, found, active⟩
  simp [current]

open DirectSafety.Apriori in
/-- The block proposer credits of one epoch of a run from fin fit one epoch of `baseSum`.

The epoch is read at its start state `m`, and `pulled` is the state whose total the window reads.

The active stake at `pulled` must be at least one increment. -/
private theorem proposerCredits_le_baseSum
    (h : Setting config checks g split fin pulled anc counted V)
    {m n : BeaconState preset fork} (toM : Run config checks ⟨fork, fin⟩ ⟨fork, m⟩)
    (inner : Run config checks ⟨fork, m⟩ ⟨fork, n⟩)
    (same : getCurrentEpoch n = getCurrentEpoch m)
    {high : ℕ} (inside : (getCurrentEpoch m).toNat ≤ (getCurrentEpoch pulled).toNat)
    (stake : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      ∑ v ∈ activeVoters pulled, balanceAt pulled v.toNat)
    {events : List (BalanceEvent preset)} (replayed : inner.balanceEvents high = .ok events) :
    DirectSafety.Apriori.Internal.sourceCredits .rewards events ≤ baseSum pulled := by
  classical
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  have fullP : Run config checks ⟨fork, fin⟩ ⟨fork, pulled⟩ := fromFin.append toPulled
  have mWithin : (getCurrentEpoch m).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by omega
  have supportedM : DirectSafety.Apriori.Internal.Supported toFin toM
      (getCurrentEpoch pulled).toNat :=
    ⟨h.genesis, h.parameters, h.caps, h.aligned, h.early, mWithin, h.guard⟩
  obtain ⟨curM, prevM, -⟩ := DirectSafety.Apriori.Internal.ceilingFloor_electra toFin toM
    (getCurrentEpoch pulled).toNat supportedM h.twoSlots electra
  have data := DirectSafety.Apriori.Internal.epoch_credits_data inner electra h.early same high
    replayed
  rcases data.1 with ⟨Tm, pm, TmOk, pmOk⟩ | ⟨zero, -, -, -⟩
  swap
  · rw [zero]
    exact Nat.zero_le _
  obtain ⟨Tp, TpOk⟩ := h.pulledTotal
  have bound := (data.2 Tm pm TmOk pmOk).1
  have incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    refine Nat.pos_of_ne_zero fun zero => ?_
    have room := h.room
    rw [zero, Nat.zero_mul] at room
    exact absurd room (by decide)
  -- The two totals are within three halves of each other, and the ceiling of the epoch of `m`.
  have band := total_band_of_guard toFin h.genesis h.parameters h.caps h.aligned h.twoSlots
    electra h.guard toM h.early mWithin fullP h.early (Nat.le_succ _) TmOk TpOk
  obtain ⟨floorLast, -⟩ := total_within_guard toFin h.genesis h.parameters h.caps h.aligned
    h.twoSlots electra h.guard fullP h.early (Nat.le_succ _) TpOk
  have notBefore : ¬ (⟨fork, fin⟩ : ForkedBeaconState preset).fork < .pectra :=
    Nat.not_lt_of_ge electra
  have zeroEpochs : preElectraEpochs config (⟨fork, fin⟩ : ForkedBeaconState preset)
      (getCurrentEpoch pulled).toNat = 0 := by simp [preElectraEpochs, notBefore]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ratioGuard, -⟩ := id h.guard
  rw [zeroEpochs] at ratioGuard
  have ratio := ratioGuard ((getCurrentEpoch pulled).toNat + 1 - (getCurrentEpoch fin).toNat)
    (Nat.zero_le _) (by unfold driftHorizon; dsimp only; omega)
  have mono := stakeCeilingAt_mono (config := config) (x := (⟨fork, fin⟩ : ForkedBeaconState preset))
    (high := (getCurrentEpoch pulled).toNat) electra
    (s := (getCurrentEpoch m).toNat - (getCurrentEpoch fin).toNat)
    (t := (getCurrentEpoch pulled).toNat + 1 - (getCurrentEpoch fin).toNat) (by omega)
  have ceilingBound : 2 * stakeCeilingAt config (⟨fork, fin⟩ : ForkedBeaconState preset)
      (getCurrentEpoch pulled).toNat
        ((getCurrentEpoch m).toNat - (getCurrentEpoch fin).toNat) ≤ 3 * Tp.toNat := by
    simp only [stakeCeilingAt, stakeFloorAt, zeroEpochs] at mono floorLast ratio ⊢
    omega
  -- The totals as stakes.
  obtain ⟨-, -, valueP⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok TpOk)
  obtain ⟨-, -, valueM⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok TmOk)
  have TpEq : Tp.toNat = ∑ v ∈ activeVoters pulled, balanceAt pulled v.toNat := by
    rw [valueP]
    exact max_eq_right stake
  have TmLow : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ Tm.toNat := by
    rw [valueM]
    exact le_max_left _ _
  -- The quarter total and its reward per increment.
  have getTotalEq : (getTotalActiveBalance pulled).toOption.getD 0 = Tp := by
    rw [TpOk]
    rfl
  have quarterNat : (max preset.EFFECTIVE_BALANCE_INCREMENT
      (((getTotalActiveBalance pulled).toOption.getD 0) / 4)).toNat =
        max preset.EFFECTIVE_BALANCE_INCREMENT.toNat (Tp.toNat / 4) := by
    rw [getTotalEq, toNat_max, UInt64.toNat_div]
    rfl
  have quarterLe : (max preset.EFFECTIVE_BALANCE_INCREMENT
      (((getTotalActiveBalance pulled).toOption.getD 0) / 4)).toNat ≤ Tm.toNat := by
    rw [quarterNat]
    exact max_le TmLow (by omega)
  have quarterPos : 0 < (max preset.EFFECTIVE_BALANCE_INCREMENT
      (((getTotalActiveBalance pulled).toOption.getD 0) / 4)).toNat := by
    rw [quarterNat]
    exact Nat.lt_of_lt_of_le incPos (le_max_left _ _)
  obtain ⟨pq, pqOk⟩ := perIncrement_ok_of pmOk quarterPos
  have rate : pm.toNat ≤ pq.toNat := by
    rw [toNat_getBaseRewardPerIncrement pmOk, toNat_getBaseRewardPerIncrement pqOk]
    exact Nat.div_le_div_left (Nat.sqrt_le_sqrt quarterLe) (Nat.sqrt_pos.mpr quarterPos)
  -- The base rewards of the recent keys hold one quarter-rate reward for each active increment.
  have alignedP : EffectiveBalancesAligned pulled :=
    (run_justified_separated (toFin.append fullP) h.genesis).1.aligned h.aligned
  have recent := baseSum_ge h.early incPos alignedP pqOk
  -- The arithmetic of increments.
  have divides : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣
      ∑ v ∈ activeVoters pulled, balanceAt pulled v.toNat :=
    Finset.dvd_sum fun v _ => dvd_balanceAt_of_aligned alignedP dvd_rfl v.toNat
  obtain ⟨steps, stepsEq⟩ := divides
  have stepsDiv : (∑ v ∈ activeVoters pulled, balanceAt pulled v.toNat) /
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat = steps := by
    rw [stepsEq, Nat.mul_div_cancel_left _ incPos]
  rw [stepsDiv] at recent
  have two : 2 * (stakeCeilingAt config (⟨fork, fin⟩ : ForkedBeaconState preset)
      (getCurrentEpoch pulled).toNat
        ((getCurrentEpoch m).toNat - (getCurrentEpoch fin).toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤ 3 * steps := by
    refine Nat.le_of_mul_le_mul_right (c := preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ?_ incPos
    calc 2 * (stakeCeilingAt config (⟨fork, fin⟩ : ForkedBeaconState preset)
          (getCurrentEpoch pulled).toNat
            ((getCurrentEpoch m).toNat - (getCurrentEpoch fin).toNat) /
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) *
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat
        = 2 * (stakeCeilingAt config (⟨fork, fin⟩ : ForkedBeaconState preset)
          (getCurrentEpoch pulled).toNat
            ((getCurrentEpoch m).toNat - (getCurrentEpoch fin).toNat) /
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by rw [Nat.mul_assoc]
      _ ≤ 2 * stakeCeilingAt config (⟨fork, fin⟩ : ForkedBeaconState preset)
          (getCurrentEpoch pulled).toNat
            ((getCurrentEpoch m).toNat - (getCurrentEpoch fin).toNat) :=
          Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
      _ ≤ 3 * Tp.toNat := ceilingBound
      _ = 3 * steps * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
          rw [TpEq, stepsEq]
          ring
  have sums : (∑ i ∈ (getActiveValidatorIndices (⟨fork, m⟩ : ForkedBeaconState preset).state
        (getPreviousEpoch (⟨fork, m⟩ : ForkedBeaconState preset).state)).toFinset,
        effectiveAt (⟨fork, m⟩ : ForkedBeaconState preset) i.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
      (∑ i ∈ (getActiveValidatorIndices (⟨fork, m⟩ : ForkedBeaconState preset).state
        (getCurrentEpoch (⟨fork, m⟩ : ForkedBeaconState preset).state)).toFinset,
        effectiveAt (⟨fork, m⟩ : ForkedBeaconState preset) i.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      2 * (stakeCeilingAt config (⟨fork, fin⟩ : ForkedBeaconState preset)
        (getCurrentEpoch pulled).toNat
          ((getCurrentEpoch m).toNat - (getCurrentEpoch fin).toNat) /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
    exact le_trans
      (Nat.add_le_add (Nat.div_le_div_right (c := preset.EFFECTIVE_BALANCE_INCREMENT.toNat) prevM)
        (Nat.div_le_div_right (c := preset.EFFECTIVE_BALANCE_INCREMENT.toNat) curM))
      (Nat.two_mul _).symm.le
  have first := Nat.mul_le_mul_left (54 * pm.toNat) sums
  have second := Nat.mul_le_mul_left (54 * pm.toNat) two
  have third := Nat.mul_le_mul_right (3 * steps) (Nat.mul_le_mul_left 54 rate)
  have scaled : DirectSafety.Apriori.Internal.sourceCredits .rewards events * 448 ≤
      54 * pq.toNat * (3 * steps) := bound.trans (first.trans (second.trans third))
  have regroup : 54 * pq.toNat * (3 * steps) = 162 * (pq.toNat * steps) := by ring
  omega

/-- The credits to some keys at the events that a test selects are at most the events' credit
limits, when each event is within its limit. -/
private theorem keyCredits_le_limits (S : Finset ValidatorIndex) (q : BalanceEvent preset → Bool)
    {events : List (BalanceEvent preset)} (bounded : ∀ e ∈ events, e.credits ≤ e.creditLimit) :
    ∑ v ∈ S, ((events.filter q).map (keyCredit v.toNat)).sum ≤
      ((events.filter q).map (·.creditLimit)).sum := by
  induction events with
  | nil => simp
  | cons a rest ih =>
    have tail := ih fun e member => bounded e (List.mem_cons_of_mem _ member)
    have head := bounded a List.mem_cons_self
    have single := sum_keyCredit_le_credits S a
    by_cases hq : q a = true
    · rw [List.filter_cons_of_pos hq]
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
      omega
    · rw [List.filter_cons_of_neg hq]
      exact tail

/-- The credit limits of one source are the sum over the events that name it. -/
private theorem sourceCredits_eq_filter (source : BalanceSource) (events : List (BalanceEvent preset)) :
    DirectSafety.Apriori.Internal.sourceCredits source events =
      ((events.filter fun e => decide (e.source = source)).map (·.creditLimit)).sum := by
  induction events with
  | nil => simp [DirectSafety.Apriori.Internal.sourceCredits]
  | cons a rest ih =>
    have split : DirectSafety.Apriori.Internal.sourceCredits source (a :: rest) =
        (if a.source = source then a.creditLimit else 0) +
          DirectSafety.Apriori.Internal.sourceCredits source rest := by
      simp [DirectSafety.Apriori.Internal.sourceCredits]
    rw [split, ih]
    by_cases hs : a.source = source
    · simp [hs]
    · simp [hs]

/-- A slot step has no scanned credit when the slot test selects nothing. -/
private theorem stepCredit_slot_zero (p : BalanceSource → Bool) (v : ℕ)
    {x y : ForkedBeaconState preset} (ok : advanceSlotAcross config checks x = .ok y) :
    stepCredit p (fun _ => false) v (Step.slot ok : Step config checks x y) = 0 := by
  show ((((Step.slot (config := config) (checks := checks) ok).balanceEvents.toOption.getD
    []).filter ((fun _ => false) ·.source)).map (keyCredit v)).sum = 0
  rw [List.filter_eq_nil_iff.mpr (fun a _ => by simp)]
  rfl

/-- A run whose steps all start in the epoch of its first state scans, for a test that ignores slot
steps, no more than a run that ends in that epoch.

The last step is a block step, which stays in the epoch, or a slot step, which scans for nothing. -/
private theorem run_in_epoch {m n : ForkedBeaconState preset} (mid : Run config checks m n)
    (inside : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      mid.Contains step → getCurrentEpoch u.state = getCurrentEpoch m.state) :
    ∃ (k : ForkedBeaconState preset) (kept : Run config checks m k),
      getCurrentEpoch k.state = getCurrentEpoch m.state ∧ k.fork ≤ n.fork ∧
        ∀ (p : BalanceSource → Bool) (v high : ℕ),
          (creditScan p (fun _ => false) v high mid).1 ≤
            (creditScan p (fun _ => false) v high kept).1 := by
  cases mid with
  | nil => exact ⟨m, .nil, rfl, Nat.le_refl _, fun _ _ _ => Nat.le_refl _⟩
  | @snoc u l pre step =>
    have start := inside step (.last pre step)
    cases step with
    | slot ok =>
      refine ⟨_, pre, start, (Step.slot ok : Step config checks _ _).chainStep.fork_le,
        fun p v high => ?_⟩
      rw [creditScan_snoc_fst]
      split
      · rw [stepCredit_slot_zero]
        omega
      · exact Nat.le_refl _
    | @block f s t engine signed due ok =>
      refine ⟨_, pre.snoc (.block engine signed due ok), ?_, Nat.le_refl _,
        fun _ _ _ => Nat.le_refl _⟩
      have slotEq := processBlock_slot (applySignedBlock_ok ok).2.1
      have kept : getCurrentEpoch t = getCurrentEpoch s := by
        simp only [getCurrentEpoch, slotEq]
      exact kept.trans start

/-- One epoch of a run from fin credits the keys of `V` at most `baseSum` in rewards. -/
private theorem segment_rewards_le (h : Setting config checks g split fin pulled anc counted V)
    {m : BeaconState preset fork} (toM : Run config checks ⟨fork, fin⟩ ⟨fork, m⟩)
    {n : BeaconState preset fork} (inner : Run config checks ⟨fork, m⟩ ⟨fork, n⟩)
    (same : getCurrentEpoch n = getCurrentEpoch m)
    (inside : (getCurrentEpoch m).toNat ≤ (getCurrentEpoch pulled).toNat) (high : ℕ)
    (stake : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      ∑ v ∈ activeVoters pulled, balanceAt pulled v.toNat) :
    ∑ v ∈ V, (creditScan (fun s => decide (s = .rewards)) (fun _ => false) v.toNat high
      inner).1 ≤ baseSum pulled := by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨events, replayed, bounded⟩ :=
    Run.balanceEvents_bounded (toFin.append toM) inner h.genesis h.early high
  have scans : ∀ v : ValidatorIndex, (creditScan (fun s => decide (s = .rewards))
      (fun _ => false) v.toNat high inner).1 ≤
        ((events.filter fun e => decide (e.source = .rewards)).map (keyCredit v.toNat)).sum := by
    intro v
    have := creditScan_le_events (fun s => decide (s = .rewards)) (fun _ => false) v.toNat high
      inner replayed
    simpa only [Bool.or_false] using this
  have limits := keyCredits_le_limits V (fun e => decide (e.source = .rewards))
    (fun e member => (bounded e member).1)
  have epoch := proposerCredits_le_baseSum h toM inner same inside stake replayed
  rw [← sourceCredits_eq_filter .rewards events] at limits
  exact (Finset.sum_le_sum fun v _ => scans v).trans (limits.trans epoch)

/-- R's rewards to the keys of `V` since the split are at most one `baseSum` for each epoch. -/
private theorem rewards_le_total (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (stake : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      ∑ v ∈ activeVoters pulled, balanceAt pulled v.toNat) :
    ∑ v ∈ V, (creditScan (fun s => decide (s = .rewards)) (fun _ => false) v.toNat high
      tail).1 ≤
        ((getCurrentEpoch pulled).toNat - (getCurrentEpoch split).toNat + 1) *
          baseSum pulled := by
  obtain ⟨fromFin⟩ := h.fromFin
  have cuts := DirectSafety.Apriori.Internal.run_cuts_measure_le (config := config)
    (checks := checks) tail h.early
    (fun {_ _} r => ∑ v ∈ V, (creditScan (fun s => decide (s = .rewards)) (fun _ => false)
      v.toNat high r).1)
    (fun {_} => Finset.sum_eq_zero fun _ _ => rfl)
    (fun {_ _ _} pre post _ => by simp only [creditScan_append, Finset.sum_add_distrib])
    (fun _ => True) (fun _ => baseSum pulled) (fun _ _ _ _ => trivial)
    (fun {m n} toM mid rest inside _ => by
      obtain ⟨k, kept, kEpoch, kFork, scanLe⟩ := run_in_epoch mid inside
      obtain ⟨mf, ms⟩ := m
      have mFork : mf = fork := by
        have low := fork_le_of_chainSteps toM.chainSteps
        have high := fork_le_of_chainSteps (mid.append rest).chainSteps
        exact Fork.ctorIdx_injective (Nat.le_antisymm high low)
      subst mFork
      obtain ⟨kf, ks⟩ := k
      have kFork' : kf = mf := by
        have low := fork_le_of_chainSteps kept.chainSteps
        have above := fork_le_of_chainSteps rest.chainSteps
        exact Fork.ctorIdx_injective (Nat.le_antisymm (Nat.le_trans kFork above) low)
      subst kFork'
      have epochLe := UInt64.le_iff_toNat_le.mp
        (currentEpoch_le_of_chainSteps (mid.append rest).chainSteps)
      exact (Finset.sum_le_sum fun v _ => scanLe _ _ _).trans
        (segment_rewards_le h (fromFin.append toM) kept kEpoch epochLe high stake))
    ((getCurrentEpoch pulled).toNat - (getCurrentEpoch split).toNat + 1)
    (fun {u w} step member => by
      obtain ⟨pre, post, -⟩ := tail.contains_split step member
      have le := UInt64.le_iff_toNat_le.mp (UInt64.le_trans step.chainStep.currentEpoch_le
        (currentEpoch_le_of_chainSteps post.chainSteps))
      have called := UInt64.le_iff_toNat_le.mp h.called
      dsimp only at le ⊢
      omega)
  have sumConst : ((List.range ((getCurrentEpoch pulled).toNat - (getCurrentEpoch split).toNat +
      1)).map fun _ => baseSum pulled).sum =
        ((getCurrentEpoch pulled).toNat - (getCurrentEpoch split).toNat + 1) * baseSum pulled := by
    simp [List.map_const', List.sum_replicate]
  exact cuts.trans sumConst.le

/-- R1 (branchR): R's credits to V keys since the split, weight 3.

The slashing of a key on R's branch is charged here for the keys of `K4` and `K5`.

So is a sync debit of R that `rise` omits.

The keys of `K4` weigh one, and those of `K5` weigh three.

The `syncProposer` part of `proposerCredit` is not used by `credR`, which leaves out sync events, so
`bud_sync` takes it. -/
theorem bud_branchR (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    3 * (∑ v ∈ V, credR tail high v.toNat) +
        3 * ((pinTerms config pulled anc fin).depth *
          (pinTerms config pulled anc fin).syncProposer) +
        (∑ v ∈ (K4 pulled counted V),
          (slashR (pinTerms config pulled anc fin) v.toNat + bandR events v.toNat)) +
        3 * (∑ v ∈ (K5 counted V),
          (slashR (pinTerms config pulled anc fin) v.toNat + bandR events v.toNat)) +
        (∑ v ∈ (K6 pulled counted),
          (slashR (pinTerms config pulled anc fin) v.toNat + bandR events v.toNat)) ≤
      (pinTerms config pulled anc fin).branchR := sorry

/-- S1 (syncSeats): every seat, weight 3 for V, K4 and K5 and 1 for K6.

The proposer's share of the sync credits is in `syncF`, so the bound adds the `syncProposer` part
that `credits`, `exitingCredits` and `branchR` leave. -/
theorem bud_sync (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    3 * ((∑ v ∈ V, (syncF events v.toNat + syncF eventsC v.toNat)) + (∑ v ∈ (K4 pulled counted V), (syncF events v.toNat + syncF eventsC v.toNat)) +
      (∑ v ∈ (K5 counted V), (syncF events v.toNat + syncF eventsC v.toNat))) +
      (∑ v ∈ (K6 pulled counted), (syncF events v.toNat + syncF eventsC v.toNat)) ≤
        (pinTerms config pulled anc fin).syncSeats +
          6 * ((pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).syncProposer) := sorry

/-- W (`reserveW`, `flagged`, `seatShortfall`, K7, cS): whistleblower rewards on C's branch,
weight 3, are paid by the slashed key's own slack, or charged. -/
theorem bud_whistle (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    3 * ((∑ v ∈ (K4 pulled counted V), (whistC tailC highC v.toNat : ℤ)) +
      (∑ v ∈ (K5 counted V), (whistC tailC highC v.toNat : ℤ)) +
      (∑ v ∈ (K6 pulled counted), (whistC tailC highC v.toNat : ℤ))) ≤
      -cK7 pulled counted - cS pulled counted V + (pinTerms config pulled anc fin).reserveW +
        (pinTerms config pulled anc fin).flagged + (pinTerms config pulled anc fin).seatShortfall :=
  sorry

/-- Glue: V keys are current at R, and distinct keys have distinct positions. -/
theorem bud_fall (h : Setting config checks g split fin pulled anc counted V) :
    (∑ v ∈ V, (pinTerms config pulled anc fin).fall v.toNat) ≤ ∑ i ∈ (pinTerms config pulled anc fin).positions with (pinTerms config pulled anc fin).current i = true, (pinTerms config pulled anc fin).fall i := by
  have within := BeaconState.registryWithinLimit_of_lt h.early pulled
  have sub : V.image UInt64.toNat ⊆ (pinTerms config pulled anc fin).positions.filter
      (fun i => (pinTerms config pulled anc fin).current i = true) := by
    intro i member
    obtain ⟨v, voter, rfl⟩ := Finset.mem_image.mp member
    have listed : v ∈ getActiveValidatorIndices pulled (getCurrentEpoch pulled) := by
      simpa [activeVoters] using (h.voting v voter).1
    obtain ⟨validator, found, active⟩ := (mem_getActiveValidatorIndices within).mp listed
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1,
      isActiveAt_eq_true_iff.mpr ⟨validator, found, active⟩⟩
  rw [← Finset.sum_image (f := (pinTerms config pulled anc fin).fall)
    fun a _ b _ same => UInt64.toNat_inj.mp same]
  exact Finset.sum_le_sum_of_subset sub

/-- Glue: (K4 pulled counted V) keys are current at R. -/
theorem bud_rise (h : Setting config checks g split fin pulled anc counted V) :
    (∑ v ∈ (K4 pulled counted V), (pinTerms config pulled anc fin).rise v.toNat) ≤ ∑ i ∈ (pinTerms config pulled anc fin).positions with (pinTerms config pulled anc fin).current i = true, (pinTerms config pulled anc fin).rise i :=
  sorry

/-- `quorumReserve` holds `joining` (its gain term). -/
theorem bud_joining : (pinTerms config pulled anc fin).joining ≤ (pinTerms config pulled anc fin).quorum := sorry

end Stubs

/-! ## The top-level step, from the stubs -/

section Closure
variable {g : ForkedBeaconState preset} {split fin pulled anc counted : BeaconState preset fork}
  {V : Finset ValidatorIndex}


private theorem sum_eq_U {S W : Finset ValidatorIndex} (sub : S ⊆ W) (f : ValidatorIndex → ℤ) :
    ∑ v ∈ S, f v = ∑ v ∈ W, if v ∈ S then f v else 0 := by
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr sub]

/-- The weighted drift, key by key: exact per-key algebra, no reserve term. -/
private theorem drift_le_costs (h : Setting config checks g split fin pulled anc counted V) :
    3 * (∑ v ∈ Q counted, (eC counted v : ℤ)) + 3 * (∑ v ∈ V, (eR pulled v : ℤ)) -
        2 * (∑ v ∈ AC counted, (eC counted v : ℤ)) - (∑ v ∈ AR pulled, (eR pulled v : ℤ)) -
        3 * (∑ v ∈ (Q counted).filter (· ∈ V), (eC counted v : ℤ)) ≤
      2 * cV1 pulled counted V + 2 * cV2 pulled counted V + cN pulled counted V +
        3 * cP pulled counted V + cJ pulled counted + cK7 pulled counted +
        cS pulled counted V := by
  have hAR : ∀ v ∈ V, v ∈ AR pulled := fun v m => (h.voting v m).1
  have hQ := glue_quorum h
  have subQ : Q counted ⊆ U pulled counted := fun v m => by simp [U, m]
  have subAC : AC counted ⊆ U pulled counted := fun v m => by simp [U, m]
  have subAR : AR pulled ⊆ U pulled counted := fun v m => by simp [U, m]
  have subV : V ⊆ U pulled counted := fun v m => subAR (hAR v m)
  have subQV : (Q counted).filter (· ∈ V) ⊆ U pulled counted :=
    fun v m => subQ (Finset.mem_filter.mp m).1
  rw [sum_eq_U subQ, sum_eq_U subV, sum_eq_U subAC, sum_eq_U subAR, sum_eq_U subQV]
  unfold cV1 cV2 cN cP cJ cK7 cS
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro v _
  simp only [Finset.mem_filter]
  by_cases hv : v ∈ V
  · have hr := hAR v hv
    by_cases ha : v ∈ AC counted
    · have hq := hQ v hv ha
      simp [hv, ha, hr, hq]
      omega
    · by_cases hq : v ∈ Q counted <;> simp [hv, ha, hr, hq] <;> omega
  · by_cases hq : v ∈ Q counted <;> by_cases ha : v ∈ AC counted <;>
      by_cases hr : v ∈ AR pulled <;> simp [hv, ha, hr, hq] <;> omega

private theorem two_le_three {x : ℤ} {r : ℕ} (le : x ≤ r) : 2 * x ≤ 3 * (r : ℤ) := by omega

/-- The total read is at least the active stake. -/
private theorem stake_le_total {state : BeaconState preset fork} {total : Gwei}
    (ok : getTotalActiveBalance state = .ok total) :
    (∑ v ∈ activeVoters state, balanceAt state v.toNat) ≤ total.toNat := by
  obtain ⟨-, -, value⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok ok)
  rw [value]
  exact le_max_right _ _

/-- The top-level step, closed from the stubs.

It closes only with the extra term `3 · Σ_{(K5 counted V)} (rise + credC)`: the C-side rise of keys that are
previous-epoch-only in C weighs 3 in the drift, and no term of `pinReserve` charges it at 3. -/
theorem pinDrift_le_of_stubs (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (highLe : highC ≤ (getCurrentEpoch pulled).toNat)
    (highLeR : high ≤ (getCurrentEpoch pulled).toNat)
    (band : 10 * preset.upwardBand ≤ preset.MAX_EFFECTIVE_BALANCE.toNat)
    {total pulledTotal : Gwei} (totalOk : getTotalActiveBalance counted = .ok total)
    (pulledOk : getTotalActiveBalance pulled = .ok pulledTotal) :
    3 * stake (fun v => balanceAt counted v.toNat) (quorumVoters counted) +
        3 * stake (fun v => balanceAt pulled v.toNat) V ≤
      2 * total.toNat + pulledTotal.toNat + pinReserve config pulled anc fin +
        3 * stake (fun v => balanceAt counted v.toNat) {v ∈ quorumVoters counted | v ∈ V} := by
  have key := drift_le_costs h
  have tC := stake_le_total totalOk
  have tR := stake_le_total pulledOk
  have sV := two_le_three (stub_V (config := config) h tail high endEpoch replayed tailC highC endEpochC replayedC)
  have sN := stub_N (config := config) h tail high endEpoch replayed tailC highC endEpochC replayedC
  have sP := stub_P (config := config) h tail high endEpoch replayed tailC highC endEpochC replayedC
  have sJ := stub_J (config := config) h tail high endEpoch replayed tailC highC endEpochC replayedC
  have b1 := bud_exiting (config := config) (pulled := pulled) (anc := anc) (fin := fin)
    (counted := counted) (V := V)
  have b2 := bud_late (config := config) h
  have b3 := bud_queues (config := config) h tailC
  have b4 := bud_credits (config := config) h tailC highC endEpochC replayedC
  have b5 := bud_branchR (config := config) h tail high endEpoch replayed
  have b6 := bud_sync (config := config) h tail high replayed tailC highC replayedC
  have b7 := bud_fall (config := config) h
  have b8 := bud_rise (config := config) h
  have b10 := bud_deposits (config := config) h tail high endEpoch replayed
  have b11 := bud_queueRise (config := config) h tailC highC endEpochC
  have b12 := bud_exitingRise (config := config) h
  have b13 := bud_exitingCredits (config := config) h tailC highC endEpochC replayedC
  have b17 := bud_exitingBands (config := config) h tailC highC endEpochC
  have b18 := bud_pendingR (config := config) h
  -- `stub_J` reads `creditGain` only in its high regime.
  have gainHighLe : (if (pinTerms config pulled anc fin).gainHigh then
      (pinTerms config pulled anc fin).creditGain else 0) ≤
        (pinTerms config pulled anc fin).creditGain := by
    split <;> omega
  obtain ⟨fromFin⟩ := h.fromFin
  have b15 := bud_consolidations (config := config) h fromFin tail high endEpoch replayed highLeR
    tailC highC endEpochC replayedC highLe h.shallow band
  have b16 := bud_exitedR (config := config) (pulled := pulled) (anc := anc) (fin := fin)
    (counted := counted)
  -- The band of each due entry naming a V key is paid by `bud_consolidations`' V share.
  have bandV : 3 * (preset.upwardBand * dueAt fin high V) ≤
      preset.upwardBand * (dueAt fin highC (K4 pulled counted V) +
        dueAt fin highC (K6 pulled counted) + 3 * dueAt fin highC (K5 counted V) +
        3 * dueAt fin high V) := by
    rw [Nat.mul_left_comm]
    exact Nat.mul_le_mul_left _ (by omega)
  have b15' := Nat.le_trans (Nat.add_le_add_left bandV _) b15
  have qs := queues_split config pulled anc fin
  have b14 := bud_whistle (config := config) h tailC highC endEpochC replayedC
  have w4 : 0 ≤ ∑ v ∈ (K4 pulled counted V), (whistC tailC highC v.toNat : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  have w6 : 0 ≤ ∑ v ∈ (K6 pulled counted), (whistC tailC highC v.toNat : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  have b9 := bud_joining (config := config) (pulled := pulled) (anc := anc) (fin := fin)
  rw [pinReserve_eq_total]
  unfold PinTerms.total stake
  simp only [AC, AR, Q, eC, eR] at *
  simp only [Finset.sum_add_distrib] at sV sN sP sJ b2 b5 b6 b16 b18 ⊢
  zify at *
  have syncPos : 0 ≤ ∑ x ∈ K4 pulled counted V, (syncF events x.toNat : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  have syncPosC : 0 ≤ ∑ x ∈ K4 pulled counted V, (syncF eventsC x.toNat : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  have xPos : 0 ≤ (33 * ((pinTerms config pulled anc fin).consolidationsX : ℤ) + 9) / 10 := by
    positivity
  have proposerPos : 0 ≤ ((pinTerms config pulled anc fin).depth : ℤ) *
      ((pinTerms config pulled anc fin).syncProposer : ℤ) := by positivity
  -- A key of `K6` whose exit R reads weighs once in the drift and three times in `exiting`.
  have exitingK6 : 0 ≤ ∑ v ∈ K6 pulled counted with
      (pinTerms config pulled anc fin).exitingB v.toNat = true, (balanceAt pulled v.toNat : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  have riseK6 : 0 ≤ ∑ v ∈ K6 pulled counted with
      (pinTerms config pulled anc fin).exitingB v.toNat = true,
        ((pinTerms config pulled anc fin).rise v.toNat : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  linarith

end Closure

end PinSum
end EthLib.Consensus.Models.Network
