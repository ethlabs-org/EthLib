module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumReserve
public import EthLib.Consensus.Proofs.Transition.BalanceDrift
public import EthLib.Consensus.Proofs.Transition.FfgJustification
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.SlashedExit
import EthLib.Consensus.Proofs.Transition.SlashedPersistence
import EthLib.Consensus.Proofs.Transition.EpochPassAtCall
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

/-!
# The quorum of a call drifts by at most its pin reserve, on another branch

A call of the fast confirmation rule reads the pulled-up head state R of an honest store.

A counting state C of another honest store may lie on another branch since the finalized checkpoint.

The two branches leave one split state, at or after the finalized checkpoint's epoch.

This file bounds the drift of the quorum from R to C by `pinReserve`.

## Keys active only in the previous epoch of the counting state

A key that counts in C's quorum but is not active at C's epoch exits by the epoch after R's.

When activity up to C's epoch is fixed at the split, R reads that exit exactly.

So `pinReserve` charges such a key in its `exiting` term.

A slashed key there was slashed after the split, since C does not hold the slashing.

A slashing sets the withdrawable epoch at least `EPOCHS_PER_SLASHINGS_VECTOR` after it.

## The penalties of one key over several epochs

A key pays penalties only in the rewards pass at the end of each epoch.

The pass reads the total, the key's effective balance and its score at the epoch's last state.

So a bound on that rate at each such state bounds the key's penalties over the branch.

## The band of totals

The reserve reads its rates at the call's total, so it needs every total on both branches nearby.

`aprioriGuardAt` at the finalized state bounds each total of a branch from it by a floor and a
ceiling.

Before Gloas, twice the last ceiling of the window is at most three times its last floor.

So two totals of the window are within three halves of each other.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- A key in the counting state's quorum that is not active at its epoch is in `exiting`.

Activity up to the counting state's epoch is fixed at the split, so both states read it alike.

The key is active in the counting state's previous epoch and not in its current one.

So it is active in R's previous or current epoch, and it exits by the epoch after R's.

If R holds it slashed, the slashing came after the split.

The counting state holds it unslashed, and a run keeps every slashing.

Then its withdrawable epoch is at least the split's epoch plus `EPOCHS_PER_SLASHINGS_VECTOR`. -/
private theorem previousOnly_mem_exiting {split pulled counted anc : BeaconState preset fork}
    (toPulled : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (toCounted : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    (early : fork < .glamsterdam) (caps : CapOrder preset)
    (withdrawDelay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (finalized : anc.finalizedCheckpoint.epoch ≤ getCurrentEpoch split)
    (tight : getCurrentEpoch counted ≤ activityFixedEpoch split)
    (later : getCurrentEpoch pulled ≤ getCurrentEpoch counted)
    (near : (getCurrentEpoch counted).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {v : ValidatorIndex} (quorum : v ∈ quorumVoters counted)
    (inactive : v ∉ getActiveValidatorIndices counted (getCurrentEpoch counted)) :
    ∃ validator, pulled.validators.data[v.toNat]? = some validator ∧
      (isActiveAt pulled (getPreviousEpoch pulled) v.toNat ||
        isActiveAt pulled (getCurrentEpoch pulled) v.toNat) = true ∧
      (validator.slashed = false ∨ anc.finalizedCheckpoint.epoch.toNat +
        preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤ validator.withdrawableEpoch.toNat) ∧
      validator.exitEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
  have within := BeaconState.registryWithinLimit_of_lt early counted
  simp only [quorumVoters, Finset.mem_filter, List.mem_toFinset, List.mem_append] at quorum
  obtain ⟨member, unslashedC⟩ := quorum
  have previous := member.resolve_left inactive
  have keptC := activeKept_of_chainSteps toCounted.chainSteps
  have keptP := activeKept_of_chainSteps toPulled.chainSteps
  have pNat := getPreviousEpoch_toNat counted
  have pLe := getPreviousEpoch_le counted
  have pulledPrev := getPreviousEpoch_toNat pulled
  generalize getPreviousEpoch counted = p at *
  generalize getCurrentEpoch counted = c at *
  -- Activity up to the counting state's epoch is the split's, on both runs.
  have pFixed : p ≤ activityFixedEpoch split := UInt64.le_trans pLe tight
  have activeP : isActiveAt counted p v.toNat = true := by
    obtain ⟨val, found, active⟩ := (mem_getActiveValidatorIndices within).mp previous
    simp [isActiveAt, found, active]
  have notActiveC : isActiveAt counted c v.toNat = false := by
    cases h : isActiveAt counted c v.toNat
    · rfl
    · exact absurd (mem_getActiveValidatorIndices_of_isActiveAt h) inactive
  have splitP : isActiveAt split p v.toNat = true := (keptC p pFixed v.toNat).symm.trans activeP
  have pulledP : isActiveAt pulled p v.toNat = true := (keptP p pFixed v.toNat).trans splitP
  have pulledC : isActiveAt pulled c v.toNat = false :=
    (keptP c tight v.toNat).trans ((keptC c tight v.toNat).symm.trans notActiveC)
  obtain ⟨validator, found, activeAtP⟩ := isActiveAt_eq_true_iff.mp pulledP
  have inactiveAtC : isActiveValidator validator c = false := by
    simpa [isActiveAt, found] using pulledC
  -- Active at `p` and not at `c`: so `p` is the epoch before `c`, and the exit is by `c`.
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, Bool.and_eq_false_iff,
    decide_eq_false_iff_not] at activeAtP inactiveAtC
  have pc := UInt64.le_iff_toNat_le.mp pLe
  have lowP := UInt64.le_iff_toNat_le.mp activeAtP.1
  have highP := UInt64.lt_iff_toNat_lt.mp activeAtP.2
  have exitLe : validator.exitEpoch.toNat ≤ c.toNat := by
    rcases inactiveAtC with low | high
    · exact absurd (UInt64.le_iff_toNat_le.mpr (by omega)) low
    · exact Nat.le_of_not_lt fun lt => high (UInt64.lt_iff_toNat_lt.mpr lt)
  have laterNat := UInt64.le_iff_toNat_le.mp later
  refine ⟨validator, found, ?_, ?_, by omega⟩
  · -- `p` is R's previous epoch or its current one.
    rcases Nat.lt_or_ge c.toNat ((getCurrentEpoch pulled).toNat + 1) with same | next
    · have : p = getPreviousEpoch pulled := UInt64.toNat_inj.mp (by omega)
      simp [← this, pulledP]
    · have : p = getCurrentEpoch pulled := UInt64.toNat_inj.mp (by omega)
      simp [← this, pulledP]
  · -- A slashing that R holds and the counting state does not came after the split.
    cases slashed : validator.slashed
    · exact .inl rfl
    · obtain ⟨old, oldFound, -⟩ := isActiveAt_eq_true_iff.mp splitP
      cases oldSlashed : old.slashed
      · have delayed := (toPulled.newly_slashed_withdrawableEpoch caps.activation
          caps.compounding early withdrawDelay v.toNat old validator oldFound found oldSlashed
          slashed).2
        have := UInt64.le_iff_toNat_le.mp finalized
        exact .inr (Nat.le_trans (Nat.add_le_add_right this _) delayed)
      · obtain ⟨now, nowFound, nowSlashed⟩ :=
          toCounted.slashedPersistence v.toNat old oldFound oldSlashed
        simp [nowFound, nowSlashed] at unslashedC

open DirectSafety DirectSafety.Apriori.Internal

/-- The rate at which one rewards pass can debit a key, read at the last state of the epoch.

It reads the total active balance, the key's effective balance and its score there.

The pass reads the score after its update, which adds at most the score bias. -/
private def passPenaltyRate (config : Config) (z : ForkedBeaconState preset) (v : ℕ) : ℕ :=
  let total := max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (∑ i ∈ (Finset.range z.state.validators.data.size).filter
        (fun i => isActiveAt z.state (getCurrentEpoch z.state) i = true),
      ((z.state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0)
  let score := if altair : .altair ≤ z.fork then
      (((z.state.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0
  (TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat) * preset.BASE_REWARD_FACTOR.toNat *
      effectiveAt z v / (WEIGHT_DENOMINATOR.toNat * total.sqrt) +
    effectiveAt z v * (score + config.INACTIVITY_SCORE_BIAS.toNat) /
      (config.INACTIVITY_SCORE_BIAS.toNat *
        (parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat)

/-- Events with no penalty or inactivity source debit no key as a penalty. -/
private theorem penaltyDebit_sum_zero {events : List (BalanceEvent preset)}
    (free : PenaltyFree events) (v : ℕ) : (events.map (penaltyDebit v)).sum = 0 :=
  List.sum_eq_zero fun _ member => by
    obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
    simp [penaltyDebit, (free e inside).1, (free e inside).2]

/-- The penalties of one key in one segment of a branch fit its pass rate, if the segment ends an
epoch, and are zero otherwise.

Every step of the segment starts at the epoch of its start `m`.

Inside the epoch only blocks run, and they record no penalty.

The slot that ends the epoch runs the rewards pass, read at its last state.

So a segment that stays in its epoch pays nothing. -/
private theorem segment_passDebit_le {m n : ForkedBeaconState preset}
    (mid : Run config checks m n) (early : n.fork < .glamsterdam) (altair : .altair ≤ m.fork)
    (high : ℕ) (endEpoch : (getCurrentEpoch n.state).toNat ≤ high + 1)
    (starts : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      mid.Contains step → getCurrentEpoch u.state = getCurrentEpoch m.state)
    {v : ℕ} (inside : v < m.state.validators.data.size) (pen : ℕ)
    (rate : ∀ {z : ForkedBeaconState preset} (pre : Run config checks m z)
      (post : Run config checks z n), mid = pre.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch n.state).toNat →
      passPenaltyRate config z v ≤ pen)
    {found : List (BalanceEvent preset)} (replayed : mid.balanceEvents high = .ok found) :
    (found.map (penaltyDebit v)).sum ≤
      if getCurrentEpoch m.state < getCurrentEpoch n.state then pen else 0 := by
  by_cases same : getCurrentEpoch n.state = getCurrentEpoch m.state
  · -- A segment inside its epoch runs only blocks, which record no penalty.
    have free := (epoch_sync_data mid altair early same high replayed).2.1
    rw [penaltyDebit_sum_zero free]
    exact Nat.zero_le _
  cases mid with
  | nil => exact absurd rfl same
  | @snoc u _ inner step =>
  have uEarly : u.fork < .glamsterdam := Nat.lt_of_le_of_lt step.chainStep.fork_le early
  have uEpoch : getCurrentEpoch u.state = getCurrentEpoch m.state := starts step (.last _ _)
  have crossing : getCurrentEpoch u.state < getCurrentEpoch n.state :=
    UInt64.lt_of_le_of_ne step.chainStep.currentEpoch_le
      (fun equal => same (equal.symm.trans uEpoch))
  rw [ite_eq_left (uEpoch ▸ crossing)]
  -- The last step leaves the epoch, so it is the slot that ends it.
  obtain ⟨boundary, rfl⟩ : ∃ boundary, step = .slot boundary := by
    cases step with
    | block engine signed due ok =>
      exact absurd (by simp only [getCurrentEpoch, (frame_processBlock
        (applySignedBlock_ok ok).2.1).slot]) (UInt64.ne_of_lt crossing).symm
    | slot ok => exact ⟨ok, rfl⟩
  obtain ⟨added, addedOk⟩ := (Step.slot boundary).balanceEvents_ok early
  obtain ⟨during, duringOk⟩ := inner.balanceEvents_ok uEarly high
  have split : found = during ++ added := by
    simp only [Run.balanceEvents, duringOk, addedOk, bind, Except.bind,
      show (getCurrentEpoch u.state).toNat ≤ high + 1 by
        have := UInt64.lt_iff_toNat_lt.mp crossing; omega,
      ↓reduceIte, pure, Except.pure, Except.ok.injEq] at replayed
    exact replayed.symm
  subst split
  have free := (epoch_sync_data inner altair uEarly uEpoch high duringOk).2.1
  simp only [List.map_append, List.sum_append, penaltyDebit_sum_zero free, Nat.zero_add]
  -- The slot records the epoch passes, then the upgrades, which are fork crossings.
  obtain ⟨advanced, cached, crossings, -, -, cachedOk, crossingOk, kind⟩ :=
    Step.balanceEvents_slot boundary early addedOk
  have crossed := upgradeBalanceReplay_crossing crossingOk
  have crossingsFree : PenaltyFree crossings := fun e member => by
    simp [crossed e member]
  rcases kind with ⟨-, rfl⟩ | ⟨middle, -, recorded, recordOk, -, -, -, rfl, -⟩
  · rw [penaltyDebit_sum_zero crossingsFree]
    exact Nat.zero_le _
  have altairU : .altair ≤ u.fork := Nat.le_trans altair (fork_le_of_chainSteps inner.chainSteps)
  obtain ⟨just, pass, rewarded, later, justified, scored, rewardedOk, recordedEq, laterSources,
    -⟩ := epochReplay_events altairU (epochBalanceReplay_trace recordOk)
  simp only at recordedEq
  subst recordedEq
  have laterFree : PenaltyFree later := fun e member => by
    rcases laterSources e member with s | s | s <;> simp [s]
  simp only [List.map_append, List.sum_append, penaltyDebit_sum_zero laterFree,
    penaltyDebit_sum_zero crossingsFree, Nat.add_zero]
  -- The pass reads the registry, the slot and the scores of `u`, after one update of the scores.
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  have one := justified.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have two := scored.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have validators : pass.validators = u.state.validators := two.1.trans one.1
  have slot : pass.slot = u.state.slot := two.2.2.2.2.trans one.2.2.2.2
  have passEpoch : getCurrentEpoch pass = getCurrentEpoch u.state := by
    simp only [getCurrentEpoch, slot]
  have scoredOk : processInactivityUpdates config just altairU = .ok pass := by
    simpa only [EpochStage.Edge, altairU, ↓reduceDIte] using scored
  have justScores := processJustificationAndFinalization_inactivityScores justified
  have grows := registryGrows_of_chainSteps inner.chainSteps
  have insidePass : v < pass.validators.data.size := by rw [validators]; omega
  rcases replayRewards_penalty_scalar_cases altairU (pass.validators.bound uEarly) rewardedOk {v}
      (fun j member => by rw [Finset.mem_singleton.mp member]; exact insidePass) with
    ⟨total, -, passTotal, -⟩ | quiet
  swap
  · simp only [Finset.sum_singleton] at quiet
    rw [quiet]
    exact Nat.zero_le _
  set score := (if later : .altair ≤ u.fork then
      (((u.state.inactivityScores later).data[v]?).map (·.toNat)).getD 0 else 0) with scoreDef
  have bound := passPenalties_le altairU (pass.validators.bound uEarly) rewardedOk passTotal {v}
    (fun j member => by rw [Finset.mem_singleton.mp member]; exact insidePass)
    (maxScore := score + config.INACTIVITY_SCORE_BIAS.toNat) (fun j member found' updated => by
      rw [Finset.mem_singleton.mp member] at updated
      obtain ⟨old, olds, raised⟩ := processInactivityUpdates_score_le scoredOk updated
      rw [justScores] at olds
      have : old.toNat = score := by simp [scoreDef, altairU, olds]
      omega)
  simp only [Finset.sum_singleton] at bound
  refine bound.trans (le_trans ?_ (rate inner (.snoc .nil (.slot boundary)) rfl
    (UInt64.lt_iff_toNat_lt.mp crossing)))
  -- The pass's reads are those of `u`.
  have weight : eligibleWeight pass v ≤ effectiveAt u v := by
    unfold eligibleWeight
    simp only [validators, effectiveAt]
    split <;> [split <;> simp_all; simp]
  have totalValue : total.toNat = max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (∑ i ∈ (Finset.range u.state.validators.data.size).filter
          (fun i => isActiveAt u.state (getCurrentEpoch u.state) i = true),
        ((u.state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0) := by
    rw [getTotalActiveBalance_toNat passTotal, ← passEpoch]
    simp only [isActiveAt, validators]
    congr
  unfold passPenaltyRate
  dsimp only
  rw [← totalValue, ← scoreDef]
  apply Nat.add_le_add
  · apply Nat.div_le_div_right
    exact Nat.mul_le_mul_left _ weight
  · apply Nat.div_le_div_right
    exact Nat.mul_le_mul_right _ weight

/-- The first `k` of the first `j` terms each count `pen`. -/
private theorem sum_range_ite_lt (pen k : ℕ) :
    ∀ j, ((List.range j).map fun t => if t < k then pen else 0).sum = min j k * pen
  | 0 => by simp
  | j + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_ite_lt pen k j]
    by_cases below : j < k
    · simp [below, Nat.min_eq_left (Nat.le_of_lt below), Nat.min_eq_left (Nat.succ_le_of_lt below),
        Nat.succ_mul]
    · have atLeast : k ≤ j := Nat.le_of_not_lt below
      simp [below, Nat.min_eq_right atLeast, Nat.min_eq_right (Nat.le_succ_of_le atLeast)]

/-- The penalties of one key over a branch from Altair are at most its pass rate per epoch ended.

The rate must hold at each state of the branch before the epoch of its end.

The branch ends `epoch y - epoch x` epochs, and each runs one rewards pass.

The cut induction of the a priori bound, `run_cuts_le`, sums the segments. -/
private theorem Run.passDebit_le {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (altair : .altair ≤ x.fork) (high : ℕ)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    {v : ℕ} (inside : v < x.state.validators.data.size) (pen : ℕ)
    (rate : ∀ {z : ForkedBeaconState preset} (pre : Run config checks x z)
      (post : Run config checks z y), tail = pre.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch y.state).toNat →
      passPenaltyRate config z v ≤ pen)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    (events.map (penaltyDebit v)).sum ≤
      ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) * pen := by
  have total := run_cuts_le high tail early (fun z => passPenaltyRate config z v ≤ pen)
    (penaltyDebit v) (fun t => if t < ix x y then pen else 0) rate
    (fun {m n} toM mid rest starts rates {found} found_ok => by
      have nEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) early
      have ny := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest.chainSteps)
      have segment := segment_passDebit_le mid nEarly
        (Nat.le_trans altair (fork_le_of_chainSteps toM.chainSteps)) high (by omega) starts
        (Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps toM.chainSteps)) pen rates
        found_ok
      refine segment.trans ?_
      split
      · rename_i before
        have := UInt64.lt_iff_toNat_lt.mp before
        have xm := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps toM.chainSteps)
        simp only [ix]
        rw [ite_eq_left (by omega)]
      · exact Nat.zero_le _)
    (ix x y + 1) (fun step member => steps_before_end tail step member) replayed
  rw [sum_range_ite_lt, Nat.min_eq_right (Nat.le_succ _)] at total
  exact total

/-- The sync debit of one key in one event. -/
private def syncDebit (v : ℕ) (event : BalanceEvent preset) : ℕ :=
  if event.source = .sync then actualBalanceAt event.before v - actualBalanceAt event.after v else 0

/-- The balance of a key that stays unslashed falls over a branch only by its debits.

It starts from the smaller of its balance and its largest effective balance.

A sweep of its excess and a switch to compounding leave at least that much.

The debits are its passes, at most its pass rate per epoch ended, its sync penalties, and the
partial withdrawals that the branch pays it.

The guards are those of the per-key floor of the a priori bound, `FloorTrace.run_of_le_cap`. -/
private theorem Run.balanceFloor {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (early : y.fork < .glamsterdam) (altair : .altair ≤ x.fork) (high : ℕ)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (v : ValidatorIndex) (val : Validator) (initial : x.state.validators.data[v.toNat]? = some val)
    (unslashed : val.slashed = false) (activated : val.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (quotient : ℕ) (positive : 0 < quotient)
    (guards : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks x m)
      (step : Step config checks m n) (post : Run config checks n y),
      (pre.snoc step).append post = tail → ∀ w, n.state.validators.data[v.toNat]? = some w →
      high + 1 < w.exitEpoch.toNat ∧
      (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
        preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
          (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat ∧
      quotient ≤ (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
      ∀ events, step.balanceEvents = .ok events → ∀ e ∈ events, e.source ≠ .crossing)
    (stays : ∀ w, y.state.validators.data[v.toNat]? = some w → w.slashed = false)
    (pen : ℕ)
    (rate : ∀ {z : ForkedBeaconState preset} (pre : Run config checks x z)
      (post : Run config checks z y), tail = pre.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch y.state).toNat →
      passPenaltyRate config z v.toNat ≤ pen)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    min (actualBalanceAt x v.toNat) (withdrawalMaxEffectiveBalance preset x.fork val).toNat ≤
      actualBalanceAt y v.toNat +
        ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) * pen +
        (events.map (syncDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum := by
  obtain ⟨last, trace, balance, debt, -, w, final, -, used, -⟩ :=
    FloorTrace.run_of_le_cap shared tail genesis caps delay early high endEpoch v val initial
      unslashed
      activated (min (actualBalanceAt x v.toNat)
        (withdrawalMaxEffectiveBalance preset x.fork val).toNat) 0 quotient
      (Nat.min_le_right _ _) positive guards replayed
  have clean : last.slashedHigh = none := by
    cases flag : last.slashedHigh with
    | none => rfl
    | some _ => simp [flag, stays w final] at used
  have floor := FloorTrace.unslashed_balance_floor trace (by simp) clean
  have inside := (Array.getElem?_eq_some_iff.mp initial).1
  have passes := Run.passDebit_le tail early altair high endEpoch inside pen rate replayed
  have split : (events.map (floorPenaltyDebit v.toNat)).sum =
      (events.map (penaltyDebit v.toNat)).sum + (events.map (syncDebit v.toNat)).sum := by
    rw [← List.sum_map_add]
    rfl
  rw [balance, debt, split] at floor
  omega

/-- The partial payments to one key are a cost that selects that key's queued entries. -/
private theorem partialCost_key (v : ValidatorIndex) :
    PartialCost (config := config) (checks := checks) (floorPartialDebit (preset := preset) v)
      (fun entry => decide (entry.validatorIndex = v)) where
  quiet e source := by simp [floorPartialDebit, source]
  paid := by
    intro _ _ _ electra _ _ _ _ _ _ computed
    simpa [floorPartialDebit, electra, computed] using
      (getPendingPartialWithdrawals_taken computed).2 v
  slot ok early _ replayed := List.sum_eq_zero fun _ member => by
    obtain ⟨e, present, rfl⟩ := List.mem_map.mp member
    simp [floorPartialDebit, slot_events_no_withdrawals ok early replayed e present]

/-- The partial payments to one key over a branch from Electra are its entries of the queue at
the start that are due by the cutoff, while the cutoff is within the withdrawal delay of the start.

An entry appended along the branch is due no earlier than the delay after the start. -/
private theorem Run.partialDebit_le {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (high cutoff : ℕ) (endpoint : (getCurrentEpoch y.state).toNat ≤ cutoff)
    (short : cutoff < (getCurrentEpoch x.state).toNat +
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (v : ValidatorIndex) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events) :
    (events.map (floorPartialDebit v)).sum ≤
      ((((x.state.pendingPartialWithdrawals electra).data.toList.filter
        fun entry => decide (entry.validatorIndex = v)).filter
          (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)).map (·.amount.toNat)).sum := by
  obtain ⟨added, late, bound⟩ :=
    run_partial_queue_kept (partialCost_key v) high cutoff electra tail early replayed endpoint
  have none : ((added.filter fun entry => decide (entry.validatorIndex = v)).filter
      (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro entry member
    have := late entry (List.mem_of_mem_filter member)
    simp only [decide_eq_true_eq]
    omega
  rw [none] at bound
  simpa using bound

/-! ## The band of totals from the guard at the finalized state -/

section Band

open DirectSafety.Apriori

/-- From Electra, the ceiling of a window grows with the epoch of the window. -/
private theorem stakeCeilingAt_mono {x : ForkedBeaconState preset} {high : ℕ}
    (electra : .pectra ≤ x.fork) {s t : ℕ} (le : s ≤ t) :
    stakeCeilingAt config x high s ≤ stakeCeilingAt config x high t := by
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  have zero : preElectraEpochs config x high = 0 := by simp [preElectraEpochs, notBefore]
  induction le with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    refine ih.trans ?_
    simp only [stakeCeilingAt, stakeCeiling, zero, Nat.lt_irrefl, false_and, ↓reduceIte]
    omega

/-- The floor of a window falls with the epoch of the window. -/
private theorem stakeFloorAt_anti {x : ForkedBeaconState preset} {high : ℕ} {s t : ℕ}
    (le : s ≤ t) : stakeFloorAt config x high t ≤ stakeFloorAt config x high s := by
  induction le with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    refine Nat.le_trans ?_ ih
    simp only [stakeFloorAt, stakeFloor, stakeFloorPath]
    omega

/-- From Electra and before Gloas, a state reached from a guarded state within its window has its
total between the window's last floor and last ceiling.

The window's last index is the epoch after `high`, counted from the guarded state's epoch. -/
private theorem total_within_guard {g x z : ForkedBeaconState preset} {high : ℕ}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : DirectSafety.Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (electra : .pectra ≤ x.fork) (guard : aprioriGuardAt config x high)
    (run : Run config checks x z) (early : z.fork < .glamsterdam)
    (within : (getCurrentEpoch z.state).toNat ≤ high + 1) {total : Gwei}
    (totalOk : getTotalActiveBalance z.state = .ok total) :
    let last := high + 1 - (getCurrentEpoch x.state).toNat
    stakeFloorAt config x high last ≤ total.toNat ∧
      total.toNat ≤ stakeCeilingAt config x high last := by
  intro last
  have index : ix x z ≤ last := by
    simp only [ix, last]
    omega
  obtain ⟨ceiling, -, floor⟩ := ceilingFloor_electra shared run high
    ⟨genesis, parameters, caps, aligned, early, within, guard⟩ twoSlots electra
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps run.chainSteps) early
  have unit := (ceiling_unit_of_guard shared genesis aligned xEarly electra guard).trans
    (stakeCeilingAt_mono electra (Nat.zero_le last))
  refine ⟨(stakeFloorAt_anti index).trans (floor total totalOk), ?_⟩
  obtain ⟨-, -, value⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok totalOk)
  rw [value]
  exact max_le unit (Nat.le_trans ceiling (stakeCeilingAt_mono electra index))

/-- From Electra and before Gloas, two states reached from a guarded state within its window have
totals within three halves of each other.

Both lie between the window's last floor and ceiling, and the guard asks that twice that ceiling
be at most three times that floor. -/
private theorem total_band_of_guard {g x y z : ForkedBeaconState preset} {high : ℕ}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : DirectSafety.Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (electra : .pectra ≤ x.fork) (guard : aprioriGuardAt config x high)
    (toY : Run config checks x y) (yEarly : y.fork < .glamsterdam)
    (yWithin : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (toZ : Run config checks x z) (zEarly : z.fork < .glamsterdam)
    (zWithin : (getCurrentEpoch z.state).toNat ≤ high + 1) {yTotal zTotal : Gwei}
    (yOk : getTotalActiveBalance y.state = .ok yTotal)
    (zOk : getTotalActiveBalance z.state = .ok zTotal) :
    2 * zTotal.toNat ≤ 3 * yTotal.toNat := by
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  have zero : preElectraEpochs config x high = 0 := by simp [preElectraEpochs, notBefore]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ratioGuard, -⟩ := id guard
  rw [zero] at ratioGuard
  have ratio := ratioGuard (high + 1 - (getCurrentEpoch x.state).toNat) (Nat.zero_le _)
    (by unfold driftHorizon; omega)
  obtain ⟨yLow, -⟩ := total_within_guard shared genesis parameters caps aligned twoSlots electra
    guard toY yEarly yWithin yOk
  obtain ⟨-, zHigh⟩ := total_within_guard shared genesis parameters caps aligned twoSlots electra
    guard toZ zEarly zWithin zOk
  simp only [stakeCeilingAt, stakeFloorAt, zero] at yLow zHigh ⊢
  omega

end Band


/-! ## Credits to exiting keys -/

/-- A pending deposit leaves a balance alone unless its key is first found at that position.

The validators only grow at the end. -/
private theorem applyPendingDeposit_frame {s s' : BeaconState preset fork}
    {deposit : PendingDeposit}
    (altair : .altair ≤ fork)
    (computed : applyPendingDeposit config checks s deposit = .ok s') {i : ℕ}
    (inside : i < s.validators.data.size)
    (other : s.validators.data.findIdx? (·.pubkey == deposit.pubkey) ≠ some i) :
    s'.balances.data[i]? = s.balances.data[i]? ∧
      ∃ suffix : List Validator,
        s'.validators.data.toList = s.validators.data.toList ++ suffix := by
  cases hf : s.validators.data.findIdx? (·.pubkey == deposit.pubkey) with
  | some j =>
    have ne : i ≠ j := fun same => other (same ▸ hf)
    exact ⟨(applyPendingDeposit_known_balances hf computed).2 i ne, [], by
      rw [(applyPendingDeposit_known hf computed).2, List.append_nil]⟩
  | none =>
    refine ⟨DirectSafety.Apriori.Internal.applyPendingDeposit_absent_balances altair hf computed
      inside, ?_⟩
    rcases applyPendingDeposit_cases computed with rfl | ⟨_, raised⟩ | ⟨_, added⟩
    · exact ⟨[], by simp⟩
    · exact ⟨[], by rw [increaseBalance_validators raised, List.append_nil]⟩
    · exact ⟨[getValidatorFromDeposit preset fork deposit.pubkey deposit.withdrawalCredentials
        deposit.amount], by rw [addValidatorToRegistry_validators_eq_push added, Array.toList_push]⟩

/-- From Electra, the pending deposits of an epoch leave a key's balance alone.

This holds while the key exits and is not yet withdrawable.

Such a key's deposits are postponed (`processPendingDeposits_postponed_epochs`). -/
private theorem processPendingDeposits_exited_balance {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after)
    {i : ℕ} {v : Validator} (found : state.validators.data[i]? = some v)
    (exited : v.exitEpoch.toNat < 2 ^ 64 - 1)
    (held : (getCurrentEpoch state).toNat < v.withdrawableEpoch.toNat) :
    after.balances.data[i]? = state.balances.data[i]? := by
  obtain ⟨read, rest, next, pending, carried, -, -, -, folded, rfl⟩ :=
    processPendingDeposits_postponed_epochs computed
  have inside : i < state.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
  have vAt : state.validators.data[i] = v := (Array.getElem?_eq_some_iff.mp found).2
  let P : BeaconState preset fork → Prop := fun s =>
    s.balances.data[i]? = state.balances.data[i]? ∧
      ∃ suffix : List Validator, s.validators.data.toList = state.validators.data.toList ++ suffix
  have final : P next := by
    refine foldlM_ok_invariant_of_mem P (fun s d s' member ⟨bal, suffix, pre⟩ step => ?_)
      ⟨rfl, [], by simp⟩ folded
    have sizeV : state.validators.data.size ≤ s.validators.data.size := by
      have := congrArg List.length pre
      simp only [Array.length_toList, List.length_append] at this
      omega
    have get : ∀ j (hj : j < state.validators.data.size) (hs : j < s.validators.data.size),
        s.validators.data[j] = state.validators.data[j] := by
      intro j hj hs
      have := congrArg (·[j]?) pre
      rw [List.getElem?_append_left (by rw [Array.length_toList]; exact hj),
        Array.getElem?_toList, Array.getElem?_toList, Array.getElem?_eq_getElem hs,
        Array.getElem?_eq_getElem hj] at this
      exact Option.some.inj this
    -- The deposit does not go to position `i`: its key would find `v`, which is postponed.
    have other : s.validators.data.findIdx? (·.pubkey == d.pubkey) ≠ some i := by
      intro hit
      obtain ⟨h, hitMatch, before⟩ := Array.findIdx?_eq_some_iff_getElem.mp hit
      have atI : s.validators.data[i] = v := (get i inside h).trans vAt
      have firstMatch : state.validators.data.find? (·.pubkey == d.pubkey) = some v := by
        rw [← Array.find?_toList, List.find?_eq_some_iff_getElem]
        refine ⟨atI ▸ hitMatch, i, by rw [Array.length_toList]; exact inside,
          by simp [vAt], fun j hj => ?_⟩
        have hjs : j < state.validators.data.size := by omega
        have := before j hj
        rw [get j hjs (by omega)] at this
        simpa using this
      have kept := (List.mem_filter.mp member).2
      rw [firstMatch] at kept
      simp only [Option.any_some, Bool.not_eq_true', Bool.and_eq_false_iff,
        decide_eq_false_iff_not] at kept
      omega
    obtain ⟨bal', suffix', pre2⟩ := applyPendingDeposit_frame
      (Nat.le_trans (show Fork.altair ≤ Fork.pectra by decide) electra) step
      (Nat.lt_of_lt_of_le inside sizeV) other
    exact ⟨bal'.trans bal, suffix ++ suffix', by rw [pre2, pre, List.append_assoc]⟩
  exact final.1

end EthLib.Consensus.Models.Network

namespace EthLib.Consensus.Models.Network

section GroupB

/-! ## PinSlashing -/

namespace PinSplit

open Base Uint64 Models DirectSafety

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- The credit of key `i` in one replayed event. -/
private def keyCredit (i : ℕ) (e : BalanceEvent preset) : ℕ :=
  actualBalanceAt e.after i - actualBalanceAt e.before i

/-- One slashing credits at most the slashed key's effective balance over the quotient.

The credits go to the proposer and the whistleblower together. -/
private theorem slashValidator_credits_le {state after : BeaconState preset fork}
    {slashed : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (computed : slashValidator config state slashed whistleblower = .ok after) :
    ∑ i ∈ Finset.range after.balances.data.size,
        (((after.balances.data[i]?).map (·.toNat)).getD 0 -
          ((state.balances.data[i]?).map (·.toNat)).getD 0) ≤
      balanceAt state slashed.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := by
  obtain ⟨exited, -, -, -, -, -, -, -, -, -, -, -, exitedOk, -⟩ := slashValidator_ok computed
  obtain ⟨v, found, -⟩ := initiateValidatorExit_ok exitedOk
  have bound := (initial_slashing_bounds state after slashed whistleblower v found computed).2
  have effective : balanceAt state slashed.toNat = v.effectiveBalance.toNat := by
    simp [balanceAt, getValidator_eq_ok_iff.mp found]
  rw [effective]
  exact bound

/-- A slashing of a key that has not started to exit starts its exit through the exit queue.

The exit epoch of the key is then not the far future, since the delay is positive. -/
private theorem slashValidator_exit_churn {state after : BeaconState preset fork}
    (electra : .pectra ≤ fork) {slashed : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (computed : slashValidator config state slashed whistleblower = .ok after)
    (fresh :
      ((state.validators.data[slashed.toNat]?).map (·.exitEpoch)).getD 0 = FAR_FUTURE_EPOCH) :
    ∃ middle, initiateValidatorExit config state slashed = .ok middle ∧
      (middle.validators.data[slashed.toNat]?).any (·.exitEpoch ≠ FAR_FUTURE_EPOCH) := by
  have _ := electra
  obtain ⟨exited, -, -, -, -, -, -, -, -, -, -, -, exitedOk, -⟩ := slashValidator_ok computed
  refine ⟨exited, exitedOk, ?_⟩
  obtain ⟨v, found, started | ⟨far, queued, exitEpoch, withdrawable, queue, summed, set⟩⟩ :=
    initiateValidatorExit_ok exitedOk
  · have read := getValidator_eq_ok_iff.mp found
    simp [read] at fresh
    exact absurd fresh started.1
  · obtain ⟨inside, rfl⟩ := setValidator_ok set
    have sum := (addChecked_ok_iff.mp summed).1
    have finite : exitEpoch ≠ FAR_FUTURE_EPOCH := by
      intro same
      rw [same] at sum
      have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
      omega
    simp [BeaconState.putValidator, finite]

/-- A value of a list is at most the largest value of the list. -/
private theorem le_foldr_max {α : Type} (f : α → ℕ) {l : List α} {z : α} (member : z ∈ l) :
    f z ≤ (l.map f).foldr max 0 := by
  induction l with
  | nil => cases member
  | cons head rest ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp member with rfl | inRest
    · exact Nat.le_max_left _ _
    · exact (ih inRest).trans (Nat.le_max_right _ _)

/-- Events within their credit limits credit the slashing events at most their limits. -/
private theorem slashing_credits_le_limits (events : List (BalanceEvent preset))
    (bounded : ∀ e ∈ events, e.credits ≤ e.creditLimit) :
    ((events.filter (·.source = .slashings)).map BalanceEvent.credits).sum ≤
      (events.map fun e => if e.source = .slashings then e.creditLimit else 0).sum := by
  induction events with
  | nil => simp
  | cons head rest ih =>
    have tailLe := ih fun e member => bounded e (List.mem_cons_of_mem _ member)
    have headLe := bounded head List.mem_cons_self
    by_cases source : head.source = .slashings
    · simp only [List.filter_cons, source, decide_true, ↓reduceIte, List.map_cons, List.sum_cons]
      omega
    · simp only [List.filter_cons, source, decide_false, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.sum_cons]
      omega

/-- Along a run from Electra, each key is slashed at most once.

So its whistleblower reward is paid once, at its effective balance when it is slashed. -/
private theorem Run.slashed_once {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (caps : CapOrder preset) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (high : ℕ)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    ((events.filter (·.source = .slashings)).map BalanceEvent.credits).sum ≤
      ∑ i ∈ Finset.range y.state.validators.data.size,
        if ((x.state.validators.data[i]?).map (·.slashed)).getD false = false ∧
            ((y.state.validators.data[i]?).map (·.slashed)).getD false = true
        then (((tail.balancePath.map fun z => effectiveAt z i).foldr max 0) /
            (parameters preset y.fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)
        else 0 := by
  obtain ⟨found, foundOk, bounded⟩ := Run.balanceEvents_bounded shared tail genesis early high
  rw [replayed] at foundOk
  cases foundOk
  refine (slashing_credits_le_limits events fun e member => (bounded e member).1).trans ?_
  let keys := (Finset.range y.state.validators.data.size).filter fun i =>
    ((x.state.validators.data[i]?).map (·.slashed)).getD false = false ∧
      ((y.state.validators.data[i]?).map (·.slashed)).getD false = true
  let charge (i : ℕ) : ℕ := ((tail.balancePath.map fun z => effectiveAt z i).foldr max 0) /
    (parameters preset y.fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  rw [← Finset.sum_filter]
  refine Apriori.Internal.slashing_credits_le shared tail genesis early caps.compounding high
    endEpoch keys charge ?_ replayed
  intro a b step contained i inside marked
  obtain ⟨pre, post, split⟩ := tail.contains_split step contained
  have flags : (a.state.validators.data[i]?.map (·.slashed)).getD false = false ∧
      (b.state.validators.data[i]?.map (·.slashed)).getD false = true := by
    simpa only [Bool.and_eq_true, Bool.not_eq_true'] using marked
  have last : (y.state.validators.data[i]?.map (·.slashed)).getD false = true := by
    cases found : b.state.validators.data[i]? with
    | none => simp [found] at flags
    | some v =>
      have was : v.slashed = true := by simpa [found] using flags.2
      obtain ⟨w, read, flag⟩ := post.slashedPersistence i v found was
      simp [read, flag]
  have first : (x.state.validators.data[i]?.map (·.slashed)).getD false = false := by
    cases found : x.state.validators.data[i]? with
    | none => simp
    | some v =>
      cases flag : v.slashed with
      | false => simp [flag]
      | true =>
        obtain ⟨w, read, kept⟩ := pre.slashedPersistence i v found flag
        simp [read, kept] at flags
  have onPath : a ∈ tail.balancePath := by
    rw [split, Run.balancePath_append]
    have head := Step.balancePath_ends step
    have inStep := List.mem_of_mem_head? head.1
    simp [Run.balancePath, inStep]
  have atLeast : a.fork ≥ .pectra := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
  have atMost : a.fork ≤ y.fork :=
    Nat.le_trans step.chainStep.fork_le (fork_le_of_chainSteps post.chainSteps)
  have sameQuotient : (EthLib.Consensus.parameters preset a.fork).WHISTLEBLOWER_REWARD_QUOTIENT =
      (parameters preset y.fork).WHISTLEBLOWER_REWARD_QUOTIENT := by
    have yLeast : y.fork ≥ .pectra := Nat.le_trans atLeast atMost
    simp [EthLib.Consensus.parameters, atLeast, yLeast]
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
    (Nat.lt_of_lt_of_le (Finset.mem_range.mp inside) post.registryLifecycle.size_le),
      first, last⟩, ?_⟩
  rw [sameQuotient]
  exact Nat.div_le_div_right (le_foldr_max (fun z => effectiveAt z i) onPath)
end PinSplit

/-! ## PinEffectiveFloor -/

namespace PinSplit2

open Base Uint64 Models

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- A key's cap at a state, `0` past the registry. -/
private def capAt (z : ForkedBeaconState preset) (i : ℕ) : ℕ :=
  ((z.state.validators.data[i]?).map fun v =>
    (withdrawalMaxEffectiveBalance preset z.fork v).toNat).getD 0

/-- The update of the effective balances keeps a lower bound on the effective balance of a key.

The balance must be at least `floor` and the cap at least `capLow`.

The bound must be at most `capLow` and at most `floor + 1` less one increment.

The new value is the old one, or the balance rounded down to an increment, at most the cap.

The rounding leaves less than one increment. -/
private theorem effective_floor_update {f : Fork} {s t : BeaconState preset f}
    (ok : processEffectiveBalanceUpdates s = .ok t) (i floor capLow low : ℕ)
    (positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (lowCap : low ≤ capLow)
    (lowFloor : low ≤ floor + 1 - preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (funded : floor ≤ actualBalanceAt ⟨f, s⟩ i) (previous : low ≤ effectiveAt ⟨f, s⟩ i)
    (cap : ∀ v, t.validators.data[i]? = some v →
      capLow ≤ (withdrawalMaxEffectiveBalance preset f v).toNat) :
    low ≤ effectiveAt ⟨f, t⟩ i := by
  have one {a b : BeaconState preset f} {j : Nat}
      (step : updateEffectiveBalance a j = .ok b) :
      b.balances = a.balances ∧
      (∀ v, b.validators.data[i]? = some v →
        capLow ≤ (withdrawalMaxEffectiveBalance preset f v).toNat) →
      (∀ v, a.validators.data[i]? = some v →
        capLow ≤ (withdrawalMaxEffectiveBalance preset f v).toNat) ∧
      (floor ≤ actualBalanceAt ⟨f, a⟩ i → low ≤ effectiveAt ⟨f, a⟩ i →
        low ≤ effectiveAt ⟨f, b⟩ i) := by
    simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at step
    obtain ⟨v, found, balance, read, next, changed, set⟩ := step
    obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
    intro premise
    have located := getValidatorAt_eq_ok_iff.mp found
    by_cases eq : i = j
    · subst i
      have nextRead :
          (a.putValidator j inside { v with effectiveBalance := next }).validators.data[j]? =
          some { v with effectiveBalance := next } := by
        simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set]
      have capped := premise.2 _ nextRead
      change capLow ≤ (withdrawalMaxEffectiveBalance preset f v).toNat at capped
      constructor
      · intro w wRead
        rw [located, Option.some.injEq] at wRead
        subst w
        exact capped
      · intro funded previous
        simp only [actualBalanceAt, getBalanceAt_eq_ok_iff.mp read, effectiveAt, located,
          Option.map_some, Option.getD_some] at funded previous
        simp only [effectiveAt, nextRead, Option.map_some, Option.getD_some]
        rcases updatedEffectiveBalance_cases changed with rfl | rfl
        · exact previous
        · have rounded : balance % preset.EFFECTIVE_BALANCE_INCREMENT ≤ balance :=
            UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_mod]; exact Nat.mod_le _ _)
          have remainder := Nat.mod_lt balance.toNat positive
          rw [Base.Uint64.toNat_min, UInt64.toNat_sub_of_le _ _ rounded, UInt64.toNat_mod]
          omega
    · have same :
          (a.putValidator j inside { v with effectiveBalance := next }).validators.data[i]? =
          a.validators.data[i]? := by
        simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, Ne.symm eq]
      constructor
      · simpa only [same] using premise.2
      · intro _ previous
        simpa only [effectiveAt, same] using previous
  have fold : ∀ (xs : List Nat) {a b : BeaconState preset f},
      xs.foldlM updateEffectiveBalance a = .ok b →
      (∀ v, b.validators.data[i]? = some v →
        capLow ≤ (withdrawalMaxEffectiveBalance preset f v).toNat) →
      (∀ v, a.validators.data[i]? = some v →
        capLow ≤ (withdrawalMaxEffectiveBalance preset f v).toNat) ∧
      (floor ≤ actualBalanceAt ⟨f, a⟩ i → low ≤ effectiveAt ⟨f, a⟩ i →
        low ≤ effectiveAt ⟨f, b⟩ i) := by
    intro xs
    induction xs with
    | nil => intro a b ok cap; cases ok; exact ⟨cap, fun _ previous => previous⟩
    | cons j xs ih =>
      intro a b ok cap
      obtain ⟨middle, updated, rest⟩ := bind_ok_iff.mp ok
      have tail := ih rest cap
      have balances : middle.balances = a.balances := by
        simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at updated
        obtain ⟨_, _, _, _, _, _, set⟩ := updated
        obtain ⟨_, rfl⟩ := setValidatorAt_ok set
        rfl
      have head := one updated ⟨balances, tail.1⟩
      exact ⟨head.1, fun funded previous => tail.2
        (by simpa only [actualBalanceAt, balances] using funded) (head.2 funded previous)⟩
  unfold processEffectiveBalanceUpdates at ok
  exact (fold _ ok cap).2 funded previous

/-- One slot step keeps the lower bound, given the balance and the cap after it.

Only the epoch transition changes an effective balance, in its update. -/
private theorem effective_floor_slot {f : Fork} {s t : BeaconState preset f}
    (ok : advanceSlot config checks s = .ok t) (i floor capLow low : ℕ)
    (inside : i < s.validators.data.size)
    (positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (lowCap : low ≤ capLow)
    (lowFloor : low ≤ floor + 1 - preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (funded : floor ≤ actualBalanceAt ⟨f, t⟩ i) (previous : low ≤ effectiveAt ⟨f, s⟩ i)
    (cap : ∀ v, t.validators.data[i]? = some v →
      capLow ≤ (withdrawalMaxEffectiveBalance preset f v).toNat) :
    low ≤ effectiveAt ⟨f, t⟩ i := by
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨next, _, cached, cache, advanced, advance, rfl⟩ := ok
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
  unfold epochIfLast at advance
  split at advance
  · obtain ⟨before, after, kept, updated, validators, balances⟩ := balanceDrift_epoch advance
    have prior : low ≤ effectiveAt ⟨f, before⟩ i := by
      rw [kept i inside]
      exact previous
    have bound := effective_floor_update updated i floor capLow low positive lowCap lowFloor
      (by simpa only [actualBalanceAt, balances] using funded) prior
      (fun v read => cap v (by rw [validators]; exact read))
    simpa only [effectiveAt, validators] using bound
  · cases advance
    exact previous

/-- Between the first fork of Fulu and Gloas, the upgrades leave the state as it is.

The only upgrade from a fork of that range leads to Gloas. -/
private theorem processUpgrades_eq_of_window {z z' : ForkedBeaconState preset}
    (ok : processUpgrades config checks z = .ok z') (fulu : .fusaka ≤ z.fork)
    (early : z'.fork < .glamsterdam) : z' = z := by
  have stays : z'.fork ≤ z.fork := by
    rw [processUpgrades] at ok
    split at ok
    · obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
      have later := processUpgrades_fork_le rest
      have reached : Fork.glamsterdam ≤ next.val.fork := by
        obtain ⟨fork, state⟩ := z
        cases fork <;> dsimp only at fulu <;>
          first
            | exact absurd fulu (by decide)
            | (simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
                throwThe, MonadExceptOf.throw, reduceCtorEq] at nextOk
               all_goals first
                 | (obtain ⟨_, -, rfl⟩ := nextOk; exact Nat.le_refl _)
                 | (obtain ⟨_, -, rfl⟩ := nextOk
                    exact Nat.le_of_lt (by decide : Fork.glamsterdam < Fork.hegota)))
      exact absurd (Nat.lt_of_le_of_lt (Nat.le_trans reached later) early) (Nat.lt_irrefl _)
    · cases ok
      exact Nat.le_refl _
  exact processUpgrades_eq_of_fork_le ok stays

/-- H4. A balance floor and a cap floor along a run give an effective-balance floor.

Suppose a key's balance stays at least `floor` at every state of a run.

Suppose also that its cap stays at least `capLow`.

Then its effective balance at the end is at least the least of three values.

They are its effective balance at the start, `capLow`, and `floor` less one increment of rounding.

An update moves the effective balance only at an epoch's first slot.

It moves it down to the balance rounded to an increment, which is at least `floor + 1 - inc`.

It moves it up to at most the cap, and never below where it was. -/
private theorem Run.effective_floor_of_balance_floor {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ x.fork)
    (bands : preset.IncrementWithinUpwardBand) (i : ℕ) (inside : i < x.state.validators.data.size)
    (floor capLow : ℕ)
    (balanceFloor : ∀ z ∈ tail.balancePath, floor ≤ actualBalanceAt z i)
    (capFloor : ∀ z ∈ tail.balancePath, capLow ≤ capAt z i) :
    min (effectiveAt x i) (min capLow (floor + 1 - preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
      effectiveAt y i := by
  have positive := bands.1
  induction tail with
  | nil => exact Nat.min_le_left _ _
  | @snoc middle last pre step ih =>
    have middleEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have prior := ih middleEarly (fun p member => balanceFloor p (List.mem_append_left _ member))
      (fun p member => capFloor p (List.mem_append_left _ member))
    have room : i < middle.state.validators.data.size :=
      Nat.lt_of_lt_of_le inside pre.registryLifecycle.size_le
    cases step with
    | @block fork before after engine signed due ok =>
      rw [effectiveKept_processBlock (applySignedBlock_ok ok).2.1 i room]
      exact prior
    | slot ok =>
      obtain ⟨next, advanced, upgraded⟩ := bind_ok_iff.mp ok
      have onPath : (⟨middle.fork, next⟩ : ForkedBeaconState preset) ∈
          (Step.slot ok).balancePath := by
        simp [Step.balancePath, advanced, Except.toOption]
      have funded := balanceFloor _ (List.mem_append_right _ onPath)
      have capped := capFloor _ (List.mem_append_right _ onPath)
      have fuluMiddle : Fork.fusaka ≤ middle.fork :=
        Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
      have same := processUpgrades_eq_of_window upgraded fuluMiddle early
      subst same
      refine effective_floor_slot advanced i floor capLow _ room positive
        (Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)) ?_ funded prior ?_
      · exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)
      · intro v read
        simpa [capAt, read] using capped
end PinSplit2

end GroupB

section GroupD

/-! ## PinPenaltyRate -/

namespace PinSplit2

open Base Uint64 Models

variable {preset : Preset} {config : Config}

/-- The rate at which one rewards pass can debit a key at a state is at most the leak rate the pin reserve reads.

The rate is taken at the key's effective balance at the state.

`pulledTotal` is R's total read, and `quarter` is `max inc (pulledTotal / 4)`.
The reserve reads the base reward per increment at the quarter.

The state's total is at least two thirds of R's, so its square root is at least the quarter's.

The score bound `scoreBound` covers the pass's score after its update, which is the score plus one bias.

Effective balances are whole increments.

`roomy` makes the rounding of the per-increment reward lose less than its fraction.

The flag term is `40 / 64` of a base reward per increment for each increment.
It fits in `2 * (increments * perIncrement)`, because the floor of a quotient that is at least one is at least half of it.

The left side is `passPenaltyRate config z v` of `PinDriftBound`, restated. -/
private theorem passPenaltyRate_le_leak (z : ForkedBeaconState preset) (v : ℕ) (pulledTotal : ℕ)
    (scoreBound : ℕ)
    (positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (roomy : 2 ^ 33 ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat)
    (pulledFits : pulledTotal < 2 ^ 64)
    (aligned : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ effectiveAt z v)
    (band : 2 * pulledTotal ≤ 3 * max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (∑ i ∈ (Finset.range z.state.validators.data.size).filter
          (fun i => isActiveAt z.state (getCurrentEpoch z.state) i = true),
        ((z.state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0))
    (scored : (if altair : .altair ≤ z.fork then
        (((z.state.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0) +
      config.INACTIVITY_SCORE_BIAS.toNat ≤ scoreBound) :
    let inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    let total := max inc
      (∑ i ∈ (Finset.range z.state.validators.data.size).filter
          (fun i => isActiveAt z.state (getCurrentEpoch z.state) i = true),
        ((z.state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0)
    let score := if altair : .altair ≤ z.fork then
        (((z.state.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0
    let quarter := max inc (pulledTotal / 4)
    let perIncrement := inc * preset.BASE_REWARD_FACTOR.toNat / quarter.sqrt
    (TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat) * preset.BASE_REWARD_FACTOR.toNat *
        effectiveAt z v / (WEIGHT_DENOMINATOR.toNat * total.sqrt) +
      effectiveAt z v * (score + config.INACTIVITY_SCORE_BIAS.toNat) /
        (config.INACTIVITY_SCORE_BIAS.toNat *
          (parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat) ≤
    2 * (effectiveAt z v / inc * perIncrement) +
      effectiveAt z v * scoreBound /
        (config.INACTIVITY_SCORE_BIAS.toNat *
          (parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
  intro inc total score quarter perIncrement
  have weights : TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat = 40 := by decide
  have denominator : WEIGHT_DENOMINATOR.toNat = 64 := by decide
  rw [weights, denominator]
  obtain ⟨k, hk⟩ := aligned
  have hinc : inc ≤ total := le_max_left _ _
  have hfactor : 1 ≤ preset.BASE_REWARD_FACTOR.toNat := by
    rcases Nat.eq_zero_or_pos preset.BASE_REWARD_FACTOR.toNat with zero | pos
    · rw [zero, Nat.mul_zero] at roomy
      exact absurd roomy (by decide)
    · exact pos
  -- the numerator of the per-increment reward, `X`, dominates the square root of the quarter
  obtain ⟨X, hX⟩ : ∃ X, inc * preset.BASE_REWARD_FACTOR.toNat = X := ⟨_, rfl⟩
  rw [hX] at roomy
  have hp : perIncrement = X / quarter.sqrt := by
    simp only [perIncrement, hX]
  have incX : inc ≤ X := by
    rw [← hX]
    exact Nat.le_mul_of_pos_right _ hfactor
  have quarterLe : quarter ≤ X ^ 2 := by
    refine max_le ?_ ?_
    · exact Nat.le_trans incX (Nat.le_self_pow (by decide) _)
    · have : 2 ^ 66 ≤ X ^ 2 := by
        calc 2 ^ 66 = (2 ^ 33) ^ 2 := by norm_num
          _ ≤ X ^ 2 := Nat.pow_le_pow_left roomy 2
      have : pulledTotal / 4 < 2 ^ 62 := by omega
      omega
  have quarterRoot : quarter.sqrt ≤ X := by
    have := Nat.sqrt_le_sqrt quarterLe
    rwa [Nat.sqrt_eq'] at this
  have quarterTotal : quarter ≤ total := by
    refine max_le hinc ?_
    have : 2 * pulledTotal ≤ 3 * total := band
    omega
  have totalRoot : quarter.sqrt ≤ total.sqrt := Nat.sqrt_le_sqrt quarterTotal
  have quarterPositive : 0 < quarter.sqrt :=
    Nat.sqrt_pos.mpr (Nat.lt_of_lt_of_le positive (le_max_left _ _))
  have perOne : 1 ≤ X / quarter.sqrt := (Nat.le_div_iff_mul_le quarterPositive).mpr (by omega)
  have rewardRate : 40 * preset.BASE_REWARD_FACTOR.toNat * effectiveAt z v / (64 * total.sqrt) ≤
      2 * (effectiveAt z v / inc * perIncrement) := by
    have increments : effectiveAt z v / inc = k := by
      rw [hk, Nat.mul_div_cancel_left _ positive]
    have numerator : 40 * preset.BASE_REWARD_FACTOR.toNat * effectiveAt z v = 40 * (k * X) := by
      rw [hk, ← hX]
      ring
    have totalPositive : 0 < total.sqrt := Nat.lt_of_lt_of_le quarterPositive totalRoot
    rw [increments, numerator]
    calc 40 * (k * X) / (64 * total.sqrt)
        ≤ 40 * (k * X) / (40 * total.sqrt) :=
          Nat.div_le_div_left (Nat.mul_le_mul_right _ (by decide)) (by positivity)
      _ = k * X / total.sqrt := Nat.mul_div_mul_left _ _ (by decide)
      _ ≤ k * X / quarter.sqrt := Nat.div_le_div_left totalRoot quarterPositive
      _ ≤ 2 * (k * perIncrement) := by
        refine Nat.div_le_of_le_mul ?_
        have split : X < (X / quarter.sqrt + 1) * quarter.sqrt := by
          have := Nat.lt_mul_div_succ X quarterPositive
          rwa [Nat.mul_comm] at this
        have step : X ≤ 2 * perIncrement * quarter.sqrt := by
          have : (X / quarter.sqrt + 1) ≤ 2 * (X / quarter.sqrt) := by omega
          rw [hp]
          exact Nat.le_of_lt (Nat.lt_of_lt_of_le split (Nat.mul_le_mul_right _ this))
        calc k * X ≤ k * (2 * perIncrement * quarter.sqrt) := Nat.mul_le_mul_left _ step
          _ = quarter.sqrt * (2 * (k * perIncrement)) := by ring
  have scoreRate : effectiveAt z v * (score + config.INACTIVITY_SCORE_BIAS.toNat) /
        (config.INACTIVITY_SCORE_BIAS.toNat *
          (parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat) ≤
      effectiveAt z v * scoreBound /
        (config.INACTIVITY_SCORE_BIAS.toNat *
          (parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat) :=
    Nat.div_le_div_right (Nat.mul_le_mul_left _ scored)
  exact Nat.add_le_add rewardRate scoreRate

/-- `roomy` on mainnet and minimal. -/
private theorem roomy_mainnet :
    2 ^ 33 ≤ Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT.toNat *
      Preset.mainnet.BASE_REWARD_FACTOR.toNat ∧
    2 ^ 33 ≤ Preset.minimal.EFFECTIVE_BALANCE_INCREMENT.toNat *
      Preset.minimal.BASE_REWARD_FACTOR.toNat := by
  decide
end PinSplit2

/-! ## PinWithdrawalFloor -/

namespace PinSplit3

open Base Uint64 Models

variable {preset : Preset} {fork : Fork}

/-- The loop of the queued partial withdrawals keeps a floor of a key's balance.

What the withdrawals take from the key, plus a floor at most the activation balance, stays within its balance.

Each entry pays at most the balance left above the activation balance. -/
private theorem getPendingPartialWithdrawals_loop_floor {state : BeaconState preset fork}
    {prior : Array Withdrawal} {epoch : Epoch} {limit : Nat} {index : ValidatorIndex}
    {balance : Gwei} {floor : Nat}
    (found : state.balances.data[index.toNat]? = some balance)
    (capped : floor ≤ preset.MIN_ACTIVATION_BALANCE.toNat) :
    ∀ (queue : List PendingPartialWithdrawal) (withdrawals : Array Withdrawal)
      (next : WithdrawalIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    withdrawnFrom (prior ++ withdrawals) index + floor ≤ balance.toNat →
    getPendingPartialWithdrawals.loop state prior epoch limit queue withdrawals next processed =
      .ok result →
    withdrawnFrom (prior ++ result.1) index + floor ≤ balance.toNat
  | [], _, _, _, _, bounded, computed => by
    simp only [getPendingPartialWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact bounded
  | pending :: rest, _, _, _, _, bounded, computed => by
    simp only [getPendingPartialWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact bounded
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, left, leftOk, computed⟩ := computed
      have leftOk := liftAccessor_ok.mp leftOk
      split at computed
      · rename_i eligible
        simp only [isEligibleForPartialWithdrawals, Bool.and_eq_true, decide_eq_true_eq]
          at eligible
        simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨⟨appended, following⟩, appendedOk, rest'⟩ := computed
        refine getPendingPartialWithdrawals_loop_floor found capped rest _ _ _ ?_ rest'
        rw [appendWithdrawal_withdrawnFrom_eq appendedOk]
        split
        · rename_i named
          subst named
          obtain ⟨read, readAt, sum⟩ := getBalanceAfterWithdrawals_ok leftOk
          rw [found, Option.some.injEq] at readAt
          subst readAt
          have above := UInt64.lt_iff_toNat_lt.mp eligible.2
          have paid : (min (left - preset.MIN_ACTIVATION_BALANCE) pending.amount).toNat ≤
              left.toNat - preset.MIN_ACTIVATION_BALANCE.toNat := by
            have := UInt64.toNat_sub_of_le left preset.MIN_ACTIVATION_BALANCE
              (UInt64.le_of_lt eligible.2)
            rw [UInt64.min_def]
            split
            · omega
            · have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp ‹_›)
              omega
          omega
        · simpa using bounded
      · exact getPendingPartialWithdrawals_loop_floor found capped rest _ _ _ bounded computed

/-- From Electra and before Gloas, a block's withdrawals leave a key that is not yet withdrawable
with at least the least of its balance before and `MIN_ACTIVATION_BALANCE`.

A pending partial pays at most the balance above `MIN_ACTIVATION_BALANCE`.
The sweep pays at most the balance above the key's cap, which is at least `MIN_ACTIVATION_BALANCE` because `compounding` bounds the cap of a compounding key.
Only a withdrawable key is paid in full. -/
private theorem processWithdrawals_balance_floor {state after : BeaconState preset fork}
    (capella : .shapella ≤ fork) (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after)
    (i : Nat) (v : Validator) (found : state.validators.data[i]? = some v)
    (notWithdrawable : getCurrentEpoch state < v.withdrawableEpoch) :
    min (((state.balances.data[i]?).map (·.toNat)).getD 0) preset.MIN_ACTIVATION_BALANCE.toNat ≤
      ((after.balances.data[i]?).map (·.toNat)).getD 0 := by
  obtain ⟨expected, expectedOk, -, appliedOk⟩ := processWithdrawals_expected early computed
  obtain ⟨applied, appliedFold, balances, -⟩ := applyExpectedWithdrawals_balances appliedOk
  unfold applyWithdrawals at appliedFold
  rw [← Array.foldlM_toList] at appliedFold
  rw [balances]
  cases held : state.balances.data[i]? with
  | none => simp
  | some balance =>
    simp only [Option.map_some, Option.getD_some]
    by_cases small : i < 2 ^ 64
    · have same : i.toUInt64.toNat = i := UInt64.toNat_ofNat_of_lt' small
      rw [← same] at found held
      have bounded := getExpectedWithdrawals_withdrawnFrom (.inl early) expectedOk held
      have lowered := applyWithdrawals_balance (.inl early) _ _ _ _ appliedFold held
        (by simpa using bounded)
      -- the cap of the key is at least the activation balance
      have cap : preset.MIN_ACTIVATION_BALANCE.toNat ≤
          (withdrawalMaxEffectiveBalance preset fork v).toNat := by
        unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance
        simp only [electra, ↓reduceIte]
        split
        · exact UInt64.le_iff_toNat_le.mp compounding
        · exact Nat.le_refl _
      obtain ⟨partials, next, partialsOk, sweepFloor⟩ :=
        getExpectedWithdrawals_sweep_floor early expectedOk found notWithdrawable held
      simp only [electra, ↓reduceDIte] at partialsOk
      have partialFloor : withdrawnFrom partials i.toUInt64 +
          min balance.toNat preset.MIN_ACTIVATION_BALANCE.toNat ≤ balance.toNat := by
        unfold getPendingPartialWithdrawals at partialsOk
        simp only [bind_ok_iff, ensure_ok_iff] at partialsOk
        obtain ⟨_, _, _, _, loopOk⟩ := partialsOk
        simpa using getPendingPartialWithdrawals_loop_floor held (Nat.min_le_right _ _) _ _ _ _
          (by
            have : withdrawnFrom (#[] ++ #[]) i.toUInt64 = 0 := by simp [withdrawnFrom]
            omega) loopOk
      rw [same] at lowered
      simp only [Array.toArray_toList] at lowered
      cases atLater : applied.balances.data[i]? with
      | none => simp [atLater] at lowered
      | some later =>
        simp only [atLater, Option.map_some, Option.some.injEq] at lowered
        simp only [Option.map_some, Option.getD_some]
        omega
    · -- No withdrawal names the index, so the balance is unchanged.
      have unchanged := applyWithdrawals_unnamed (index := i) _ _ _ appliedFold
        fun withdrawal _ atIndex => by
          have := UInt64.toNat_lt_size withdrawal.validatorIndex
          simp only [UInt64.size] at this
          omega
      rw [unchanged, held]
      simp only [Option.map_some, Option.getD_some]
      exact Nat.min_le_left _ _
end PinSplit3

/-! ## PinEventsKept -/

namespace PinSplit4

open Base Uint64 Models DirectSafety

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- What a chain of steps keeps of the registry, at any forks.

Assigned exits stay, a slash stays, and the withdrawable epoch of a key with an exit set only rises, and only for a slashed key. -/
private structure Kept {f g : Fork} (s : BeaconState preset f) (t : BeaconState preset g) :
    Prop where
  life : RegistryLifecycle s t
  slashed : SlashedPersistence s t
  withdrawable : WithdrawableKept s t

/-- Two steps keep what one keeps.

The exit of the first comes from its lifecycle, and the slash of the second from its persistence. -/
private theorem Kept.trans {f g h : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    {u : BeaconState preset h} (one : Kept s t) (two : Kept t u) : Kept s u where
  life := one.life.trans two.life
  slashed := one.slashed.trans two.slashed
  withdrawable i v w found read far := by
    obtain ⟨m, mFound, step⟩ := one.life.validators i v found
    have mFar : m.exitEpoch ≠ FAR_FUTURE_EPOCH := by rw [step.exitEpoch far]; exact far
    obtain ⟨le1, moved1⟩ := one.withdrawable i v m found mFound far
    obtain ⟨le2, moved2⟩ := two.withdrawable i m w mFound read mFar
    refine ⟨UInt64.le_trans le1 le2, ?_⟩
    rcases moved2 with flag | same
    · exact .inl flag
    · rcases moved1 with flag | same1
      · obtain ⟨w', read', marked⟩ := two.slashed i m mFound flag
        rw [read, Option.some.injEq] at read'
        subst read'
        exact .inl marked
      · exact .inr (same.trans same1)

/-- A state with the same validators keeps everything. -/
private theorem Kept.of_data {f g : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    (same : t.validators.data = s.validators.data) : Kept s t where
  life := .of_data same
  slashed := .of_data same
  withdrawable i v w found read _ := by
    rw [same, found, Option.some.injEq] at read
    subst read
    exact ⟨UInt64.le_refl _, .inr rfl⟩

/-- A step that keeps the lifecycle and the slashes, and each withdrawable epoch, keeps everything. -/
private theorem Kept.of_withdrawable {f g : Fork} {s : BeaconState preset f}
    {t : BeaconState preset g} (life : RegistryLifecycle s t) (slashed : SlashedPersistence s t)
    (same : ∀ (i : ℕ) (v : Validator), s.validators.data[i]? = some v →
      ∃ w, t.validators.data[i]? = some w ∧ w.withdrawableEpoch = v.withdrawableEpoch) :
    Kept s t where
  life := life
  slashed := slashed
  withdrawable i v w found read _ := by
    obtain ⟨w', read', equal⟩ := same i v found
    rw [read, Option.some.injEq] at read'
    subst read'
    exact ⟨UInt64.le_of_eq equal.symm, .inr equal⟩

/-- The pending deposits keep every validator of the registry before them as it was. -/
private theorem pendingDeposits_entries {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} (ok : processPendingDeposits config checks s electra = .ok t)
    (i : ℕ) (v : Validator) (found : s.validators.data[i]? = some v) :
    t.validators.data[i]? = some v := by
  obtain ⟨_, _, applied, _, next, _, _, _, _, _, _, _, _, appliedOk, rfl⟩ :=
    processPendingDeposits_applied ok
  have kept := foldlM_ok_invariant
    (fun u : BeaconState preset fork => u.validators.data[i]? = some v)
    (fun u deposit u' previous step => by
      rcases applyPendingDeposit_cases step with rfl | ⟨index, raised⟩ | ⟨_, added⟩
      · exact previous
      · rw [increaseBalance_validators raised]
        exact previous
      · have inside := (Array.getElem?_eq_some_iff.mp previous).1
        rw [addValidatorToRegistry_validators_eq_push added, Array.getElem?_push]
        simp only [Nat.ne_of_lt inside, ↓reduceIte]
        exact previous)
    found appliedOk
  exact kept

/-- The update of the effective balances keeps the withdrawable epoch of each validator. -/
private theorem effectiveUpdates_withdrawable {fork : Fork} {s t : BeaconState preset fork}
    (ok : processEffectiveBalanceUpdates s = .ok t) (i : ℕ) (v : Validator)
    (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧ w.withdrawableEpoch = v.withdrawableEpoch := by
  unfold processEffectiveBalanceUpdates at ok
  refine foldlM_ok_invariant (fun u : BeaconState preset fork =>
    ∃ w, u.validators.data[i]? = some w ∧ w.withdrawableEpoch = v.withdrawableEpoch)
    (fun u j u' previous step => ?_) ⟨v, found, rfl⟩ ok
  obtain ⟨w, read, equal⟩ := previous
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at step
  obtain ⟨validator, validatorOk, balance, _, next, _, set⟩ := step
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  by_cases same : i = j
  · subst same
    rw [getValidatorAt_eq_ok_iff.mp validatorOk, Option.some.injEq] at read
    subst read
    exact ⟨{ validator with effectiveBalance := next },
      by simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set], equal⟩
  · refine ⟨w, ?_, equal⟩
    simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, Ne.symm same,
      same] using read

/-- From Electra, every stage of an epoch keeps the registry. -/
private theorem kept_stage {fork : Fork} {k : EpochStage} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (edge : EpochStage.Edge config checks k s t) : Kept s t := by
  cases k
  case registry =>
    simp only [EpochStage.Edge] at edge
    exact ⟨registryLifecycle_processRegistryUpdates edge,
      .of_frame (frame_processRegistryUpdates edge).toFrame,
      withdrawableKept_processRegistryUpdates electra edge⟩
  case pendingDeposits =>
    simp only [EpochStage.Edge, electra, ↓reduceDIte] at edge
    exact Kept.of_withdrawable (registryLifecycle_processPendingDeposits edge)
      (.of_frame (frame_processPendingDeposits edge).toFrame)
      fun i v found => ⟨v, pendingDeposits_entries edge i v found, rfl⟩
  case effectiveBalances =>
    simp only [EpochStage.Edge] at edge
    exact Kept.of_withdrawable (registryLifecycle_processEffectiveBalanceUpdates edge)
      (.of_frame (frame_processEffectiveBalanceUpdates edge).toFrame)
      (effectiveUpdates_withdrawable edge)
  all_goals exact Kept.of_data (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))

/-- From Electra, a whole epoch transition keeps the registry. -/
private theorem kept_processEpoch {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (ok : processEpoch config checks s = .ok t) : Kept s t :=
  (processEpoch_trace ok).transport (fun a b => Kept a b) (fun _ => Kept.of_data rfl)
    (fun one two => one.trans two)
    (fun _ _ _ _ computed => kept_stage electra (EpochStage.action_cases.mp computed))

/-- From Electra, an upgrade keeps the validators as the same sequence. -/
private theorem upgradeNext_validators {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (electra : .pectra ≤ pre.fork) (computed : upgradeNext config checks pre = .ok post) :
    post.val.state.validators.data = pre.state.validators.data := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
  all_goals try (dsimp only at electra; exact absurd electra (by decide))
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact (upgradeToFulu_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact (upgradeToGloas_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact (upgradeHezeFields_lists _).1

/-- From Electra, a slot of a run keeps the registry. -/
private theorem kept_slot {u w : ForkedBeaconState preset} (electra : .pectra ≤ u.fork)
    (ok : advanceSlotAcross config checks u = .ok w) : Kept u.state w.state := by
  obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
  obtain ⟨_, cached, epoched, _, cachedOk, epochedOk, afterEq⟩ := advanceSlot_ok slotOk
  have cachedKept : Kept u.state cached := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact Kept.of_data rfl
  have epochKept : Kept cached epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact kept_processEpoch electra epochedOk
    · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
      exact epochedOk ▸ Kept.of_data rfl
  have advancedKept : Kept u.state advanced := by
    rw [afterEq]
    exact cachedKept.trans (epochKept.trans (Kept.of_data rfl))
  exact (processUpgrades_induction (forked := ⟨u.fork, advanced⟩)
    (property := fun z => .pectra ≤ z.fork ∧ Kept u.state z.state)
    (fun {_ post} held more => ⟨Nat.le_trans held.1 (Nat.le_of_lt post.property),
      held.2.trans (Kept.of_data (upgradeNext_validators held.1 more))⟩)
    ⟨electra, advancedKept⟩ upgrades).2

/-- From Fulu and before Gloas, a block keeps the registry. -/
private theorem kept_block {fork : Fork} {a t : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    {due : upgradeDue config ⟨fork, a⟩ = false}
    {ok : applySignedBlock config checks engine a signed true = .ok t}
    (fulu : .fusaka ≤ fork) (early : fork < .glamsterdam) (matched : BalancesMatch a) :
    Kept a t := by
  have processed := (applySignedBlock_ok ok).2.1
  have frame := frame_processBlock processed
  refine ⟨registryLifecycle_processBlock processed, .of_frame frame, ?_⟩
  exact Run.withdrawableKept_of_same_epoch (Run.nil.snoc (Step.block engine signed due ok)) early
    fulu (by simp only [getCurrentEpoch, frame.slot]) matched

/-- From Fulu and before Gloas, a run keeps the registry. -/
private theorem kept_run {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (fulu : .fusaka ≤ x.fork) (tail : Run config checks x y) (early : y.fork < .glamsterdam) :
    Kept x.state y.state := by
  induction tail with
  | nil => exact Kept.of_data rfl
  | @snoc middle last pre step ih =>
    have earlyMiddle : middle.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have fuluMiddle : .fusaka ≤ middle.fork :=
      Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
    refine (ih earlyMiddle).trans ?_
    cases step with
    | slot ok =>
      exact kept_slot (Nat.le_trans (by decide) fuluMiddle) ok
    | block engine signed due ok =>
      exact kept_block (engine := engine) (signed := signed) (due := due) (ok := ok)
        fuluMiddle early
        (run_justified_separated (shared.append pre) genesis).1.balancesMatch

/-- A replay step keeps the registry and the slot, and records no deposit event. -/
private structure Grew {f : Fork} (p q : BalanceReplay preset f) : Prop where
  kept : Kept p.1 q.1
  slot : q.1.slot = p.1.slot
  events : ∀ e ∈ q.2, e ∈ p.2 ∨ e.source ≠ .deposits

private theorem Grew.refl {f : Fork} (p : BalanceReplay preset f) : Grew p p :=
  ⟨Kept.of_data rfl, rfl, fun _ member => .inl member⟩

private theorem Grew.trans {f : Fork} {p q r : BalanceReplay preset f} (one : Grew p q)
    (two : Grew q r) : Grew p r where
  kept := one.kept.trans two.kept
  slot := two.slot.trans one.slot
  events e member := by
    rcases two.events e member with old | other
    · exact one.events e old
    · exact .inr other

/-- A recorded pass appends one event of its source to the events, after its action. -/
private theorem recordBalance_cases {f : Fork} {source : BalanceSource}
    {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    {p q : BalanceReplay preset f} (ok : recordBalance source limits action p = .ok q) :
    action p.1 = .ok q.1 ∧ ∀ e ∈ q.2, e ∈ p.2 ∨ e.source = source := by
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨⟨credit, debit⟩, _, after, computed, rfl⟩ := ok
  refine ⟨computed, fun e member => ?_⟩
  rcases List.mem_append.mp member with old | added
  · exact .inl old
  · exact .inr (by rw [List.mem_singleton.mp added])

/-- A carried pass changes the state by its action and records nothing. -/
private theorem carryBalance_cases {f : Fork}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    {p q : BalanceReplay preset f} (ok : carryBalance action p = .ok q) :
    action p.1 = .ok q.1 ∧ q.2 = p.2 := by
  simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨after, computed, rfl⟩ := ok
  exact ⟨computed, rfl⟩

/-- A replay of reward and penalty deltas keeps the registry and records no deposit. -/
private theorem replayDeltas_grew {f : Fork} {source : BalanceSource}
    {deltas : Array Gwei × Array Gwei} {p q : BalanceReplay preset f}
    (notDeposit : source ≠ .deposits) (ok : replayDeltas source deltas p = .ok q) : Grew p q := by
  unfold replayDeltas at ok
  refine foldlM_ok_invariant (fun r => Grew p r) (fun r i r' previous step => ?_) (Grew.refl p) ok
  refine previous.trans ?_
  simp only [bind_ok_iff] at step
  obtain ⟨index, _, raised, raisedOk, loweredOk⟩ := step
  obtain ⟨raisedAction, raisedEvents⟩ := recordBalance_cases raisedOk
  obtain ⟨loweredAction, loweredEvents⟩ := recordBalance_cases loweredOk
  have raisedAction := liftAccessor_ok.mp raisedAction
  have loweredAction := liftAccessor_ok.mp loweredAction
  have first : Grew r raised :=
    ⟨Kept.of_data (congrArg (·.data) (increaseBalance_validators raisedAction)),
      (frame_increaseBalance raisedAction).toFrame.slot, fun e member => by
        rcases raisedEvents e member with old | new
        · exact .inl old
        · exact .inr (by rw [new]; decide)⟩
  have second : Grew raised r' :=
    ⟨Kept.of_data (congrArg (·.data) (decreaseBalance_validators loweredAction)),
      (frame_decreaseBalance loweredAction).toFrame.slot, fun e member => by
        rcases loweredEvents e member with old | new
        · exact .inl old
        · exact .inr (by rw [new]; exact notDeposit)⟩
  exact first.trans second

/-- The replay of the rewards and penalties keeps the registry and records no deposit. -/
private theorem replayRewards_grew {f : Fork} {p q : BalanceReplay preset f}
    (ok : replayRewards (config := config) p = .ok q) : Grew p q := by
  unfold replayRewards at ok
  split at ok
  · simp only [pure, Except.pure, Except.ok.injEq] at ok
    subst ok
    exact Grew.refl _
  · simp only [bind_ok_iff] at ok
    obtain ⟨ordinary, _, inactivity, _, ok⟩ := ok
    split at ok
    · obtain ⟨middle, middleOk, lastOk⟩ := bind_ok_iff.mp ok
      have first : Grew p middle := foldlM_ok_invariant (fun r => Grew p r)
        (fun _ _ _ previous step => previous.trans (replayDeltas_grew (by decide) step))
        (Grew.refl p) middleOk
      exact first.trans (replayDeltas_grew (by decide) lastOk)
    · obtain ⟨_, _, ok⟩ := bind_ok_iff.mp ok
      obtain ⟨one, oneOk, ok⟩ := bind_ok_iff.mp ok
      obtain ⟨two, twoOk, lastOk⟩ := bind_ok_iff.mp ok
      have middle : Grew one two := foldlM_ok_invariant (fun r => Grew one r)
        (fun _ _ _ previous step => previous.trans (replayDeltas_grew (by decide) step))
        (Grew.refl one) twoOk
      exact ((replayDeltas_grew (by decide) oneOk).trans middle).trans
        (replayDeltas_grew (by decide) lastOk)

/-- From Electra, each stage of an epoch before the pending deposits keeps the registry. -/
private theorem replay_stage {f : Fork} (electra : .pectra ≤ f) {k : EpochStage}
    (member : k ∈ [EpochStage.justification, .inactivity, .rewards, .registry, .slashings,
      .eth1Reset]) {p q : BalanceReplay preset f}
    (ok : epochReplayAction (config := config) (checks := checks) k p = .ok q) : Grew p q := by
  have ofEdge (edge : EpochStage.Edge config checks k p.1 q.1) (same : q.2 = p.2) : Grew p q :=
    ⟨kept_stage electra edge, edge.slot_eq, fun e member => .inl (same ▸ member)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [epochReplayAction] at ok
    obtain ⟨action, same⟩ := carryBalance_cases ok
    exact ofEdge action same
  · simp only [epochReplayAction] at ok
    split at ok
    · obtain ⟨action, same⟩ := carryBalance_cases ok
      rename_i h
      exact ofEdge (by simp only [EpochStage.Edge, h, ↓reduceDIte]; exact action) same
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      exact Grew.refl _
  · simp only [epochReplayAction] at ok
    exact replayRewards_grew ok
  · simp only [epochReplayAction] at ok
    obtain ⟨action, same⟩ := carryBalance_cases ok
    exact ofEdge action same
  · simp only [epochReplayAction] at ok
    obtain ⟨action, events⟩ := recordBalance_cases ok
    have edge : EpochStage.Edge config checks .slashings p.1 q.1 := action
    exact ⟨kept_stage electra edge, edge.slot_eq, fun e member => by
        rcases events e member with old | new
        · exact .inl old
        · exact .inr (by rw [new]; decide)⟩
  · simp only [epochReplayAction] at ok
    split at ok
    · obtain ⟨action, same⟩ := carryBalance_cases ok
      rename_i h
      exact ofEdge (by simp only [EpochStage.Edge, h, ↓reduceDIte]; exact action) same
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      exact Grew.refl _

/-- Every deposit event of a slot step of the run starts at a state that keeps the registry.

A slot step records a deposit event only for the pending deposits of its epoch pass.

So the event starts at the input of that pass: the state after justification, inactivity, rewards, registry updates, slashings and the eth1 reset.

The steps of the run before the slot keep the registry, and so does each of those stages.

Block deposits are not covered.
From Electra they credit no existing key. -/
private theorem Run.events_kept {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (fulu : .fusaka ≤ x.fork) (early : y.fork < .glamsterdam)
    {u w : ForkedBeaconState preset} (ok : advanceSlotAcross config checks u = .ok w)
    (contained : tail.Contains (Step.slot ok))
    {events : List (BalanceEvent preset)}
    (replayed : (Step.slot ok : Step config checks u w).balanceEvents = .ok events) :
    ∀ e ∈ events, e.source = .deposits →
      RegistryLifecycle x.state e.before.state ∧
      WithdrawableKept x.state e.before.state ∧
      getCurrentEpoch e.before.state ≤ getCurrentEpoch y.state := by
  intro e member source
  obtain ⟨pre, post, rfl⟩ := Run.contains_split tail (Step.slot ok) contained
  have stepFork := (Step.slot ok : Step config checks u w).chainStep.fork_le
  have earlyW : w.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early
  have earlyU : u.fork < .glamsterdam := Nat.lt_of_le_of_lt stepFork earlyW
  have fuluU : .fusaka ≤ u.fork := Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
  have electraU : .pectra ≤ u.fork := Nat.le_trans (by decide) fuluU
  have run : Kept x.state u.state := kept_run shared genesis fulu pre earlyU
  have epochLe : getCurrentEpoch u.state ≤ getCurrentEpoch y.state :=
    currentEpoch_le_of_chainSteps
      (Relation.ReflTransGen.head (Step.slot ok : Step config checks u w).chainStep
        post.chainSteps)
  obtain ⟨advanced, cached, crossings, advanceOk, upgrades, cachedOk, crossingOk, branch⟩ :=
    Step.balanceEvents_slot ok earlyW replayed
  have noCrossings : crossings = [] :=
    DirectSafety.Apriori.Internal.upgradeBalanceReplay_electra_nil
      (u := ⟨u.fork, advanced⟩) electraU crossingOk
  rcases branch with ⟨_, eventsEq⟩ | ⟨middle, updated, recorded, recordOk, _, _, _, eventsEq, _⟩
  · rw [eventsEq, noCrossings] at member
    cases member
  rw [eventsEq, noCrossings, List.append_nil] at member
  have cachedKept : Kept u.state cached := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact Kept.of_data rfl
  have cachedSlot : cached.slot = u.state.slot := (frame_processSlot cachedOk).slot
  have trace := epochBalanceReplay_trace recordOk
  change EpochTrace _ ([EpochStage.justification, .inactivity, .rewards, .registry, .slashings,
    .eth1Reset] ++ [.pendingDeposits, .pendingConsolidations]) _ _ at trace
  obtain ⟨six, head, rest⟩ := EpochTrace.append_iff.mp trace
  have grew : Grew (cached, []) six := head.transport (fun p q => Grew p q) Grew.refl Grew.trans
    (fun _ member _ _ computed => replay_stage electraU member computed)
  cases rest with
  | cons first rest =>
    cases rest with
    | cons second rest =>
      cases rest
      simp only [epochReplayAction, electraU, ↓reduceDIte, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at first second
      obtain ⟨deposited, _, rfl⟩ := first
      obtain ⟨consolidated, _, same⟩ := second
      simp only [Prod.mk.injEq] at same
      obtain ⟨-, rfl⟩ := same
      rcases List.mem_append.mp member with old | last
      · rcases List.mem_append.mp old with old | added
        · rcases grew.events e old with listed | other
          · cases listed
          · exact absurd source other
        · rw [List.mem_singleton.mp added]
          have total : Kept x.state six.1 := run.trans (cachedKept.trans grew.kept)
          refine ⟨total.life, total.withdrawable, ?_⟩
          have same : getCurrentEpoch six.1 = getCurrentEpoch u.state := by
            simp only [getCurrentEpoch, grew.slot, cachedSlot]
          exact same ▸ epochLe
      · rw [List.mem_singleton.mp last] at source
        cases source
end PinSplit4

end GroupD

section GroupA

/-! ## PinExitCredits -/

namespace PinSplit

open Base Uint64 Models DirectSafety

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-! ## Deposits leave the balance of an exiting key alone -/

/-- Every exiting key of the first state keeps its balance in the second state. -/
private def KeepsExiting {f g : Fork} (s : BeaconState preset f) (t : BeaconState preset g) :
    Prop :=
  ∀ (i : ℕ) (v : Validator), s.validators.data[i]? = some v → v.exitEpoch.toNat < 2 ^ 64 - 1 →
    (getCurrentEpoch s).toNat < v.withdrawableEpoch.toNat →
    t.balances.data[i]? = s.balances.data[i]?

/-- Every deposit event of the list leaves the balance of an exiting key alone. -/
private def Quiet (events : List (BalanceEvent preset)) : Prop :=
  ∀ e ∈ events, e.source = .deposits → KeepsExiting e.before.state e.after.state

/-- The event raises no balance of the registry. -/
private def Unconditional (e : BalanceEvent preset) : Prop :=
  ∀ i, actualBalanceAt e.after i ≤ actualBalanceAt e.before i

private theorem quiet_nil : Quiet ([] : List (BalanceEvent preset)) := fun _ mem => by
  simp at mem

private theorem quiet_carry {f : Fork}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    {pre post : BalanceReplay preset f} (initial : Quiet pre.2)
    (ok : carryBalance action pre = .ok post) : Quiet post.2 := by
  simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  exact initial

private theorem quiet_record {f : Fork} {source : BalanceSource}
    {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    {pre post : BalanceReplay preset f} (initial : Quiet pre.2)
    (keeps : source = .deposits → ∀ t, action pre.1 = .ok t → KeepsExiting pre.1 t)
    (ok : recordBalance source limits action pre = .ok post) : Quiet post.2 := by
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨⟨credit, debit⟩, _, t, actionOk, rfl⟩ := ok
  intro e member sourceEq
  rcases List.mem_append.mp member with old | new
  · exact initial e old sourceEq
  · obtain rfl := List.mem_singleton.mp new
    exact keeps sourceEq t actionOk

/-- A new validator with no balance never raises a balance. -/
private theorem addValidatorToRegistry_zero_balance {f : Fork} {s t : BeaconState preset f}
    (altair : .altair ≤ f) {pubkey : Cryptography.Bls.BLSPubkey} {credentials : Bytes32}
    (ok : addValidatorToRegistry s pubkey credentials 0 = .ok t) (i : ℕ) :
    ((t.balances.data[i]?).map (·.toNat)).getD 0 ≤
      ((s.balances.data[i]?).map (·.toNat)).getD 0 := by
  unfold addValidatorToRegistry at ok
  simp only [altair, ↓reduceDIte, addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, balancesOk, _, _, _, _, _, _, rfl⟩ := ok
  show ((_ : Option Gwei).map (·.toNat)).getD 0 ≤ _
  rw [setOrAppendList_getElem? balancesOk]
  split <;> simp

/-- From Electra, a block deposit raises no balance. -/
private theorem processDeposit_balance_le {f : Fork} {s t : BeaconState preset f}
    (electra : .pectra ≤ f) {before : f < .hegota} {dep : Deposit}
    (ok : processDeposit config checks before s dep = .ok t) (i : ℕ) :
    actualBalanceAt ⟨f, t⟩ i ≤ actualBalanceAt ⟨f, s⟩ i := by
  obtain ⟨-, -, next, -, applied⟩ := processDeposit_ok ok
  rcases applyDeposit_cases applied with rfl | ⟨_, middle, pending, rfl | added, rfl⟩ |
      ⟨early, _⟩
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · exact addValidatorToRegistry_zero_balance (Nat.le_trans (by decide) electra) added i
  · exact absurd (Nat.lt_of_lt_of_le early electra) (Nat.lt_irrefl _)

/-- A property of the events of a block replay that each recorded event keeps.

Every operation of a block records an event of its own source.

The deposits of the block are the only events of the source `.deposits`.

No operation of a block records the source `.consolidations`. -/
private theorem blockReplay_invariant {f : Fork} (electra : .pectra ≤ f) (early : f < .glamsterdam)
    (P : List (BalanceEvent preset) → Prop) (nil : P [])
    (ordinary : ∀ (l : List (BalanceEvent preset)) (e : BalanceEvent preset),
      e.source ≠ .deposits → e.source ≠ .consolidations → P l → P (l ++ [e]))
    (deposit : ∀ (l : List (BalanceEvent preset)) (s t : BeaconState preset f)
      (before : f < .hegota) (dep : Deposit) (credit debit : ℕ), P l →
      processDeposit config checks before s dep = .ok t →
      P (l ++ [⟨.deposits, ⟨f, s⟩, ⟨f, t⟩, credit, debit⟩]))
    (engine : ExecutionEngine preset f) (s : BeaconState preset f)
    (block : BeaconBlock preset f) {post : BalanceReplay preset f}
    (ok : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok post) : P post.2 := by
  have carry {pre post : BalanceReplay preset f}
      {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
      (initial : P pre.2) (ok : carryBalance action pre = .ok post) : P post.2 := by
    simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, rfl⟩ := ok
    exact initial
  have record {pre post : BalanceReplay preset f} {source : BalanceSource}
      {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
      {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
      (notDeposit : source ≠ .deposits) (notConsolidation : source ≠ .consolidations)
      (initial : P pre.2) (ok : recordBalance source limits action pre = .ok post) :
      P post.2 := by
    simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨⟨credit, debit⟩, _, t, _, rfl⟩ := ok
    exact ordinary _ _ notDeposit notConsolidation initial
  have altair : .altair ≤ f := Nat.le_trans (by decide) electra
  have bellatrix : .bellatrix ≤ f := Nat.le_trans (by decide) electra
  unfold blockBalanceReplay at ok
  obtain ⟨headed, headedOk, rest⟩ := bind_ok_iff.mp ok
  have headedQuiet := carry nil headedOk
  simp only [bellatrix, ↓reduceDIte] at rest
  obtain ⟨executed, executedOk, rest⟩ := bind_ok_iff.mp rest
  have executedQuiet := record (by decide : BalanceSource.withdrawals ≠ .deposits)
    (by decide) headedQuiet executedOk
  simp only [bind_ok_iff] at rest
  obtain ⟨randao, randaoOk, voted, votedOk, expected, _, _, _,
    proposed, proposedOk, attested, attestedOk, rewarded, rewardedOk, deposited, depositOk,
    exited, exitOk, changed, changedOk, rest⟩ := rest
  have randaoQuiet := carry executedQuiet randaoOk
  have votedQuiet := carry randaoQuiet votedOk
  have proposedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun _ _ _ h ok => record (by decide : BalanceSource.slashings ≠ .deposits) (by decide) h ok)
    votedQuiet proposedOk
  have attestedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun _ _ _ h ok => record (by decide : BalanceSource.slashings ≠ .deposits) (by decide) h ok)
    proposedQuiet attestedOk
  have rewardedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun _ _ _ h ok => record (by decide : BalanceSource.rewards ≠ .deposits) (by decide) h ok)
    attestedQuiet rewardedOk
  have depositedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun pre dep post h ok => by
      simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨⟨credit, debit⟩, _, t, actionOk, rfl⟩ := ok
      exact deposit _ _ _ _ _ _ _ h actionOk)
    rewardedQuiet depositOk
  have exitedQuiet := carry depositedQuiet exitOk
  have changedQuiet := carry exitedQuiet changedOk
  simp only [electra, ↓reduceDIte, bind_ok_iff] at rest
  obtain ⟨deposits, depositRequestOk, withdrawals, withdrawalOk,
    requested, consolidations, rest⟩ := rest
  have depositsQuiet := carry changedQuiet depositRequestOk
  have withdrawalsQuiet := carry depositsQuiet withdrawalOk
  have requestedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun _ _ _ h ok => record (by decide : BalanceSource.excess ≠ .deposits) (by decide) h ok)
    withdrawalsQuiet consolidations
  simp only [altair, ↓reduceDIte] at rest
  exact record (by decide : BalanceSource.sync ≠ .deposits) (by decide) requestedQuiet rest

/-- From Electra, the deposit events of a block replay raise no balance. -/
private theorem blockReplay_unconditional {f : Fork} (electra : .pectra ≤ f)
    (early : f < .glamsterdam)
    (engine : ExecutionEngine preset f) (s : BeaconState preset f)
    (block : BeaconBlock preset f) {post : BalanceReplay preset f}
    (ok : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok post) :
    ∀ e ∈ post.2, e.source = .deposits → Unconditional e :=
  blockReplay_invariant electra early (fun l => ∀ e ∈ l, e.source = .deposits → Unconditional e)
    (fun _ h => by simp at h)
    (fun l e notDeposit _ held e' member sourceEq => by
      rcases List.mem_append.mp member with old | new
      · exact held e' old sourceEq
      · exact absurd ((List.mem_singleton.mp new) ▸ sourceEq) notDeposit)
    (fun l s t _ dep credit debit held computed e' member sourceEq => by
      rcases List.mem_append.mp member with old | new
      · exact held e' old sourceEq
      · obtain rfl := List.mem_singleton.mp new
        exact fun i => processDeposit_balance_le electra computed i)
    engine s block ok

/-- No operation of a block records a consolidation event. -/
private theorem blockReplay_noConsolidations {f : Fork} (electra : .pectra ≤ f)
    (early : f < .glamsterdam) (engine : ExecutionEngine preset f) (s : BeaconState preset f)
    (block : BeaconBlock preset f) {post : BalanceReplay preset f}
    (ok : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok post) : ∀ e ∈ post.2, e.source ≠ .consolidations :=
  blockReplay_invariant electra early (fun l => ∀ e ∈ l, e.source ≠ .consolidations)
    (fun _ h => by simp at h)
    (fun l e _ notConsolidation held e' member => by
      rcases List.mem_append.mp member with old | new
      · exact held e' old
      · exact (List.mem_singleton.mp new) ▸ notConsolidation)
    (fun l s t _ dep credit debit held _ e' member => by
      rcases List.mem_append.mp member with old | new
      · exact held e' old
      · obtain rfl := List.mem_singleton.mp new
        exact fun eq => by cases eq)
    engine s block ok

/-- The deposit events of an epoch replay leave the balance of an exiting key alone.

The pending deposits of an epoch are the only deposit events of the replay. -/
private theorem epochReplay_quiet {f : Fork} {s : BeaconState preset f} {post : BalanceReplay preset f}
    (ok : epochBalanceReplay (config := config) (checks := checks) s = .ok post) :
    Quiet post.2 := by
  refine (epochBalanceReplay_trace ok).transport
    (fun a b : BalanceReplay preset f => Quiet a.2 → Quiet b.2)
    (fun _ => id) (fun one two held => two (one held)) ?_ quiet_nil
  intro k member pre after step held
  cases k <;> simp only [epochReplayAction] at step
  case justification | registry => exact quiet_carry held step
  case inactivity | eth1Reset =>
    split at step
    · exact quiet_carry held step
    · cases step; exact held
  case rewards =>
    exact replayRewards_induction (fun pre => Quiet pre.2)
      (fun prior ok => quiet_record prior (fun eq => by cases eq) ok)
      (fun penalty prior ok => quiet_record prior
        (fun eq => by rcases penalty with rfl | rfl <;> cases eq) ok) held step
  case slashings => exact quiet_record held (fun eq => by cases eq) step
  case pendingDeposits =>
    split at step
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
      obtain ⟨deposited, depositedOk, rfl⟩ := step
      intro e member sourceEq
      rcases List.mem_append.mp member with old | new
      · exact held e old sourceEq
      · obtain rfl := List.mem_singleton.mp new
        intro i v found exited withdrawable
        exact processPendingDeposits_exited_balance depositedOk found exited withdrawable
    · cases step; exact held
  case pendingConsolidations =>
    split at step
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
      obtain ⟨consolidated, consolidatedOk, rfl⟩ := step
      intro e member sourceEq
      rcases List.mem_append.mp member with old | new
      · exact held e old sourceEq
      · obtain rfl := List.mem_singleton.mp new
        cases sourceEq
    · cases step; exact held
  all_goals simp [EpochStage.prefixStages] at member

/-- The deposit events of a slot step leave the balance of an exiting key alone. -/
private theorem slot_quiet {x y : ForkedBeaconState preset} (ok : advanceSlotAcross config checks x = .ok y)
    (early : y.fork < .glamsterdam)
    {events : List (BalanceEvent preset)} (replayed : (Step.slot ok).balanceEvents = .ok events) :
    Quiet events := by
  obtain ⟨advanced, cached, crossings, -, -, -, crossingOk, split⟩ :=
    Step.balanceEvents_slot ok early replayed
  have crossed : Quiet crossings := fun e member sourceEq => by
    cases (upgradeBalanceReplay_crossing crossingOk e member).symm.trans sourceEq
  rcases split with ⟨-, rfl⟩ | ⟨middle, updated, recorded, recordOk, -, -, -, rfl, -⟩
  · exact crossed
  · intro e member sourceEq
    rcases List.mem_append.mp member with old | new
    · exact epochReplay_quiet recordOk e old sourceEq
    · exact crossed e new sourceEq

/-- A deposit event of a run raises no balance, or it is an epoch's deposit event of a slot step.

Then it leaves the balance of an exiting key alone. -/
private def Located {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (e : BalanceEvent preset) : Prop :=
  Unconditional e ∨ ∃ (u w : ForkedBeaconState preset)
    (ok : advanceSlotAcross config checks u = .ok w) (es : List (BalanceEvent preset)),
    tail.Contains (Step.slot ok) ∧ (Step.slot ok : Step config checks u w).balanceEvents = .ok es ∧
      e ∈ es ∧ KeepsExiting e.before.state e.after.state

/-- Locate each deposit event of a run. -/
private theorem run_located {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    ∀ e ∈ events, e.source = .deposits → Located tail e := by
  induction tail generalizing events with
  | nil => cases replayed; intro e member; simp at member
  | @snoc middle last pre step ih =>
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    have priorLocated := ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early) priorOk
    have lift : ∀ e, Located pre e → Located (pre.snoc step) e := by
      rintro e (unconditional | ⟨u, w, ok, es, contains, replayedEs, member, keeps⟩)
      · exact .inl unconditional
      · exact .inr ⟨u, w, ok, es, .earlier contains step, replayedEs, member, keeps⟩
    by_cases selected : (getCurrentEpoch middle.state).toNat ≤ high + 1
    · simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at rest
      obtain ⟨added, addedOk, rfl⟩ := rest
      have inFork : .pectra ≤ middle.fork :=
        Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
      intro e member sourceEq
      rcases List.mem_append.mp member with old | new
      · exact lift e (priorLocated e old sourceEq)
      · cases step with
        | block engine signed due ok =>
          exact .inl (blockReplay_unconditional inFork early engine _ _
            (Step.balanceEvents_block early addedOk) e new sourceEq)
        | slot ok =>
          exact .inr ⟨_, _, ok, added, .last pre _, addedOk, new,
            slot_quiet ok early addedOk e new sourceEq⟩
    · simp only [selected, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      intro e member sourceEq
      exact lift e (priorLocated e member sourceEq)

/-! ## Consolidation credits of one pass -/

/-- The stake that a pending consolidation can move at a pass: the source's effective balance.

It counts only a source that is unslashed and can withdraw by the next epoch.

A pass reads the other sources without moving anything. -/
private def sourceBound {f : Fork} (s : BeaconState preset f) (next : Epoch)
    (c : PendingConsolidation) : ℕ :=
  match s.validators.data[c.sourceIndex.toNat]? with
  | some v => if v.slashed = false ∧ v.withdrawableEpoch ≤ next then v.effectiveBalance.toNat else 0
  | none => 0

/-- The credits of the balances from one state to another, over the later balances. -/
private def credited {f : Fork} (s t : BeaconState preset f) : ℕ :=
  ∑ j ∈ Finset.range t.balances.data.size,
    (actualBalanceAt ⟨f, t⟩ j - actualBalanceAt ⟨f, s⟩ j)

private theorem credited_trans {f : Fork} {a b c : BeaconState preset f}
    (ab : b.balances.data.size = a.balances.data.size)
    (bc : c.balances.data.size = b.balances.data.size) :
    credited a c ≤ credited a b + credited b c := by
  unfold credited
  rw [bc, ab, ← ab, ← Finset.sum_add_distrib]
  rw [ab, bc] at *
  apply Finset.sum_le_sum
  intro j _
  omega

/-- One transfer of a pass credits at most the amount moved. -/
private theorem credited_transfer {f : Fork} {s lowered raised : BeaconState preset f}
    {source target : ValidatorIndex} {moved : Gwei}
    (lowerOk : decreaseBalance s source moved = .ok lowered)
    (raiseOk : increaseBalance lowered target moved = .ok raised) :
    credited s raised ≤ moved.toNat := by
  have sizes := (sameSizes_increaseBalance raiseOk).2.trans (sameSizes_decreaseBalance lowerOk).2
  unfold credited
  have pointwise : ∀ j, actualBalanceAt ⟨f, raised⟩ j - actualBalanceAt ⟨f, s⟩ j ≤
      if target.toNat = j then moved.toNat else 0 := by
    intro j
    by_cases inside : j < s.balances.data.size
    · obtain ⟨balance, found⟩ : ∃ balance, s.balances.data[j]? = some balance :=
        ⟨_, Array.getElem?_eq_getElem inside⟩
      obtain ⟨down, downFound, downEq⟩ := balance_decreaseBalance lowerOk found
      obtain ⟨up, upFound, upEq⟩ := balance_increaseBalance raiseOk downFound
      simp only [actualBalanceAt, found, upFound, Option.map_some, Option.getD_some]
      split at downEq <;> split at upEq <;> split <;> omega
    · have missing : s.balances.data[j]? = Option.none := Array.getElem?_eq_none (by omega)
      have outside : raised.balances.data[j]? = Option.none := Array.getElem?_eq_none (by omega)
      simp [actualBalanceAt, missing, outside]
  calc ∑ j ∈ Finset.range raised.balances.data.size,
        (actualBalanceAt ⟨f, raised⟩ j - actualBalanceAt ⟨f, s⟩ j)
      ≤ ∑ j ∈ Finset.range raised.balances.data.size, if target.toNat = j then moved.toNat else 0 :=
        Finset.sum_le_sum fun j _ => pointwise j
    _ ≤ moved.toNat := by
        rw [Finset.sum_ite_eq]
        split <;> omega

/-- A pass credits at most the effective balances of the unslashed due sources it reads.

It keeps the registry and the number of balances. -/
private theorem pass_credits_le {f : Fork} (next : Epoch) :
    ∀ (items : List PendingConsolidation) {s t : BeaconState preset f} {read : ℕ},
      passPendingConsolidations next s items = .ok (t, read) →
      t.validators = s.validators ∧ t.balances.data.size = s.balances.data.size ∧
        credited s t ≤ ((items.take read).map (sourceBound s next)).sum
  | [], s, t, read, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at computed
    obtain ⟨rfl, rfl⟩ := computed
    refine ⟨rfl, rfl, ?_⟩
    simp [credited, actualBalanceAt]
  | c :: rest, s, t, read, computed => by
    simp only [passPendingConsolidations, liftAccessor, bind_ok_iff, mapError_ok_iff] at computed
    obtain ⟨source, sourceRead, computed⟩ := computed
    have found := getValidator_eq_ok_iff.mp sourceRead
    have bound : sourceBound s next c = if source.slashed = false ∧ source.withdrawableEpoch ≤ next
        then source.effectiveBalance.toNat else 0 := by
      simp [sourceBound, found]
    by_cases slashed : source.slashed = true
    · simp only [slashed, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at computed
      obtain ⟨⟨state', read'⟩, passed, rfl, rfl⟩ := computed
      obtain ⟨validators, sizes, credits⟩ := pass_credits_le next rest passed
      refine ⟨validators, sizes, ?_⟩
      simpa [bound, slashed, List.take_succ_cons] using credits
    · replace slashed : source.slashed = false := by simpa using slashed
      by_cases early : next < source.withdrawableEpoch
      · simp only [slashed, early, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq] at computed
        obtain ⟨rfl, rfl⟩ := computed
        refine ⟨rfl, rfl, ?_⟩
        simp [credited, actualBalanceAt]
      · simp only [slashed, early, Bool.false_eq_true, ↓reduceIte, bind_ok_iff,
          mapError_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
        obtain ⟨balance, balanceOk, lowered, loweredOk, raised, raisedOk,
          ⟨state', read'⟩, passed, rfl, rfl⟩ := computed
        obtain ⟨validators, sizes, credits⟩ := pass_credits_le next rest passed
        have sameValidators := (increaseBalance_validators raisedOk).trans
          (decreaseBalance_validators loweredOk)
        have step := credited_transfer loweredOk raisedOk
        have sizeStep := (sameSizes_increaseBalance raisedOk).2.trans
          (sameSizes_decreaseBalance loweredOk).2
        have moved : (min balance source.effectiveBalance).toNat ≤
            source.effectiveBalance.toNat := by
          rw [Uint64.toNat_min]; exact Nat.min_le_right _ _
        have restBound : ((rest.take read').map (sourceBound raised next)) =
            ((rest.take read').map (sourceBound s next)) := by
          congr 1
          funext d
          simp only [sourceBound, sameValidators]
        refine ⟨validators.trans sameValidators, sizes.trans sizeStep, ?_⟩
        have total := credited_trans (a := s) (b := raised) (c := state') sizeStep sizes
        rw [restBound] at credits
        have isDue : sourceBound s next c = source.effectiveBalance.toNat := by
          rw [bound]; simp [slashed, UInt64.not_lt.mp early]
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons, isDue]
        omega

/-! ## The queue of pending consolidations over a block -/

/-- The queue only grows at its end inside a block.

Each new entry has a source whose exit is assigned after the current epoch. -/
private def Grows {f : Fork} (s t : BeaconState preset f) : Prop :=
  ∀ electra : .pectra ≤ f, ∃ added : List PendingConsolidation,
    (t.pendingConsolidations electra).data.toList =
      (s.pendingConsolidations electra).data.toList ++ added ∧
    ∀ c ∈ added, ∃ w, t.validators.data[c.sourceIndex.toNat]? = some w ∧
      getCurrentEpoch s < w.exitEpoch ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH

private theorem Grows.of_same {f : Fork} {s t : BeaconState preset f}
    (queue : .pectra ≤ f → SamePendingQueue s t) : Grows s t := by
  intro electra
  refine ⟨[], ?_, fun _ member => by simp at member⟩
  rw [show t.pendingConsolidations electra = s.pendingConsolidations electra from
    congrFun (queue electra) electra, List.append_nil]

private theorem Grows.trans {f : Fork} {s u t : BeaconState preset f}
    (one : Grows s u) (two : Grows u t) (life : RegistryLifecycle u t)
    (slot : u.slot = s.slot) : Grows s t := by
  intro electra
  obtain ⟨added, queue, new⟩ := one electra
  obtain ⟨added', queue', new'⟩ := two electra
  have epoch : getCurrentEpoch u = getCurrentEpoch s := by simp only [getCurrentEpoch, slot]
  refine ⟨added ++ added', by rw [queue', queue, List.append_assoc], fun c member => ?_⟩
  rcases List.mem_append.mp member with old | fresh
  · obtain ⟨w, read, later, assigned⟩ := new c old
    obtain ⟨w', read', kept⟩ := life.validators _ w read
    have exit := kept.exitEpoch assigned
    exact ⟨w', read', by rw [exit]; exact later, by rw [exit]; exact assigned⟩
  · obtain ⟨w, read, later, assigned⟩ := new' c fresh
    exact ⟨w, read, epoch ▸ later, assigned⟩

/-- A block step: master's frame and lifecycle, and the growth of the queue. -/
private def GrowStep {f : Fork} (s t : BeaconState preset f) : Prop :=
  Frame s t ∧ RegistryLifecycle s t ∧ Grows s t

private theorem GrowStep.of_same {f : Fork} {s t : BeaconState preset f} (frame : Frame s t)
    (life : RegistryLifecycle s t) (queue : .pectra ≤ f → SamePendingQueue s t) :
    GrowStep s t :=
  ⟨frame, life, Grows.of_same queue⟩

private theorem GrowStep.of_data {f : Fork} {s t : BeaconState preset f} (frame : Frame s t)
    (same : t.validators.data = s.validators.data)
    (queue : .pectra ≤ f → SamePendingQueue s t) : GrowStep s t :=
  GrowStep.of_same frame (RegistryLifecycle.of_data same) queue

private theorem GrowStep.refl {f : Fork} (s : BeaconState preset f) : GrowStep s s :=
  GrowStep.of_data (Frame.refl s) rfl fun _ => rfl

private theorem GrowStep.trans {f : Fork} {s u t : BeaconState preset f}
    (one : GrowStep s u) (two : GrowStep u t) : GrowStep s t :=
  ⟨one.1.trans two.1, one.2.1.trans two.2.1, one.2.2.trans two.2.2 two.2.1 one.1.slot⟩

private theorem GrowStep.fold {f : Fork} {s t : BeaconState preset f} {α ε : Type}
    {step : BeaconState preset f → α → Except ε (BeaconState preset f)} {xs : List α}
    (kept : ∀ a item b, step a item = .ok b → GrowStep a b)
    (ok : xs.foldlM step s = .ok t) : GrowStep s t :=
  foldlM_ok_invariant (GrowStep s)
    (fun _ _ _ prior computed => prior.trans (kept _ _ _ computed)) (GrowStep.refl s) ok

section GrowSteps

variable {f : Fork} {s t : BeaconState preset f}

private theorem growStep_processProposerSlashing {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processProposerSlashing ok).toFrame
    (registryLifecycle_processProposerSlashing ok) (fun _ => SamePendingQueue.proposer ok)

private theorem growStep_processAttesterSlashing {slashing : AttesterSlashing preset f}
    (ok : processAttesterSlashing config checks s slashing = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processAttesterSlashing ok).toFrame
    (registryLifecycle_processAttesterSlashing ok) (fun _ => SamePendingQueue.attester ok)

private theorem growStep_processAttestation {attestation : Attestation preset f} {parent : Slot}
    (ok : processAttestation config checks s parent attestation = .ok t) : GrowStep s t :=
  GrowStep.of_data (frame_processAttestation ok)
    (congrArg (·.data) (processAttestation_registry ok).1)
    (fun electra => SamePendingQueue.attestation electra ok)

private theorem growStep_processDeposit {before : f < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processDeposit ok).toFrame (registryLifecycle_processDeposit ok)
    (fun electra => SamePendingQueue.deposit electra ok)

private theorem growStep_processVoluntaryExit {signed : SignedVoluntaryExit}
    (ok : processVoluntaryExit config checks s signed = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processVoluntaryExit ok).toFrame
    (registryLifecycle_processVoluntaryExit ok) (fun _ => SamePendingQueue.voluntary ok)

private theorem growStep_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processBlsToExecutionChange ok).toFrame
    (registryLifecycle_processBlsToExecutionChange ok) (fun _ => SamePendingQueue.bls ok)

private theorem growStep_processDepositRequest {electra : .pectra ≤ f} {request : DepositRequest}
    (ok : processDepositRequest s electra request = .ok t) : GrowStep s t :=
  GrowStep.of_data (frame_processDepositRequest ok).toFrame
    (congrArg (·.data) (processDepositRequest_ok ok).2.1)
    (fun _ => SamePendingQueue.depositRequest ok)

private theorem growStep_processWithdrawalRequest {electra : .pectra ≤ f}
    {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processWithdrawalRequest ok).toFrame
    (registryLifecycle_processWithdrawalRequest ok)
    (fun _ => SamePendingQueue.withdrawalRequest ok)

/-- A queued consolidation assigns its source an exit after the current epoch. -/
private theorem grows_queueConsolidation {electra : .pectra ≤ f}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    Grows s t := by
  obtain ⟨churned, written, epoch, withdrawal, -, assigned, later, -, set, validators, pushed⟩ :=
    queueConsolidation_queued delay ok
  intro electra'
  refine ⟨[⟨sourceIndex, targetIndex⟩], ?_, fun c member => ?_⟩
  · exact pushed
  · rw [List.mem_singleton] at member
    subst member
    rw [validators]
    exact ⟨_, getValidator_eq_ok_iff.mp (getValidator_setValidator_self set), later, assigned⟩

/-- A consolidation request switches credentials or queues a consolidation. -/
private theorem growStep_processConsolidationRequest {electra : .pectra ≤ f}
    {request : ConsolidationRequest}
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processConsolidationRequest config s electra request = .ok t) : GrowStep s t := by
  have frame := (frame_processConsolidationRequest ok).toFrame
  have life := registryLifecycle_processConsolidationRequest ok
  suffices new : Grows s t from ⟨frame, life, new⟩
  clear frame life
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals try first
    | (cases ok; done)
    | (cases ok; exact Grows.of_same fun _ => rfl)
    | exact Grows.of_same fun _ => SamePendingQueue.compounding (liftAccessor_ok.mp ok)
  exact grows_queueConsolidation delay ok

private theorem growStep_processExecutionRequests {body : BeaconBlockBody preset f}
    {electra : .pectra ≤ f ∧ f < .glamsterdam}
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processExecutionRequests config s body electra = .ok t) : GrowStep s t := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
  exact (GrowStep.fold (fun _ _ _ ok => growStep_processDepositRequest ok) deposits).trans <|
    (GrowStep.fold (fun _ _ _ ok => growStep_processWithdrawalRequest ok) withdrawals).trans
      (GrowStep.fold (fun _ _ _ ok => growStep_processConsolidationRequest delay ok)
        consolidations)

private theorem growStep_processOperations {body : BeaconBlockBody preset f} {parent : Slot}
    (early : f < .glamsterdam) (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processOperations config checks s body parent = .ok t) :
    GrowStep s t := by
  unfold processOperations at ok
  rw [dite_eq_right (show ¬ .glamsterdam ≤ f from Nat.not_le_of_lt early)] at ok
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, _, _, _, _, proposers, _, attesters, _, attested, _, deposits, exited,
    exits, changed, changes, requests⟩ := ok
  have c : GrowStep exited changed := by
    unfold processBlsToExecutionChanges at changes
    split at changes
    · rw [← Array.foldlM_toList] at changes
      exact GrowStep.fold (fun _ _ _ ok => growStep_processBlsToExecutionChange ok) changes
    · cases changes; exact GrowStep.refl _
  have r : GrowStep changed t := by
    split at requests
    · exact growStep_processExecutionRequests delay requests
    · cases requests; exact GrowStep.refl _
  exact (GrowStep.fold (fun _ _ _ ok => growStep_processProposerSlashing ok) proposers).trans <|
    (GrowStep.fold (fun _ _ _ ok => growStep_processAttesterSlashing ok) attesters).trans <|
    (GrowStep.fold (fun _ _ _ ok => growStep_processAttestation ok) attested).trans <|
    (GrowStep.fold (fun _ _ _ ok => growStep_processDeposit ok) deposits).trans <|
    (GrowStep.fold (fun _ _ _ ok => growStep_processVoluntaryExit ok) exits).trans <|
    c.trans r

/-- A block from Altair and before Gloas keeps the frame and the lifecycle.

It also grows the queue. -/
private theorem growStep_processBlock {engine : ExecutionEngine preset f}
    {block : BeaconBlock preset f} (altair : .altair ≤ f) (early : f < .glamsterdam)
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processBlock config checks engine s block = .ok t) : GrowStep s t := by
  unfold processBlock at ok
  simp only [altair, ↓reduceDIte] at ok
  unfold processBlockAltair at ok
  simp only [stateBeforeOperations, bind_assoc, bind_ok_iff] at ok
  obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
    votedOk, operated, operatedOk, synced⟩ := ok
  rw [dite_eq_right (show ¬ .glamsterdam ≤ f from Nat.not_le_of_lt early)] at paidOk
  cases paidOk
  have header : GrowStep s headed := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
    exact GrowStep.of_data (frame_processBlockHeader headedOk).toFrame rfl fun _ => rfl
  have e : GrowStep headed executed := by
    split at executedOk
    · exact GrowStep.of_data (frame_processBlockExecution executedOk).toFrame
        (congrArg (·.data) (processBlockExecution_validators executedOk))
        (fun _ => SamePendingQueue.blockExecution early executedOk)
    · cases executedOk; exact GrowStep.refl _
  have randao : GrowStep executed revealed := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealedOk
    exact GrowStep.of_data (frame_processRandao revealedOk).toFrame rfl fun _ => rfl
  have v : GrowStep revealed voted := by
    split at votedOk
    · obtain ⟨_, _, rest⟩ := processEth1Data_eq votedOk
      exact GrowStep.of_data (frame_processEth1Data votedOk).toFrame (by rw [← rest])
        (fun _ => by unfold SamePendingQueue; rw [← rest])
    · cases votedOk; exact GrowStep.refl _
  have sync : GrowStep operated t := by
    have frame := (frame_processSyncAggregate synced).toFrame
    obtain ⟨balances, rfl⟩ := processSyncAggregate_eq synced
    exact GrowStep.of_data frame rfl fun _ => rfl
  exact header.trans <| e.trans <| randao.trans <| v.trans <|
    (growStep_processOperations early delay operatedOk).trans sync

end GrowSteps

/-! ## The queue of a run from X, and the stake a pass can move -/

private theorem fundingSources_eq {f : Fork} (electra : .pectra ≤ f) (s : BeaconState preset f) :
    fundingSources s = (s.pendingConsolidations electra).data.toList := by
  simp [fundingSources, electra]

/-- The queue is the unread part of X's queue, then entries that are new since X.

Every new entry has a source whose exit was assigned after `e0`, the epoch of X. -/
private def Shape (L : List PendingConsolidation) (e0 : Epoch) (n : ℕ) {f : Fork}
    (z : BeaconState preset f) : Prop :=
  ∃ N : List PendingConsolidation, fundingSources z = L.drop n ++ N ∧
    ∀ c ∈ N, ∃ w, z.validators.data[c.sourceIndex.toNat]? = some w ∧
      e0 < w.exitEpoch ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH

/-- A state of any fork with the same queue and a later life of its validators has the shape. -/
private theorem Shape.carry {L : List PendingConsolidation} {e0 : Epoch} {n : ℕ} {f g : Fork}
    {a : BeaconState preset f} {b : BeaconState preset g} (shape : Shape L e0 n a)
    (queue : fundingSources b = fundingSources a) (life : RegistryLifecycle a b) :
    Shape L e0 n b := by
  obtain ⟨N, eq, new⟩ := shape
  refine ⟨N, queue.trans eq, fun c member => ?_⟩
  obtain ⟨w, read, later, assigned⟩ := new c member
  obtain ⟨w', read', kept⟩ := life.validators _ w read
  have exit := kept.exitEpoch assigned
  exact ⟨w', read', by rw [exit]; exact later, by rw [exit]; exact assigned⟩

/-- A block that grows the queue keeps the shape. -/
private theorem Shape.grow {L : List PendingConsolidation} {e0 : Epoch} {n : ℕ} {f : Fork}
    {a b : BeaconState preset f} (electra : .pectra ≤ f) (shape : Shape L e0 n a)
    (grows : Grows a b) (life : RegistryLifecycle a b) (started : e0 ≤ getCurrentEpoch a) :
    Shape L e0 n b := by
  obtain ⟨N, eq, new⟩ := shape
  obtain ⟨added, queue, fresh⟩ := grows electra
  refine ⟨N ++ added, by rw [fundingSources_eq electra, queue, ← fundingSources_eq electra, eq,
    List.append_assoc], fun c member => ?_⟩
  rcases List.mem_append.mp member with old | recent
  · obtain ⟨w, read, later, assigned⟩ := new c old
    obtain ⟨w', read', kept⟩ := life.validators _ w read
    have exit := kept.exitEpoch assigned
    exact ⟨w', read', by rw [exit]; exact later, by rw [exit]; exact assigned⟩
  · obtain ⟨w, read, later, assigned⟩ := fresh c recent
    exact ⟨w, read, UInt64.lt_of_le_of_lt started later, assigned⟩

/-- A pass that reads `r` entries moves the shape on by `r`. -/
private theorem Shape.pass {L : List PendingConsolidation} {e0 : Epoch} {n r : ℕ} {f : Fork}
    {a b : BeaconState preset f} (shape : Shape L e0 n a)
    (queue : fundingSources b = (fundingSources a).drop r) (life : RegistryLifecycle a b) :
    Shape L e0 (n + r) b := by
  obtain ⟨N, eq, new⟩ := shape
  refine ⟨N.drop (r - (L.length - n)), ?_, fun c member => ?_⟩
  · rw [queue, eq, List.drop_append, List.drop_drop]
    simp [List.length_drop]
  · obtain ⟨w, read, later, assigned⟩ := new c (List.mem_of_mem_drop member)
    obtain ⟨w', read', kept⟩ := life.validators _ w read
    have exit := kept.exitEpoch assigned
    exact ⟨w', read', by rw [exit]; exact later, by rw [exit]; exact assigned⟩

/-- The stake that X lets a pending consolidation move: the cap of its source at X.

It counts only a source that is unslashed at X and can withdraw by `high + 1`. -/
private def capBound (x : ForkedBeaconState preset) (high : ℕ) (c : PendingConsolidation) : ℕ :=
  match x.state.validators.data[c.sourceIndex.toNat]? with
  | some v =>
    if v.slashed = false ∧ v.withdrawableEpoch.toNat ≤ high + 1 then
      (withdrawalMaxEffectiveBalance preset x.fork v).toNat
    else 0
  | none => 0

/-- A key that cannot switch to compounding credentials has a cap that does not rise. -/
private theorem withdrawalMax_le {f g : Fork} (hf : .pectra ≤ f) (hg : .pectra ≤ g)
    (caps : CapOrder preset) {v w : Validator}
    (frozen : hasCompoundingWithdrawalCredential w = true →
      hasCompoundingWithdrawalCredential v = true) :
    withdrawalMaxEffectiveBalance preset f w ≤ withdrawalMaxEffectiveBalance preset g v := by
  simp only [withdrawalMaxEffectiveBalance, hf, hg, ↓reduceIte, getMaxEffectiveBalance]
  by_cases hw : hasCompoundingWithdrawalCredential w = true
  · simp [hw, frozen hw]
  · by_cases hv : hasCompoundingWithdrawalCredential v = true
    · simp only [hw, hv, Bool.false_eq_true, ↓reduceIte]
      exact caps.compounding
    · simp only [hw, hv, Bool.false_eq_true, ↓reduceIte]
      exact UInt64.le_refl _

/-- What a run from X, at a state `p` of the epoch pass, knows about the pending consolidations. -/
private structure PassFacts (x : ForkedBeaconState preset) (high : ℕ) {f : Fork}
    (p : BeaconState preset f) : Prop where
  electraX : .pectra ≤ x.fork
  electraP : .pectra ≤ f
  caps : CapOrder preset
  delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  within : high + 2 ≤ (getCurrentEpoch x.state).toNat +
    config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  life : RegistryLifecycle x.state p
  cap : Internal.CapStep config x.state p
  orderedX : PendingConsolidationsOrdered config (getCurrentEpoch x.state).toNat x.state
  invariantP : PendingConsolidationInvariant config p
  cappedX : ∀ v ∈ x.state.validators.data,
    v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset x.fork v
  next : (getCurrentEpoch p).toNat + 1 ≤ high + 1
  nextNat : (getCurrentEpoch p + 1).toNat = (getCurrentEpoch p).toNat + 1

/-- An entry of X's queue, still queued at the pass, moves at most its cap at X. -/
private theorem old_entry_bound {x : ForkedBeaconState preset} {high : ℕ} {f : Fork}
    {p : BeaconState preset f} (facts : PassFacts (config := config) x high p)
    {c : PendingConsolidation}
    (inX : c ∈ (x.state.pendingConsolidations facts.electraX).data.toList)
    (inP : c ∈ (p.pendingConsolidations facts.electraP).data.toList) :
    sourceBound p (getCurrentEpoch p + 1) c ≤ capBound x high c := by
  obtain ⟨v, foundX, -, -, assignedX⟩ := (facts.orderedX.1 facts.electraX).2 c inX
  obtain ⟨-, unslashedX, -⟩ := (facts.orderedX.2 facts.electraX).2 c inX v foundX
  obtain ⟨wP, foundP', -, exitDelayP, -⟩ := (facts.invariantP facts.electraP).2 c inP
  obtain ⟨w, foundP, lifecycle⟩ := facts.life.validators _ v foundX
  obtain rfl : w = wP := Option.some.inj (foundP.symm.trans foundP')
  simp only [sourceBound, capBound, foundP, foundX]
  split
  · rename_i due
    have exitEq := lifecycle.exitEpoch assignedX
    have slashedX : v.slashed = false := by
      cases flag : v.slashed
      · rfl
      · have := ((facts.cap.withdrawal _ v w foundX foundP).1 flag assignedX).1
        rw [due.1] at this
        cases this
    have dueNat := UInt64.le_iff_toNat_le.mp due.2
    have withdrawX := unslashedX slashedX
    rw [facts.nextNat] at dueNat
    have exitNat := congrArg UInt64.toNat exitEq
    have exitDelay : w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
        w.withdrawableEpoch.toNat := exitDelayP
    have dueX : v.slashed = false ∧ v.withdrawableEpoch.toNat ≤ high + 1 :=
      ⟨slashedX, by have := facts.next; omega⟩
    simp only [dueX, and_self, ↓reduceIte]
    have capped : w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f w :=
      facts.cap.capped facts.cappedX w (Array.mem_of_getElem? foundP)
    have bounded := withdrawalMax_le facts.electraP facts.electraX facts.caps
      ((facts.cap.frozen _ v w foundX foundP assignedX).2)
    exact UInt64.le_iff_toNat_le.mp (UInt64.le_trans capped bounded)
  · exact Nat.zero_le _

/-- An entry that is new since X moves nothing at the pass.

Its source exits after X, so it withdraws after the run. -/
private theorem new_entry_zero {x : ForkedBeaconState preset} {high : ℕ} {f : Fork}
    {p : BeaconState preset f} (facts : PassFacts (config := config) x high p)
    {c : PendingConsolidation}
    (inP : c ∈ (p.pendingConsolidations facts.electraP).data.toList) {w : Validator}
    (foundW : p.validators.data[c.sourceIndex.toNat]? = some w)
    (fresh : getCurrentEpoch x.state < w.exitEpoch) :
    sourceBound p (getCurrentEpoch p + 1) c = 0 := by
  obtain ⟨w', found', -, exitDelay, -⟩ := (facts.invariantP facts.electraP).2 c inP
  obtain rfl : w' = w := Option.some.inj (found'.symm.trans foundW)
  have later := UInt64.lt_iff_toNat_lt.mp fresh
  simp only [sourceBound, foundW]
  split
  · rename_i due
    have dueNat := UInt64.le_iff_toNat_le.mp due.2
    rw [facts.nextNat] at dueNat
    have := facts.next
    have := facts.within
    have := facts.delay
    omega
  · rfl

/-- A pass, from a state with the shape, credits at most the caps at X of the entries it reads. -/
private theorem pass_step {x : ForkedBeaconState preset} {high : ℕ} {f : Fork}
    {p t : BeaconState preset f} {n : ℕ} (facts : PassFacts (config := config) x high p)
    (shape : Shape (x.state.pendingConsolidations facts.electraX).data.toList
      (getCurrentEpoch x.state) n p)
    (computed : processPendingConsolidations p facts.electraP = .ok t) :
    ∃ r, Shape (x.state.pendingConsolidations facts.electraX).data.toList
        (getCurrentEpoch x.state) (n + r) t ∧ RegistryLifecycle p t ∧
      credited p t ≤
        ((((x.state.pendingConsolidations facts.electraX).data.toList.drop n).take r).map
          (capBound x high)).sum := by
  obtain ⟨result, passed, balancesEq, queueEq⟩ := processPendingConsolidations_pass computed
  obtain ⟨validators, sizes, credits⟩ :=
    pass_credits_le (getCurrentEpoch p + 1) _ passed
  have sameValidators := (processPendingConsolidations_kept computed).1
  have life : RegistryLifecycle p t := .of_data (congrArg (·.data) sameValidators)
  have queue : fundingSources t = (fundingSources p).drop result.2 := by
    rw [fundingSources_eq facts.electraP, fundingSources_eq facts.electraP]
    exact queueEq
  refine ⟨result.2, shape.pass queue life, life, ?_⟩
  have creditsEq : credited p t = credited p result.1 := by
    simp [credited, actualBalanceAt, balancesEq]
  rw [creditsEq]
  refine Nat.le_trans credits ?_
  obtain ⟨N, eq, new⟩ := shape
  rw [← fundingSources_eq facts.electraP, eq, List.take_append, List.map_append,
    List.sum_append]
  have oldPart : ((((x.state.pendingConsolidations facts.electraX).data.toList.drop n).take
      result.2).map (sourceBound p (getCurrentEpoch p + 1))).sum ≤
      ((((x.state.pendingConsolidations facts.electraX).data.toList.drop n).take result.2).map
        (capBound x high)).sum := by
    apply List.sum_le_sum
    intro c member
    have inDrop := List.mem_of_mem_take member
    refine old_entry_bound facts (List.mem_of_mem_drop inDrop) ?_
    rw [← fundingSources_eq facts.electraP, eq]
    exact List.mem_append_left _ inDrop
  have newPart : ((N.take (result.2 -
      ((x.state.pendingConsolidations facts.electraX).data.toList.drop n).length)).map
        (sourceBound p (getCurrentEpoch p + 1))).sum = 0 := by
    apply List.sum_eq_zero
    intro m member
    obtain ⟨c, inTake, rfl⟩ := List.mem_map.mp member
    have inN := List.mem_of_mem_take inTake
    obtain ⟨w, foundW, fresh, -⟩ := new c inN
    refine new_entry_zero facts ?_ foundW fresh
    rw [← fundingSources_eq facts.electraP, eq]
    exact List.mem_append_right _ inN
  omega

/-- The upgrades due at a slot keep the shape of the queue. -/
private theorem upgrade_shape {L : List PendingConsolidation} {e0 : Epoch} {n : ℕ}
    {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (electra : .pectra ≤ pre.fork) (shape : Shape L e0 n pre.state)
    (ok : upgradeNext config checks pre = .ok post) (early : post.val.fork < .glamsterdam) :
    .pectra ≤ post.val.fork ∧ Shape L e0 n post.val.state := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · exact absurd electra (Nat.not_le_of_lt (by decide : Fork.phase0 < Fork.pectra))
  · exact absurd electra (Nat.not_le_of_lt (by decide : Fork.altair < Fork.pectra))
  · exact absurd electra (Nat.not_le_of_lt (by decide : Fork.bellatrix < Fork.pectra))
  · exact absurd electra (Nat.not_le_of_lt (by decide : Fork.shapella < Fork.pectra))
  · exact absurd electra (Nat.not_le_of_lt (by decide : Fork.dencun < Fork.pectra))
  · obtain ⟨_, upgraded, rfl⟩ := ok
    refine ⟨(by decide : Fork.pectra ≤ Fork.fusaka),
      shape.carry ?_ (.of_data (upgradeToFulu_spec upgraded).1)⟩
    simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
    obtain ⟨_, -, rfl⟩ := upgraded
    simp [fundingSources, carryFields, carryList, carryRooted,
      show Fork.pectra ≤ Fork.fusaka from by decide]
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.lt_irrefl _ early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.not_le_of_lt early (show Fork.glamsterdam ≤ .hegota from by decide))

private theorem upgrades_shape {L : List PendingConsolidation} {e0 : Epoch} {n : ℕ}
    {advanced last : ForkedBeaconState preset} (electra : .pectra ≤ advanced.fork)
    (early : last.fork < .glamsterdam) (shape : Shape L e0 n advanced.state)
    (ok : processUpgrades config checks advanced = .ok last) : Shape L e0 n last.state := by
  have rest := processUpgrades_induction
    (property := fun z => z.fork < .glamsterdam → .pectra ≤ z.fork ∧ Shape L e0 n z.state)
    (fun {pre post} h ok early => by
      obtain ⟨electraPre, shapePre⟩ := h (Nat.lt_trans post.property early)
      exact upgrade_shape electraPre shapePre ok early)
    (fun _ => ⟨electra, shape⟩) ok
  exact (rest early).2

/-! ## The stages of an epoch -/

/-- The order of the pending consolidations of a state at its own epoch. -/
private abbrev OrderedAt {f : Fork} (config : Config) (s : BeaconState preset f) : Prop :=
  PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s

/-- A stage other than the pass keeps the slot, the queue and the order, and the lifecycle. -/
private theorem stage_rel {f : Fork} (electra : .pectra ≤ f) {k : EpochStage}
    (notPass : k ≠ .pendingConsolidations) {a b : BeaconState preset f}
    (edge : EpochStage.Edge config checks k a b) :
    RegistryLifecycle a b ∧ b.slot = a.slot ∧ fundingSources b = fundingSources a ∧
      (OrderedAt config a → OrderedAt config b) := by
  refine ⟨edge.registryLifecycle, edge.slot_eq, ?_, edge.pendingConsolidationsOrdered⟩
  rw [fundingSources_eq electra, fundingSources_eq electra,
    show b.pendingConsolidations = a.pendingConsolidations from edge.samePendingQueue notPass]

/-- The stages before the pass, from the cached state, keep what the pass reads. -/
private theorem prefix_rel {f : Fork} (electra : .pectra ≤ f) {stages : List EpochStage}
    (notPass : ∀ k ∈ stages, k ≠ .pendingConsolidations) {a b : BeaconState preset f}
    (trace : EpochTrace (EpochStage.action config checks) stages a b) :
    RegistryLifecycle a b ∧ b.slot = a.slot ∧ fundingSources b = fundingSources a ∧
      (OrderedAt config a → OrderedAt config b) := by
  apply trace.transport
    (fun a b : BeaconState preset f => RegistryLifecycle a b ∧ b.slot = a.slot ∧
      fundingSources b = fundingSources a ∧ (OrderedAt config a → OrderedAt config b))
    (fun _ => ⟨.refl _, rfl, rfl, id⟩)
    (fun one two => ⟨one.1.trans two.1, two.2.1.trans one.2.1, two.2.2.1.trans one.2.2.1,
      two.2.2.2 ∘ one.2.2.2⟩)
  intro k member s t computed
  exact stage_rel electra (notPass k member) (EpochStage.action_cases.mp computed)

/-- The events that the replay of the rewards records are rewards, penalties or inactivity. -/
private theorem rewards_noConsolidations {f : Fork} {pre post : BalanceReplay preset f}
    (initial : ∀ e ∈ pre.2, e.source ≠ .consolidations)
    (ok : replayRewards (config := config) pre = .ok post) :
    ∀ e ∈ post.2, e.source ≠ .consolidations := by
  have record {pre post : BalanceReplay preset f} {source : BalanceSource}
      {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
      {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
      (notConsolidation : source ≠ .consolidations)
      (initial : ∀ e ∈ pre.2, e.source ≠ .consolidations)
      (ok : recordBalance source limits action pre = .ok post) :
      ∀ e ∈ post.2, e.source ≠ .consolidations := by
    simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨⟨credit, debit⟩, _, t, _, rfl⟩ := ok
    intro e member
    rcases List.mem_append.mp member with old | new
    · exact initial e old
    · exact (List.mem_singleton.mp new) ▸ notConsolidation
  exact replayRewards_induction (fun pre => ∀ e ∈ pre.2, e.source ≠ .consolidations)
    (fun prior ok => record (by decide) prior ok)
    (fun penalty prior ok => record (by rcases penalty with rfl | rfl <;> decide) prior ok)
    initial ok

/-- The queue of X. -/
private abbrev queueX (x : ForkedBeaconState preset) (h : .pectra ≤ x.fork) :
    List PendingConsolidation :=
  (x.state.pendingConsolidations h).data.toList

/-- A slot step moves the shape of the queue on, and its consolidation credits are bounded. -/
private theorem slot_step {g x m last : ForkedBeaconState preset}
    (shared : Run config checks g x) (pre : Run config checks x m)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) (electra : .pectra ≤ x.fork)
    (high : ℕ) (within : high + 2 ≤ (getCurrentEpoch x.state).toNat +
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : advanceSlotAcross config checks m = .ok last) (early : last.fork < .glamsterdam)
    (endEpoch : (getCurrentEpoch last.state).toNat ≤ high + 1) {n : ℕ}
    (shape : Shape (queueX x electra) (getCurrentEpoch x.state) n m.state) :
    ∃ r, Shape (queueX x electra) (getCurrentEpoch x.state) (n + r) last.state ∧
      ∀ {events : List (BalanceEvent preset)},
        (Step.slot ok : Step config checks m last).balanceEvents = .ok events →
        ((events.filter (·.source = .consolidations)).map BalanceEvent.credits).sum ≤
          ((((queueX x electra).drop n).take r).map (capBound x high)).sum := by
  have beforeFork : m.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Step.slot ok).chainStep.fork_le early
  have mFork : .pectra ≤ m.fork := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
  obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
  obtain ⟨crossings, crossingOk, -⟩ := upgradeBalanceReplay_bounded upgrades
  have advanceCopy := slotOk
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at advanceCopy
  obtain ⟨next, nextOk, cached, cachedOk, epoched, epochOk, afterEq⟩ := advanceCopy
  have sum : next.toNat = m.state.slot.toNat + 1 :=
    (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp (liftAccessor_ok.mp nextOk))).2
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have shapeCached : Shape (queueX x electra) (getCurrentEpoch x.state) n cached := by
    rw [cachedEq]; exact shape
  by_cases boundary : next % preset.SLOTS_PER_EPOCH = 0
  · simp only [epochIfLast, boundary, ↓reduceIte] at epochOk
    obtain ⟨middle, updated, recorded, recordOk, updatedOk, validators, balances, cutOk⟩ :=
      epochBalanceReplay_result_before cached epoched beforeFork epochOk
    obtain ⟨justified, scored, rewarded, registered, slashed, reset, deposited, rewardEvents,
      limit, trace6, justifiedOk, scoredOk, rewardedOk, registeredOk, slashedOk, resetOk,
      depositedOk, consolidatedOk, rewardReplay, recordedEq⟩ := funding_epoch_site cutOk recordOk
    have trace7 : EpochTrace (EpochStage.action config checks)
        [.justification, .inactivity, .rewards, .registry, .slashings, .eth1Reset,
          .pendingDeposits] cached deposited :=
      EpochTrace.append_iff.mpr
        ⟨reset, trace6, .cons (EpochStage.action_cases.mpr depositedOk) .nil⟩
    simp only [EpochStage.Edge, mFork, ↓reduceDIte] at consolidatedOk
    simp only [mFork, ↓reduceDIte] at recordedEq
    -- The facts about the run before the step.
    have xEarly : x.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps pre.chainSteps) beforeFork
    have lifeXM : RegistryLifecycle x.state m.state := pre.registryLifecycle
    have capXM := (Internal.CapStep.run pre caps.activation caps.compounding beforeFork).1
    have orderedM : OrderedAt config m.state :=
      (shared.append pre).pendingConsolidationsOrdered genesis beforeFork delay
    have orderedX := shared.pendingConsolidationsOrdered genesis xEarly delay
    have cappedX := shared.effectiveBalance_capped genesis caps.activation caps.compounding xEarly
    -- The cached state is the state of the step, up to its roots.
    have lifeMC : RegistryLifecycle m.state cached := .of_data (by rw [cachedEq])
    have slotMC : cached.slot = m.state.slot := by rw [cachedEq]
    have queueMC : fundingSources cached = fundingSources m.state := by rw [cachedEq]; rfl
    have orderedC : OrderedAt config cached := by rw [cachedEq]; exact orderedM
    have capMC : Internal.CapStep config m.state cached := by
      rw [cachedEq]; exact Internal.CapStep.data
    -- The stages up to the pass.
    obtain ⟨lifeCD, slotCD, queueCD, orderedCD⟩ := prefix_rel mFork (by
      intro k member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact fun h => by cases h)
      trace7
    have capCD := Internal.CapStep.epochTrace trace7
    have epochD : getCurrentEpoch deposited = getCurrentEpoch m.state := by
      simp only [getCurrentEpoch, slotCD, slotMC]
    -- The epoch of the next state.
    have divides : preset.SLOTS_PER_EPOCH.toNat ∣ m.state.slot.toNat + 1 := by
      rw [← sum]
      exact Nat.dvd_of_mod_eq_zero (by simpa using congrArg UInt64.toNat boundary)
    have epochLast : (getCurrentEpoch last.state).toNat = (getCurrentEpoch m.state).toNat + 1 := by
      have advancedEpoch : getCurrentEpoch last.state = getCurrentEpoch
          ({ epoched with slot := next } : BeaconState preset m.fork) := by
        rw [afterEq]
        exact congrArg (computeEpochAtSlot preset) (processUpgrades_slot upgrades)
      rw [advancedEpoch]
      have nextEpoch :=
        getCurrentEpoch_toNat ({ epoched with slot := next } : BeaconState preset m.fork)
      simp only at nextEpoch
      rw [nextEpoch, sum, Nat.succ_div_of_dvd divides, getCurrentEpoch_toNat m.state]
    have nextBound : (getCurrentEpoch deposited).toNat + 1 ≤ high + 1 := by
      rw [epochD]; omega
    have nextNat :
        (getCurrentEpoch deposited + 1).toNat = (getCurrentEpoch deposited).toNat + 1 := by
      have fits := (getCurrentEpoch last.state).toNat_lt
      rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt]
      rw [epochD]; omega
    have facts : PassFacts (config := config) x high deposited :=
      { electraX := electra, electraP := mFork, caps := caps, delay := delay, within := within,
        life := lifeXM.trans (lifeMC.trans lifeCD), cap := capXM.trans (capMC.trans capCD),
        orderedX := orderedX, invariantP := (orderedCD orderedC).1, cappedX := cappedX,
        next := nextBound, nextNat := nextNat }
    have shapeD : Shape (queueX x electra) (getCurrentEpoch x.state) n deposited :=
      shapeCached.carry queueCD lifeCD
    obtain ⟨r, shapeMiddle, lifePM, credits⟩ := pass_step facts shapeD consolidatedOk
    refine ⟨r, ?_, fun {events} replayed => ?_⟩
    · have trace := processEpoch_trace epochOk
      change EpochTrace _ (EpochStage.prefixStages ++ [.payments, .effectiveBalances,
        .slashingsReset, .randaoReset, .history, .participation, .syncCommittees,
        .proposerLookahead, .ptcWindow]) _ _ at trace
      obtain ⟨middle', head, tailTrace⟩ := EpochTrace.append_iff.mp trace
      have midEq : middle' = middle := by
        have h1 : epochBeforePayments config checks cached = .ok middle' :=
          (epochBeforePayments_eq_run config checks cached).trans
            (EpochTrace.run_ok_iff.mpr head)
        rw [h1] at cutOk
        exact Except.ok.inj cutOk
      subst midEq
      obtain ⟨lifeTail, -, queueTail, -⟩ := prefix_rel mFork (by
        intro k member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact fun h => by cases h) tailTrace
      have shapeEpoched := shapeMiddle.carry queueTail lifeTail
      have shapeAdvanced : Shape (queueX x electra) (getCurrentEpoch x.state) (n + r)
          advanced := by
        rw [← afterEq]
        exact shapeEpoched.carry rfl (.of_data rfl)
      exact upgrades_shape (advanced := ⟨m.fork, advanced⟩) mFork early shapeAdvanced upgrades
    · have eventsEq : events = recorded ++ crossings :=
        Except.ok.inj (replayed.symm.trans (Step.balanceEvents_epoch_slot ok cachedOk nextOk
          boundary recordOk slotOk crossingOk))
      have rewardsNo := rewards_noConsolidations (pre := (scored, [])) (by simp) rewardReplay
      have f1 : rewardEvents.filter (fun e => decide (e.source = .consolidations)) = [] :=
        List.filter_eq_nil_iff.mpr fun e member => by simpa using rewardsNo e member
      have f2 : crossings.filter (fun e => decide (e.source = .consolidations)) = [] :=
        List.filter_eq_nil_iff.mpr fun e member => by
          simp [upgradeBalanceReplay_crossing crossingOk e member]
      rw [eventsEq, recordedEq]
      simp only [List.append_assoc, List.filter_append, f1, f2]
      simpa [List.filter_cons, credited, BalanceEvent.credits, actualBalanceAt] using credits
  · simp only [epochIfLast, boundary, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochOk
    subst epochOk
    refine ⟨0, ?_, fun {events} replayed => ?_⟩
    · have shapeAdvanced : Shape (queueX x electra) (getCurrentEpoch x.state) (n + 0)
          advanced := by
        rw [← afterEq]
        exact shapeCached.carry rfl (.of_data rfl)
      exact upgrades_shape (advanced := ⟨m.fork, advanced⟩) mFork early shapeAdvanced upgrades
    · have eventsEq : events = crossings := by
        simpa [Step.balanceEvents, cachedOk, nextOk, boundary, slotOk, crossingOk, pure,
          Except.pure,
          bind, Except.bind] using replayed.symm
      subst eventsEq
      have none : (events.filter (·.source = .consolidations)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro e member
        simp [upgradeBalanceReplay_crossing crossingOk e member]
      simp [none]

/-- A block keeps the shape of the queue: it only appends entries that are new since X. -/
private theorem block_step {f : Fork} {e0 : Epoch} {L : List PendingConsolidation} {n : ℕ}
    (electra : .pectra ≤ f) (early : f < .glamsterdam)
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {engine : ExecutionEngine preset f} {signed : SignedBeaconBlock preset f}
    {s t : BeaconState preset f}
    (ok : applySignedBlock config checks engine s signed true = .ok t)
    (started : e0 ≤ getCurrentEpoch s) (shape : Shape L e0 n s) : Shape L e0 n t := by
  have grown := growStep_processBlock (Nat.le_trans (by decide) electra) early delay
    (applySignedBlock_ok ok).2.1
  exact shape.grow electra grown.2.2 grown.2.1 started

/-- The consolidation credits of a run from X are within the caps of the entries it reads. -/
private theorem run_credits {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (electra : .pectra ≤ x.fork) (high : ℕ)
    (within : high + 2 ≤ (getCurrentEpoch x.state).toNat +
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    ∃ n, Shape (queueX x electra) (getCurrentEpoch x.state) n y.state ∧
      ((events.filter (·.source = .consolidations)).map BalanceEvent.credits).sum ≤
        (((queueX x electra).take n).map (capBound x high)).sum := by
  induction tail generalizing events with
  | nil =>
    cases replayed
    refine ⟨0, ⟨[], ?_, fun c member => by simp at member⟩, by simp⟩
    rw [fundingSources_eq electra]
    simp [queueX]
  | @snoc middle last pre step ih =>
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    have epochStep := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
    obtain ⟨n, shape, bound⟩ := ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early)
      (by omega) priorOk
    have inFork : .pectra ≤ middle.fork :=
      Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
    have started : getCurrentEpoch x.state ≤ getCurrentEpoch middle.state :=
      currentEpoch_le_of_chainSteps pre.chainSteps
    have beforeFork : middle.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have growth : ∀ {r : ℕ}, (((queueX x electra).take n).map (capBound x high)).sum +
        ((((queueX x electra).drop n).take r).map (capBound x high)).sum =
        (((queueX x electra).take (n + r)).map (capBound x high)).sum := by
      intro r
      rw [List.take_add, List.map_append, List.sum_append]
    have stepResult : ∃ r, Shape (queueX x electra) (getCurrentEpoch x.state) (n + r) last.state ∧
        ∀ {added : List (BalanceEvent preset)}, step.balanceEvents = .ok added →
          ((added.filter (·.source = .consolidations)).map BalanceEvent.credits).sum ≤
            ((((queueX x electra).drop n).take r).map (capBound x high)).sum := by
      cases step with
      | block engine signed due ok =>
        refine ⟨0, block_step inFork early (by omega) ok started shape, fun {added} addedOk => ?_⟩
        have none : (added.filter (·.source = .consolidations)) = [] :=
          List.filter_eq_nil_iff.mpr fun e member => by
            simpa using blockReplay_noConsolidations inFork early engine _ _
              (Step.balanceEvents_block early addedOk) e member
        simp [none]
      | slot ok =>
        obtain ⟨r, shapeLast, credits⟩ := slot_step shared pre genesis caps delay electra high
          within ok early endEpoch shape
        exact ⟨r, shapeLast, fun {added} addedOk => credits addedOk⟩
    obtain ⟨r, shapeLast, credits⟩ := stepResult
    refine ⟨n + r, shapeLast, ?_⟩
    by_cases selected : (getCurrentEpoch middle.state).toNat ≤ high + 1
    · simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
      obtain ⟨added, addedOk, rfl⟩ := rest
      have := credits addedOk
      rw [List.filter_append, List.map_append, List.sum_append, ← growth]
      omega
    · simp only [selected, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      rw [← growth]
      omega

/-- The caps of the entries of a queue, as the caps of their sources that X lets move. -/
private theorem capBound_sum (x : ForkedBeaconState preset) (high : ℕ)
    (queue : List PendingConsolidation) :
    (queue.map (capBound x high)).sum =
      ((((queue.filterMap fun c => x.state.validators.data[c.sourceIndex.toNat]?).filter
        fun v => !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)).map
          fun v => (withdrawalMaxEffectiveBalance preset x.fork v).toNat).sum) := by
  induction queue with
  | nil => simp
  | cons c rest ih =>
    cases lookup : x.state.validators.data[c.sourceIndex.toNat]? with
    | none => simpa [capBound, lookup] using ih
    | some v =>
      by_cases due : v.slashed = false ∧ v.withdrawableEpoch.toNat ≤ high + 1
      · simp [capBound, lookup, due, ih]
      · have : ¬ (!v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)) = true := by
          simpa [Bool.not_eq_true'] using due
        simp [capBound, lookup, due, this, ih]

/-! ## Group A: credits to exiting keys -/

/-- A1 (item 14, run lift).

Along C's run, no deposit credits a key that exits at the run's start.

The key stays not withdrawable through the run's end.

`kept` is the withdrawable-kept fact at the state before each deposit event of a slot step.

A block deposit needs none: from Electra it raises no balance.

It says that an assigned exit stays (`RegistryLifecycle`).

It says that once the exit is set, the withdrawable epoch only rises (`WithdrawableKept`).

The private sources of these facts are `WithdrawalKept` in PendingConsolidations.

The other private source is `Lives` in BranchLedger.

It also says that the epoch of each event's state is at most the run's last epoch. -/
private theorem Run.exiting_deposit_credit_zero_of_kept {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (high : ℕ) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (kept : ∀ {u w : ForkedBeaconState preset} (ok : advanceSlotAcross config checks u = .ok w),
      tail.Contains (Step.slot ok) → ∀ {es : List (BalanceEvent preset)},
        (Step.slot ok : Step config checks u w).balanceEvents = .ok es →
        ∀ e ∈ es, e.source = .deposits →
          RegistryLifecycle x.state e.before.state ∧ WithdrawableKept x.state e.before.state ∧
          getCurrentEpoch e.before.state ≤ getCurrentEpoch y.state)
    (i : ℕ) (v : Validator) (found : x.state.validators.data[i]? = some v)
    (exited : v.exitEpoch.toNat < 2 ^ 64 - 1)
    (held : (getCurrentEpoch y.state).toNat < v.withdrawableEpoch.toNat) :
    ((events.filter (·.source = .deposits)).map (keyCredit i)).sum = 0 := by
  have located := run_located tail electra early high replayed
  apply List.sum_eq_zero
  intro n member
  obtain ⟨e, filtered, rfl⟩ := List.mem_map.mp member
  obtain ⟨inEvents, sourceEq⟩ := List.mem_filter.mp filtered
  simp only [decide_eq_true_eq] at sourceEq
  rcases located e inEvents sourceEq with unconditional | ⟨u, w, ok, es, contains, replayedEs,
      inStep, keeps⟩
  · have := unconditional i
    simp only [keyCredit]
    omega
  · obtain ⟨life, withdrawal, epoch⟩ := kept ok contains replayedEs e inStep sourceEq
    obtain ⟨w, read, lifecycle⟩ := life.validators i v found
    have assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
      rw [far] at exited
      exact absurd exited (Nat.lt_irrefl _)
    have sameExit := lifecycle.exitEpoch assigned
    have later := UInt64.le_iff_toNat_le.mp (withdrawal i v w found read assigned).1
    have now := UInt64.le_iff_toNat_le.mp epoch
    have same := keeps i w read (by rw [sameExit]; exact exited) (by omega)
    simp [keyCredit, actualBalanceAt, same]

/-- Along C's run from Fulu, no deposit credits a key that exits at the run's start.

The key stays not withdrawable through the run's end.

The withdrawable-kept fact at each deposit event of a slot step is `Run.events_kept`. -/
private theorem Run.exiting_deposit_credit_zero {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (fulu : .fusaka ≤ x.fork) (early : y.fork < .glamsterdam)
    (high : ℕ) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (i : ℕ) (v : Validator) (found : x.state.validators.data[i]? = some v)
    (exited : v.exitEpoch.toNat < 2 ^ 64 - 1)
    (held : (getCurrentEpoch y.state).toNat < v.withdrawableEpoch.toNat) :
    ((events.filter (·.source = .deposits)).map (keyCredit i)).sum = 0 :=
  Run.exiting_deposit_credit_zero_of_kept tail (Nat.le_trans (by decide) fulu) early high replayed
    (fun {_ _} ok contained {_} replayedEs =>
      PinSplit4.Run.events_kept shared genesis tail fulu early ok contained replayedEs)
    i v found exited held

/-- A2'' (rev 2.5.1).

Take a run from X whose last epoch is within the withdrawal delay of X's.

The consolidation credits to all keys along it are at most a sum of caps.

The sum is over the sources of X's pending consolidations.

They are unslashed at X and withdrawable by `high + 1`.

Each source counts at its cap at X.

An entry requested after X is due only past the run, so every applied entry is in X's queue.

It moves at most the source's effective balance, which is at most its cap.

An exited key cannot switch to compounding, so its cap does not rise after X. -/
private theorem Run.consolidation_credits_le_X {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset)
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (high : ℕ) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (withinDelay : high + 2 ≤
      (getCurrentEpoch x.state).toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    ((events.filter (·.source = .consolidations)).map BalanceEvent.credits).sum ≤
      ((((x.state.pendingConsolidations electra).data.toList.filterMap fun c =>
        x.state.validators.data[c.sourceIndex.toNat]?).filter fun v =>
          !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)).map fun v =>
            (withdrawalMaxEffectiveBalance preset x.fork v).toNat).sum := by
  obtain ⟨n, -, bound⟩ := run_credits shared genesis caps delay electra high withinDelay tail
    early endEpoch replayed
  rw [← capBound_sum]
  refine Nat.le_trans bound ?_
  have split := List.take_append_drop n (x.state.pendingConsolidations electra).data.toList
  conv_rhs => rw [← split, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _
end PinSplit

end GroupA

end EthLib.Consensus.Models.Network
