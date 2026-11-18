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

/-- The terms below an index count their value, and the others count zero. -/
private theorem sum_range_ite_lt_fn (pen : ℕ → ℕ) (k : ℕ) :
    ∀ j, ∑ t ∈ Finset.range j, (if t < k then pen t else 0) = ∑ t ∈ Finset.range (min j k), pen t
  | 0 => by simp
  | j + 1 => by
    rw [Finset.sum_range_succ, sum_range_ite_lt_fn pen k j]
    by_cases below : j < k
    · simp [below, Nat.min_eq_left (Nat.le_of_lt below),
        Nat.min_eq_left (Nat.succ_le_of_lt below), Finset.sum_range_succ]
    · have atLeast : k ≤ j := Nat.le_of_not_lt below
      simp [below, Nat.min_eq_right atLeast, Nat.min_eq_right (Nat.le_succ_of_le atLeast)]

/-- A sum over an interval of naturals is the sum over the offsets from its start. -/
private theorem sum_Ico_offsets (pen : ℕ → ℕ) (a b : ℕ) :
    ∑ t ∈ Finset.Ico a b, pen t = ∑ t ∈ Finset.range (b - a), pen (a + t) := by
  refine Finset.sum_nbij' (fun t => t - a) (fun t => a + t) ?_ ?_ ?_ ?_ ?_
  · intro t member
    simp only [Finset.mem_Ico, Finset.mem_range] at member ⊢
    omega
  · intro t member
    simp only [Finset.mem_Ico, Finset.mem_range] at member ⊢
    omega
  · intro t member
    simp only [Finset.mem_Ico] at member
    omega
  · intro t member
    omega
  · intro t member
    simp only [Finset.mem_Ico] at member
    congr 1
    omega

/-- A sum over a list of the first terms is the sum over the finite set of the first terms. -/
private theorem list_range_sum (pen : ℕ → ℕ) :
    ∀ j, ((List.range j).map pen).sum = ∑ t ∈ Finset.range j, pen t
  | 0 => by simp
  | j + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_range_sum pen j,
      Finset.sum_range_succ]
    simp

/-- A state of a segment that is followed by a step of the segment is in the epoch of its start. -/
private theorem segment_epoch_eq {m n z : ForkedBeaconState preset}
    (mid : Run config checks m n) (pre : Run config checks m z) (post : Run config checks z n)
    (split : mid = pre.append post)
    (starts : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      mid.Contains step → getCurrentEpoch u.state = getCurrentEpoch m.state)
    (before : (getCurrentEpoch z.state).toNat < (getCurrentEpoch n.state).toNat) :
    getCurrentEpoch z.state = getCurrentEpoch m.state := by
  subst split
  cases post with
  | nil => exact absurd before (Nat.lt_irrefl _)
  | @snoc u _ inner step =>
    have atU : getCurrentEpoch u.state = getCurrentEpoch m.state :=
      starts step (.last (pre.append inner) step)
    exact UInt64.le_antisymm
      (atU ▸ currentEpoch_le_of_chainSteps inner.chainSteps)
      (currentEpoch_le_of_chainSteps pre.chainSteps)

/-- The penalties of one key over a branch from Altair are at most the sum of its pass rates.

The rate must hold at each state of the branch before the epoch of its end, at that state's epoch.

The branch ends `epoch y - epoch x` epochs, and each runs one rewards pass.

The cut induction of the a priori bound, `run_cuts_le`, sums the segments. -/
private theorem Run.passDebit_le_rates {x y : ForkedBeaconState preset}
    (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (altair : .altair ≤ x.fork) (high : ℕ)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    {v : ℕ} (inside : v < x.state.validators.data.size) (pen : ℕ → ℕ)
    (rate : ∀ {z : ForkedBeaconState preset} (pre : Run config checks x z)
      (post : Run config checks z y), tail = pre.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch y.state).toNat →
      passPenaltyRate config z v ≤ pen (getCurrentEpoch z.state).toNat)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    (events.map (penaltyDebit v)).sum ≤
      ∑ t ∈ Finset.Ico (getCurrentEpoch x.state).toNat (getCurrentEpoch y.state).toNat, pen t := by
  have total := run_cuts_le high tail early
    (fun z => passPenaltyRate config z v ≤ pen (getCurrentEpoch z.state).toNat)
    (penaltyDebit v)
    (fun t => if t < ix x y then pen ((getCurrentEpoch x.state).toNat + t) else 0) rate
    (fun {m n} toM mid rest starts rates {found} found_ok => by
      have nEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) early
      have ny := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest.chainSteps)
      have segment := segment_passDebit_le mid nEarly
        (Nat.le_trans altair (fork_le_of_chainSteps toM.chainSteps)) high (by omega) starts
        (Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps toM.chainSteps))
        (pen (getCurrentEpoch m.state).toNat)
        (fun {z} preZ postZ split before => by
          have same := segment_epoch_eq mid preZ postZ split starts before
          rw [← same]
          exact rates preZ postZ split before)
        found_ok
      refine segment.trans ?_
      split
      · rename_i before
        have := UInt64.lt_iff_toNat_lt.mp before
        have xm := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps toM.chainSteps)
        simp only [ix]
        rw [ite_eq_left (by omega), Nat.add_sub_cancel' xm]
      · exact Nat.zero_le _)
    (ix x y + 1) (fun step member => steps_before_end tail step member) replayed
  rw [list_range_sum, sum_range_ite_lt_fn (fun t => pen ((getCurrentEpoch x.state).toNat + t))
    (ix x y) (ix x y + 1), Nat.min_eq_right (Nat.le_succ _)] at total
  rw [sum_Ico_offsets]
  simpa [ix] using total

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
  simpa using Run.passDebit_le_rates tail early altair high endEpoch inside (fun _ => pen) rate
    replayed

/-- The sync debit of one key in one event. -/
private def syncDebit (v : ℕ) (event : BalanceEvent preset) : ℕ :=
  if event.source = .sync then actualBalanceAt event.before v - actualBalanceAt event.after v else 0

/-- The balance of a key that stays unslashed falls over a branch only by its debits.

It starts from the smaller of its balance and its largest effective balance.

A sweep of its excess and a switch to compounding leave at least that much.

The debits are its passes, its sync penalties and its partial withdrawals.

The passes are at most its pass rates at the epochs ended.

The guards are those of the per-key floor of the a priori bound, `FloorTrace.run_of_le_cap`. -/
private theorem Run.balanceFloor_rates {g x y : ForkedBeaconState preset}
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
    (pen : ℕ → ℕ)
    (rate : ∀ {z : ForkedBeaconState preset} (pre : Run config checks x z)
      (post : Run config checks z y), tail = pre.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch y.state).toNat →
      passPenaltyRate config z v.toNat ≤ pen (getCurrentEpoch z.state).toNat)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    min (actualBalanceAt x v.toNat) (withdrawalMaxEffectiveBalance preset x.fork val).toNat ≤
      actualBalanceAt y v.toNat +
        ∑ t ∈ Finset.Ico (getCurrentEpoch x.state).toNat (getCurrentEpoch y.state).toNat, pen t +
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
  have passes := Run.passDebit_le_rates tail early altair high endEpoch inside pen rate replayed
  have split : (events.map (floorPenaltyDebit v.toNat)).sum =
      (events.map (penaltyDebit v.toNat)).sum + (events.map (syncDebit v.toNat)).sum := by
    rw [← List.sum_map_add]
    rfl
  rw [balance, debt, split] at floor
  omega

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
  have rates := Run.balanceFloor_rates shared tail genesis caps delay early altair high endEpoch v
    val initial unslashed activated quotient positive guards stays (fun _ => pen) rate replayed
  simpa using rates

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

/-- The preset facts that the producer of the pin needs.

Each field is a fact about the preset alone, and a deployed preset has it. -/
private structure PinPresetFacts (preset : Preset) : Prop where
  /-- (preset fact) One epoch's base reward factor at an increment is at least `2 ^ 33`. -/
  room : 2 ^ 33 ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat
  /-- (preset fact) The downward band is below an increment. -/
  below : preset.downwardBand < preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  /-- (preset fact) An increment is at least 900 times the slashings vector. -/
  rounding : 900 * preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat

/-- The mainnet preset has the preset facts of the pin. -/
private theorem PinPresetFacts.mainnet : PinPresetFacts Preset.mainnet :=
  ⟨by decide, by decide, by decide⟩

/-- The minimal preset has the preset facts of the pin. -/
private theorem PinPresetFacts.minimal : PinPresetFacts Preset.minimal :=
  ⟨by decide, by decide, by decide⟩

/-- From Electra and before Gloas, the floor of the window at its start leaves room for the window.

The guard asks that twice the last ceiling be at most three times the last floor.

The ceiling is at least an increment, and the floor falls with the epoch of the window.

So the first floor is at least two thirds of an increment.

The window is shorter than the slashings vector, and an increment is at least 900 vectors. -/
private theorem room_of_guard {g x : ForkedBeaconState preset} {high : ℕ}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (aligned : MaxEffectiveBalancesAligned preset)
    (xEarly : x.fork < .glamsterdam)
    (electra : .pectra ≤ x.fork) (guard : aprioriGuardAt config x high)
    (facts : PinPresetFacts preset) :
    600 * (high + 2 - (getCurrentEpoch x.state).toNat) ≤ stakeFloorAt config x high 0 := by
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  have zero : preElectraEpochs config x high = 0 := by simp [preElectraEpochs, notBefore]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, window, -, ratioGuard, -⟩ := id guard
  rw [zero] at ratioGuard
  have ratio := ratioGuard (high + 1 - (getCurrentEpoch x.state).toNat) (Nat.zero_le _)
    (by unfold driftHorizon; omega)
  have unit := (ceiling_unit_of_guard shared genesis aligned xEarly electra guard).trans
    (stakeCeilingAt_mono electra (Nat.zero_le (high + 1 - (getCurrentEpoch x.state).toNat)))
  have anti := stakeFloorAt_anti (config := config) (x := x) (high := high)
    (Nat.zero_le (high + 1 - (getCurrentEpoch x.state).toNat))
  have rounding := facts.rounding
  simp only [stakeCeilingAt, stakeFloorAt, zero] at unit anti ratio ⊢
  unfold driftHorizon at window
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
