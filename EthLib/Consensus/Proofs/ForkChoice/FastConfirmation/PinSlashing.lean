module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Whistleblower
import EthLib.Consensus.Proofs.DirectSafety.BalanceSources
import EthLib.Consensus.Proofs.Mutators
import EthLib.Consensus.Proofs.Transition.SlashedPersistence
import EthLib.Consensus.Proofs.Transition.Trace

/-!
# The slashing credits and the exit of a slashing

A slashing credits the proposer and the whistleblower, and the credits are bounded.

One slashing credits them together at most the slashed key's effective balance over the quotient.

Along a run from Electra, each key is slashed at most once.

So the slashing credits are at most the sum over the newly slashed keys.

Each key adds its largest effective balance on the run over the quotient.

A slashing of a key that has not started to exit starts its exit through the exit churn.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network.PinSplit

open Base Uint64 Models DirectSafety

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- The credit of key `i` in one replayed event. -/
def keyCredit (i : ℕ) (e : BalanceEvent preset) : ℕ :=
  actualBalanceAt e.after i - actualBalanceAt e.before i

/-- One slashing credits at most the slashed key's effective balance over the quotient.

The credits go to the proposer and the whistleblower together. -/
theorem slashValidator_credits_le {state after : BeaconState preset fork}
    (electra : .pectra ≤ fork) {slashed : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (computed : slashValidator config state slashed whistleblower = .ok after) :
    ∑ i ∈ Finset.range after.balances.data.size,
        (((after.balances.data[i]?).map (·.toNat)).getD 0 -
          ((state.balances.data[i]?).map (·.toNat)).getD 0) ≤
      balanceAt state slashed.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := by
  have _ := electra
  obtain ⟨exited, -, -, -, -, -, -, -, -, -, -, -, exitedOk, -⟩ := slashValidator_ok computed
  obtain ⟨v, found, -⟩ := initiateValidatorExit_ok exitedOk
  have bound := (initial_slashing_bounds state after slashed whistleblower v found computed).2
  have effective : balanceAt state slashed.toNat = v.effectiveBalance.toNat := by
    simp [balanceAt, getValidator_eq_ok_iff.mp found]
  rw [effective]
  exact bound

/-- A slashing of a key that has not started to exit starts its exit through the exit queue.

The exit epoch of the key is then not the far future, since the delay is positive. -/
theorem slashValidator_exit_churn {state after : BeaconState preset fork}
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
theorem Run.slashed_once {g x y : ForkedBeaconState preset}
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

end EthLib.Consensus.Models.Network.PinSplit
