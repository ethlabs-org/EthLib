module

import all EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound
import all EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinSum

namespace EthLib.Consensus.Models.Network
namespace PinSum

open Base Uint64 Models DirectSafety PinSplit

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- The whistleblower credits of a set of keys over a run are at most a bound on the slashing
events that the run replays, when each slashing event credits the set within its bound. -/
private theorem whistC_sum_le (S : Finset ValidatorIndex) (high : ℕ)
    (T : BalanceEvent preset → ℕ) {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (each : ∀ e ∈ events, e.source = .slashings → ∑ v ∈ S, keyCredit v.toNat e ≤ T e) :
    ∑ v ∈ S, whistC tail high v.toNat ≤
      (events.map fun e => if e.source = .slashings then T e else 0).sum := by
  induction tail generalizing events with
  | nil =>
    simp only [Run.balanceEvents, pure, Except.pure, Except.ok.injEq] at replayed
    subst replayed
    simp [whistC, creditScan_nil_fst]
  | @snoc middle last pre step ih =>
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    by_cases selected : (getCurrentEpoch middle.state).toNat ≤ high + 1
    · simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
      obtain ⟨added, addedOk, rfl⟩ := rest
      have previous := ih priorOk fun e member => each e (List.mem_append_left _ member)
      have step_le : ∑ v ∈ S, stepCredit (fun s => decide (s = .slashings)) (fun _ => false)
          v.toNat step ≤ (added.map fun e => if e.source = .slashings then T e else 0).sum := by
        cases step with
        | slot ok =>
          simp only [stepCredit, addedOk, Except.toOption, Option.getD_some, sum_filter_none]
          simp
        | block engine signed due ok =>
          simp only [stepCredit, addedOk, Except.toOption, Option.getD_some]
          have ite : ((added.filter fun x => decide (x.source = .slashings)).map T).sum =
              (added.map fun e => if e.source = .slashings then T e else 0).sum := by
            rw [List.sum_map_ite (fun e : BalanceEvent preset => e.source = .slashings) T
              (fun _ => 0)]
            simp
          have swap (L : List (BalanceEvent preset)) : ∑ v ∈ S, (L.map (keyCredit v.toNat)).sum =
              (L.map fun e => ∑ v ∈ S, keyCredit v.toNat e).sum := by
            simpa using (Multiset.sum_map_sum (m := (L : Multiset (BalanceEvent preset)))
              (s := S) (f := fun e v => keyCredit v.toNat e)).symm
          rw [swap, ← ite]
          exact List.sum_le_sum fun e member => each e
            (List.mem_append_right _ (List.mem_filter.mp member).1)
            (by simpa using (List.mem_filter.mp member).2)
      unfold whistC at previous ⊢
      simp only [creditScan_snoc_fst, selected, ↓reduceIte, Finset.sum_add_distrib,
        List.map_append, List.sum_append]
      omega
    · simp only [selected, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at rest
      obtain rfl := rest
      have previous := ih priorOk each
      unfold whistC at previous ⊢
      simp only [creditScan_snoc_fst, selected, ↓reduceIte]
      exact previous

/-- The credits of a set of distinct keys in one event are at most the credits of the event. -/
private theorem keyCredit_sum_le (S : Finset ValidatorIndex) (e : BalanceEvent preset) :
    ∑ v ∈ S, keyCredit v.toNat e ≤ e.credits := by
  classical
  rw [← Finset.sum_image (f := fun i => keyCredit i e) (s := S)
    (g := fun v : ValidatorIndex => v.toNat) fun a _ b _ same => UInt64.toNat_inj.mp same,
    ← Finset.sum_filter_add_sum_filter_not (S.image fun v : ValidatorIndex => v.toNat)
      (fun i => i < e.after.state.balances.data.size)]
  have missing : ∑ i ∈ (S.image fun v : ValidatorIndex => v.toNat).filter
      (fun i => ¬ i < e.after.state.balances.data.size), keyCredit i e = 0 :=
    Finset.sum_eq_zero fun i member => by
      have out := (Finset.mem_filter.mp member).2
      have none : actualBalanceAt e.after i = 0 := by
        simp [actualBalanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt out)]
      simp [keyCredit, none]
  rw [missing, Nat.add_zero]
  exact Finset.sum_le_sum_of_subset fun i member => Finset.mem_range.mpr
    (Finset.mem_filter.mp member).2

/-- The whistleblower credits of a set of keys over a run are at most the credit limits of its
slashing events. -/
private theorem whistC_sum_le_limits {g m y : ForkedBeaconState preset}
    (shared : Run config checks g m) (genesis : Genesis config checks g)
    (tail : Run config checks m y) (early : y.fork < .glamsterdam) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (S : Finset ValidatorIndex) :
    ∑ v ∈ S, whistC tail high v.toNat ≤
      (events.map fun e => if e.source = .slashings then e.creditLimit else 0).sum := by
  obtain ⟨found, foundOk, bounded⟩ := Run.balanceEvents_bounded shared tail genesis early high
  rw [replayed] at foundOk
  cases foundOk
  exact whistC_sum_le S high _ tail replayed fun e member _ =>
    (keyCredit_sum_le S e).trans (bounded e member).1

end PinSum
end EthLib.Consensus.Models.Network
