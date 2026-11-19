import all EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound
import all EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinSum

namespace EthLib.Consensus.Models.Network
namespace PinSum

open Base Uint64 Models DirectSafety PinSplit

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- A sum over keys of the sums of a list adds in either order. -/
private theorem sum_list_comm (S : Finset ValidatorIndex) (L : List (BalanceEvent preset))
    (f : ℕ → BalanceEvent preset → ℕ) :
    ∑ v ∈ S, (L.map (f v.toNat)).sum = (L.map fun e => ∑ v ∈ S, f v.toNat e).sum := by
  induction L with
  | nil => simp
  | cons e rest ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

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
          rw [sum_list_comm S _ keyCredit, ← ite]
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

end PinSum
end EthLib.Consensus.Models.Network
