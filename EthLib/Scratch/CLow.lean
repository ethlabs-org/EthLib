module

import all EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound
import all EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinSum

namespace EthLib.Consensus.Models.Network
namespace PinSum

open Base Uint64 Models DirectSafety DirectSafety.Apriori DirectSafety.Apriori.Internal

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
variable {g : ForkedBeaconState preset} {split fin pulled anc counted : BeaconState preset fork}
  {V : Finset ValidatorIndex}

/-- A key of `K5` with a charge on the run has its first counted charge as its `exitQ`. -/
private theorem exitQ_eq_charge (early : fork < .glamsterdam) {x : ForkedBeaconState preset}
    (tail : Run config checks x ⟨fork, counted⟩) {v : ValidatorIndex} (member : v ∈ K5 counted V)
    (charged : ∃ c ∈ tail.departureCharges, c.index = v.toNat) :
    ∃ c ∈ tail.departureCharges, c.index = v.toNat ∧ exitQ tail v.toNat = c.amount := by
  obtain ⟨c, mem, idx⟩ := charged
  have le := charge_epoch_le_of_K5 early tail member c mem idx
  refine ⟨c, mem, idx, ?_⟩
  cases found : tail.departureCharges.find? fun c =>
      c.index == v.toNat && decide (c.epoch ≤ (getCurrentEpoch counted).toNat) with
  | none =>
    have := List.find?_eq_none.mp found c mem
    simp [idx, le] at this
  | some d =>
    have both := List.find?_some found
    simp only [Bool.and_eq_true, beq_iff_eq] at both
    have same := charge_unique tail (List.mem_of_find?_eq_some found) mem (both.1.trans idx.symm)
    simp [exitQ, found, same]

/-- The penalties of one key in one step fit a rate read at the start of the step. -/
private theorem step_passDebit_le {m n : ForkedBeaconState preset} (step : Step config checks m n)
    (early : n.fork < .glamsterdam) (altair : .altair ≤ m.fork) (high : ℕ)
    (endEpoch : (getCurrentEpoch n.state).toNat ≤ high + 1)
    (startEpoch : (getCurrentEpoch m.state).toNat ≤ high + 1) {v : ℕ}
    (inside : v < m.state.validators.data.size) (pen : ℕ)
    (rate : (getCurrentEpoch m.state).toNat < (getCurrentEpoch n.state).toNat →
      (∃ total, getTotalActiveBalance m.state = .ok total) → passPenaltyRate config m v ≤ pen)
    {evs : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok evs) :
    (evs.map (penaltyDebit v)).sum ≤ pen := by
  have run : (Run.nil.snoc step : Run config checks m n).balanceEvents high = .ok evs := by
    simp [Run.balanceEvents, startEpoch, replayed, bind, Except.bind, pure, Except.pure]
  have bound := segment_passDebit_le_guarded (Run.nil.snoc step : Run config checks m n) early
    altair high endEpoch
    (fun {u w} step' member => by
      cases member with
      | last => rfl
      | earlier inner _ => cases inner)
    inside pen
    (fun {z} pre ok split before total => by
      injection split with middle _ _ _
      subst middle
      exact rate before total) run
  refine bound.trans ?_
  split <;> simp

/-- A rate that is linear in an aligned effective balance bounds the two terms of a leak. -/
private theorem leak_linear (inc pi score depth bias quotient : ℕ) (incPos : 0 < inc) :
    ∃ ρn ρd : ℕ, 0 < ρd ∧ ∀ eb : ℕ, inc ∣ eb →
      2 * (eb / inc * pi) + eb * (score + depth * bias) / (bias * quotient) ≤ ρn * eb / ρd := by
  by_cases zero : bias * quotient = 0
  · refine ⟨2 * pi, inc, incPos, fun eb aligned => ?_⟩
    obtain ⟨u, rfl⟩ := aligned
    simp only [zero, Nat.div_zero, Nat.add_zero]
    rw [Nat.mul_div_cancel_left _ incPos, show 2 * pi * (inc * u) = inc * (2 * pi * u) by ring,
      Nat.mul_div_cancel_left _ incPos]
    ring_nf
    exact le_refl _
  · have positive : 0 < bias * quotient := Nat.pos_of_ne_zero zero
    refine ⟨2 * pi * (bias * quotient) + (score + depth * bias) * inc, inc * (bias * quotient),
      Nat.mul_pos incPos positive, fun eb aligned => ?_⟩
    obtain ⟨u, rfl⟩ := aligned
    have lhs : 2 * (inc * u / inc * pi) + inc * u * (score + depth * bias) / (bias * quotient) =
        2 * (u * pi) + (score + depth * bias) * inc * u / (bias * quotient) := by
      rw [Nat.mul_div_cancel_left _ incPos]
      congr 2
      ring
    have rhs : (2 * pi * (bias * quotient) + (score + depth * bias) * inc) * (inc * u) /
        (inc * (bias * quotient)) =
        2 * (u * pi) + (score + depth * bias) * inc * u / (bias * quotient) := by
      rw [show (2 * pi * (bias * quotient) + (score + depth * bias) * inc) * (inc * u) =
        inc * ((bias * quotient) * (2 * (u * pi)) + (score + depth * bias) * inc * u) by ring,
        Nat.mul_div_mul_left _ _ incPos, Nat.mul_add_div positive]
    rw [lhs, rhs]

end PinSum
end EthLib.Consensus.Models.Network
