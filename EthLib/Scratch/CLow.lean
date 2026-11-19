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


/-- The potential floor of a key's balance at a state of the run from the finalized state.

The balance and the debits that are no pass penalties keep a fraction of the start.

The start is the smaller of the balance and the cap at the finalized state, plus its band and the
shortfall of the balance below the stored effective balance. -/
private theorem run_state_floor (h : Setting config checks g split fin pulled anc counted V)
    {z : BeaconState preset fork} (rp : Run config checks ⟨fork, fin⟩ ⟨fork, z⟩)
    (nearZ : (getCurrentEpoch z).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    (v : ValidatorIndex) (val : Validator) (initial : fin.validators.data[v.toNat]? = some val)
    (clean : ∀ w, z.validators.data[v.toNat]? = some w → w.slashed = false)
    (far : ∀ w, z.validators.data[v.toNat]? = some w → w.exitEpoch = FAR_FUTURE_EPOCH)
    {evz : List (BalanceEvent preset)}
    (replayed : rp.balanceEvents (getCurrentEpoch pulled).toNat = .ok evz)
    (ρn ρd : ℕ)
    (leaky : ∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
      (pinTerms config pulled anc fin).leakAt eb v.toNat ≤ ρn * eb / ρd)
    (quarter : ∃ pq, getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5) = .ok pq) :
    (ρd - ρn * ((getCurrentEpoch z).toNat - (getCurrentEpoch fin).toNat)) *
        (min (actualBalanceAt ⟨fork, fin⟩ v.toNat)
            (withdrawalMaxEffectiveBalance preset fork val).toNat +
          (preset.downwardBand + (effectiveAt ⟨fork, fin⟩ v.toNat -
            actualBalanceAt ⟨fork, fin⟩ v.toNat))) ≤
      ρd * (actualBalanceAt ⟨fork, z⟩ v.toNat +
        ((evz.map (syncDebit v.toNat)).sum + (evz.map (floorPartialDebit v)).sum) +
        (preset.downwardBand + (effectiveAt ⟨fork, fin⟩ v.toNat -
          actualBalanceAt ⟨fork, fin⟩ v.toNat))) := by
  obtain ⟨shared⟩ := h.toFin
  have altair : .altair ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨positive, guards⟩ :=
    floor_guards h (Run.nil : Run config checks ⟨fork, fin⟩ ⟨fork, fin⟩) (y := z) nearZ
  have retained : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (post : Run config checks n ⟨fork, z⟩),
      (pre.snoc step).append post = rp → ∀ w, n.state.validators.data[v.toNat]? = some w →
      (getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat := by
    intro m n pre step post cut w found
    obtain ⟨last, located, kept⟩ := post.registryLifecycle.validators v.toNat w found
    by_cases e : w.exitEpoch = FAR_FUTURE_EPOCH
    · rw [e]
      exact getCurrentEpoch_succ_lt_farFuture h.twoSlots pulled
    · exact absurd ((kept.exitEpoch e).symm.trans (far last located)) e
  obtain ⟨D, split, closed⟩ := FloorTrace.run_potential_floor shared rp h.genesis h.caps h.delay
    h.early h.fulu h.bands (getCurrentEpoch pulled).toNat nearZ v val initial clean _ positive
    (fun {m n} pre step post cut w found =>
      ⟨retained pre step post cut w found, guards pre step post⟩)
    replayed (effectiveAt ⟨fork, fin⟩ v.toNat - actualBalanceAt ⟨fork, fin⟩ v.toNat) ρn ρd
    (by omega)
    (fun {m n} pre step post cut evs ok => by
      have above : fork ≤ m.fork :=
        Nat.le_trans (le_refl _) (fork_le_of_chainSteps pre.chainSteps)
      have below : m.fork ≤ fork :=
        Nat.le_trans step.chainStep.fork_le (fork_le_of_chainSteps post.chainSteps)
      have startE : (getCurrentEpoch m.state).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
        have := UInt64.le_iff_toNat_le.mp
          (currentEpoch_le_of_chainSteps ((Run.nil.snoc step).append post).chainSteps)
        simp only at this
        omega
      have endE : (getCurrentEpoch n.state).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
        have := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
        simp only at this
        omega
      have nEarly : n.fork < .glamsterdam :=
        Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early
      have mSize := registryGrows_of_chainSteps pre.chainSteps
      obtain ⟨mf, ms⟩ := m
      have same : mf = fork := Fork.ctorIdx_injective (Nat.le_antisymm below above)
      subst same
      have inside : v.toNat < ms.validators.data.size :=
        Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp initial).1 mSize
      refine step_passDebit_le step nEarly altair (getCurrentEpoch pulled).toNat endE startE inside
        (ρn * effectiveAt ⟨mf, ms⟩ v.toNat / ρd) (fun _ total => ?_) ok
      obtain ⟨T, totalOk⟩ := total
      obtain ⟨pq, pqOk⟩ := quarter
      have rate := passRate_le_leakAt h pre startE totalOk pqOk v.toNat
      exact rate.trans (leaky _ (Nat.dvd_of_mod_eq_zero
        (effective_aligned (shared.append pre) h.genesis h.aligned v.toNat))))
  have splitDebit : (evz.map (floorPenaltyDebit v.toNat)).sum =
      (evz.map (penaltyDebit v.toNat)).sum + (evz.map (syncDebit v.toNat)).sum := by
    rw [← List.sum_map_add]
    rfl
  have hD : D = (evz.map (syncDebit v.toNat)).sum + (evz.map (floorPartialDebit v)).sum := by
    omega
  rw [hD] at closed
  exact closed

end PinSum
end EthLib.Consensus.Models.Network
