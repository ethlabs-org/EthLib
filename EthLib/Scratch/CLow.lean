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
      (∃ total perIncrement, getTotalActiveBalance m.state = .ok total ∧
        getBaseRewardPerIncrement preset total = .ok perIncrement) →
      passPenaltyRate config m v ≤ pen)
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


/-- The pass premise of the potential floor, from a rate that is linear in aligned balances. -/
private theorem pass_of_leak (h : Setting config checks g split fin pulled anc counted V)
    {e : BeaconState preset fork} (whole : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    (i : ValidatorIndex) (initial : ∃ val, fin.validators.data[i.toNat]? = some val)
    (ρn ρd : ℕ)
    (leaky : ∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
      (pinTerms config pulled anc fin).leakAt eb i.toNat ≤ ρn * eb / ρd) :
    ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, e⟩),
      (before.snoc step).append after = whole → ∀ evs, step.balanceEvents = .ok evs →
      (evs.map (penaltyDebit i.toNat)).sum ≤ ρn * effectiveAt m i.toNat / ρd := by
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨val, initial⟩ := initial
  have altair : .altair ≤ fork := Nat.le_trans (by decide) h.fulu
  intro m n pre step post cut evs ok
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
  have inside : i.toNat < ms.validators.data.size :=
    Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp initial).1 mSize
  refine step_passDebit_le step nEarly altair (getCurrentEpoch pulled).toNat endE startE inside
    (ρn * effectiveAt ⟨mf, ms⟩ i.toNat / ρd) (fun _ total => ?_) ok
  obtain ⟨T, perIncrement, totalOk, perOk⟩ := total
  obtain ⟨pq, pqOk⟩ :=
    quarter_base_ok h.facts perOk ((getTotalActiveBalance pulled).toOption.getD 0)
  have rate := passRate_le_leakAt h pre startE totalOk pqOk i.toNat
  exact rate.trans (leaky _ (Nat.dvd_of_mod_eq_zero
    (effective_aligned (shared.append pre) h.genesis h.aligned i.toNat)))

/-- The floor of the potential, in naturals: the closed form less the shortfall and the debits. -/
private def potentialFloor (ρn ρd K X c cost : ℕ) : ℕ :=
  (ρd - ρn * K) * (X + c) / ρd - (c + cost)

/-- The queued partials of the key at the finalized state that are due by the call's cutoff are
at most the key's `partialsDue`. -/
private theorem partials_le_due (electra : .pectra ≤ fork) (v : ValidatorIndex) :
    ((((fin.pendingPartialWithdrawals electra).data.toList.filter
        fun entry => decide (entry.validatorIndex = v)).filter
          (fun entry => entry.withdrawableEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1)).map
            (·.amount.toNat)).sum ≤
      (pinTerms config pulled anc fin).partialsDue v.toNat := by
  refine le_trans ?_ (le_max_left (_ : ℕ) _)
  dsimp only
  simp only [electra, ↓reduceDIte, List.filter_filter]
  refine le_of_eq ?_
  congr 3
  funext entry
  simp [Bool.decide_and, UInt64.toNat_inj, Bool.and_comm]

/-- The effective balance of a key at a state of the run from the finalized state, before its exit.

It is at least the least of its effective balance and cap at the finalized state, and the floor of
its potential rounded down to an increment.

The floor loses the shortfall of the balance below the stored effective balance, and the debits.

The debits are the sync debits of the run and the partials due, in `cost`. -/
private theorem exitQ_at (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    {sd : ForkedBeaconState preset} (pre : Run config checks ⟨fork, fin⟩ sd)
    (post : Run config checks sd ⟨fork, counted⟩)
    (cut : pre.append post = fromFin.append tailC)
    (v : ValidatorIndex) (member : v ∈ K5 counted V) (val : Validator)
    (initial : fin.validators.data[v.toNat]? = some val)
    (far : ∀ w, sd.state.validators.data[v.toNat]? = some w → w.exitEpoch = FAR_FUTURE_EPOCH)
    (ρn ρd : ℕ)
    (leaky : ∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
      (pinTerms config pulled anc fin).leakAt eb v.toNat ≤ ρn * eb / ρd) :
    min (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
        (min (withdrawalMaxEffectiveBalance preset fork val).toNat
          (potentialFloor ρn ρd ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
              (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
                (withdrawalMaxEffectiveBalance preset fork val).toNat)
              (preset.downwardBand + (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
                actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat))
              ((events.map (syncDebit v.toNat)).sum +
                (pinTerms config pulled anc fin).partialsDue v.toNat) -
            potentialFloor ρn ρd ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
              (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
                (withdrawalMaxEffectiveBalance preset fork val).toNat)
              (preset.downwardBand + (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
                actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat))
              ((events.map (syncDebit v.toNat)).sum +
                (pinTerms config pulled anc fin).partialsDue v.toNat) %
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
      effectiveAt sd v.toNat := by
  obtain ⟨fromFin'⟩ := h.fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have cleanC := K5_unslashed member
  have finSplit := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin'.chainSteps)
  have called := UInt64.le_iff_toNat_le.mp h.called
  have shallow := h.shallow
  have nearC := h.near
  obtain ⟨sf, se⟩ := sd
  have same : fork = sf := (Fork.ctorIdx_injective
    (Nat.le_antisymm (fork_le_of_chainSteps post.chainSteps) (fork_le_of_chainSteps pre.chainSteps))).symm
  subst same
  have toCounted := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
  simp only at toCounted finSplit called
  have near : (getCurrentEpoch se).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by omega
  obtain ⟨before, beforeOk, isPrefix⟩ := Run.balanceEvents_prefix pre post
    (getCurrentEpoch pulled).toNat events (by rw [cut]; exact replayed)
  have clean : ∀ w, se.validators.data[v.toNat]? = some w → w.slashed = false := by
    intro w found
    cases flag : w.slashed with
    | false => rfl
    | true =>
      obtain ⟨last, located, marked⟩ := post.slashedPersistence v.toNat w found flag
      have := cleanC last located
      simp [this] at marked
  have retained : ∀ {m n : ForkedBeaconState preset} (b : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (a : Run config checks n ⟨fork, se⟩),
      (b.snoc step).append a = pre → ∀ w, n.state.validators.data[v.toNat]? = some w →
      (getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat := by
    intro m n b step a cut' w found
    obtain ⟨last, located, kept⟩ := a.registryLifecycle.validators v.toNat w found
    by_cases e : w.exitEpoch = FAR_FUTURE_EPOCH
    · rw [e]
      exact getCurrentEpoch_succ_lt_farFuture h.twoSlots pulled
    · exact absurd ((kept.exitEpoch e).symm.trans (far last located)) e
  have syncLe : (before.map (syncDebit v.toNat)).sum ≤ (events.map (syncDebit v.toNat)).sum :=
    (isPrefix.sublist.map (syncDebit v.toNat)).sum_le_sum fun _ _ => Nat.zero_le _
  have partialLe : (before.map (floorPartialDebit v)).sum ≤
      (pinTerms config pulled anc fin).partialsDue v.toNat :=
    (Run.partialDebit_le pre electra h.early (getCurrentEpoch pulled).toNat
      ((getCurrentEpoch pulled).toNat + 1) near (by omega) v beforeOk).trans
      (partials_le_due electra v)
  have final := cfloor_endpoint h se pre near beforeOk v val initial clean retained
    (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
      actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat) ρn ρd
    (potentialFloor ρn ρd ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
      (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
        (withdrawalMaxEffectiveBalance preset fork val).toNat)
      (preset.downwardBand + (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
        actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat))
      ((before.map (syncDebit v.toNat)).sum + (before.map (floorPartialDebit v)).sum))
    (by omega)
    (pass_of_leak h pre near v ⟨val, initial⟩ ρn ρd leaky)
    (fun a D k hk hD closed => by
      have mono : ρd - ρn * ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat) ≤
          ρd - ρn * k :=
        Nat.sub_le_sub_left (Nat.mul_le_mul_left _ (hk.trans (Nat.sub_le_sub_right toCounted _))) _
      have step2 := (Nat.mul_le_mul_right _ mono).trans closed
      have step3 := Nat.div_le_of_le_mul step2
      unfold potentialFloor
      omega)
    pre Run.nil rfl
  refine le_trans (min_le_min le_rfl (min_le_min le_rfl (rounded_mono _ ?_))) final
  unfold potentialFloor
  omega

/-- The key's effective balance at its exit call, from the potential floor of the run to the call.

The key is in `K5`, activated at the finalized state, and charged on the run from the split. -/
private theorem exitQ_potential (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex) (member : v ∈ K5 counted V) (val : Validator)
    (initial : fin.validators.data[v.toNat]? = some val)
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v.toNat)
    (ρn ρd : ℕ)
    (leaky : ∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
      (pinTerms config pulled anc fin).leakAt eb v.toNat ≤ ρn * eb / ρd) :
    min (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
        (min (withdrawalMaxEffectiveBalance preset fork val).toNat
          (potentialFloor ρn ρd ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
              (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
                (withdrawalMaxEffectiveBalance preset fork val).toNat)
              (preset.downwardBand + (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
                actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat))
              ((events.map (syncDebit v.toNat)).sum +
                (pinTerms config pulled anc fin).partialsDue v.toNat) -
            potentialFloor ρn ρd ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
              (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
                (withdrawalMaxEffectiveBalance preset fork val).toNat)
              (preset.downwardBand + (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
                actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat))
              ((events.map (syncDebit v.toNat)).sum +
                (pinTerms config pulled anc fin).partialsDue v.toNat) %
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
      exitQ tailC v.toNat := by
  classical
  obtain ⟨c0, member0, index0, amount0⟩ := exitQ_eq_charge h.early tailC member charged
  have inTail : c0 ∈ (fromFin.append tailC).departureCharges := by
    rw [Run.departureCharges_append]
    exact List.mem_append_right _ member0
  obtain ⟨stop⟩ := Stop.exists (fromFin.append tailC) v.toNat
  obtain ⟨c, chosen⟩ : ∃ c, stop.charge = some c := by
    cases hc : stop.charge with
    | none =>
      have selected := stop.selected
      rw [hc] at selected
      exact absurd index0 (selected.2 c0 inTail)
    | some c => exact ⟨c, rfl⟩
  have selected := stop.selected
  rw [chosen] at selected
  have cEq : c = c0 := charge_unique _ selected.1 inTail (selected.2.1.trans index0.symm)
  subst cEq
  obtain ⟨-, -, amount, next, assignedStep, rest, split', charged', vv, w, atStop, atNext,
    unset, assigned, epoch⟩ := selected
  have far : ∀ w', stop.state.state.validators.data[v.toNat]? = some w' →
      w'.exitEpoch = FAR_FUTURE_EPOCH := by
    intro w' found
    have same := Option.some.inj (found.symm.trans atStop)
    subst same
    exact unset
  rw [amount0, amount]
  exact exitQ_at h fromFin tailC replayed stop.pre stop.post stop.split v member val initial far
    ρn ρd leaky

/-- The leak of an aligned effective balance is at most a rate times it. -/
private theorem leak_rate (config : Config) (pulled anc fin : BeaconState preset fork)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (v : ℕ) :
    ∃ ρn ρd : ℕ, 0 < ρd ∧ ∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
      (pinTerms config pulled anc fin).leakAt eb v ≤ ρn * eb / ρd := by
  obtain ⟨ρn, ρd, positive, bound⟩ := leak_linear preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    ((getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat
    (if altair : .altair ≤ fork then
      (((fin.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0)
    ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)
    config.INACTIVITY_SCORE_BIAS.toNat
    (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat incPos
  exact ⟨ρn, ρd, positive, fun eb aligned => bound eb aligned⟩

end PinSum
end EthLib.Consensus.Models.Network
