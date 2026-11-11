module

public import EthLib.Consensus.Proofs.Transition.BalanceDrift
public import EthLib.Consensus.Proofs.DirectSafety.Drift
public import EthLib.Consensus.Proofs.Churn

/-!
# Churn windows and the Electra crossing

Before Electra, activation and exit cohorts are bounded by the validator-count churn.

Electra exits spend balance churn; consolidations spend their own queue's churn.

The queues and their carry-in must be counted, not replaced by an assumed accounting cap.

The balance queues are specified by [EIP-7251].

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

def cohortCap (config : Config) (size : Nat) : Nat :=
  max config.MIN_PER_EPOCH_CHURN_LIMIT.toNat (size / config.CHURN_LIMIT_QUOTIENT.toNat)

/-- Calls that finish in an already opened epoch cannot replenish its remaining capacity.

The first eligible epoch and rate may vary between calls. -/
theorem churnQueue_same_epoch_spend {epoch : UInt64} :
    ∀ (calls : List (UInt64 × UInt64 × UInt64)) (left finalLeft : UInt64),
      calls.foldlM (fun (queue : UInt64 × UInt64) call =>
        churnQueue queue.1 call.1 call.2.1 queue.2 call.2.2) (epoch, left) =
          .ok (epoch, finalLeft) →
      finalLeft.toNat + (calls.map fun c => c.2.2.toNat).sum = left.toNat := by
  intro calls
  induction calls with
  | nil =>
    intro left finalLeft computed
    have same := congrArg Prod.snd (Except.ok.inj computed)
    simp only [List.map_nil, List.sum_nil, Nat.add_zero]
    exact congrArg UInt64.toNat same.symm
  | cons call rest ih =>
    intro left finalLeft computed
    simp only [List.foldlM_cons, Base.bind_ok_iff] at computed
    obtain ⟨⟨middle, available⟩, queued, restOk⟩ := computed
    have monotone : ∀ (xs : List (UInt64 × UInt64 × UInt64)) (a b c d : UInt64),
        xs.foldlM (fun (queue : UInt64 × UInt64) call =>
          churnQueue queue.1 call.1 call.2.1 queue.2 call.2.2) (a, b) = .ok (c, d) → a ≤ c := by
      intro xs
      induction xs with
      | nil => intro a b c d ok; cases Except.ok.inj ok; exact UInt64.le_refl _
      | cons head tail ih =>
        intro a b c d ok
        simp only [List.foldlM_cons, Base.bind_ok_iff] at ok
        obtain ⟨⟨m, n⟩, step, tailOk⟩ := ok
        have h := (churnQueue_spend step).1
        have start : a ≤ max a head.1 := by
          rw [UInt64.le_iff_toNat_le, Base.Uint64.toNat_max]
          exact Nat.le_max_left _ _
        exact UInt64.le_trans (UInt64.le_trans start h) (ih m n c d tailOk)
    obtain ⟨placed, spent, _⟩ := churnQueue_spend queued
    have start : epoch ≤ max epoch call.1 := by
      rw [UInt64.le_iff_toNat_le, Base.Uint64.toNat_max]
      exact Nat.le_max_left _ _
    have back := monotone rest middle available epoch finalLeft restOk
    have same : middle = epoch := UInt64.le_antisymm back (UInt64.le_trans start placed)
    subst middle
    have opened : max epoch call.1 = epoch := UInt64.le_antisymm placed start
    rw [opened] at spent
    simp only [UInt64.lt_irrefl, ↓reduceIte, Nat.sub_self, Nat.zero_mul, Nat.add_zero] at spent
    have restSpent := ih available finalLeft restOk
    simp only [List.map_cons, List.sum_cons]
    omega

/-- A cohort can exceed its rate because the first amount can consume earlier epochs.

After that first completion, only the remaining capacity of its epoch can be spent.

The extra maximum amount is a boundary burst, not a per-epoch charge. -/
theorem churnQueue_cohort_le
    {earliest first rate available amount epoch left finalLeft : UInt64}
    {rest : List (UInt64 × UInt64 × UInt64)} {cap largest : Nat}
    (queued : churnQueue earliest first rate available amount = .ok (epoch, left))
    (completed : rest.foldlM (fun (queue : UInt64 × UInt64) call =>
      churnQueue queue.1 call.1 call.2.1 queue.2 call.2.2) (epoch, left) = .ok (epoch, finalLeft))
    (rateBound : rate.toNat ≤ cap) (carryBound : available.toNat ≤ cap)
    (amountBound : amount.toNat ≤ largest) :
    amount.toNat + (rest.map fun c => c.2.2.toNat).sum ≤ largest + cap := by
  obtain ⟨_, spent, boundary⟩ := churnQueue_spend queued
  have remainder := churnQueue_same_epoch_spend rest left finalLeft completed
  rcases boundary with same | small
  · rw [same, Nat.sub_self, Nat.zero_mul, Nat.add_zero] at spent
    split at spent <;> omega
  · omega

/-- A newly opened cohort needs no bound on inherited queue capacity.

Its first charge plus later charges cost at most one maximum amount and the opening rate. -/
theorem churnQueue_new_cohort_le
    {earliest first rate available amount epoch left finalLeft : UInt64}
    {rest : List (UInt64 × UInt64 × UInt64)} {largest : Nat}
    (queued : churnQueue earliest first rate available amount = .ok (epoch, left))
    (completed : rest.foldlM (fun (queue : UInt64 × UInt64) call =>
      churnQueue queue.1 call.1 call.2.1 queue.2 call.2.2) (epoch, left) = .ok (epoch, finalLeft))
    (newer : earliest < epoch) (amountBound : amount.toNat ≤ largest) :
    amount.toNat + (rest.map fun c => c.2.2.toNat).sum ≤ largest + rate.toNat := by
  obtain ⟨_, spent, boundary⟩ := churnQueue_spend queued
  have remainder := churnQueue_same_epoch_spend rest left finalLeft completed
  rcases boundary with same | small
  · have reset : earliest < max earliest first := by rw [← same]; exact newer
    rw [if_pos reset, same, Nat.sub_self, Nat.zero_mul, Nat.add_zero] at spent
    omega
  · omega

/-- Variable-rate calls spend at most initial capacity plus the cap per elapsed queue epoch.

The first eligible epoch may also vary; a reset discards rather than preserves old capacity. -/
theorem churnQueue_window_le (cap : Nat) :
    ∀ (calls : List (UInt64 × UInt64 × UInt64)) (earliest available epoch left : UInt64),
      (∀ call ∈ calls, call.2.1.toNat ≤ cap) →
      calls.foldlM (fun (queue : UInt64 × UInt64) call =>
        churnQueue queue.1 call.1 call.2.1 queue.2 call.2.2) (earliest, available) =
          .ok (epoch, left) →
      earliest.toNat ≤ epoch.toNat ∧
        left.toNat + (calls.map fun c => c.2.2.toNat).sum ≤
          available.toNat + (epoch.toNat - earliest.toNat) * cap := by
  intro calls
  induction calls with
  | nil =>
    intro earliest available epoch left _ computed
    cases Except.ok.inj computed
    simp
  | cons call rest ih =>
    intro earliest available epoch left rates computed
    simp only [List.foldlM_cons, Base.bind_ok_iff] at computed
    obtain ⟨⟨middle, remaining⟩, queued, restOk⟩ := computed
    obtain ⟨placed, spent, _⟩ := churnQueue_spend queued
    have rate := rates call (by simp)
    have later := UInt64.le_iff_toNat_le.mp placed
    rw [Base.Uint64.toNat_max] at later
    have firstLe : earliest.toNat ≤ middle.toNat := le_trans (Nat.le_max_left _ _) later
    obtain ⟨lastLe, tailBound⟩ := ih middle remaining epoch left
      (fun c hc => rates c (List.mem_cons_of_mem _ hc)) restOk
    have oneBound : remaining.toNat + call.2.2.toNat ≤
        available.toNat + (middle.toNat - earliest.toNat) * cap := by
      split at spent
      · rename_i reset
        have reset := UInt64.lt_iff_toNat_lt.mp reset
        rw [Base.Uint64.toNat_max] at reset
        have distance : middle.toNat - max earliest.toNat call.1.toNat + 1 ≤
            middle.toNat - earliest.toNat := by omega
        rw [Base.Uint64.toNat_max] at spent
        have product := Nat.mul_le_mul distance rate
        rw [Nat.add_mul, Nat.one_mul] at product
        omega
      · rw [Base.Uint64.toNat_max] at spent
        have distance : middle.toNat - max earliest.toNat call.1.toNat ≤
            middle.toNat - earliest.toNat := by omega
        have product := Nat.mul_le_mul distance rate
        omega
    refine ⟨le_trans firstLe lastLe, ?_⟩
    have distance : epoch.toNat - earliest.toNat =
        (epoch.toNat - middle.toNat) + (middle.toNat - earliest.toNat) := by omega
    simp only [List.map_cons, List.sum_cons]
    rw [distance, Nat.add_mul]
    omega

/-- The charge visible when a selected transition assigns a previously unset exit epoch. -/
structure DepartureCharge where
  index : Nat
  epoch : Nat
  amount : Nat

/-- Effective balances are read before scheduling, not after the later effective-balance pass. -/
def _root_.EthLib.Consensus.Step.departureCharges {x y : ForkedBeaconState preset}
    (_step : Step config checks x y) : List DepartureCharge :=
  x.state.validators.data.toList.zipIdx.filterMap fun (v, i) =>
    match y.state.validators.data[i]? with
    | none => none
    | some next => if v.exitEpoch == FAR_FUTURE_EPOCH && next.exitEpoch != FAR_FUTURE_EPOCH then
        some ⟨i, next.exitEpoch.toNat, v.effectiveBalance.toNat⟩
      else none

def _root_.EthLib.Consensus.Run.departureCharges {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → List DepartureCharge
  | _, .nil => []
  | _, .snoc pre step => pre.departureCharges ++ step.departureCharges

/-- Reference weights of the one inherited cohort, including the initial boundary. -/
def inheritedCohort (x : ForkedBeaconState preset) (epoch : Nat) : Nat :=
  (x.state.validators.data.toList.filter fun v =>
    v.activationEpoch.toNat < epoch && v.exitEpoch.toNat == epoch).foldl
      (fun n v => n + v.effectiveBalance.toNat) 0

/-- Previous-only voting support consists exactly of the cohort exiting at the current epoch. -/
theorem previous_only_iff_exit {fork : Fork} (state : BeaconState preset fork) (v : Validator) :
    (isActiveValidator v (getPreviousEpoch state) = true ∧
      isActiveValidator v (getCurrentEpoch state) = false) ↔
    v.activationEpoch.toNat < (getCurrentEpoch state).toNat ∧
      v.exitEpoch.toNat = (getCurrentEpoch state).toNat := by
  simp only [isActiveValidator, Bool.and_eq_true, Bool.and_eq_false_iff,
    decide_eq_true_eq, decide_eq_false_iff_not, UInt64.le_iff_toNat_le,
    UInt64.lt_iff_toNat_lt, getPreviousEpoch_toNat]
  omega

/-- Positive effective-weight growth since reference or scheduling, for this boundary only. -/
def cohortGrowth {x y : ForkedBeaconState preset} (tail : Run config checks x y) : Nat :=
  (y.state.validators.data.toList.zipIdx.map fun (v, i) =>
    let epoch := (getCurrentEpoch y.state).toNat
    if v.activationEpoch.toNat < epoch && v.exitEpoch.toNat == epoch then
      let baseline := match tail.departureCharges.find? (fun c => c.index == i) with
        | some c => c.amount
        | none => effectiveAt x i
      v.effectiveBalance.toNat - baseline
    else 0).sum

/-- The boundary splits into inherited stake, newly assigned charges and growth after assignment.

Queue bounds apply to the charges, never directly to current effective balances. -/
theorem boundary_stake_le_charges {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (early : y.fork < .glamsterdam) :
    boundaryStake y ≤ inheritedCohort x (getCurrentEpoch y.state).toNat +
      ((tail.departureCharges.filter fun c => c.epoch == (getCurrentEpoch y.state).toNat).map
        (·.amount)).sum + cohortGrowth tail := by
  sorry

theorem leaving_before_electra {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset) (early : y.fork < .pectra) :
    leaving x y ≤ ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) *
      max 1 (cohortCap config y.state.validators.data.size) *
        preset.MAX_EFFECTIVE_BALANCE.toNat := by
  sorry

/-- The extra cohort covers previous-epoch voters who exited at the reference epoch. -/
theorem joining_before_electra {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset) (early : y.fork < .pectra) :
    Quorum.weight (effectiveWeight y.state) (recentKeys y.state \ activeKeys x.state) ≤
      (((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) *
        cohortCap config y.state.validators.data.size +
        max 1 (cohortCap config y.state.validators.data.size)) *
          preset.MAX_EFFECTIVE_BALANCE.toNat := by
  sorry

/-- A reachable Electra upgrade starts the exit queue after all previously scheduled exits. -/
theorem electra_crossing_queues {pre : BeaconState preset .dencun}
    {post : BeaconState preset .pectra} (ok : upgradeToElectra config pre = .ok post) :
    getCurrentEpoch post = getCurrentEpoch pre ∧
    (∀ (i : Nat) (v : Validator), pre.validators.data[i]? = some v →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH →
      v.exitEpoch < post.earliestExitEpoch (by decide)) ∧
    exitChurnLimit config post = .ok (post.exitBalanceToConsume (by decide)) ∧
    getConsolidationChurnLimit config post =
      .ok (post.consolidationBalanceToConsume (by decide)) := by
  sorry

/-- The entire crossing step includes its preceding epoch and any simultaneous upgrades. -/
theorem split_electra_crossing {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (early : x.fork < .pectra) (late : .pectra ≤ y.fork) :
    ∃ u v, ∃ head : Run config checks x u, ∃ step : Step config checks u v,
      ∃ rest : Run config checks v y,
        u.fork < .pectra ∧ .pectra ≤ v.fork ∧ (head.snoc step).append rest = tail := by
  sorry

/-- A queue charge can spend earlier epochs; an arbitrary window needs its carry-in. -/
theorem exit_queue_charge {fork : Fork} (s t : BeaconState preset fork)
    (electra : .pectra ≤ fork) (amount : Gwei) (epoch : Epoch)
    (ok : computeExitEpochAndUpdateChurn config s electra amount = .ok (t, epoch)) :
    ∃ first churn,
      computeActivationExitEpoch preset (getCurrentEpoch s) = .ok first ∧
      exitChurnLimit config s = .ok churn ∧
      amount.toNat + (t.exitBalanceToConsume electra).toNat =
        (if (s.earliestExitEpoch electra) < max (s.earliestExitEpoch electra) first
          then churn.toNat else (s.exitBalanceToConsume electra).toNat) +
        (epoch.toNat - (max (s.earliestExitEpoch electra) first).toNat) * churn.toNat := by
  simp only [computeExitEpochAndUpdateChurn, Base.bind_ok_iff, liftArith,
    Base.mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨first, firstOk, churn, churnOk, ⟨placed, left⟩, queued, result⟩ := ok
  cases result
  refine ⟨first, churn, firstOk, churnOk, ?_⟩
  have spent := (churnQueue_spend queued).2.1
  split at spent <;> rename_i branch
  all_goals simp only [branch, ↓reduceIte]; omega

theorem consolidation_queue_charge {fork : Fork} (s t : BeaconState preset fork)
    (electra : .pectra ≤ fork) (amount : Gwei) (epoch : Epoch)
    (ok : computeConsolidationEpochAndUpdateChurn config s electra amount = .ok (t, epoch)) :
    ∃ first churn,
      computeActivationExitEpoch preset (getCurrentEpoch s) = .ok first ∧
      getConsolidationChurnLimit config s = .ok churn ∧
      amount.toNat + (t.consolidationBalanceToConsume electra).toNat =
        (if (s.earliestConsolidationEpoch electra) <
            max (s.earliestConsolidationEpoch electra) first then churn.toNat
          else (s.consolidationBalanceToConsume electra).toNat) +
        (epoch.toNat - (max (s.earliestConsolidationEpoch electra) first).toNat) * churn.toNat := by
  simp only [computeConsolidationEpochAndUpdateChurn, Base.bind_ok_iff, liftArith,
    Base.mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨first, firstOk, churn, churnOk, ⟨placed, left⟩, queued, result⟩ := ok
  cases result
  refine ⟨first, churn, firstOk, churnOk, ?_⟩
  have spent := (churnQueue_spend queued).2.1
  split at spent <;> rename_i branch
  all_goals simp only [branch, ↓reduceIte]; omega

/-- The pre-Gloas exit rate is a configuration value, not an assumed cap. -/
theorem exit_churn_from_config {fork : Fork} (s : BeaconState preset fork)
    (early : fork < .glamsterdam) (churn : Gwei) (ok : exitChurnLimit config s = .ok churn) :
    churn ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [exitChurnLimit, notGloas, ↓reduceIte, getActivationExitChurnLimit,
    Base.bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨whole, _, rfl⟩ := ok
  rw [UInt64.le_iff_toNat_le, Base.Uint64.toNat_min]
  exact Nat.min_le_left _ _

end EthLib.Consensus.DirectSafety
