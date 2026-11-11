module

public import EthLib.Consensus.Proofs.DirectSafety.BalanceBounds

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
  sorry

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
  sorry

/-- The pre-Gloas exit rate is a configuration value, not an assumed cap. -/
theorem exit_churn_from_config {fork : Fork} (s : BeaconState preset fork)
    (early : fork < .glamsterdam) (churn : Gwei) (ok : exitChurnLimit config s = .ok churn) :
    churn ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT := by
  sorry

end EthLib.Consensus.DirectSafety
