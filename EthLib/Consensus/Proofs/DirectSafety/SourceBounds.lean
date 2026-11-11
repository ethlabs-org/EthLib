module

public import EthLib.Consensus.Proofs.DirectSafety.ChurnBounds

/-!
# Bounds for the sources of balance drift

These contracts use the amounts computed by the transition, not arbitrary accounting caps.

Epoch-interval bounds sum the per-call amounts, including queues inherited at the first state.

Deposits to withdrawn validators bypass the Electra churn and are accounted separately.

Consolidations count both their debit and credit even though their net balance change is zero.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

def sumAmounts (values : Array Gwei) : Nat := (values.toList.map (·.toNat)).sum

def totalBalance {fork : Fork} (s : BeaconState preset fork) : Nat := sumAmounts s.balances.data

/-- Positive changes are summed per index, so a transfer cannot cancel a loss elsewhere. -/
def balanceCredits {fork : Fork} (s t : BeaconState preset fork) : Nat :=
  ∑ i ∈ Finset.range t.balances.data.size, (balanceAt ⟨fork, t⟩ i - balanceAt ⟨fork, s⟩ i)

def balanceDebits {fork : Fork} (s t : BeaconState preset fork) : Nat :=
  ∑ i ∈ Finset.range s.balances.data.size, (balanceAt ⟨fork, s⟩ i - balanceAt ⟨fork, t⟩ i)

/-- Rewards and ordinary penalties are kept separate from the inactivity pass. -/
def rewardPasses {fork : Fork} (s : BeaconState preset fork) :
    Except TransitionError (List (Array Gwei × Array Gwei)) := do
  if getCurrentEpoch s = GENESIS_EPOCH then return []
  if altair : .altair ≤ fork then
    (List.finRange PARTICIPATION_FLAG_WEIGHTS.length).mapM (getFlagIndexDeltas s altair)
  else
    let early := Nat.lt_of_not_le altair
    return [← getSourceDeltas s early, ← getTargetDeltas s early,
      ← getHeadDeltas s early, ← getInclusionDelayDeltas s early]

theorem epoch_rewards_penalties {fork : Fork} (s t : BeaconState preset fork)
    (ordinary : List (Array Gwei × Array Gwei)) (inactivity : Array Gwei × Array Gwei)
    (rewards : rewardPasses s = .ok ordinary)
    (leak : getInactivityPenaltyDeltas config s = .ok inactivity)
    (ok : processRewardsAndPenalties config s = .ok t) :
    balanceCredits s t ≤ (ordinary.map fun p => sumAmounts p.1).sum ∧
    balanceDebits s t ≤ (ordinary.map fun p => sumAmounts p.2).sum +
      sumAmounts inactivity.2 := by
  sorry

/-- Initial scores cannot be discarded when the interval starts during a leak. -/
theorem inactivity_score_growth (hit : Bool) (leaking : Except TransitionError Bool)
    (old next : Gwei) (ok : nextInactivityScore config hit leaking old = .ok next) :
    next.toNat ≤ old.toNat + config.INACTIVITY_SCORE_BIAS.toNat := by
  sorry

theorem inactivity_penalty_altair {fork : Fork} (s : BeaconState preset fork)
    (altair : .altair ≤ fork) (target : Array Bool) (penalties result : Array Gwei)
    (i : ValidatorIndex) (v : Validator) (score : Gwei)
    (found : getValidator s i = .ok v)
    (read : (s.inactivityScores altair).data[i.toNat]? = some score)
    (ok : addInactivityScorePenalty config s altair target penalties i = .ok result) :
    sumAmounts result ≤ sumAmounts penalties +
      v.effectiveBalance.toNat * score.toNat /
        (config.INACTIVITY_SCORE_BIAS.toNat *
          (EthLib.Consensus.parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
  sorry

theorem inactivity_penalty_phase0 {fork : Fork} (s : BeaconState preset fork)
    (total delay : Gwei) (target : Array Bool) (penalties result : Array Gwei)
    (i : ValidatorIndex) (v : Validator) (base : Gwei)
    (found : getValidator s i = .ok v) (reward : getBaseReward s total i = .ok base)
    (ok : addInactivityPenalty s total delay target penalties i = .ok result) :
    sumAmounts result ≤ sumAmounts penalties + BASE_REWARDS_PER_EPOCH.toNat * base.toNat +
      v.effectiveBalance.toNat * delay.toNat /
        (EthLib.Consensus.parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat := by
  sorry

/-- Both recipient credits are included, also when proposer and whistleblower coincide. -/
theorem initial_slashing_bounds {fork : Fork} (s t : BeaconState preset fork)
    (i : ValidatorIndex) (whistleblower : Option ValidatorIndex) (v : Validator)
    (found : getValidator s i = .ok v)
    (ok : slashValidator config s i whistleblower = .ok t) :
    balanceDebits s t ≤ v.effectiveBalance.toNat /
      (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
    balanceCredits s t ≤ v.effectiveBalance.toNat /
      (EthLib.Consensus.parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := by
  sorry

/-- The delayed penalty is capped by the effective balance, including the Electra rounding. -/
theorem delayed_slashing_bounds {fork : Fork} (s t : BeaconState preset fork)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (aligned : ∀ (v : Validator), v ∈ s.validators.data.toList →
      v.effectiveBalance.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (ok : processSlashings s = .ok t) :
    balanceCredits s t = 0 ∧
    balanceDebits s t ≤
      (s.validators.data.toList.map fun v => v.effectiveBalance.toNat).sum := by
  sorry

theorem sync_reward_bounds {fork : Fork} (s t : BeaconState preset fork)
    (reward proposerReward : Gwei) (proposer : Except AccessorError ValidatorIndex)
    (member : ValidatorIndex × Bool)
    (ok : applySyncReward reward proposerReward proposer s member = .ok t) :
    balanceCredits s t ≤ (if member.2 then reward.toNat + proposerReward.toNat else 0) ∧
    balanceDebits s t ≤ (if member.2 then 0 else reward.toNat) := by
  sorry

/-- Recompute the proposer credit from the newly set participation flags. -/
def attestationCredit {fork : Fork} (s : BeaconState preset fork)
    (att : Attestation preset fork) (parent : Slot) : Except TransitionError Nat := do
  if altair : .altair ≤ fork then
    let earned ← liftAccessor
      (getAttestationParticipationFlagIndices s att.data (s.slot - att.data.slot) parent)
    let participation := if att.data.target.epoch == getCurrentEpoch s then
        s.currentEpochParticipation altair else s.previousEpochParticipation altair
    let total ← liftAccessor (getTotalActiveBalance s)
    let attesters ← liftAccessor (getAttestingIndices s att)
    let (_, numerator) ← attesters.foldlM (addAttesterFlags s total earned) (participation, 0)
    let denominator :=
      (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR / PROPOSER_WEIGHT
    return (numerator / denominator).toNat
  else return 0

/-- Attestation proposer rewards are the checked numerator divided by the protocol denominator. -/
theorem attestation_proposer_bound {fork : Fork} (s t : BeaconState preset fork)
    (att : Attestation preset fork) (parent : Slot) (early : fork < .glamsterdam)
    (ok : processAttestation config checks s parent att = .ok t) :
    ∃ credit, attestationCredit s att parent = .ok credit ∧
      balanceDebits s t = 0 ∧ balanceCredits s t ≤ credit := by
  sorry

/-- The amount is an input, so top-ups are not silently bounded by activation churn. -/
theorem deposit_credit_bound {fork : Fork} (s t : BeaconState preset fork)
    (deposit : PendingDeposit) (ok : applyPendingDeposit config checks s deposit = .ok t) :
    balanceDebits s t = 0 ∧ balanceCredits s t ≤ deposit.amount.toNat := by
  sorry

/-- Applied pending deposits divide into churn-charged and withdrawn-key exceptions. -/
theorem pending_deposit_bound {fork : Fork} (s t : BeaconState preset fork)
    (electra : .pectra ≤ fork)
    (ok : processPendingDeposits config checks s electra = .ok t) :
    ∃ churn : Gwei, depositChurnLimit config s = .ok churn ∧
      balanceCredits s t ≤ (s.depositBalanceToConsume electra).toNat + churn.toNat +
        ((s.pendingDeposits electra).data.toList.filter fun d =>
          Option.getD ((depositTargetStatus s (getCurrentEpoch s + 1) d.pubkey).toOption.map
            Prod.snd) false).foldl (fun n d => n + d.amount.toNat) 0 := by
  sorry

/-- Consolidations cannot mint balance, but a target can gain all the source's moved balance. -/
theorem consolidation_transfer_bound {fork : Fork} (s t : BeaconState preset fork)
    (electra : .pectra ≤ fork) (ok : processPendingConsolidations s electra = .ok t) :
    totalBalance t = totalBalance s ∧
    balanceCredits s t ≤
      ((s.pendingConsolidations electra).data.toList.map fun c =>
        effectiveAt ⟨fork, s⟩ c.sourceIndex.toNat).sum ∧
    balanceDebits s t ≤
      ((s.pendingConsolidations electra).data.toList.map fun c =>
        effectiveAt ⟨fork, s⟩ c.sourceIndex.toNat).sum := by
  sorry

theorem withdrawal_debit_bound {fork : Fork} (s t : BeaconState preset fork)
    (withdrawals : Array Withdrawal) (ok : applyWithdrawals s withdrawals = .ok t) :
    balanceCredits s t = 0 ∧ balanceDebits s t ≤
      (withdrawals.toList.map fun w => w.amount.toNat).sum := by
  sorry

theorem excess_queue_debit {fork : Fork} (s t : BeaconState preset fork)
    (electra : .pectra ≤ fork) (i : ValidatorIndex) (balance : Gwei)
    (read : getBalance s i = .ok balance)
    (ok : queueExcessActiveBalance s electra i = .ok t) :
    balanceCredits s t = 0 ∧ balanceDebits s t ≤
      (balance.toNat - preset.MIN_ACTIVATION_BALANCE.toNat) := by
  sorry

/-- The crossing queues balance instead of losing it; the debit is counted before later credits. -/
theorem electra_upgrade_debit (s : BeaconState preset .dencun) (t : BeaconState preset .pectra)
    (ok : upgradeToElectra config s = .ok t) :
    totalBalance t ≤ totalBalance s ∧ totalBalance s ≤ totalBalance t +
      ((t.pendingDeposits (by decide)).data.toList.map fun d => d.amount.toNat).sum := by
  sorry

/-- Summing per-call bounds preserves source separation over any finite epoch interval. -/
theorem source_interval_sum {α : Type} (calls : List α)
    (credit debit boundCredit boundDebit : α → Nat)
    (credits : ∀ c ∈ calls, credit c ≤ boundCredit c)
    (debits : ∀ c ∈ calls, debit c ≤ boundDebit c) :
    (calls.map credit).sum ≤ (calls.map boundCredit).sum ∧
      (calls.map debit).sum ≤ (calls.map boundDebit).sum := by
  sorry

end EthLib.Consensus.DirectSafety
