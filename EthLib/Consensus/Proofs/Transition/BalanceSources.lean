module

public import EthLib.Consensus.Proofs.Transition.BalanceDrift
public import EthLib.Consensus.Proofs.Transition.EpochUpdates

/-!
# Bounds for the sources of balance drift

These contracts use the amounts computed by the transition, not arbitrary accounting caps.

Epoch-interval bounds sum the per-call amounts, including queues inherited at the first state.

Deposits to withdrawn validators bypass the Electra churn and are accounted separately.

Consolidations count both their debit and credit even though their net balance change is zero.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

def sumAmounts (values : Array Gwei) : Nat := (values.toList.map (·.toNat)).sum

def totalBalance {fork : Fork} (s : BeaconState preset fork) : Nat := sumAmounts s.balances.data

/-- Positive changes are summed per index, so a transfer cannot cancel a loss elsewhere. -/
def balanceCredits {fork : Fork} (s t : BeaconState preset fork) : Nat :=
  ∑ i ∈ Finset.range t.balances.data.size,
    (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i)

def balanceDebits {fork : Fork} (s t : BeaconState preset fork) : Nat :=
  ∑ i ∈ Finset.range s.balances.data.size,
    (actualBalanceAt ⟨fork, s⟩ i - actualBalanceAt ⟨fork, t⟩ i)

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

/-- Sum only due penalties, with the fork's actual rounding and adjusted slashing balance. -/
def delayedSlashingLimit {fork : Fork} (s : BeaconState preset fork) :
    Except TransitionError Nat := do
  let total ← liftAccessor (getTotalActiveBalance s)
  let slashed ← slashingsSum s
  let adjusted := min (slashed.toNat *
    (EthLib.Consensus.parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat) total.toNat
  let increment := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  return (s.validators.data.toList.map fun v =>
    if SlashingPenaltyDue preset (getCurrentEpoch s) v then
      if .pectra ≤ fork then
        adjusted / (total.toNat / increment) * (v.effectiveBalance.toNat / increment)
      else v.effectiveBalance.toNat / increment * adjusted / total.toNat * increment
    else 0).sum

/-- No penalty is charged merely because a validator has effective stake. -/
theorem delayed_slashing_bounds {fork : Fork} (s t : BeaconState preset fork)
    (within : s.RegistryWithinLimit)
    (ok : processSlashings s = .ok t) :
    ∃ limit, delayedSlashingLimit s = .ok limit ∧
      balanceCredits s t = 0 ∧ balanceDebits s t ≤ limit := by
  sorry

theorem delayed_slashing_limit_zero {fork : Fork} (s : BeaconState preset fork)
    (noneDue : ∀ v ∈ s.validators.data.toList,
      ¬ SlashingPenaltyDue preset (getCurrentEpoch s) v)
    (limit : Nat) (computed : delayedSlashingLimit s = .ok limit) : limit = 0 := by
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

/-- Deposits retained or postponed by the real pass are not charged in this interval. -/
def consumedDeposits {fork : Fork} (s t : BeaconState preset fork) (electra : .pectra ≤ fork) :
    Nat :=
  ((s.pendingDeposits electra).data.toList.map fun d => d.amount.toNat).sum -
    ((t.pendingDeposits electra).data.toList.map fun d => d.amount.toNat).sum

/-- This covers top-ups and withdrawn-key exceptions without charging an unprocessed queue. -/
theorem pending_deposit_bound {fork : Fork} (s t : BeaconState preset fork)
    (electra : .pectra ≤ fork)
    (ok : processPendingDeposits config checks s electra = .ok t) :
    balanceDebits s t = 0 ∧ balanceCredits s t ≤ consumedDeposits s t electra := by
  sorry

/-- The real pass removes a prefix; slashed entries are dropped without a transfer. -/
def consumedConsolidations {fork : Fork} (s t : BeaconState preset fork)
    (electra : .pectra ≤ fork) : Nat :=
  (((s.pendingConsolidations electra).data.toList.take
    ((s.pendingConsolidations electra).data.size - (t.pendingConsolidations electra).data.size)).map
      fun c => match s.validators.data[c.sourceIndex.toNat]? with
        | none => 0
        | some v => if v.slashed then 0 else v.effectiveBalance.toNat).sum

/-- Consolidations cannot mint balance, but a target can gain all the source's moved balance. -/
theorem consolidation_transfer_bound {fork : Fork} (s t : BeaconState preset fork)
    (electra : .pectra ≤ fork) (ok : processPendingConsolidations s electra = .ok t) :
    totalBalance t = totalBalance s ∧
    balanceCredits s t ≤ consumedConsolidations s t electra ∧
    balanceDebits s t ≤ consumedConsolidations s t electra := by
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
    (∑ i ∈ Finset.range t.balances.data.size,
      (actualBalanceAt ⟨.pectra, t⟩ i - actualBalanceAt ⟨.dencun, s⟩ i)) = 0 ∧
    (∑ i ∈ Finset.range s.balances.data.size,
      (actualBalanceAt ⟨.dencun, s⟩ i - actualBalanceAt ⟨.pectra, t⟩ i)) ≤
      ((t.pendingDeposits (by decide)).data.toList.map fun d => d.amount.toNat).sum := by
  sorry

end EthLib.Consensus
