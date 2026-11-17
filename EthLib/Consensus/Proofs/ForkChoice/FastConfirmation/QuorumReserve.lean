module

public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Consensus.Proofs.Transition.EpochUpdates
public import EthLib.Consensus.Proofs.Transition.FfgStake

/-!
# The reserve of the quorum of a fast-confirmation call

A call of the fast confirmation rule counts the stake of honest voters in its pulled-up head state.

A later state that counts the same voters can hold a different total and different balances.

The reserve bounds by how much that changes the quorum, from the fields of the call's state alone.

This file holds only the definition, so that the bound and its consumers both read one copy.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64

variable {preset : Preset} {fork : Fork}

/-- The stake by which the quorum of the call can drift from the reference state to a later state.

The state is the pulled-up head state of the call, and the ancestor is the state of its target root.

Every term reads the state, except the queue of partial withdrawals, which the ancestor holds.

Every read is a function on natural numbers of the fields of the state.

Each equals the executable read whenever that read succeeds, as the lemmas on the reads show.

The reserve is twice the gain plus three times the loss.

```text
gain  = joining + min headroom (crossing + (recipients + debited) * upwardBand
          + debited * creditMax + transfers + depositGain)
loss  = sum of fall + creditedP * (increment + 2 * downwardBand + syncPMax) + maskBudget
```

- The gain is the rise of the total active balance over the next epoch.
  Validators that join the active set count in full.
  A validator that stays active gains at most the credit that crosses the upward band.
  Validators that receive a transfer, or that a block of the epoch debits, gain one band more.
- The loss is the fall of the stake of the active validators.
  A validator falls by its penalties and the partial withdrawals that the ancestor queue pays.
  Validators credited on the branch of the state, other than by sync rewards, add a band.
  The partial withdrawals that those credits hide add the mask budget.
- The credits and penalties of an epoch are bounds on the rewards of its end.
  Altair pays a share of the base reward for each flag, scaled by the previous-to-current ratio.
  Before Altair the three components of the attestation rewards and the inclusion reward count.
- From Electra the deposit churn and the pending consolidations that come due add transfers.
  Before Electra the deposits of a block add a gain at the largest effective balance.
-/
def quorumReserve (config : Config) (state ancestor : BeaconState preset fork) : ℕ :=
  let epoch := getCurrentEpoch state
  let inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  let slots := preset.SLOTS_PER_EPOCH.toNat
  let p := parameters preset fork
  let positions := Finset.range state.validators.data.size
  let validator (i : ℕ) := state.validators.data[i]?
  let effective (i : ℕ) := balanceAt state i
  let actual (i : ℕ) := ((state.balances.data[i]?).map (·.toNat)).getD 0
  let cap (i : ℕ) :=
    ((validator i).map fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat).getD 0
  let capMax := if .pectra ≤ fork then preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
    else preset.MAX_EFFECTIVE_BALANCE.toNat
  let current (i : ℕ) := isActiveAt state epoch i
  let upcoming (i : ℕ) := isActiveAt state (epoch + 1) i
  let before (i : ℕ) := isActiveAt state (getPreviousEpoch state) i
  let recent (i : ℕ) := before i || current i
  let slashed (i : ℕ) := ((validator i).map (·.slashed)).getD false
  let total := max inc (∑ i ∈ positions with current i, effective i)
  let root := (integerSquareroot (UInt64.ofNat total)).toNat
  let perIncrement := inc * preset.BASE_REWARD_FACTOR.toNat / root
  let base (i : ℕ) := if .altair ≤ fork then effective i / inc * perIncrement
    else effective i * preset.BASE_REWARD_FACTOR.toNat / root / BASE_REWARDS_PER_EPOCH.toNat
  let num := max 1 ((∑ i ∈ positions with before i, effective i) / inc)
  let den := max 1 (total / inc)
  let flagWeight := (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum
  let seatReward := if .altair ≤ fork then
      total / inc * perIncrement * SYNC_REWARD_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat /
        slots / preset.SYNC_COMMITTEE_SIZE.toNat
    else 0
  let seats (i : ℕ) := if altair : .altair ≤ fork then
      ((state.currentSyncCommittee altair).value.pubkeys.toList.filter fun key =>
        (validator i).any (·.pubkey == key)).length
    else 0
  let sync (i : ℕ) := seats i * seatReward
  let depositChurn :=
    if .glamsterdam ≤ fork then
      let limit := max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
        (total / config.CHURN_LIMIT_QUOTIENT_GLOAS.toNat)
      min config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS.toNat (limit - limit % inc)
    else
      let limit := max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
        (total / config.CHURN_LIMIT_QUOTIENT.toNat)
      min config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat (limit - limit % inc)
  let score (i : ℕ) := if altair : .altair ≤ fork then
      (((state.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0
  let delay := (getPreviousEpoch state).toNat - state.finalizedCheckpoint.epoch.toNat
  let inactivity (i : ℕ) := if .altair ≤ fork then
      effective i * (score i + config.INACTIVITY_SCORE_BIAS.toNat) /
        (config.INACTIVITY_SCORE_BIAS.toNat * p.INACTIVITY_PENALTY_QUOTIENT.toNat)
    else if preset.MIN_EPOCHS_TO_INACTIVITY_PENALTY.toNat < delay then
      4 * base i + effective i * delay / p.INACTIVITY_PENALTY_QUOTIENT.toNat
    else 0
  let credit (i : ℕ) :=
    (if .altair ≤ fork then base i * flagWeight * num / (WEIGHT_DENOMINATOR.toNat * den)
     else 3 * (base i * max num den / den) + base i) + slots * sync i
  let penalty (i : ℕ) :=
    (if .altair ≤ fork then base i else 3 * base i) + inactivity i + slots * sync i
  -- The proposer share of the sync rewards of a full epoch, paid per seat as in the sync step.
  let syncProposer := if .altair ≤ fork then
      slots * preset.SYNC_COMMITTEE_SIZE.toNat *
        (seatReward * PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat))
    else 0
  let proposerCredit := (∑ i ∈ positions with recent i, base i) + syncProposer
  let whistleblower := (∑ i ∈ positions with (validator i).any (fun v =>
      v.activationEpoch ≤ epoch && epoch < v.withdrawableEpoch), effective i) /
    p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  let depositCredit := if electra : .pectra ≤ fork then
      (state.depositBalanceToConsume electra).toNat + depositChurn else 0
  let due := if electra : .pectra ≤ fork then
      (state.pendingConsolidations electra).data.toList.filter fun c =>
        ((validator c.sourceIndex.toNat).map fun v =>
          v.slashed || decide (v.withdrawableEpoch ≤ epoch + 1)).getD false
    else []
  let dueStake := (due.map fun c => effective c.sourceIndex.toNat).sum
  let proposers := if .altair ≤ fork then slots else 2 * slots
  let depositRecipients := if .pectra ≤ fork then preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat
    else slots * preset.MAX_DEPOSITS.toNat
  let recipients := (if .pectra ≤ fork then depositRecipients else 0) + due.length + proposers
  let nP := state.slot.toNat - epoch.toNat * slots + 1
  let debited := ((if .shapella ≤ fork then preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat else 0) +
    (if .pectra ≤ fork then preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat else 0)) * nP
  let transfers := depositCredit + dueStake + proposerCredit + whistleblower
  let depositGain := if .pectra ≤ fork then 0 else depositRecipients * capMax
  let slashBack (i : ℕ) :=
    if slashed i then effective i / p.MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0
  let syncP (i : ℕ) := nP * sync i
  let blockDeposits := if h : fork < .hegota then
      (if .pectra ≤ fork then 0
       else min (preset.MAX_DEPOSITS.toNat * nP) (state.eth1DepositIndex h).toNat)
    else 0
  let creditedP :=
    (if proposerCredit = 0 ∧ seatReward = 0 ∧ positions.filter (slashed ·) = ∅ then 0 else nP) +
      blockDeposits
  let creditMax := positions.sup fun i => if upcoming i then credit i else 0
  let joining := ∑ i ∈ positions with current i = false ∧ upcoming i = true, effective i
  let crossing := ∑ i ∈ positions with upcoming i,
    if effective i < cap i then
      (let top := actual i + slashBack i + syncP i + credit i
       if effective i + preset.upwardBand < top then top - effective i else 0)
    else (if preset.upwardBand < credit i then credit i else 0)
  let headroom := ∑ i ∈ positions with upcoming i, (capMax - effective i)
  let gain := joining + min headroom (crossing + (recipients + debited) * preset.upwardBand +
    debited * creditMax + transfers + depositGain)
  let partials (i : ℕ) := if electra : .pectra ≤ fork then
      (((ancestor.pendingPartialWithdrawals electra).data.toList.filter fun w =>
        w.validatorIndex.toNat = i ∧ w.withdrawableEpoch ≤ epoch).map (·.amount.toNat)).sum
    else 0
  let fall (i : ℕ) :=
    let low := min (actual i - syncP i) (effective i) - (partials i + penalty i)
    if effective i ≤ low + preset.downwardBand then 0 else effective i - (low - low % inc)
  let syncPMax := positions.sup fun i => if current i then syncP i else 0
  let whistleblowerP :=
    (∑ i ∈ positions with slashed i, effective i) / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  let maskBudget := if .pectra ≤ fork then
      min (proposerCredit + whistleblowerP)
        (preset.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP.toNat *
          (capMax - preset.MIN_ACTIVATION_BALANCE.toNat))
    else 0
  let loss := (∑ i ∈ positions with current i, fall i) +
    creditedP * (inc + 2 * preset.downwardBand + syncPMax) + maskBudget
  2 * gain + 3 * loss

end EthLib.Consensus.Models.Network
