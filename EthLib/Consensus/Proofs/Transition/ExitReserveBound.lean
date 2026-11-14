module

public import EthLib.Consensus.Proofs.Transition.ExitReserve
public import EthLib.Consensus.Proofs.Models.Stake

/-!
# Exit reserves over transition runs

The reserve bounds stake leaving the active set within two epochs.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}

/-- The validators that are active in the epoch of a state. -/
def activeVoters (state : BeaconState preset fork) : Finset ValidatorIndex :=
  (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset

namespace Models.Network

/-- The stake that can leave the active set of a source of balances within two epochs.

The first term is the stake already scheduled to exit by two epochs after the source's epoch.

The second is what exits charged during the source's epoch can still add by then.

Those charges read the source's effective balances, so the churn of the source bounds them.

From Electra the exit and consolidation queues each add their churn and their churn left over.

Each also adds one maximum effective balance, for an exit that carries churn from earlier epochs.

Before Electra the exit queue counts validators, so it adds a churn of maximum balances.

A churn read that fails adds nothing, since a charge that reads it then fails too. -/
def exitReserve (config : Config) (source : BeaconState preset fork) : ℕ :=
  stake (fun v => balanceAt source v.toNat)
      {v ∈ activeVoters source | (source.validators.data[v.toNat]?).any fun validator =>
        validator.exitEpoch.toNat ≤ (getCurrentEpoch source).toNat + 2} +
    if electra : .pectra ≤ fork then
      ((exitChurnLimit config source).toOption.getD 0).toNat +
        (source.exitBalanceToConsume electra).toNat +
        ((getConsolidationChurnLimit config source).toOption.getD 0).toNat +
        (source.consolidationBalanceToConsume electra).toNat +
        2 * preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
    else max 1 (getValidatorChurnLimit config source).toNat * preset.MAX_EFFECTIVE_BALANCE.toNat

/-- The stake that is inactive at a queried epoch of a later state fits the reserve of the source.

The epoch is no earlier than the epoch of the later state, and within two epochs of the source.

The later state need not be at that epoch: its registry at the epoch is read as it is. -/
theorem exitStake_le_exitReserve_epoch {g y : ForkedBeaconState preset}
    {source : BeaconState preset fork}
    (genesis : Genesis (config := config) (checks := checks) g)
    (shared : Run config checks g ⟨fork, source⟩)
    (tail : Run config checks ⟨fork, source⟩ y)
    (lookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (preGloas : y.fork < .glamsterdam) {epoch : Epoch}
    (later : getCurrentEpoch y.state ≤ epoch)
    (near : epoch.toNat ≤ (getCurrentEpoch source).toNat + 2) :
    stake (fun v => balanceAt source v.toNat)
        {v ∈ activeVoters source | isActiveAt y.state epoch v.toNat = false} ≤
      exitReserve config source := by
  have bound := ExitChurn.departing_stake_le_epoch genesis shared tail lookahead preGloas later
    near
  unfold ExitChurn.activeSet ExitChurn.scheduled at bound
  unfold exitReserve activeVoters
  exact bound

end Models.Network

end EthLib.Consensus
