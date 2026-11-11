module

public import EthLib.Consensus.Proofs.DirectSafety.Attestations
public import EthLib.Base.Proofs.Quorum

/-!
# Validator identities and weights

Keys, not branch-local indices, identify the validators in the conclusion.

The reference registry counts each key once; this is proved from genesis, not assumed silently.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

def registryKeys {fork : Fork} (state : BeaconState preset fork) : List BLSPubkey :=
  state.validators.data.toList.map (·.pubkey)

def uniqueKeys {fork : Fork} (state : BeaconState preset fork) : Prop :=
  (registryKeys state).Nodup

noncomputable def keysAt {fork : Fork} (state : BeaconState preset fork)
    (indices : List ValidatorIndex) : Finset BLSPubkey := by
  classical
  exact (indices.filterMap fun i => (state.validators.data[i.toNat]?).map (·.pubkey)).toFinset

noncomputable def activeKeys {fork : Fork} (state : BeaconState preset fork) : Finset BLSPubkey :=
  keysAt state (getActiveValidatorIndices state (getCurrentEpoch state))

def effectiveWeight {fork : Fork} (state : BeaconState preset fork) (key : BLSPubkey) : Nat :=
  ((state.validators.data.toList.find? fun v => v.pubkey == key).map
    (·.effectiveBalance.toNat)).getD 0

theorem genesis_unique {g : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) : uniqueKeys g.state := by
  sorry

theorem Run.unique {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (initial : uniqueKeys g.state) : uniqueKeys a.state := by
  sorry

theorem Run.key_preserved {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (i : Nat) (old : Validator) (found : g.state.validators.data[i]? = some old) :
    ∃ current, a.state.validators.data[i]? = some current ∧ current.pubkey = old.pubkey := by
  sorry

theorem receipt_key_preserved {fork : Fork} {state : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    {key : BLSPubkey} {data : AttestationData}
    (receipt : Receipt (config := config) (checks := checks) engine state block key data) :
    ∃ validator, state.validators.data[receipt.index.toNat]? = some validator ∧
      validator.pubkey = key := by
  sorry

theorem keys_weight {fork : Fork} (state : BeaconState preset fork)
    (indices : List ValidatorIndex) (unique : uniqueKeys state)
    (inside : ∀ i ∈ indices, i.toNat < state.validators.data.size) :
    Quorum.weight (effectiveWeight state) (keysAt state indices) =
      ∑ i ∈ indices.toFinset,
        ((state.validators.data[i.toNat]?).map (·.effectiveBalance.toNat)).getD 0 := by
  sorry

end EthLib.Consensus.DirectSafety
