module

public import EthLib.Consensus.Proofs.DirectSafety.Execution
public import EthLib.Consensus.Proofs.Transition.TargetPending

/-!
# Accepted attestations of one selected execution

The votes are upstream blockVotes, taken only from the actual validated block inputs.

Each index is interpreted in the registry before its own block, not in the other branch.

Acceptance is separate from the assumption that accepting signature checks means actual signing.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

def Step.votes {before after : ForkedBeaconState preset}
    (step : Step config checks before after) : Set (ValidatorIndex × AttestationData) :=
  match step with
  | .slot _ => ∅
  | .block _ signed _ _ => blockVotes before.state signed.message

def Run.votes {first last : ForkedBeaconState preset}
    (run : Run config checks first last) : Set (ValidatorIndex × AttestationData) :=
  {vote | ∃ before after, ∃ step : Step config checks before after,
    run.Contains step ∧ vote ∈ step.votes}

def Step.Accepted {before after : ForkedBeaconState preset}
    (step : Step config checks before after) (key : BLSPubkey) (data : AttestationData) : Prop :=
  ∃ i v, (i, data) ∈ step.votes ∧ before.state.validators.data[i.toNat]? = some v ∧ v.pubkey = key

def Run.Accepted {first last : ForkedBeaconState preset}
    (run : Run config checks first last) (key : BLSPubkey) (data : AttestationData) : Prop :=
  ∃ before after, ∃ step : Step config checks before after,
    run.Contains step ∧ step.Accepted key data

namespace DirectSafety

/-- The signature interpretation is a separate assumption about accepted block votes. -/
def Authenticated {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (signed : BLSPubkey → AttestationData → Prop) : Prop :=
  ∀ key data, run.Accepted key data → signed key data

end DirectSafety
end EthLib.Consensus
