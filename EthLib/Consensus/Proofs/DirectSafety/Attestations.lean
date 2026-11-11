module

public import EthLib.Consensus.Proofs.DirectSafety.Execution

/-!
# Accepted attestations of one selected execution

The site is computed from the actual block input and the operations before the attestation.

The first version covers forks before Gloas, including the Electra upgrade.

Acceptance is not a claim that an individual signed: that interpretation is a separate assumption.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The concrete prefix of block processing before its attestation loop, before Gloas. -/
def attestationStart {fork : Fork} (early : fork < .glamsterdam)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) : Except TransitionError (BeaconState preset fork) := do
  let state ← processBlockHeader state block
  let state ← if bellatrix : .bellatrix ≤ fork then
      processBlockExecution config checks engine state block.body bellatrix else pure state
  let state ← processRandao config checks state block.body
  let state ← processEth1Data (Nat.lt_trans early (by decide)) state block.body
  let expected ← expectedDepositCount state (Nat.lt_trans early (by decide))
  let deposits := (block.body.deposits (Nat.lt_trans early (by decide))).data
  ensure (deposits.size = expected) (.wrongDepositCount deposits.size expected)
  let state ← block.body.proposerSlashings.data.foldlM (processProposerSlashing config checks) state
  block.body.attesterSlashings.data.foldlM (processAttesterSlashing config checks) state

structure Receipt {fork : Fork} (engine : ExecutionEngine preset fork)
    (state : BeaconState preset fork) (block : BeaconBlock preset fork)
    (key : BLSPubkey) (data : AttestationData) where
  early : fork < .glamsterdam
  position : Fin block.body.attestations.data.size
  first : BeaconState preset fork
  site : BeaconState preset fork
  after : BeaconState preset fork
  started : attestationStart (config := config) (checks := checks) early engine state block =
    .ok first
  prior : (block.body.attestations.data.toList.take position.val).foldlM
    (processAttestation config checks · state.latestBlockHeader.slot ·) first = .ok site
  processed : processAttestation config checks site state.latestBlockHeader.slot
    block.body.attestations.data[position] = .ok after
  indexed : IndexedAttestation preset fork
  indexedOk : getIndexedAttestation site block.body.attestations.data[position] = .ok indexed
  valid : isValidIndexedAttestation config checks site indexed = .ok true
  dataEq : indexed.data = data
  index : ValidatorIndex
  member : index ∈ indexed.attestingIndices.data
  validator : Validator
  found : site.validators.data[index.toNat]? = some validator
  keyEq : validator.pubkey = key

def _root_.EthLib.Consensus.Step.Accepted {before after : ForkedBeaconState preset}
    (step : Step config checks before after) (key : BLSPubkey) (data : AttestationData) : Prop :=
  match step with
  | .slot _ => False
  | .block engine signed _ _ => Nonempty
      (Receipt (config := config) (checks := checks) engine before.state signed.message key data)

def _root_.EthLib.Consensus.Run.Accepted {first last : ForkedBeaconState preset}
    (run : Run config checks first last) (key : BLSPubkey) (data : AttestationData) : Prop :=
  ∃ before after, ∃ step : Step config checks before after,
    run.Contains step ∧ step.Accepted key data

theorem _root_.EthLib.Consensus.Run.accepted_append {g x y : ForkedBeaconState preset}
    (pre : Run config checks g x) (tail : Run config checks x y)
    (key : BLSPubkey) (data : AttestationData) :
    (pre.append tail).Accepted key data ↔ pre.Accepted key data ∨ tail.Accepted key data := by
  sorry

theorem block_attestation_sites {fork : Fork} {state after : BeaconState preset fork}
    (early : fork < .glamsterdam) (engine : ExecutionEngine preset fork)
    (signed : SignedBeaconBlock preset fork)
    (ok : applySignedBlock config checks engine state signed true = .ok after) :
    ∃ first last, attestationStart (config := config) (checks := checks)
      early engine state signed.message = .ok first ∧
      signed.message.body.attestations.data.toList.foldlM
        (processAttestation config checks · state.latestBlockHeader.slot ·) first = .ok last := by
  sorry

/-- No probability model: callers name which data each key really signed. -/
def Authenticated {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (signed : BLSPubkey → AttestationData → Prop) : Prop :=
  ∀ key data, run.Accepted key data → signed key data

end EthLib.Consensus.DirectSafety
