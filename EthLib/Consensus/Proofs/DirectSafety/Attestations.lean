module

public import EthLib.Consensus.Proofs.DirectSafety.Execution
public import EthLib.Consensus.Proofs.Transition.FfgSlackChain
public import EthLib.Consensus.Proofs.Transition.TargetPending
public import EthLib.Consensus.Proofs.Transition.ValidatorKeys

/-!
# Accepted attestations of one selected execution

The votes are upstream blockVotes, taken only from the actual validated block inputs.

Each index is interpreted in the registry before its own block, not in the other branch.

Each accepted vote comes with the aggregate check that a block of the run executed on it.

The check is the call of `isValidIndexedAttestation`, on the state where the operations ran it.

No assumption about the signature checks is made.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The votes that a step casts: none for a slot, and the votes of its block for a block. -/
def Step.votes {before after : ForkedBeaconState preset}
    (step : Step config checks before after) : Set (ValidatorIndex × AttestationData) :=
  match step with
  | .slot _ => ∅
  | .block _ signed _ _ => blockVotes before.state signed.message

/-- The votes that the steps of a run cast. -/
def Run.votes {first last : ForkedBeaconState preset}
    (run : Run config checks first last) : Set (ValidatorIndex × AttestationData) :=
  {vote | ∃ before after, ∃ step : Step config checks before after,
    run.Contains step ∧ vote ∈ step.votes}

/-- A vote of the step for `data` names a validator whose key is `key` before the step.

The index is read in the registry of the state before the step. -/
def Step.Accepted {before after : ForkedBeaconState preset}
    (step : Step config checks before after) (key : BLSPubkey) (data : AttestationData) : Prop :=
  ∃ i v, (i, data) ∈ step.votes ∧ before.state.validators.data[i.toNat]? = some v ∧ v.pubkey = key

/-- A step of the run accepted a vote for `data` by the validator with key `key`. -/
def Run.Accepted {first last : ForkedBeaconState preset}
    (run : Run config checks first last) (key : BLSPubkey) (data : AttestationData) : Prop :=
  ∃ before after, ∃ step : Step config checks before after,
    run.Contains step ∧ step.Accepted key data

namespace DirectSafety

/-- A block step of a run, with the state at which its operations start. -/
structure CheckSite {g a : ForkedBeaconState preset} (run : Run config checks g a) where
  fork : Fork
  before : BeaconState preset fork
  after : BeaconState preset fork
  engine : ExecutionEngine preset fork
  signed : SignedBeaconBlock preset fork
  due : upgradeDue config ⟨fork, before⟩ = false
  applied : applySignedBlock config checks engine before signed true = .ok after
  member : run.Contains (.block engine signed due applied)
  input : BeaconState preset fork
  started : OperationsInput config checks engine before signed.message input

/-- An aggregate check that a block of the run executed, on an indexed attestation naming `key`. -/
structure AttestationCheck {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (key : BLSPubkey) extends CheckSite run where
  checked : BeaconState preset fork
  indexed : IndexedAttestation preset fork
  site : AttestationSite config checks input signed.message.body
    before.latestBlockHeader.slot checked indexed
  /-- Some index of the aggregate holds `key` in the registry of the checked state.

  This does not say that `key` signed. -/
  signer : ∃ i ∈ indexed.attestingIndices.data.toList, ∃ v,
    checked.validators.data[i.toNat]? = some v ∧ v.pubkey = key
  valid : isValidIndexedAttestation config checks checked indexed = .ok true

/-- Case 1: a vote that a block of the run accepted was checked in its attestation.

The vote names its validator by index, in the registry before the block.

The check is the one that `blockVotes_verified` gives, and the key reaches its state by a frame. -/
theorem _root_.EthLib.Consensus.Run.attestationCheck_of_accepted {g a : ForkedBeaconState preset}
    {run : Run config checks g a}
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 <
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {key : BLSPubkey} {data : AttestationData} (accepted : run.Accepted key data) :
    ∃ c : AttestationCheck run key, c.indexed.data = data := by
  obtain ⟨x, y, step, member, i, v, vote, found, keyEq⟩ := accepted
  cases step with
  | slot ok => simp [Step.votes] at vote
  | @block fork before after engine signed due applied =>
    obtain ⟨_, processed, _⟩ := applySignedBlock_ok applied
    obtain ⟨input, checked, indexed, started, site, signs, dataEq, valid⟩ :=
      blockVotes_verified lookahead processed vote
    -- The validator of the vote keeps its key from the state before the block to the check.
    obtain ⟨current, foundCurrent, currentKey⟩ :=
      validators_getElem?_of_validatorKeys_prefix
        ((frame_operationsInput started).toFrame.trans site.frame).pubkeysPrefix found
    exact ⟨⟨⟨fork, before, after, engine, signed, due, applied, member, input, started⟩,
      checked, indexed, site, ⟨i, signs, current, foundCurrent, currentKey.trans keyEq⟩, valid⟩,
      dataEq⟩

end DirectSafety
end EthLib.Consensus
