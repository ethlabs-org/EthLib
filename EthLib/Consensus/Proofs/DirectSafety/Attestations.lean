module

public import EthLib.Consensus.Proofs.DirectSafety.Execution
public import EthLib.Consensus.Proofs.Transition.TargetPending

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

/-- Where the operations of a block check an indexed attestation, and on which state.

An attester slashing checks both of its attestations on the state before it.

From Altair an attestation is checked on the state before it.

Before Altair it is checked on the state after its pending attestation is recorded.

That state is the one that the attestation returns. -/
inductive AttestationSite (config : Config) (checks : SignatureChecks) {fork : Fork}
    (input : BeaconState preset fork) (body : BeaconBlockBody preset fork) (parentSlot : Slot) :
    BeaconState preset fork → IndexedAttestation preset fork → Prop where
  | slashing {proposersDone checked next : BeaconState preset fork}
      {pre post : List (AttesterSlashing preset fork)} {slashing : AttesterSlashing preset fork}
      {indexed : IndexedAttestation preset fork}
      (split : body.attesterSlashings.data.toList = pre ++ slashing :: post)
      (proposers : body.proposerSlashings.data.toList.foldlM
        (processProposerSlashing config checks) input = .ok proposersDone)
      (earlier : pre.foldlM (processAttesterSlashing config checks) proposersDone = .ok checked)
      (processed : processAttesterSlashing config checks checked slashing = .ok next)
      (which : indexed = slashing.attestation1 ∨ indexed = slashing.attestation2) :
      AttestationSite config checks input body parentSlot checked indexed
  | attestation {proposersDone slashingsDone mid next : BeaconState preset fork}
      {pre post : List (Attestation preset fork)} {attestation : Attestation preset fork}
      {indexed : IndexedAttestation preset fork}
      (split : body.attestations.data.toList = pre ++ attestation :: post)
      (proposers : body.proposerSlashings.data.toList.foldlM
        (processProposerSlashing config checks) input = .ok proposersDone)
      (slashings : body.attesterSlashings.data.toList.foldlM
        (processAttesterSlashing config checks) proposersDone = .ok slashingsDone)
      (earlier : pre.foldlM (processAttestation config checks · parentSlot ·) slashingsDone =
        .ok mid)
      (processed : processAttestation config checks mid parentSlot attestation = .ok next)
      (indexedOk : getIndexedAttestation (if .altair ≤ fork then mid else next) attestation =
        .ok indexed) :
      AttestationSite config checks input body parentSlot
        (if .altair ≤ fork then mid else next) indexed

/-- An aggregate check that a block of the run executed, on an indexed attestation naming `key`. -/
structure AttestationCheck {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (key : BLSPubkey) extends CheckSite run where
  checked : BeaconState preset fork
  indexed : IndexedAttestation preset fork
  site : AttestationSite config checks input signed.message.body
    before.latestBlockHeader.slot checked indexed
  signer : ∃ i ∈ indexed.attestingIndices.data.toList, ∃ v,
    checked.validators.data[i.toNat]? = some v ∧ v.pubkey = key
  valid : isValidIndexedAttestation config checks checked indexed = .ok true

/-- A key at a position of a state is at that position, with the same key, after a frame. -/
theorem _root_.EthLib.Consensus.Frame.key_preserved {fork : Fork}
    {state after : BeaconState preset fork} (frame : Frame state after) {i : Nat}
    {old : Validator} (found : state.validators.data[i]? = some old) :
    ∃ current, after.validators.data[i]? = some current ∧ current.pubkey = old.pubkey := by
  obtain ⟨inside, oldEq⟩ := Array.getElem?_eq_some_iff.mp found
  have small : i < (validatorKeys state).length := by simpa [validatorKeys] using inside
  have lastSmall : i < after.validators.data.size := by
    simpa [validatorKeys] using Nat.lt_of_lt_of_le small frame.pubkeysPrefix.length_le
  refine ⟨after.validators.data[i], by simp [lastSmall], ?_⟩
  have same := frame.pubkeysPrefix.getElem small
  simpa [validatorKeys, oldEq] using same.symm

/-- The steps of a block before its operations are a block frame. -/
theorem _root_.EthLib.Consensus.OperationsInput.frame {fork : Fork}
    {engine : ExecutionEngine preset fork} {state input : BeaconState preset fork}
    {block : BeaconBlock preset fork}
    (started : OperationsInput config checks engine state block input) :
    BlockFrame state input :=
  started.step_of BlockFrame BlockFrame.refl BlockFrame.trans
    (fun _ ok => frame_processParentExecutionPayload ok) frame_processBlockHeader
    (fun _ ok => frame_processBlockExecution ok) frame_processRandao
    (fun _ ok => frame_processEth1Data ok)

/-- The operations of a block run its three first folds from the state that it starts at. -/
private theorem processOperations_folds {fork : Fork} {input last : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks input body parentSlot = .ok last) :
    ∃ proposersDone slashingsDone attested,
      body.proposerSlashings.data.toList.foldlM (processProposerSlashing config checks) input =
        .ok proposersDone ∧
      body.attesterSlashings.data.toList.foldlM (processAttesterSlashing config checks)
        proposersDone = .ok slashingsDone ∧
      body.attestations.data.toList.foldlM (processAttestation config checks · parentSlot ·)
        slashingsDone = .ok attested := by
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, -⟩ := computed
    exact ⟨_, _, _, proposersOk, attestersOk, attestedOk⟩
  · simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, -⟩ := computed
    exact ⟨_, _, _, proposersOk, attestersOk, attestedOk⟩

/-- A block that succeeds starts its operations at an operations input.

It runs the proposer slashings from there, then the attester slashings, then the attestations.

The attestations read the slot of the latest block header before the block. -/
theorem processBlock_folds {fork : Fork} {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ input proposersDone slashingsDone attested,
      OperationsInput config checks engine state block input ∧
      block.body.proposerSlashings.data.toList.foldlM (processProposerSlashing config checks)
        input = .ok proposersDone ∧
      block.body.attesterSlashings.data.toList.foldlM (processAttesterSlashing config checks)
        proposersDone = .ok slashingsDone ∧
      block.body.attestations.data.toList.foldlM
        (processAttestation config checks · state.latestBlockHeader.slot ·) slashingsDone =
        .ok attested := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨_, paidOk, _, headedOk, _, executedOk, _, revealedOk, _, votedOk, _, operatedOk,
      -⟩ := computed
    obtain ⟨_, _, _, folds⟩ := processOperations_folds operatedOk
    exact ⟨_, _, _, _, ⟨_, _, _, _, paidOk, headedOk, executedOk, revealedOk, votedOk⟩, folds⟩
  · rename_i altair
    simp only [bind_ok_iff] at computed
    obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := computed
    obtain ⟨_, _, _, folds⟩ := processOperations_folds operationsOk
    -- Before Altair neither the payload of the parent nor the execution part runs.
    have gloas : ¬ Fork.glamsterdam ≤ fork := fun h => altair (Nat.le_trans (by decide) h)
    have bellatrix : ¬ Fork.bellatrix ≤ fork := fun h => altair (Nat.le_trans (by decide) h)
    have early : fork < .hegota := Nat.lt_trans (Nat.lt_of_not_le altair) (by decide)
    refine ⟨_, _, _, _, ⟨state, _, _, _, ?_, headerOk, ?_, randaoOk, ?_⟩, folds⟩
    · simp only [gloas, ↓reduceDIte]
      rfl
    · simp only [bellatrix, ↓reduceDIte]
      rfl
    · simp only [early, ↓reduceDIte]
      exact eth1Ok

/-- The state on which `processAttestation` checks its indexed attestation, and the check.

Before Altair it is the state that the attestation returns, and from Altair its input. -/
private theorem processAttestation_checked {fork : Fork} {state after : BeaconState preset fork}
    {parentSlot : Slot} {attestation : Attestation preset fork}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    ∃ indexed,
      getIndexedAttestation (if .altair ≤ fork then state else after) attestation =
        .ok indexed ∧
      isValidIndexedAttestation config checks (if .altair ≤ fork then state else after)
        indexed = .ok true := by
  unfold processAttestation at computed
  by_cases altair : Fork.altair ≤ fork
  · simp only [altair, ↓reduceDIte] at computed
    unfold processAttestationAltair at computed
    simp only [bind_ok_iff, liftAccessor_ok, ensure_ok_iff] at computed
    obtain ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, indexed, indexedOk, valid, validOk, _,
      validTrue, -⟩ := computed
    subst validTrue
    simp only [altair, ↓reduceIte]
    exact ⟨indexed, indexedOk, validOk⟩
  · simp only [altair, ↓reduceDIte] at computed
    simp only [bind_ok_iff, liftAccessor_ok, ensure_ok_iff] at computed
    obtain ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, updated, -,
      indexed, indexedOk, valid, validOk, _, validTrue, kept⟩ := computed
    subst validTrue
    simp only [pure, Except.pure, Except.ok.injEq] at kept
    subst kept
    simp only [altair, ↓reduceIte]
    exact ⟨indexed, indexedOk, validOk⟩

/-- Case 1: a vote that a block of the run accepted was checked in its attestation. -/
theorem _root_.EthLib.Consensus.Run.attestationCheck_of_accepted {g a : ForkedBeaconState preset}
    {run : Run config checks g a} (parameters : Parameters preset)
    {key : BLSPubkey} {data : AttestationData} (accepted : run.Accepted key data) :
    ∃ c : AttestationCheck run key, c.indexed.data = data := by
  obtain ⟨x, y, step, member, i, v, vote, found, keyEq⟩ := accepted
  cases step with
  | slot ok => simp [Step.votes] at vote
  | @block fork before after engine signed due applied =>
    obtain ⟨_, processed, _⟩ := applySignedBlock_ok applied
    obtain ⟨input, proposersDone, slashingsDone, attested, started, proposers, slashings,
      folded⟩ := processBlock_folds processed
    obtain ⟨attestation, included, dataEq, indices, indicesOk, iMem⟩ := vote
    have dataEq : data = attestation.data := dataEq
    -- The attestation sits at a position of the attestations of the block.
    obtain ⟨pre, post, split⟩ := List.append_of_mem (Array.mem_toList_iff.mpr included)
    rw [split, List.foldlM_append] at folded
    obtain ⟨mid, earlier, rest⟩ := bind_ok_iff.mp folded
    rw [List.foldlM_cons] at rest
    obtain ⟨next, processedA, -⟩ := bind_ok_iff.mp rest
    have same := getAttestingIndices_attestationsStart parameters.lookahead started proposers
      slashings earlier processedA
    -- Up to the attestation, the registry and the mixes are those where the attestations start.
    have midKept : mid.validators = slashingsDone.validators ∧
        mid.randaoMixes = slashingsDone.randaoMixes :=
      foldlM_ok_invariant (fun s => s.validators = slashingsDone.validators ∧
          s.randaoMixes = slashingsDone.randaoMixes)
        (fun _ _ _ held ok => ⟨(processAttestation_registry ok).1.trans held.1,
          (processAttestation_registry ok).2.trans held.2⟩) ⟨rfl, rfl⟩ earlier
    have midFrame : Frame slashingsDone mid :=
      Frame.foldlM (fun _ _ _ ok => frame_processAttestation ok) earlier
    have nextFrame : Frame mid next := frame_processAttestation processedA
    have kept : (if .altair ≤ fork then mid else next).validators = slashingsDone.validators ∧
        (if .altair ≤ fork then mid else next).randaoMixes = slashingsDone.randaoMixes ∧
        Frame slashingsDone (if .altair ≤ fork then mid else next) := by
      by_cases altair : Fork.altair ≤ fork
      · simp only [altair, ↓reduceIte]
        exact ⟨midKept.1, midKept.2, midFrame⟩
      · simp only [altair, ↓reduceIte]
        exact ⟨(processAttestation_registry processedA).1.trans midKept.1,
          (processAttestation_registry processedA).2.trans midKept.2, midFrame.trans nextFrame⟩
    have headFrame : BlockFrame before slashingsDone :=
      started.frame.trans <|
        (BlockFrame.foldlM (fun _ _ _ ok => frame_processProposerSlashing ok) proposers).trans <|
        BlockFrame.foldlM (fun _ _ _ ok => frame_processAttesterSlashing ok) slashings
    -- The attesters at the check are those that the vote used.
    obtain ⟨indexed, indexedOk, valid⟩ := processAttestation_checked processedA
    have attestersX : getAttestingIndices (if .altair ≤ fork then mid else next) attestation =
        .ok indices :=
      ((getAttestingIndices_eq_of_eq (congrArg (·.data) kept.1)
        (congrArg (·.elements) kept.2.1) attestation).trans same).trans indicesOk
    obtain ⟨attesters, attestersOk, listed⟩ :=
      getAttestingIndices_of_getIndexedAttestation indexedOk
    obtain rfl : attesters = indices := Except.ok.inj (attestersOk.symm.trans attestersX)
    obtain ⟨indexed', indexedOk', _, indexedData, _⟩ :=
      getIndexedAttestation_of_getAttestingIndices attestersX
    have indexedEq : indexed' = indexed := Except.ok.inj (indexedOk'.symm.trans indexedOk)
    have signs : i ∈ indexed.attestingIndices.data.toList := by
      rw [listed]
      simpa using iMem
    have dataOut : indexed.data = data := by rw [← indexedEq, indexedData, dataEq]
    obtain ⟨current, foundCurrent, currentKey⟩ :=
      (headFrame.toFrame.trans kept.2.2).key_preserved found
    refine ⟨⟨⟨fork, before, after, engine, signed, due, applied, member, input, started⟩,
      _, indexed, .attestation split proposers slashings earlier processedA indexedOk,
      ⟨i, signs, current, foundCurrent, currentKey.trans keyEq⟩, valid⟩, dataOut⟩

end DirectSafety
end EthLib.Consensus
