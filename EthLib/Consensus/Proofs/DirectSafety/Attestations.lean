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
  /-- Some index of the aggregate holds `key` in the registry of the checked state.

  This does not say that `key` signed. -/
  signer : ∃ i ∈ indexed.attestingIndices.data.toList, ∃ v,
    checked.validators.data[i.toNat]? = some v ∧ v.pubkey = key
  valid : isValidIndexedAttestation config checks checked indexed = .ok true

/-- The steps of a block before its operations are a block frame. -/
theorem frame_operationsInput {fork : Fork}
    {engine : ExecutionEngine preset fork} {state input : BeaconState preset fork}
    {block : BeaconBlock preset fork}
    (started : OperationsInput config checks engine state block input) :
    BlockFrame state input :=
  started.step_of BlockFrame BlockFrame.refl BlockFrame.trans
    (fun _ ok => frame_processParentExecutionPayload ok) frame_processBlockHeader
    (fun _ ok => frame_processBlockExecution ok) frame_processRandao
    (fun _ ok => frame_processEth1Data ok)

/-- A fold that succeeds runs its step at each member.

The list splits at the member, and the step runs on the state that the earlier members leave. -/
theorem foldlM_ok_of_mem {α β ε : Type} {g : β → α → Except ε β} {xs : List α} {x : α}
    {start done : β} (member : x ∈ xs) (computed : xs.foldlM g start = .ok done) :
    ∃ pre post before after, xs = pre ++ x :: post ∧ pre.foldlM g start = .ok before ∧
      g before x = .ok after := by
  obtain ⟨pre, post, split⟩ := List.append_of_mem member
  rw [split, List.foldlM_append] at computed
  obtain ⟨before, earlier, rest⟩ := bind_ok_iff.mp computed
  rw [List.foldlM_cons] at rest
  obtain ⟨after, step, -⟩ := bind_ok_iff.mp rest
  exact ⟨pre, post, before, after, split, earlier, step⟩

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
  by_cases altair : Fork.altair ≤ fork
  · unfold processAttestation at computed
    simp only [altair, ↓reduceDIte] at computed
    unfold processAttestationAltair at computed
    simp only [bind_ok_iff, liftAccessor_ok, ensure_ok_iff] at computed
    obtain ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, indexed, indexedOk, valid, validOk, _,
      validTrue, -⟩ := computed
    subst validTrue
    simp only [altair, ↓reduceIte]
    exact ⟨indexed, indexedOk, validOk⟩
  · obtain ⟨_, _, _, _, _, _, indexed, indexedOk, validOk⟩ :=
      processAttestation_records (Nat.lt_of_not_le altair) computed
    simp only [altair, ↓reduceIte]
    exact ⟨indexed, indexedOk, validOk⟩

/-- Case 1: a vote that a block of the run accepted was checked in its attestation. -/
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
    obtain ⟨input, proposersDone, slashingsDone, _, started, proposers, slashings, folded, -⟩ :=
      processBlock_folds processed
    obtain ⟨attestation, included, dataEq, indices, indicesOk, iMem⟩ := vote
    have dataEq : data = attestation.data := dataEq
    -- The attestation sits at a position of the attestations of the block.
    obtain ⟨pre, post, mid, next, split, earlier, processedA⟩ :=
      foldlM_ok_of_mem (Array.mem_toList_iff.mpr included) folded
    have same := getAttestingIndices_attestationsStart lookahead started proposers
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
      (frame_operationsInput started).trans <|
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
      validators_getElem?_of_validatorKeys_prefix
        (headFrame.toFrame.trans kept.2.2).pubkeysPrefix found
    refine ⟨⟨⟨fork, before, after, engine, signed, due, applied, member, input, started⟩,
      _, indexed, .attestation split proposers slashings earlier processedA indexedOk,
      ⟨i, signs, current, foundCurrent, currentKey.trans keyEq⟩, valid⟩, dataOut⟩

end DirectSafety
end EthLib.Consensus
