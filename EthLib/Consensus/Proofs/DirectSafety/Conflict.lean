module

public import EthLib.Consensus.Proofs.DirectSafety.Fields
public import EthLib.Consensus.Proofs.Transition.Block

/-!
# Conflicting concrete checkpoint fields expose slashable quorum pairs

The induction follows actual calls of the state transition and their checkpoint epochs.

No abstract voting protocol, justification relation or finality relation is an input.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

def AcceptedEither {g a b : ForkedBeaconState preset} (left : Run config checks g a)
    (right : Run config checks g b) (key : BLSPubkey) (data : AttestationData) : Prop :=
  left.Accepted key data ∨ right.Accepted key data

def Slashable {g a b : ForkedBeaconState preset} (left : Run config checks g a)
    (right : Run config checks g b) (key : BLSPubkey) : Prop :=
  ∃ d₁ d₂, AcceptedEither left right key d₁ ∧ AcceptedEither left right key d₂ ∧
    isSlashableAttestationData d₁ d₂ = true

/-- Slashing operations carry evidence even when their votes were not included as attestations. -/
def _root_.EthLib.Consensus.Step.SlashingEvidence {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (key : BLSPubkey) : Prop :=
  match step with
  | .slot _ => False
  | .block _ signed _ _ =>
    (∃ sl ∈ signed.message.body.proposerSlashings.data.toList, ∃ v,
      x.state.validators.data[sl.signedHeader1.message.proposerIndex.toNat]? = some v ∧
      v.pubkey = key) ∨
    (∃ sl ∈ signed.message.body.attesterSlashings.data.toList, ∃ i ∈ slashingIndices sl, ∃ v,
      x.state.validators.data[i.toNat]? = some v ∧ v.pubkey = key)

def _root_.EthLib.Consensus.Run.SlashingEvidence {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (key : BLSPubkey) : Prop :=
  ∃ x y, ∃ step : Step config checks x y, run.Contains step ∧ step.SlashingEvidence key

/-- Accountability includes FFG conflicts and accepted proposer or attester slashing evidence. -/
def Accountable {g a b : ForkedBeaconState preset} (left : Run config checks g a)
    (right : Run config checks g b) (key : BLSPubkey) : Prop :=
  Slashable left right key ∨ left.SlashingEvidence key ∨ right.SlashingEvidence key

/-- A slashed flag in a reachable registry must originate in evidence on the selected history. -/
theorem _root_.EthLib.Consensus.Run.slashed_evidence {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (genesis : Genesis (config := config) (checks := checks) g)
    (early : a.fork < .glamsterdam) (v : Validator)
    (member : v ∈ a.state.validators.data.toList) (slashed : v.slashed = true) :
    run.SlashingEvidence v.pubkey := by
  sorry

/-- Both calls may be on the same run: the statement must not force one witness per branch. -/
abbrev EitherCall {g a b : ForkedBeaconState preset} (left : Run config checks g a)
    (right : Run config checks g b) := QuorumCall left ⊕ QuorumCall right

def EitherCall.targetEpoch {g a b : ForkedBeaconState preset} {left : Run config checks g a}
    {right : Run config checks g b} (call : EitherCall left right) : Nat :=
  match call with
  | .inl c => c.target.epoch.toNat
  | .inr c => c.target.epoch.toNat

noncomputable def EitherCall.voters {g a b : ForkedBeaconState preset}
    {left : Run config checks g a} {right : Run config checks g b}
    (call : EitherCall left right) : Finset BLSPubkey :=
  match call with
  | .inl c => c.voters
  | .inr c => c.voters

def EitherCall.state {g a b : ForkedBeaconState preset} {left : Run config checks g a}
    {right : Run config checks g b} (call : EitherCall left right) : ForkedBeaconState preset :=
  match call with
  | .inl c => ⟨c.before.fork, c.cached⟩
  | .inr c => ⟨c.before.fork, c.cached⟩

theorem call_epochs {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (call : QuorumCall run) : call.source.epoch < call.target.epoch := by
  sorry

/-- Distinct targets at the same epoch give double votes in the common voters. -/
theorem same_epoch_histories {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (earlyA : a.fork < .glamsterdam) (earlyB : b.fork < .glamsterdam)
    (one : QuorumCall left) (two : QuorumCall right)
    (epoch : one.target.epoch = two.target.epoch) (different : one.target ≠ two.target) :
    ∀ key ∈ one.voters ∩ two.voters, Slashable left right key := by
  sorry

/-- The first call crossing an epoch is chosen from the actual justification history. -/
theorem history_crossing {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (c : Checkpoint) (history : JustificationHistory run c) (epoch : Nat)
    (positive : 0 < epoch) (reached : epoch ≤ c.epoch.toNat) :
    ∃ call ∈ history.calls,
      call.source.epoch.toNat < epoch ∧ epoch ≤ call.target.epoch.toNat := by
  sorry

theorem surround_quorums {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (earlyA : a.fork < .glamsterdam) (earlyB : b.fork < .glamsterdam)
    (outer : QuorumCall left) (inner : QuorumCall right)
    (source : outer.source.epoch < inner.source.epoch)
    (target : inner.target.epoch < outer.target.epoch) :
    ∀ key ∈ outer.voters ∩ inner.voters, Slashable left right key := by
  sorry

/-- The difficult induction: a finalized field and a later justified field on conflicting paths. -/
theorem conflicting_fields_quorums {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (earlyA : a.fork < .glamsterdam) (earlyB : b.fork < .glamsterdam)
    (j : Checkpoint)
    (field : j = b.state.previousJustifiedCheckpoint ∨ j = b.state.currentJustifiedCheckpoint ∨
      j = b.state.finalizedCheckpoint)
    (ordered : a.state.finalizedCheckpoint.epoch ≤ j.epoch)
    (conflict : Conflict left right a.state.finalizedCheckpoint j) :
    (∃ one two : EitherCall left right,
      a.state.finalizedCheckpoint.epoch.toNat ≤ one.targetEpoch ∧ one.targetEpoch ≤ j.epoch.toNat ∧
      a.state.finalizedCheckpoint.epoch.toNat ≤ two.targetEpoch ∧ two.targetEpoch ≤ j.epoch.toNat ∧
      ∀ key ∈ one.voters ∩ two.voters, Slashable left right key) ∨
      HashEvidence (left.hashObjects ++ right.hashObjects) := by
  sorry

end EthLib.Consensus.DirectSafety
