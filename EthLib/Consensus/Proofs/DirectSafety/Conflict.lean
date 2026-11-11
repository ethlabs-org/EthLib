module

public import EthLib.Consensus.Proofs.DirectSafety.Fields

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

/-- Equal target epochs with different targets give the first slashing condition. -/
theorem double_vote_data (d₁ d₂ : AttestationData)
    (sameEpoch : d₁.target.epoch = d₂.target.epoch) (different : d₁.target ≠ d₂.target) :
    isSlashableAttestationData d₁ d₂ = true := by
  sorry

theorem surround_vote_data (d₁ d₂ : AttestationData)
    (source : d₁.source.epoch < d₂.source.epoch)
    (target : d₂.target.epoch < d₁.target.epoch) :
    isSlashableAttestationData d₁ d₂ = true := by
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
