module

public import EthLib.Consensus.Proofs.ForkChoice.HonestDuties
public import EthLib.Consensus.Proofs.ForkChoice.VoteOrigins
public import EthLib.Consensus.Proofs.Models.Network.Signers

/-!
# Statements: the votes that honest stores hold for honest validators

This file states part of step 3 of the plan for the safety of the fast confirmation rule.

The rule is that of [arXiv 2405.00549v4][fcr].

The proofs are placeholders, and each statement may still change.

Each statement of an honest validator in a sent message is a vote that its duty allowed.

Two such statements of one validator are never slashable together.

So no honest store counts an honest validator among the equivocators.

Each latest vote of an honest store comes from a statement of a message of its view.

So the latest vote that an honest store holds for an honest validator is a vote of its duty.

Two lemmas of [verified-fast-confirmation][vfc] state the same facts.

They are `Execution.honest_not_equivocating` and `Execution.latest_message_eq_honest_vote`.

There the premises `no_forgery`, `not_slashable` and `votes_assigned` are assumed.

Here the network model and the duty of an honest validator give them.

[fcr]: https://arxiv.org/abs/2405.00549v4
[vfc]: https://github.com/fradamt/verified-fast-confirmation
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- A statement of an honest validator in a sent message is a vote that its duty allowed.

The validator could sign it at an earlier event, with its view and its store there. -/
theorem Execution.exists_maySign_of_signed {n : ℕ} {m : Message preset fork}
    (sent : m ∈ (e.world n).sent) {v : ValidatorIndex} {data : AttestationData}
    (signed : (v, data) ∈ statements config checks anchorState anchorBlock m) (honest : v ∈ J) :
    ∃ k < n, MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
      (e.world k).time ((e.world k).view v) ((e.world k).state v) data := by
  sorry

/-- Two statements of one honest validator in sent messages are not slashable together.

Slots must last a positive time, so that one time is the attestation deadline of one slot. -/
theorem Execution.isSlashableAttestationData_of_signed (slots : 0 < config.SLOT_DURATION_MS)
    {n : ℕ} {first second : Message preset fork} (sentFirst : first ∈ (e.world n).sent)
    (sentSecond : second ∈ (e.world n).sent) {v : ValidatorIndex} {data other : AttestationData}
    (signedFirst : (v, data) ∈ statements config checks anchorState anchorBlock first)
    (signedSecond : (v, other) ∈ statements config checks anchorState anchorBlock second)
    (honest : v ∈ J) : isSlashableAttestationData data other = false := by
  sorry

/-- No honest store counts an honest validator among the equivocators.

Each honest validator must start with no equivocator.

Slots must last a positive time. -/
theorem Execution.not_mem_equivocatingIndices (slots : 0 < config.SLOT_DURATION_MS)
    (start : ∀ u ∈ J, (e.start u).equivocatingIndices = []) {u v : ValidatorIndex}
    (receiver : u ∈ J) (honest : v ∈ J) (n : ℕ) :
    v ∉ ((e.world n).state u).equivocatingIndices := by
  sorry

/-- Each latest vote of an honest store is a statement of a message of its view.

Each honest validator must start from a store built from the anchor. -/
theorem Execution.exists_signed_of_latestMessages {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {u : ValidatorIndex} (receiver : u ∈ J) {n : ℕ}
    {v : ValidatorIndex} {message : LatestMessage fork}
    (found : ((e.world n).state u).latestMessages[v]? = some message) :
    ∃ attestation : Attestation preset fork, ∃ m ∈ (e.world n).view u,
      message = LatestMessage.ofAttestation attestation ∧
      (v, attestation.data) ∈ statements config checks anchorState anchorBlock m := by
  sorry

/-- The latest vote that an honest store holds for an honest validator is a vote of its duty.

The validator could sign its data at an earlier event, with its view and its store there.

Each honest validator must start from a store built from the anchor. -/
theorem Execution.exists_maySign_of_latestMessages {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {u v : ValidatorIndex} (receiver : u ∈ J)
    (honest : v ∈ J) {n : ℕ} {message : LatestMessage fork}
    (found : ((e.world n).state u).latestMessages[v]? = some message) :
    ∃ attestation : Attestation preset fork, ∃ k < n,
      message = LatestMessage.ofAttestation attestation ∧
      MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
        (e.world k).time ((e.world k).view v) ((e.world k).state v) attestation.data := by
  sorry

end EthLib.Consensus.Models.Network
