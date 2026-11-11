module

public import EthLib.Consensus.Proofs.ForkChoice.HonestDuties
public import EthLib.Consensus.Proofs.ForkChoice.VoteRecords

/-!
# Statements: an honest vote reaches the latest votes of each honest store

This file states part of step 3 of the plan for the safety of the fast confirmation rule.

The rule is that of [arXiv 2405.00549v4][fcr].

The proofs are placeholders, and each statement may still change.

A store takes an attestation from the wire when the attestation passes each check of the handler.

The first statements give that passage from the facts that the checks ask for.

An honest vote, cast as its duty asks, has those facts in the store of its voter.

Under synchrony the vote is in the view of each honest validator one delay later.

An honest store that is up to date has processed each message of its view that it accepts.

So when it accepts the vote, it holds a vote of that validator at the same rank or later.

A later store of the same validator still holds one, since no handler lowers a rank.

Whether the receiver accepts the vote is left as hypotheses on its store.

It must hold the voted block with the same checkpoint block, and read the same signers.

Two lemmas of [verified-fast-confirmation][vfc] state the delivery.

They are `Execution.vote_lands` and `Execution.vote_ubiquity`.

There a node processes a fixed schedule of events, and a vote lands at the start of the next slot.

Here an honest validator moves when it likes, so the statements ask that its store is up to date.

[fcr]: https://arxiv.org/abs/2405.00549v4
[vfc]: https://github.com/fradamt/verified-fast-confirmation
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Fork}

namespace Store

variable {config : Config} {store : Store preset fork}

/-- An attestation from the wire passes the checks of the store when it has the facts they ask.

Its target is in the current epoch of the store or the one before, and in the epoch of its slot.

The store holds the block of its target and the block of its vote, which is not after its slot.

From Gloas its vote on the payload passes.

Its target is the checkpoint block of the chain of its vote.

Its slot is before the current one. -/
theorem validateOnAttestation_of_facts {attestation : Attestation preset fork}
    {target voted : BeaconBlock preset fork} {current : Slot}
    (currentOk : store.getCurrentSlot config = .ok current)
    (recent : attestation.data.target.epoch = computeEpochAtSlot preset current ∨
      attestation.data.target.epoch = saturatingSub (computeEpochAtSlot preset current) 1)
    (epoch : attestation.data.target.epoch = computeEpochAtSlot preset attestation.data.slot)
    (targetKnown : store.blocks[attestation.data.target.root]? = some target)
    (votedKnown : store.blocks[attestation.data.beaconBlockRoot]? = some voted)
    (notFuture : voted.slot ≤ attestation.data.slot)
    (payload : ∀ gloas : .glamsterdam ≤ fork,
      store.validatePayloadVote gloas attestation voted = .ok ())
    (checkpoint : store.getCheckpointBlock attestation.data.beaconBlockRoot
      attestation.data.target.epoch = .ok attestation.data.target.root)
    (past : attestation.data.slot < current) :
    store.validateOnAttestation config attestation false = .ok () := by
  sorry

/-- The store takes an attestation that passes its checks and that it reads with valid signers.

The attestation must have the committees of its slot in the state of its target.

The store then holds the state of the target and records the vote for each signer. -/
theorem onAttestation_of_reads {checks : SignatureChecks} {attestation : Attestation preset fork}
    {isFromBlock : Bool} {withTarget : Store preset fork} {targetState : BeaconState preset fork}
    {indexed : IndexedAttestation preset fork}
    (valid : store.validateOnAttestation config attestation isFromBlock = .ok ())
    (stored : store.storeTargetCheckpointState config checks attestation.data.target =
      .ok withTarget)
    (found : withTarget.checkpointState attestation.data.target = .ok targetState)
    (committees : checkAttestationCommittees targetState attestation = .ok ())
    (indexedOk : getIndexedAttestation targetState attestation = .ok indexed)
    (signed : isValidIndexedAttestation config checks targetState indexed = .ok true) :
    store.onAttestation config checks attestation isFromBlock =
      .ok (withTarget.updateLatestMessages indexed.attestingIndices.data.toList attestation) := by
  sorry

end Store

namespace Models.Network

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- An up-to-date store holds a vote for each signer of an attestation of its view that it accepts.

The signer must not be among the equivocators of the store.

The vote is at the rank of the vote of the attestation or later. -/
theorem UpToDate.recorded {time : ℕ} {view : Set (Message preset fork)}
    {store after : Store preset fork}
    (upToDate : UpToDate config checks sources time view store)
    {attestation : Attestation preset fork} (seen : .attestation attestation ∈ view)
    (accepted : store.onAttestation config checks attestation false = .ok after)
    {indexed : IndexedAttestation preset fork}
    (reads : ReadsAttestation config checks store attestation indexed) {v : ValidatorIndex}
    (voter : v ∈ indexed.attestingIndices.data.toList) (counted : v ∉ store.equivocatingIndices) :
    ∃ m, store.latestMessages[v]? = some m ∧
      (LatestMessage.ofAttestation attestation).rank ≤ m.rank := by
  sorry

/-- An honest vote of a duty is for the head of its voter, in the slot of the duty.

The time of the vote is the attestation deadline of the slot, which falls inside the slot.

The voter starts from a store built from the anchor.

The data has the slot of the duty and a target in the epoch of that slot.

It votes for the head block of the store of the voter, which is not after the slot. -/
theorem VoteAt.data_head {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {v : ValidatorIndex} (honest : v ∈ J) {slot : Slot}
    {committeeIndex : CommitteeIndex} {time n : ℕ} {attestation : Attestation preset fork}
    {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex time n attestation indexed)
    (deadline : IsAttestationDeadline fork config genesisTimeMs slot time) {due : UInt64}
    (dueOk : getAttestationDueMs config fork = .ok due) (inSlot : due < config.SLOT_DURATION_MS) :
    attestation.data.slot = slot ∧
      attestation.data.target.epoch = computeEpochAtSlot preset slot ∧
      ∃ head block, ((e.world n).state v).getHead config = .ok head ∧
        ((e.world n).state v).blocks[head.root]? = some block ∧
        attestation.data.beaconBlockRoot = head.root ∧ block.slot ≤ slot := by
  sorry

/-- The target of an honest vote of a duty is the checkpoint block of its chain, for its voter.

The state of the head block names the same block at the start of the epoch as the store does.

The hypotheses are those of `VoteAt.data_head`. -/
theorem VoteAt.data_target {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {v : ValidatorIndex} (honest : v ∈ J) {slot : Slot}
    {committeeIndex : CommitteeIndex} {time n : ℕ} {attestation : Attestation preset fork}
    {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex time n attestation indexed)
    (deadline : IsAttestationDeadline fork config genesisTimeMs slot time) {due : UInt64}
    (dueOk : getAttestationDueMs config fork = .ok due) (inSlot : due < config.SLOT_DURATION_MS) :
    ((e.world n).state v).getCheckpointBlock attestation.data.beaconBlockRoot
      attestation.data.target.epoch = .ok attestation.data.target.root := by
  sorry

/-- From Gloas, the vote of an honest duty on the payload passes the check of its voter.

The voter votes for the payload only when its head has the payload, which its store has verified.

The hypotheses are those of `VoteAt.data_head`. -/
theorem VoteAt.data_payload {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {v : ValidatorIndex} (honest : v ∈ J) {slot : Slot}
    {committeeIndex : CommitteeIndex} {time n : ℕ} {attestation : Attestation preset fork}
    {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex time n attestation indexed)
    (deadline : IsAttestationDeadline fork config genesisTimeMs slot time) {due : UInt64}
    (dueOk : getAttestationDueMs config fork = .ok due) (inSlot : due < config.SLOT_DURATION_MS)
    (gloas : .glamsterdam ≤ fork) {voted : BeaconBlock preset fork}
    (known : ((e.world n).state v).blocks[attestation.data.beaconBlockRoot]? = some voted) :
    ((e.world n).state v).validatePayloadVote gloas attestation voted = .ok () := by
  sorry

/-- Under synchrony, an honest store that accepts an honest vote holds a vote of that validator.

The store is that of an honest validator, one delay after the vote or later, and up to date.

It accepts the attestation from the wire, and reads in it the signer that the voter reads.

It does not count the voter among the equivocators.

The vote that it holds is at the rank of the honest vote or later. -/
theorem VoteAt.recorded {Δ : ℕ} (sync : e.Synchronous Δ) {v u : ValidatorIndex} (honest : v ∈ J)
    (receiver : u ∈ J) {slot : Slot} {committeeIndex : CommitteeIndex} {time n : ℕ}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex time n attestation indexed) {k : ℕ}
    (late : time + Δ ≤ (e.world k).time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view u)
      ((e.world k).state u))
    {after : Store preset fork}
    (accepted : ((e.world k).state u).onAttestation config checks attestation false = .ok after)
    (reads : ReadsAttestation config checks ((e.world k).state u) attestation indexed)
    (counted : v ∉ ((e.world k).state u).equivocatingIndices) :
    ∃ m, ((e.world k).state u).latestMessages[v]? = some m ∧
      (LatestMessage.ofAttestation attestation).rank ≤ m.rank := by
  sorry

/-- A store that has recorded an honest vote holds a vote of that validator at each later event.

The hypotheses are those of `VoteAt.recorded`, at the event `k`.

At each later event the vote that the store holds is at the rank of the honest vote or later. -/
theorem VoteAt.recorded_of_le {Δ : ℕ} (sync : e.Synchronous Δ) {v u : ValidatorIndex}
    (honest : v ∈ J) (receiver : u ∈ J) {slot : Slot} {committeeIndex : CommitteeIndex}
    {time n : ℕ} {attestation : Attestation preset fork}
    {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex time n attestation indexed) {k : ℕ}
    (late : time + Δ ≤ (e.world k).time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view u)
      ((e.world k).state u))
    {after : Store preset fork}
    (accepted : ((e.world k).state u).onAttestation config checks attestation false = .ok after)
    (reads : ReadsAttestation config checks ((e.world k).state u) attestation indexed)
    (counted : v ∉ ((e.world k).state u).equivocatingIndices) {later : ℕ} (le : k ≤ later) :
    ∃ m, ((e.world later).state u).latestMessages[v]? = some m ∧
      (LatestMessage.ofAttestation attestation).rank ≤ m.rank := by
  obtain ⟨m, found, rank⟩ := vote.recorded sync honest receiver late upToDate accepted reads counted
  obtain ⟨last, kept, grew⟩ := Execution.latestMessages_rank e receiver le found
  exact ⟨last, kept, UInt64.le_trans rank grew⟩

end Models.Network

end EthLib.Consensus
