module

public import EthLib.Consensus.ForkChoice.FastConfirmation
public import EthLib.Consensus.Proofs.ForkChoice.HonestDuties
public import EthLib.Consensus.Proofs.ForkChoice.VoteRecords
import EthLib.Consensus.Proofs.HonestAggregation

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
  -- The later current slot leaves room for the checked addition of one slot.
  have slotBound : attestation.data.slot.toNat + 1 < 2 ^ 64 := by
    have := current.toNat_lt
    have := UInt64.lt_iff_toNat_lt.mp past
    omega
  have dueOk := addChecked_of_lt (a := attestation.data.slot) (b := 1)
    (by simpa using slotBound)
  have dueBound : ¬ current < attestation.data.slot + 1 := by
    rw [UInt64.lt_iff_toNat_lt, toNat_add_of_lt (by simpa using slotBound)]
    have := UInt64.lt_iff_toNat_lt.mp past
    simp only [UInt64.toNat_one]
    omega
  have recentOk : store.validateTargetEpochAgainstCurrentTime config attestation = .ok () := by
    simp [validateTargetEpochAgainstCurrentTime, getCurrentStoreEpoch, currentOk, recent,
      bind, Except.bind, pure, Except.pure]
  have targetOk := block_ok_iff.mpr targetKnown
  have votedOk := block_ok_iff.mpr votedKnown
  have notEarlier := UInt64.not_lt.mpr notFuture
  unfold validateOnAttestation
  by_cases gloas : .glamsterdam ≤ fork <;>
    simp [gloas, recentOk, targetOk, votedOk, notEarlier, payload,
      ← epoch, checkpoint, dueOk, currentOk, dueBound, bind, Except.bind, pure, Except.pure,
      Except.mapError, discard, Functor.mapConst, Except.map]

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
  simp [onAttestation, valid, stored, found, committees, indexedOk, signed,
    bind, Except.bind, Except.mapError, pure, Except.pure]

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
  -- Processing an accepted message of the view leaves an up-to-date store unchanged.
  have fixed : after = store := upToDate.2 after (.attestation seen accepted)
  obtain ⟨withTarget, targetState, stored, found, indexedOk, signed⟩ := reads
  -- The handler uses the same target state and indexed attestation as the given reads.
  have result : after =
      withTarget.updateLatestMessages indexed.attestingIndices.data.toList attestation := by
    unfold Store.onAttestation at accepted
    cases valid : store.validateOnAttestation config attestation false with
    | error err => simp [valid, bind, Except.bind] at accepted
    | ok value =>
      cases value
      simp only [valid, stored, found, indexedOk, signed, bind, Except.bind, Except.mapError,
        ↓reduceIte] at accepted
      cases committees : checkAttestationCommittees targetState attestation <;>
        simp_all [pure, Except.pure]
  have counted' : v ∉ withTarget.equivocatingIndices := by
    simpa [← fixed, result, Store.updateLatestMessages] using counted
  have voted := Store.foldl_recordVote indexed.attestingIndices.data.toList
    withTarget.latestMessages voter counted' (message := LatestMessage.ofAttestation attestation)
  simpa [← fixed, result, Store.updateLatestMessages] using voted

/-- An honest vote of a duty is for the head of its voter, in the slot of the duty.

The time of the vote is the attestation deadline of the slot, which falls inside the slot.

The voter starts from a store built from the anchor.

The data has the slot of the duty and a target in the epoch of that slot.

It votes for the head block of the store of the voter, which is not after the slot. -/
theorem VoteAt.data_head {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
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
  obtain ⟨startTime, due', startOk, dueOk', timeEq⟩ := deadline
  rw [dueOk, Except.ok.injEq] at dueOk'
  subst due'
  have current : ((e.world n).state v).getCurrentSlot config = .ok slot := by
    unfold Store.getCurrentSlot
    rw [vote.genesis]
    exact mapError_ok_iff.mpr (computeSlotAtTimeMs_inside startOk
      (vote.upToDate.1.trans timeEq) inSlot)
  have forward := e.forwardReachable
    (fun u hu => (start u hu) ▸ Store.ForwardReachable.anchor anchored) n v honest
  have positive : 0 < config.SLOT_DURATION_MS := by
    have := UInt64.lt_iff_toNat_lt.mp inSlot
    exact UInt64.lt_iff_toNat_lt.mpr (by simp; omega)
  obtain ⟨currentSlot, currentOk, blocks, states⟩ :=
    forward.slots_le_current positive anchorSlot
  rw [current, Except.ok.injEq] at currentOk
  subst currentSlot
  obtain ⟨head, block, headState, state, headOk, known, stateOk, advanced, made⟩ :=
    vote.honestData
  have stateBound : headState.slot ≤ slot :=
    states head.root headState (Store.blockState_ok_iff.mp stateOk)
  have atSlot : state.slot = slot := by
    unfold lookaheadState at advanced
    split at advanced
    · exact (processSlots_slot (mapError_ok_iff.mp advanced)).2
    · simp only [pure, Except.pure, Except.ok.injEq] at advanced
      subst state
      exact UInt64.le_antisymm stateBound (UInt64.not_lt.mp ‹¬ headState.slot < slot›)
  obtain ⟨-, -, dataSlot, dataRoot, -, epoch⟩ := getAttestationData_eq_ok_iff.mp made
  exact ⟨dataSlot.trans atSlot, by simpa [getCurrentEpoch, atSlot] using epoch,
    head, block, headOk, known, dataRoot, blocks head.root block known⟩

/-- The target of an honest vote of a duty is the checkpoint block of its chain, for its voter.

The state of the head block names the same block at the start of the epoch as the store does.

The anchor state and block share an epoch-boundary slot.

This aligns the first checkpoint in state history with the root held by the store. -/
theorem VoteAt.data_target {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
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
  have seen := e.mem_view_of_send sync vote.sends honest receiver
    (by simpa [vote.atTime] using late)
  -- Acceptance is explicit: synchrony supplies the message, not successful validation.
  exact upToDate.recorded seen accepted reads (by simp [vote.alone]) counted

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
