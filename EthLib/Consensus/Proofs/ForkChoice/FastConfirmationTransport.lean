module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationResets
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationCommittees
import EthLib.Consensus.Proofs.ForkChoice.HonestVotes
import EthLib.Consensus.Proofs.ForkChoice.JustifiedRegistry
import all EthLib.Consensus.Proofs.Transition.ActiveKept

/-!
# Statements: the honest support of a confirmed block, from a historical anchor

This file states the initial transport of step 5 for the fast confirmation rule.

The rule is that of [arXiv 2405.00549v4][fcr].

The proof of the transport is a placeholder, and its statement is proposed for review.

The caller counts an old vote of an honest validator, for a block or for its parent.

The validator may have cast a newer vote before the call.

The caller may still count the old vote, while another honest store counts the new one.

A historical anchor rules this out.

It is a block on the chain of the parent of the confirmed block.

It is of the current epoch or the one before.

It is safe at each time of the current epoch before the call.

So a counted vote has a target of the epoch before or later.

A newer vote of the same validator then has a target of the current epoch.

Its head descends from the historical anchor, so it agrees with the finality of the caller.

So the caller admits that newer vote before the call, and the old vote is not its latest one.

The induction of step 8 takes the anchor from an earlier call, or takes the block of the anchor.

[fcr]: https://arxiv.org/abs/2405.00549v4
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- A duty in a completed slot has both delivery events within the finite receiver horizon. -/
private theorem duty_delivery_before_receiver {Δ first time : Nat}
    (votes : Votes e.startTime time e) (prompt : Prompt e time)
    (fits : DelayFits fork config genesisTimeMs Δ)
    {begin last slot : Slot} {beginTime endTime : UInt64}
    (beginOk : computeTimeAtSlotMs config genesisTimeMs begin = .ok beginTime)
    (endOk : computeTimeAtSlotMs config genesisTimeMs last = .ok endTime)
    (started : e.startTime ≤ first) (fresh : first ≤ beginTime.toNat)
    (complete : endTime.toNat ≤ time)
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J)
    {committeeIndex : CommitteeIndex} (low : begin ≤ slot) (high : slot < last)
    (duty : assignment.committee v slot = some committeeIndex) :
    ∃ deadline n attestation indexed pre post,
      VoteAt e v slot committeeIndex deadline n attestation indexed ∧
      first ≤ deadline ∧ deadline < time ∧
      deadline + Δ ≤ (e.world pre).time ∧
      (e.world pre).time + 1 = (e.world post).time ∧ (e.world post).time ≤ time ∧
      UpToDate config checks sources (e.world pre).time ((e.world pre).view w)
        ((e.world pre).state w) ∧
      UpToDate config checks sources (e.world post).time ((e.world post).view w)
        ((e.world post).state w) ∧
      ∃ next start following,
        addChecked slot 1 = .ok next ∧
        computeTimeAtSlotMs config genesisTimeMs slot = .ok start ∧
        computeTimeAtSlotMs config genesisTimeMs next = .ok following ∧
        IsAttestationDeadline fork config genesisTimeMs slot deadline ∧
        (e.world post).time = following.toNat := by
  obtain ⟨next, start, following, deadline, n, attestation, indexed,
    nextOk, startOk, followingOk, due, afterFirst, delivered, bounded, vote⟩ :=
    e.exists_voteAt_of_duty_interval votes fits beginOk endOk started fresh complete
      honest low high duty
  obtain ⟨⟨pre, preTime, received, preReady⟩, ⟨post, postTime, postReady⟩⟩ :=
    e.exists_duty_boundaries fits (prompt.of_le bounded) receiver nextOk startOk followingOk
      due (started.trans afterFirst)
  exact ⟨deadline, n, attestation, indexed, pre, post, vote, afterFirst, by omega,
    received, by omega, by omega, preReady, postReady,
    next, start, following, nextOk, startOk, followingOk, due, postTime⟩

/-- Two votes that an honest validator signs for targets of one epoch are the same vote.

Two different votes for one target epoch are slashable, and an honest validator signs neither.

So when two honest stores hold votes of one validator for one target epoch, they hold one vote. -/
theorem Execution.data_eq_of_signed_of_target_epoch (slots : 0 < config.SLOT_DURATION_MS)
    {n k : ℕ} {first second : Message preset fork} (sentFirst : first ∈ (e.world n).sent)
    (sentSecond : second ∈ (e.world k).sent) {v : ValidatorIndex} {data other : AttestationData}
    (signedFirst : (v, data) ∈ statements config checks anchorState anchorBlock first)
    (signedSecond : (v, other) ∈ statements config checks anchorState anchorBlock second)
    (honest : v ∈ J) (epoch : data.target.epoch = other.target.epoch) : data = other := by
  have nonslashable := e.isSlashableAttestationData_of_signed slots
    (e.monotone_sent (Nat.le_max_left n k) sentFirst)
    (e.monotone_sent (Nat.le_max_right n k) sentSecond) signedFirst signedSecond honest
  by_contra different
  simp [isSlashableAttestationData, different, epoch] at nonslashable

/-- Equal-rank honest latest votes agree before Gloas, even across different stores. -/
private theorem latest_eq_of_rank_eq (slots : 0 < config.SLOT_DURATION_MS)
    (preGloas : fork < .glamsterdam) {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    {u w v : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) (honest : v ∈ J)
    {n k : ℕ} {first second : LatestMessage fork}
    (firstOk : ((e.world n).state u).latestMessages[v]? = some first)
    (secondOk : ((e.world k).state w).latestMessages[v]? = some second)
    (rank : first.rank = second.rank) : first = second := by
  obtain ⟨a, firstMessage, seenFirst, rfl, signedFirst, _⟩ :=
    e.exists_signed_origin_of_latestMessages anchorStore anchored caller firstOk
  obtain ⟨b, secondMessage, seenSecond, rfl, signedSecond, _⟩ :=
    e.exists_signed_origin_of_latestMessages anchorStore anchored receiver secondOk
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
  have epoch : a.data.target.epoch = b.data.target.epoch := by
    simpa [LatestMessage.rank, LatestMessage.ofAttestation, notGloas] using rank
  have same := e.data_eq_of_signed_of_target_epoch slots
    (e.view_subset_sent n u seenFirst) (e.view_subset_sent k w seenSecond)
    signedFirst signedSecond honest epoch
  simp only [LatestMessage.ofAttestation, same]

/-- An unchanged honest message keeps supporting its root in a receiver that counts its weight.

Block agreement transfers the ancestor walk; no equality of balance states is needed. -/
private theorem supporter_of_same_latest {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor) {limit : ℕ}
    (oneBlock : OneBlockPerRoot e limit) (preGloas : fork < .glamsterdam)
    {u w v : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J)
    {n k : ℕ} (callerBound : (e.world n).time ≤ limit)
    (receiverBound : (e.world k).time ≤ limit)
    {source state : BeaconState preset fork} {root : Root} {block : BeaconBlock preset fork}
    (sourceKnown : ((e.world n).state u).blocks[root]? = some block)
    (known : ((e.world k).state w).blocks[root]? = some block)
    (aboveAnchor : anchorBlock.slot ≤ block.slot)
    (supporter : v ∈ ((e.world n).state u).supportersOf source ⟨root, .pending⟩)
    (sameLatest : ((e.world k).state w).latestMessages[v]? =
      ((e.world n).state u).latestMessages[v]?)
    (counted : v ∉ ((e.world k).state w).equivocatingIndices)
    (active : v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset) :
    v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ := by
  obtain ⟨message, supported, latest, _, supportedOk, descends⟩ :=
    Store.exists_of_voteCountsFor _ (Store.voteCountsFor_of_mem_supportersOf supporter)
  have receiverLatest := sameLatest.trans latest
  obtain ⟨attestation, _, _, same, _, origin⟩ :=
    e.exists_signed_origin_of_latestMessages anchorStore anchored receiver receiverLatest
  obtain ⟨tip, tipKnown, _⟩ := origin.voted
  have rootEq := Store.getSupportedNode_root supportedOk
  rw [same] at rootEq
  have reachable := e.reachable
    (fun w hw => (anchored w hw) ▸ Store.Reachable.anchor anchorStore) k w receiver
  have transferred := Store.isAncestor_of_same_blocks reachable preGloas
    (oneBlock u caller w receiver n k callerBound receiverBound) sourceKnown known aboveAnchor
    ⟨tip, by simpa only [rootEq, LatestMessage.ofAttestation] using tipKnown⟩ descends
  have counts : ((e.world k).state w).voteCountsFor ⟨root, .pending⟩ v = true := by
    apply Store.voteCountsFor_of_check _ receiverLatest (by simpa using counted)
    have supportedReceiver : ((e.world k).state w).getSupportedNode message = .ok supported := by
      simpa only [Store.getSupportedNode_of_lt preGloas] using supportedOk
    simpa only [supportedReceiver, bind, Except.bind] using transferred
  obtain ⟨entry, member, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp active)
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨entry,
    List.mem_filter.mpr ⟨member, counts⟩, rfl⟩)

/-- A latest vote from a slot at or after the call was signed in the safe interval.

The upper bound is strict even when two events share one timestamp. -/
private theorem signing_time_of_slot_floor {anchor : Store preset fork}
    (anchored : ∀ u ∈ J, e.start u = anchor)
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J) {n k : ℕ}
    (earlier : n < k) {attestation : Attestation preset fork}
    (signed : MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
      (e.world n).time ((e.world n).view v) ((e.world n).state v) attestation.data)
    (origin : ((e.world k).state w).VoteOrigin config v attestation)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    {due : UInt64} (dueOk : getAttestationDueMs config fork = .ok due)
    (inSlot : due < config.SLOT_DURATION_MS) {slot : Slot} {begin : UInt64}
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (floor : slot ≤ attestation.data.slot) :
    begin.toNat ≤ (e.world n).time ∧ (e.world n).time < (e.world k).time := by
  obtain ⟨_, _, deadline, genesis, current, _, _⟩ := signed
  obtain ⟨startTime, due', startOk, dueOk', timeEq⟩ := deadline
  have dueEq := Except.ok.inj (dueOk'.symm.trans dueOk)
  subst due'
  obtain ⟨sameBegin, sameOk, _, timeLe⟩ := exists_timeAtSlotMs_of_le floor startOk
  have same := Except.ok.inj (sameOk.symm.trans beginOk)
  subst sameBegin
  constructor
  · have := UInt64.le_iff_toNat_le.mp timeLe
    omega
  · apply lt_of_le_of_ne (e.monotone_time earlier.le)
    intro sameTime
    have genesisEq : ((e.world k).state w).genesisTimeMs = genesisTimeMs := by
      have left := (e.clock_bounds v n).1
      have right := (e.clock_bounds w k).1
      rw [anchored v honest] at left
      rw [anchored w receiver] at right
      exact right.trans (left.symm.trans genesis)
    have sameClock : ((e.world k).state w).timeMs = ((e.world n).state v).timeMs :=
      UInt64.toNat_inj.mp (upToDate.1.trans (sameTime.symm.trans current.1.symm))
    have slotOk : ((e.world k).state w).getCurrentSlot config =
        .ok attestation.data.slot := by
      unfold Store.getCurrentSlot
      rw [genesisEq, sameClock]
      exact mapError_ok_iff.mpr (computeSlotAtTimeMs_inside startOk
        (current.1.trans timeEq) inSlot)
    obtain ⟨currentSlot, currentOk, past⟩ := origin.past
    have sameSlot := Except.ok.inj (currentOk.symm.trans slotOk)
    subst currentSlot
    exact UInt64.lt_irrefl _ past

/-- A receiver's latest honest vote from the safe slot interval supports the root. -/
private theorem supporter_of_latest_slot {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ u ∈ J, e.start u = anchor) {limit : ℕ}
    (oneBlock : OneBlockPerRoot e limit) (preGloas : fork < .glamsterdam)
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J) {k : ℕ}
    (bounded : (e.world k).time ≤ limit)
    {attestation : Attestation preset fork}
    (latest : ((e.world k).state w).latestMessages[v]? =
      some (LatestMessage.ofAttestation attestation))
    (counted : v ∉ ((e.world k).state w).equivocatingIndices)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    {due : UInt64} (dueOk : getAttestationDueMs config fork = .ok due)
    (inSlot : due < config.SLOT_DURATION_MS) {slot : Slot} {begin : UInt64}
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (floor : slot ≤ attestation.data.slot) {root : Root}
    (safe : ∀ earlier, begin.toNat ≤ earlier → earlier < (e.world k).time →
      SafeAt e earlier root)
    {block : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some block)
    (aboveAnchor : anchorBlock.slot ≤ block.slot)
    {state : BeaconState preset fork}
    (active : v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset)
    (signedOrigin : ∃ n < k,
      MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
        (e.world n).time ((e.world n).view v) ((e.world n).state v) attestation.data)
    (origin : ((e.world k).state w).VoteOrigin config v attestation) :
    v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ := by
  obtain ⟨n, earlier, signed⟩ := signedOrigin
  have range := signing_time_of_slot_floor anchored honest receiver earlier signed origin
    upToDate dueOk inSlot beginOk floor
  obtain ⟨tip, held, _⟩ := origin.voted
  exact e.mem_supportersOf_of_signed_in_range anchorStore anchored oneBlock preGloas honest
    receiver signed latest counted range.1 range.2
    ((e.monotone_time earlier.le).trans bounded) bounded safe known aboveAnchor held active

/-- A latest vote at or above a signed fresh vote's rank also comes from a fresh slot. -/
private theorem latest_slot_floor_of_signed_rank
    (slots : 0 < config.SLOT_DURATION_MS) (preGloas : fork < .glamsterdam)
    {v : ValidatorIndex} (honest : v ∈ J) {n k : ℕ}
    {message other : Message preset fork}
    (sent : message ∈ (e.world n).sent) (sentOther : other ∈ (e.world k).sent)
    {data : AttestationData} {attestation : Attestation preset fork}
    (signed : (v, data) ∈ statements config checks anchorState anchorBlock message)
    (signedOther : (v, attestation.data) ∈
      statements config checks anchorState anchorBlock other)
    {store : Store preset fork} (origin : store.VoteOrigin config v attestation)
    (epoch : data.target.epoch = computeEpochAtSlot preset data.slot)
    (rank : (LatestMessage.ofAttestation (fork := fork) attestation).rank ≥ data.target.epoch)
    {slot : Slot} (floor : slot ≤ data.slot) : slot ≤ attestation.data.slot := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
  have targetLe : data.target.epoch ≤ attestation.data.target.epoch := by
    simpa [LatestMessage.rank, LatestMessage.ofAttestation, notGloas] using rank
  by_cases same : data.target.epoch = attestation.data.target.epoch
  · have dataEq := e.data_eq_of_signed_of_target_epoch slots sent sentOther
      signed signedOther honest same
    exact dataEq ▸ floor
  · have targetLt := UInt64.lt_of_le_of_ne targetLe same
    have slotLe : data.slot ≤ attestation.data.slot := by
      by_contra h
      have reversed := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
        (UInt64.le_iff_toNat_le.mp (UInt64.le_of_lt (UInt64.not_le.mp h)))
      rw [epoch, origin.targetEpoch] at targetLt
      have strict := UInt64.lt_iff_toNat_lt.mp targetLt
      simp only [computeEpochAtSlot, UInt64.toNat_div] at strict
      omega
    exact UInt64.le_trans floor slotLe

/-- A successful clock read has a representable slot boundary no later than that clock. -/
private theorem boundary_of_current_slot {clock : UInt64} {slot : Slot}
    (read : computeSlotAtTimeMs config genesisTimeMs clock = .ok slot) :
    ∃ boundary, computeTimeAtSlotMs config genesisTimeMs slot = .ok boundary ∧
      boundary ≤ clock := by
  unfold computeSlotAtTimeMs at read
  obtain ⟨elapsed, elapsedOk, slotOk⟩ := bind_ok_iff.mp read
  have genesisLe := (subChecked_ok_iff.mp elapsedOk).1
  have elapsedEq := (subChecked_ok_iff.mp elapsedOk).2
  have slotEq := (divChecked_ok_iff.mp slotOk).2
  have productLe : slot.toNat * config.SLOT_DURATION_MS.toNat ≤ elapsed.toNat := by
    rw [slotEq]
    exact Nat.div_mul_le_self _ _
  have clockBound := clock.toNat_lt
  have productBound : slot.toNat * config.SLOT_DURATION_MS.toNat < 2 ^ 64 := by omega
  have productOk := mulChecked_of_lt productBound
  have productEq := (mulChecked_ok_iff.mp productOk).2
  have sumBound : genesisTimeMs.toNat + (slot * config.SLOT_DURATION_MS).toNat < 2 ^ 64 := by
    omega
  have sumOk := addChecked_of_lt sumBound
  have sumEq := (addChecked_ok_iff.mp sumOk).2
  refine ⟨genesisTimeMs + slot * config.SLOT_DURATION_MS, ?_, ?_⟩
  · simp [computeTimeAtSlotMs, productOk, sumOk, bind, Except.bind]
  · exact UInt64.le_iff_toNat_le.mpr (by omega)

/-- A completed safe duty is recorded by the endpoint, unless justification covers the root. -/
private theorem recorded_duty_of_safe_interval {Δ first time : ℕ}
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (preGloas : fork < .glamsterdam) (oneBlock : OneBlockPerRoot e time)
    (admitted : BlocksAdmitted e 0 Δ time)
    (votes : Votes e.startTime time e) (prompt : Prompt e time)
    (fits : DelayFits fork config genesisTimeMs Δ) {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (anchored : ∀ u ∈ J, e.start u = anchor)
    {horizon : Epoch} (chain : FinalizedPrefix e horizon time)
    (inHorizon : ∀ u ∈ J, ∀ j epoch, (e.world j).time ≤ time →
      ((e.world j).state u).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (nonzero : ∀ u ∈ J, ∀ j, (e.world j).time ≤ time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world j).state u).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    {begin last slot : Slot} {beginTime endTime : UInt64}
    (beginOk : computeTimeAtSlotMs config genesisTimeMs begin = .ok beginTime)
    (endOk : computeTimeAtSlotMs config genesisTimeMs last = .ok endTime)
    (started : e.startTime ≤ first) (fresh : first ≤ beginTime.toNat)
    (complete : endTime.toNat ≤ time)
    {root : Root} (safe : ∀ earlier, first ≤ earlier → earlier < time → SafeAt e earlier root)
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J) {k : ℕ}
    (atTime : (e.world k).time = time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (counted : ∀ j, (e.world j).time ≤ time →
      v ∉ ((e.world j).state w).equivocatingIndices)
    {block : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some block)
    (rootFinal : ∀ j ≤ k,
      UpToDate config checks sources (e.world j).time ((e.world j).view w)
        ((e.world j).state w) →
      (∃ boundary,
        computeStartSlotAtEpoch preset ((e.world j).state w).finalizedCheckpoint.epoch =
          .ok boundary ∧ boundary ≤ block.slot ∧
        ((e.world k).state w).getCheckpointBlock root
          ((e.world j).state w).finalizedCheckpoint.epoch =
            .ok ((e.world j).state w).finalizedCheckpoint.root) ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world j).state w).finalizedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true)
    {committeeIndex : CommitteeIndex} (low : begin ≤ slot) (high : slot < last)
    (duty : assignment.committee v slot = some committeeIndex) :
    (∃ deadline n attestation indexed message,
      VoteAt e v slot committeeIndex deadline n attestation indexed ∧
      attestation.data.slot = slot ∧
      attestation.data.target.epoch = computeEpochAtSlot preset slot ∧
      deadline + Δ ≤ time ∧
      ((e.world k).state w).latestMessages[v]? = some message ∧
      attestation.data.target.epoch ≤ message.rank) ∨
    ((e.world k).state w).isAncestor
      ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩
      ⟨root, .pending⟩ = .ok true := by
  obtain ⟨deadline, n, attestation, indexed, pre, post, vote, firstLe, before,
    delivered, adjacent, completePost, preReady, postReady,
    next, start, following, nextOk, startOk, followingOk, deadlineOk, postTime⟩ :=
    duty_delivery_before_receiver votes prompt fits beginOk endOk started fresh complete
      honest receiver low high duty
  obtain ⟨due, dueOk⟩ := fits.1
  have dueLt := fits.due_lt_slot nextOk startOk followingOk dueOk
  obtain ⟨dataSlot, dataEpoch, head, headBlock, headOk, headKnown, dataRoot, notFuture⟩ :=
    vote.data_head anchorStore (UInt64.le_of_eq anchorSlot) anchored honest deadlineOk dueOk dueLt
  have supports := safe deadline firstLe before v honest n head vote.atTime
    (vote.atTime.symm ▸ vote.upToDate) headOk
  have sourceKnown : ((e.world n).state v).blocks[root]? = some block := by
    have test := supports
    unfold Store.isAncestor at test
    obtain ⟨other, read, _⟩ := bind_ok_iff.mp test
    have held := Store.block_ok_iff.mp read
    have same := oneBlock v honest w receiver n k (by rw [vote.atTime]; omega)
      (by omega) root other block held known
    exact same ▸ held
  have forward := fun u hu j => e.forwardReachable
    (fun u hu => (anchored u hu) ▸ Store.ForwardReachable.anchor anchorStore) j u hu
  have epochExists : ∀ j, ∃ epoch,
      ((e.world j).state w).getCurrentStoreEpoch config = .ok epoch := by
    intro j
    obtain ⟨current, currentOk, _, _⟩ :=
      (forward w receiver j).slots_le_current slots (UInt64.le_of_eq anchorSlot)
    exact ⟨computeEpochAtSlot preset current, by
      simp [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]⟩
  have preLe : pre ≤ k := by
    by_contra h
    have bad := e.monotone_time (Nat.le_of_lt (Nat.lt_of_not_ge h))
    dsimp at bad
    omega
  obtain ⟨preEpoch, preEpochOk⟩ := epochExists pre
  obtain ⟨endpointEpoch, endpointOk⟩ := epochExists k
  rcases e.blocks_or_justified_covers sync preGloas oneBlock admitted anchorStore sound anchored
      slots anchorSlot anchorBoundary chain honest receiver preLe (by omega)
      (by simpa [vote.atTime] using delivered) preReady preEpochOk endpointOk
      (inHorizon w receiver pre preEpoch (by omega) preEpochOk)
      (inHorizon w receiver k endpointEpoch (by omega) endpointOk)
      headKnown sourceKnown known supports (rootFinal pre preLe preReady) with held | covered
  swap
  · exact .inr covered
  -- At equal timestamps use the endpoint's ready store, not an event after the endpoint.
  have arrivalExists : ∃ arrival, pre ≤ arrival ∧ arrival ≤ k ∧
      (e.world arrival).time = following.toNat ∧
      UpToDate config checks sources (e.world arrival).time ((e.world arrival).view w)
        ((e.world arrival).state w) := by
    by_cases same : following.toNat = time
    · exact ⟨k, preLe, le_refl _, by omega, upToDate⟩
    · have postLe : post ≤ k := by
        by_contra h
        have bad := e.monotone_time (Nat.le_of_lt (Nat.lt_of_not_ge h))
        dsimp at bad
        omega
      have prePost : pre ≤ post := by
        by_contra h
        have bad := e.monotone_time (Nat.le_of_lt (Nat.lt_of_not_ge h))
        dsimp at bad
        omega
      exact ⟨post, prePost, postLe, postTime, postReady⟩
  obtain ⟨arrival, preArrival, arrivalLe, arrivalTime, arrivalReady⟩ := arrivalExists
  have arrivalBound : (e.world arrival).time ≤ time :=
    (e.monotone_time arrivalLe).trans_eq atTime
  have genesis : ((e.world arrival).state w).genesisTimeMs = genesisTimeMs := by
    have left := (e.clock_bounds v n).1
    have right := (e.clock_bounds w arrival).1
    rw [anchored v honest] at left
    rw [anchored w receiver] at right
    exact right.trans (left.symm.trans vote.genesis)
  have currentOk : ((e.world arrival).state w).getCurrentSlot config = .ok next := by
    unfold Store.getCurrentSlot
    rw [genesis]
    have clock : ((e.world arrival).state w).timeMs = following :=
      UInt64.toNat_inj.mp (arrivalReady.1.trans arrivalTime)
    rw [clock]
    exact mapError_ok_iff.mpr (computeSlotAtTimeMs_computeTimeAtSlotMs slots followingOk)
  have votedKnown : ((e.world arrival).state w).blocks[attestation.data.beaconBlockRoot]? =
      some headBlock := dataRoot ▸ e.blocks_of_le preArrival held
  have targetRead := vote.data_target anchorStore anchorSlot anchorBoundary anchored honest
    (nonzero v honest n (by rw [vote.atTime]; omega)) deadlineOk dueOk dueLt
  obtain ⟨targetBoundary, targetBlock, targetBoundaryOk, targetKnown, targetLe, _⟩ :=
    Store.isAncestor_of_getCheckpointBlock preGloas targetRead
  have targetAbove := (forward v honest n).reachable.anchorSlot_le_block targetKnown
  have receiverRead := Store.getCheckpointBlock_of_same_blocks
    (forward w receiver arrival).reachable (oneBlock v honest w receiver n arrival
      (by rw [vote.atTime]; omega) arrivalBound)
    targetBoundaryOk (UInt64.le_trans targetAbove targetLe) ⟨headBlock, votedKnown⟩ targetRead
  obtain ⟨message, latest, rank⟩ := vote.recorded_at_next_slot sync preGloas anchorStore anchored
    oneBlock honest receiver dataSlot dataEpoch nextOk currentOk (by omega) arrivalReady
    (counted arrival arrivalBound) arrivalLe arrivalBound votedKnown notFuture receiverRead
  exact .inl ⟨deadline, n, attestation, indexed, message, vote, dataSlot, dataEpoch,
    by omega, latest, rank⟩

private theorem mem_insert_fold {v : ValidatorIndex}
    {items : List ValidatorIndex} {initial : Std.TreeSet ValidatorIndex} :
    v ∈ items.foldl (·.insert ·) initial ↔ v ∈ initial ∨ v ∈ items := by
  induction items generalizing initial with
  | nil => simp
  | cons first rest ih =>
    simp only [List.foldl_cons, ih, Std.TreeSet.mem_insert, List.mem_cons,
      Std.LawfulEqCmp.compare_eq_iff_eq]
    constructor
    · rintro ((rfl | inside) | later)
      · exact .inr (.inl rfl)
      · exact .inl inside
      · exact .inr (.inr later)
    · rintro (inside | rfl | later)
      · exact .inl (.inr inside)
      · exact .inl (.inl rfl)
      · exact .inr later

/-- A slot committee contains only indices active in the head state's duty epoch. -/
private theorem active_of_mem_slotCommittee {store : Store preset fork}
    {head : Root} {slot : Slot} {members : Std.TreeSet ValidatorIndex}
    {headState : BeaconState preset fork} {v : ValidatorIndex}
    (preGloas : fork < .glamsterdam)
    (stateOk : store.blockState head = .ok headState)
    (read : store.getSlotCommittee head slot = .ok members) (member : v ∈ members) :
    isActiveAt headState (computeEpochAtSlot preset slot) v.toNat = true := by
  unfold Store.getSlotCommittee at read
  rw [stateOk] at read
  dsimp only [bind, Except.bind] at read
  -- Every insertion is justified by the committee read at that iteration.
  have kept := foldlM_ok_invariant
    (fun found : Std.TreeSet ValidatorIndex => ∀ x ∈ found,
      isActiveAt headState (computeEpochAtSlot preset slot) x.toNat = true)
    (fun found index after before step => ?_) (by
      intro x hx
      exact False.elim (Std.TreeSet.not_mem_emptyc hx)) read
  · exact kept v member
  · change (do
      let committee ← (getBeaconCommittee headState slot index.toUInt64).mapError
        ForkChoiceError.accessor
      pure (committee.foldl (·.insert ·) found)) = Except.ok after at step
    simp only [bind_ok_iff, mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at step
    obtain ⟨committee, committeeOk, rfl⟩ := step
    intro x inside
    rw [← Array.foldl_toList, mem_insert_fold] at inside
    rcases inside with old | added
    · exact before x old
    · exact isActiveAt_eq_true_iff.mpr
        ((mem_getActiveValidatorIndices
          (BeaconState.registryWithinLimit_of_lt preGloas headState)).mp
          (mem_getActiveValidatorIndices_of_getBeaconCommittee committeeOk
            (Array.mem_toList_iff.mp added)))

/-- A window member has an active duty epoch in the state used to read the window. -/
private theorem active_of_mem_committeeWindow {store : Store preset fork}
    {head : Root} {first last : Slot} {members : Std.TreeSet ValidatorIndex}
    {headState : BeaconState preset fork} {v : ValidatorIndex}
    (preGloas : fork < .glamsterdam)
    (stateOk : store.blockState head = .ok headState)
    (read : store.getCommitteesBetweenSlots head first last = .ok members)
    (member : v ∈ members) :
    ∃ slot, first ≤ slot ∧ slot ≤ last ∧
      isActiveAt headState (computeEpochAtSlot preset slot) v.toNat = true := by
  simp only [Store.getCommitteesBetweenSlots, bind_ok_iff, mapError_ok_iff] at read
  obtain ⟨afterLast, afterOk, read⟩ := read
  have inside := (mem_foldlM_committees_iff read).mp member
  rcases inside with empty | ⟨offset, offsetIn, committee, committeeOk, inside⟩
  · exact False.elim (Std.TreeSet.not_mem_emptyc empty)
  · have offsetLt := List.mem_range.mp offsetIn
    have afterNat := (addChecked_ok_iff.mp afterOk).2
    have lastBound := last.toNat_lt
    have offsetBound : offset < 2 ^ 64 := by simp only [UInt64.toNat_one] at afterNat; omega
    have offsetNat : offset.toUInt64.toNat = offset := by
      simp [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' offsetBound]
    have slotNat : (first + offset.toUInt64).toNat = first.toNat + offset := by
      rw [UInt64.toNat_add, offsetNat, Nat.mod_eq_of_lt]
      simp only [UInt64.toNat_one] at afterNat
      omega
    refine ⟨first + offset.toUInt64, ?_, ?_,
      active_of_mem_slotCommittee preGloas stateOk committeeOk inside⟩
    · rw [UInt64.le_iff_toNat_le, slotNat]
      omega
    · rw [UInt64.le_iff_toNat_le, slotNat]
      simp only [UInt64.toNat_one] at afterNat
      omega

/-- A window with a participant has read its head state.
An empty slot range has no participants. -/
private theorem headState_of_mem_committeeWindow {store : Store preset fork}
    {head : Root} {first last : Slot} {members : Std.TreeSet ValidatorIndex}
    {v : ValidatorIndex}
    (read : store.getCommitteesBetweenSlots head first last = .ok members)
    (member : v ∈ members) : ∃ state, store.blockState head = .ok state := by
  cases found : store.blockState head with
  | ok state => exact ⟨state, rfl⟩
  | error err =>
    unfold Store.getCommitteesBetweenSlots at read
    obtain ⟨afterEnd, _, read⟩ := bind_ok_iff.mp read
    have empty := foldlM_ok_invariant
      (fun set : Std.TreeSet ValidatorIndex => ∀ x, x ∉ set)
      (fun set offset next before step => ?_) (by
        intro x
        exact Std.TreeSet.not_mem_emptyc) read
    · exact False.elim (empty v member)
    · simp [Store.getSlotCommittee, found, bind, Except.bind] at step

/-- Every window participant can be read in the justified registry before filtering activity. -/
private theorem validatorAt_of_mem_committeeWindow {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (start : ∀ w ∈ J, e.start w = anchor) (preGloas : fork < .glamsterdam)
    (slots : 0 < config.SLOT_DURATION_MS) {horizon : Epoch} {last : ℕ}
    (chain : FinalizedPrefix e horizon last)
    {w : ValidatorIndex} (honest : w ∈ J) {k : Nat} (bounded : (e.world k).time ≤ last)
    {current : Epoch}
    (currentOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok current)
    (inHorizon : current ≤ horizon)
    (nonzero : ∀ (r : Root) (b : BeaconBlock preset fork),
      ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    {head : ForkChoiceNode} {state : BeaconState preset fork}
    (headOk : ((e.world k).state w).getHead config = .ok head)
    (stateOk : ((e.world k).state w).checkpointState
      ((e.world k).state w).justifiedCheckpoint = .ok state)
    {first last : Slot} {members : Std.TreeSet ValidatorIndex} {v : ValidatorIndex}
    (windowOk : ((e.world k).state w).getCommitteesBetweenSlots head.root first last = .ok members)
    (member : v ∈ members) : ∃ validator, validatorAt state v = .ok validator := by
  obtain ⟨headState, headStateOk⟩ := headState_of_mem_committeeWindow windowOk member
  obtain ⟨_, _, _, active⟩ :=
    active_of_mem_committeeWindow preGloas headStateOk windowOk member
  obtain ⟨validator, found⟩ := e.validatorAt_justified_of_head_active anchored sound anchorSlot
    anchorBoundary start preGloas slots chain honest bounded currentOk inHorizon nonzero headOk
    headStateOk stateOk active
  exact ⟨validator, validatorAt_ok_iff.mpr found⟩

/-- A successful committee window supplies every shorter window with the same first slot. -/
private theorem committeeWindow_prefix {store : Store preset fork} {head : Root}
    {first last shortLast : Slot} {members : Std.TreeSet ValidatorIndex}
    (read : store.getCommitteesBetweenSlots head first last = .ok members)
    (before : shortLast ≤ last) :
    ∃ short, store.getCommitteesBetweenSlots head first shortLast = .ok short ∧
      ∀ v ∈ short, v ∈ members := by
  have original := read
  unfold Store.getCommitteesBetweenSlots at read
  obtain ⟨afterLast, afterOk, folded⟩ := bind_ok_iff.mp read
  have afterNat := (addChecked_ok_iff.mp (mapError_ok_iff.mp afterOk))
  have shorter : shortLast.toNat + (1 : UInt64).toNat < 2 ^ 64 := by
    have le := UInt64.le_iff_toNat_le.mp before
    omega
  have shortOk := addChecked_of_lt shorter
  have shortNat := (addChecked_ok_iff.mp shortOk).2
  have counts : (shortLast + 1).toNat - first.toNat ≤ afterLast.toNat - first.toNat := by
    have le := UInt64.le_iff_toNat_le.mp before
    omega
  have split : List.range (afterLast.toNat - first.toNat) =
      List.range ((shortLast + 1).toNat - first.toNat) ++
        (List.range (afterLast.toNat - first.toNat)).drop
          ((shortLast + 1).toNat - first.toNat) := by
    simpa only [List.take_range, Nat.min_eq_left counts] using
      (List.take_append_drop ((shortLast + 1).toNat - first.toNat)
        (List.range (afterLast.toNat - first.toNat))).symm
  rw [split, List.foldlM_append] at folded
  obtain ⟨short, prefixOk, _⟩ := bind_ok_iff.mp folded
  have shortRead : store.getCommitteesBetweenSlots head first shortLast = .ok short := by
    simpa only [Store.getCommitteesBetweenSlots, shortOk, Except.mapError,
      bind, Except.bind] using prefixOk
  exact ⟨short, shortRead, fun _ member =>
    Store.mem_getCommitteesBetweenSlots_of_le shortRead original before member⟩

/-- An unslashed active window member is present in the balance list used by the tally. -/
private theorem tallyActive_of_activeMember {state : BeaconState preset fork}
    {members : Std.TreeSet ValidatorIndex} {v : ValidatorIndex}
    (member : v ∈ Store.activeMembers state members) (unslashed : NotSlashed state v) :
    v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset := by
  obtain ⟨_, validator, found, active⟩ := Store.mem_activeMembers.mp member
  have flag : validator.slashed = false := by
    simpa only [NotSlashed, found, Option.map_some, Option.getD_some] using unslashed
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨(v, validator.effectiveBalance), ?_, rfl⟩
  unfold unslashedActiveBalances
  apply List.mem_filterMap.mpr
  refine ⟨(validator, v.toNat), ?_, ?_⟩
  · apply List.mem_zipIdx_iff_getElem?.mpr
    simpa using found
  · simp [active, flag, UInt64.ofNat_toNat]

/-- A successful total also bounds a subset, without requiring a bound on inactive balances. -/
private theorem totalBalance_exists_of_subset {state : BeaconState preset fork}
    {indices all : List ValidatorIndex} {total : Gwei}
    (read : getTotalBalance state all = .ok total)
    (subset : ∀ v ∈ indices, v ∈ all) :
    ∃ result, getTotalBalance state indices = .ok result := by
  obtain ⟨inside, bounded, -⟩ := getTotalBalance_ok_iff_stake.mp read
  have small : stake (fun v => balanceAt state v.toNat) indices.toFinset < 2 ^ 64 :=
    lt_of_le_of_lt (stake_mono fun v member =>
      List.mem_toFinset.mpr (subset v (List.mem_toFinset.mp member))) bounded
  -- The floor is itself a UInt64, so taking the maximum cannot introduce overflow.
  let value := max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (stake (fun v => balanceAt state v.toNat) indices.toFinset)
  have fits : value < 2 ^ 64 := max_lt preset.EFFECTIVE_BALANCE_INCREMENT.toNat_lt small
  refine ⟨value.toUInt64, getTotalBalance_ok_iff_stake.mpr
    ⟨fun v member => inside v (subset v member), small, ?_⟩⟩
  exact UInt64.toNat_ofNat_of_lt' fits

/-- A checked subset total transfers across states when its indices and weights agree. -/
private theorem totalBalance_transfer {source state : BeaconState preset fork}
    {indices : List ValidatorIndex} {total : Gwei}
    (read : getTotalBalance source indices = .ok total)
    (inside : ∀ v ∈ indices, v.toNat < state.validators.data.size)
    (weights : ∀ v ∈ indices, balanceAt state v.toNat = balanceAt source v.toNat) :
    getTotalBalance state indices = .ok total := by
  obtain ⟨_, bounded, value⟩ := getTotalBalance_ok_iff_stake.mp read
  have same := stake_congr (S := indices.toFinset)
    (fun v member => weights v (List.mem_toFinset.mp member))
  exact getTotalBalance_ok_iff_stake.mpr ⟨inside, same ▸ bounded, same ▸ value⟩

/-- Equal duty activity transfers a filtered read only after every receiver lookup succeeds. -/
private theorem filteredTotal_transfer {source state : BeaconState preset fork}
    {participants : Std.TreeSet ValidatorIndex} {active : List ValidatorIndex} {total : Gwei}
    (filtered : participants.toList.filterM (fun index => do
      return isActiveValidator (← validatorAt source index) (getCurrentEpoch source)) = .ok active)
    (read : getTotalBalance source active = .ok total)
    (inside : ∀ v ∈ participants, ∃ validator, validatorAt state v = .ok validator)
    (activity : ∀ v ∈ participants,
      isActiveAt state (getCurrentEpoch state) v.toNat =
        isActiveAt source (getCurrentEpoch source) v.toNat)
    (weights : ∀ v ∈ active, balanceAt state v.toNat = balanceAt source v.toNat) :
    ∃ other, participants.toList.filterM (fun index => do
      return isActiveValidator (← validatorAt state index) (getCurrentEpoch state)) = .ok other ∧
      getTotalBalance state other = .ok total := by
  obtain ⟨other, otherOk⟩ := filterM_exists_ok (test := fun index => do
    return isActiveValidator (← validatorAt state index) (getCurrentEpoch state))
    (list := participants.toList) (fun v member => by
      obtain ⟨validator, found⟩ := inside v (Std.TreeSet.mem_toList.mp member)
      exact ⟨isActiveValidator validator (getCurrentEpoch state), by simp [found]⟩)
  have activeMem : ∀ v, v ∈ active ↔ v ∈ participants ∧
      isActiveAt source (getCurrentEpoch source) v.toNat = true := by
    intro v
    constructor
    · intro member
      have pass := passes_of_mem_filterM_ok filtered member
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at pass
      obtain ⟨validator, found, active⟩ := pass
      exact ⟨Std.TreeSet.mem_toList.mp (mem_of_filterM_ok filtered member),
        isActiveAt_eq_true_iff.mpr ⟨validator, validatorAt_ok_iff.mp found, active⟩⟩
    · rintro ⟨member, active⟩
      obtain ⟨validator, found, active⟩ := isActiveAt_eq_true_iff.mp active
      exact mem_filterM_ok_of_test filtered (Std.TreeSet.mem_toList.mpr member)
        (by simp [validatorAt_ok_iff.mpr found, active])
  have same : ∀ v, v ∈ other ↔ v ∈ active := by
    intro v
    rw [activeMem]
    constructor
    · intro member
      have inSet := Std.TreeSet.mem_toList.mp (mem_of_filterM_ok otherOk member)
      have pass := passes_of_mem_filterM_ok otherOk member
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at pass
      obtain ⟨validator, found, active⟩ := pass
      exact ⟨inSet, activity v inSet ▸
        isActiveAt_eq_true_iff.mpr ⟨validator, validatorAt_ok_iff.mp found, active⟩⟩
    · rintro ⟨member, active⟩
      rw [← activity v member] at active
      obtain ⟨validator, found, active⟩ := isActiveAt_eq_true_iff.mp active
      exact mem_filterM_ok_of_test otherOk (Std.TreeSet.mem_toList.mpr member)
        (by simp [validatorAt_ok_iff.mpr found, active])
  refine ⟨other, otherOk, (getTotalBalance_congr same).mpr ?_⟩
  exact totalBalance_transfer read (fun v member => by
    obtain ⟨validator, found⟩ := inside v ((activeMem v).mp member).1
    exact (Array.getElem?_eq_some_iff.mp (validatorAt_ok_iff.mp found)).1) weights

/-- Full-mode totals transfer when all active positions and their weights agree. -/
private theorem activeTotal_transfer {source state : BeaconState preset fork} {total : Gwei}
    (within : state.RegistryWithinLimit)
    (read : getTotalActiveBalance source = .ok total)
    (activity : ∀ position, isActiveAt state (getCurrentEpoch state) position =
      isActiveAt source (getCurrentEpoch source) position)
    (weights : ∀ v ∈ getActiveValidatorIndices source (getCurrentEpoch source),
      balanceAt state v.toNat = balanceAt source v.toNat) :
    getTotalActiveBalance state = .ok total := by
  have checked := (bind_ok_iff.mp read).choose_spec.1
  have same : ∀ v, v ∈ getActiveValidatorIndices state (getCurrentEpoch state) ↔
      v ∈ getActiveValidatorIndices source (getCurrentEpoch source) := by
    intro v
    rw [mem_getActiveValidatorIndices within]
    rw [← getActiveValidatorIndicesChecked_ok checked,
      mem_iff_of_getActiveValidatorIndicesChecked_ok checked]
    rw [← isActiveAt_eq_true_iff, ← isActiveAt_eq_true_iff, activity]
  unfold getTotalActiveBalance
  rw [getActiveValidatorIndicesChecked_of_within within]
  change getTotalBalance state (getActiveValidatorIndices state (getCurrentEpoch state)) =
    .ok total
  apply (getTotalBalance_congr same).mpr
  exact totalBalance_transfer (getTotalActiveBalance_ok read) (fun v member => by
    obtain ⟨validator, found, _⟩ := (mem_getActiveValidatorIndices within).mp
      ((same v).mpr member)
    exact (Array.getElem?_eq_some_iff.mp found).1) weights

/-- An all-active stake bound supplies the checked total, including slashed validators. -/
private theorem activeTotal_of_stake_bound {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit)
    (bounded : stake (fun v => balanceAt state v.toNat) (activeVoters state) < 2 ^ 64) :
    ∃ total, getTotalActiveBalance state = .ok total := by
  let amount := stake (fun v => balanceAt state v.toNat) (activeVoters state)
  have fits : max preset.EFFECTIVE_BALANCE_INCREMENT.toNat amount < 2 ^ 64 :=
    max_lt (UInt64.toNat_lt _) bounded
  refine ⟨(max preset.EFFECTIVE_BALANCE_INCREMENT.toNat amount).toUInt64, ?_⟩
  unfold getTotalActiveBalance
  rw [getActiveValidatorIndicesChecked_of_within within]
  apply getTotalBalance_ok_iff_stake.mpr
  refine ⟨?_, bounded, ?_⟩
  · intro v member
    obtain ⟨validator, found, _⟩ := (mem_getActiveValidatorIndices within).mp member
    exact (Array.getElem?_eq_some_iff.mp found).1
  · exact UInt64.toNat_ofNat_of_lt' fits

/-- Registry containment and an active total suffice for the non-full window's balance read. -/
private theorem filteredTotal_exists {state : BeaconState preset fork}
    {participants : Std.TreeSet ValidatorIndex} {total : Gwei}
    (read : getTotalActiveBalance state = .ok total)
    (inside : ∀ v ∈ participants, ∃ validator, validatorAt state v = .ok validator) :
    ∃ active result,
      participants.toList.filterM (fun index => do
        return isActiveValidator (← validatorAt state index) (getCurrentEpoch state)) =
        .ok active ∧ getTotalBalance state active = .ok result := by
  obtain ⟨active, filtered⟩ := filterM_exists_ok (test := fun index => do
    return isActiveValidator (← validatorAt state index) (getCurrentEpoch state))
    (list := participants.toList) (fun v member => by
      obtain ⟨validator, found⟩ := inside v (Std.TreeSet.mem_toList.mp member)
      exact ⟨isActiveValidator validator (getCurrentEpoch state), by simp [found]⟩)
  -- The filter passes only indices in the total's active set, even if they are slashed.
  obtain ⟨result, resultOk⟩ := totalBalance_exists_of_subset
    (indices := active) (getTotalActiveBalance_ok read) (fun v member => by
      have passed := passes_of_mem_filterM_ok filtered member
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at passed
      obtain ⟨validator, found, isActive⟩ := passed
      exact mem_getActiveValidatorIndices_of_isActiveAt
        (isActiveAt_eq_true_iff.mpr ⟨validator, validatorAt_ok_iff.mp found, isActive⟩))
  exact ⟨active, result, filtered, resultOk⟩

/-- The rule maximum succeeds once its range arithmetic, registry reads and total succeed. -/
private theorem maximum_exists_of_total {store : Store preset fork} {head : Root}
    {state : BeaconState preset fork} {first last : Slot}
    {participants : Std.TreeSet ValidatorIndex} {total : Gwei} {covered : Bool}
    (coverage : isFullValidatorSetCovered preset first last = .ok covered)
    (windowOk : store.getCommitteesBetweenSlots head first last = .ok participants)
    (totalOk : getTotalActiveBalance state = .ok total)
    (inside : ∀ v ∈ participants, ∃ validator, validatorAt state v = .ok validator) :
    ∃ maximum, store.computeCommitteeWeightBetweenSlots head state first last = .ok maximum := by
  by_cases empty : last < first
  · exact ⟨0, Store.computeCommitteeWeightBetweenSlots_of_gt empty⟩
  cases covered
  · obtain ⟨active, result, filtered, resultOk⟩ := filteredTotal_exists totalOk inside
    simp only [bind, Except.bind, pure, Except.pure] at filtered
    exact ⟨result, by
      simp only [Store.computeCommitteeWeightBetweenSlots, Store.computeCommitteeWeightAndMembers,
        empty, ↓reduceIte, coverage, bind, Except.bind, Bool.false_eq_true, windowOk,
        filtered, resultOk, Except.mapError, pure, Except.pure]⟩
  · exact ⟨total, by
      rw [Store.computeCommitteeWeightBetweenSlots_of_covered coverage]
      rw [totalOk]; rfl⟩

/-- A rule maximum transfers on the same window under equal activity and active weights.

The receiver must hold even the participants that its activity filter rejects. -/
private theorem maximum_transfer {caller receiver : Store preset fork} {head otherHead : Root}
    {source state : BeaconState preset fork} {first last : Slot} {maximum : Gwei}
    (within : state.RegistryWithinLimit)
    (read : caller.computeCommitteeWeightBetweenSlots head source first last = .ok maximum)
    (windows : ∀ participants, caller.getCommitteesBetweenSlots head first last = .ok participants →
      receiver.getCommitteesBetweenSlots otherHead first last = .ok participants)
    (inside : ∀ participants, caller.getCommitteesBetweenSlots head first last = .ok participants →
      ∀ v ∈ participants, ∃ validator, validatorAt state v = .ok validator)
    (activity : ∀ position, isActiveAt state (getCurrentEpoch state) position =
      isActiveAt source (getCurrentEpoch source) position)
    (weights : ∀ v ∈ getActiveValidatorIndices source (getCurrentEpoch source),
      balanceAt state v.toNat = balanceAt source v.toNat) :
    receiver.computeCommitteeWeightBetweenSlots otherHead state first last = .ok maximum := by
  by_cases empty : last < first
  · rw [Store.computeCommitteeWeightBetweenSlots_of_gt empty] at read ⊢
    exact read
  simp only [Store.computeCommitteeWeightBetweenSlots, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at read
  obtain ⟨⟨_, members⟩, read, rfl⟩ := read
  simp only [Store.computeCommitteeWeightAndMembers, empty, ↓reduceIte, bind_ok_iff] at read
  obtain ⟨covered, coverage, read⟩ := read
  cases covered
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok_iff, mapError_ok_iff,
      pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at read
    obtain ⟨participants, windowOk, active, filtered, total, totalOk, rfl, _⟩ := read
    obtain ⟨other, otherOk, transferred⟩ := filteredTotal_transfer filtered totalOk
      (inside participants windowOk) (fun v _ => activity v.toNat) (fun v member => by
        have pass := passes_of_mem_filterM_ok filtered member
        simp only [bind_ok_iff, Except.ok.injEq] at pass
        obtain ⟨validator, found, active⟩ := pass
        exact weights v (mem_getActiveValidatorIndices_of_isActiveAt
          (isActiveAt_eq_true_iff.mpr ⟨validator, validatorAt_ok_iff.mp found, active⟩)))
    simp only [bind, Except.bind, pure, Except.pure] at otherOk
    simp only [Store.computeCommitteeWeightBetweenSlots, Store.computeCommitteeWeightAndMembers,
      empty, ↓reduceIte, coverage, bind, Except.bind, Bool.false_eq_true,
      windows participants windowOk, otherOk, transferred, Except.mapError, pure, Except.pure]
  · simp only [↓reduceIte, bind_ok_iff, mapError_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at read
    obtain ⟨total, totalOk, rfl, _⟩ := read
    rw [Store.computeCommitteeWeightBetweenSlots_of_covered coverage]
    rw [activeTotal_transfer within totalOk activity weights]
    rfl

/-- A nonempty caller read supplies the start arithmetic for another range with the same start. -/
private theorem coverage_exists_of_maximum {store : Store preset fork} {head : Root}
    {state : BeaconState preset fork} {first last otherLast afterOther : Slot} {maximum : Gwei}
    (nonempty : first ≤ last)
    (read : store.computeCommitteeWeightBetweenSlots head state first last = .ok maximum)
    (afterOk : addChecked otherLast 1 = .ok afterOther) :
    ∃ covered, isFullValidatorSetCovered preset first otherLast = .ok covered := by
  have notEmpty : ¬last < first := UInt64.not_lt.mpr nonempty
  simp only [Store.computeCommitteeWeightBetweenSlots, bind_ok_iff] at read
  obtain ⟨result, read, -⟩ := read
  simp only [Store.computeCommitteeWeightAndMembers, notEmpty, ↓reduceIte,
    bind_ok_iff] at read
  obtain ⟨covered, coverage, -⟩ := read
  simp only [isFullValidatorSetCovered, bind_ok_iff, mapError_ok_iff] at coverage
  obtain ⟨afterFirst, firstOk, lastFirst, lastFirstOk, _, _, -⟩ := coverage
  refine ⟨decide (computeEpochAtSlot preset lastFirst < computeEpochAtSlot preset afterOther), ?_⟩
  simp only [isFullValidatorSetCovered, firstOk, lastFirstOk, afterOk, Except.mapError,
    bind, Except.bind, pure, Except.pure]

/-- The receiver reads the old maximum from its own bounded balance source.

The caller supplies range arithmetic, not balances or registry containment. -/
private theorem receiver_oldMaximum {caller receiver : Store preset fork}
    {head receiverHead : Root} {source state : BeaconState preset fork}
    {first oldLast last : Slot} {maximum total : Gwei}
    {window : Std.TreeSet ValidatorIndex}
    (read : caller.computeCommitteeWeightBetweenSlots head source first oldLast = .ok maximum)
    (windowOk : receiver.getCommitteesBetweenSlots receiverHead first last = .ok window)
    (before : oldLast ≤ last) (totalOk : getTotalActiveBalance state = .ok total)
    (inside : ∀ v ∈ window, ∃ validator, validatorAt state v = .ok validator) :
    ∃ result, receiver.computeCommitteeWeightBetweenSlots receiverHead state first oldLast =
      .ok result := by
  by_cases empty : oldLast < first
  · exact ⟨0, Store.computeCommitteeWeightBetweenSlots_of_gt empty⟩
  obtain ⟨members, membersOk, subset⟩ := committeeWindow_prefix windowOk before
  have afterRead := membersOk
  unfold Store.getCommitteesBetweenSlots at afterRead
  obtain ⟨afterOld, afterOk, _⟩ := bind_ok_iff.mp afterRead
  obtain ⟨covered, coverage⟩ := coverage_exists_of_maximum (UInt64.not_lt.mp empty) read
    (mapError_ok_iff.mp afterOk)
  exact maximum_exists_of_total coverage membersOk totalOk
    (fun v member => inside v (subset v member))

/-- A slot step within one epoch does not change the registry. -/
private theorem validators_advanceSlot_sameEpoch {state after : BeaconState preset fork}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (run : advanceSlot config checks state = .ok after)
    (same : getCurrentEpoch after = getCurrentEpoch state) :
    after.validators = state.validators := by
  obtain ⟨next, cached, epoched, nextNat, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok run
  have inside : next % preset.SLOTS_PER_EPOCH ≠ 0 := by
    intro boundary
    have rem : next.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      simpa only [UInt64.toNat_mod, UInt64.toNat_zero] using congrArg UInt64.toNat boundary
    have equal : next.toNat / preset.SLOTS_PER_EPOCH.toNat =
        state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      simpa only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div] using
        congrArg UInt64.toNat same
    have beforeRem := Nat.mod_lt state.slot.toNat positive
    have before := Nat.mod_add_div state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    have after := Nat.mod_add_div next.toNat preset.SLOTS_PER_EPOCH.toNat
    rw [rem, equal] at after
    omega
  simp only [epochIfLast, inside, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochedOk
  subst epoched
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  rfl

/-- No epoch transition occurs between equal endpoint epochs of a slot-only run. -/
private theorem validators_advanceSlots_sameEpoch (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    {count : Nat} {state after : BeaconState preset fork}
    (run : advanceSlots config checks count state = .ok after)
    (same : getCurrentEpoch after = getCurrentEpoch state) :
    after.validators = state.validators := by
  induction count generalizing state with
  | zero =>
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at run
    subst after
    rfl
  | succ count ih =>
    obtain ⟨middle, first, rest⟩ := bind_ok_iff.mp run
    have low := (runKept_advanceSlot first).later
    have high : getCurrentEpoch middle ≤ getCurrentEpoch after := by
      rw [UInt64.le_iff_toNat_le, getCurrentEpoch_toNat, getCurrentEpoch_toNat]
      exact Nat.div_le_div_right (by rw [advanceSlots_slot count rest]; omega)
    have middleEq : getCurrentEpoch middle = getCurrentEpoch state :=
      UInt64.le_antisymm (same ▸ high) low
    exact (ih rest (same.trans middleEq.symm)).trans
      (validators_advanceSlot_sameEpoch positive first middleEq)

/-- A same-epoch lookahead preserves both the active total read and every slashing flag. -/
private theorem lookahead_sameEpoch_frame {state after : BeaconState preset fork} {slot : Slot}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (run : lookaheadState config checks state slot = .ok after)
    (same : getCurrentEpoch after = getCurrentEpoch state) :
    getTotalActiveBalance after = getTotalActiveBalance state ∧
      ∀ v, NotSlashed after v ↔ NotSlashed state v := by
  have validators : after.validators = state.validators := by
    unfold lookaheadState at run
    split at run
    · have slotsOk := mapError_ok_iff.mp run
      simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
      obtain ⟨_, _, advanced⟩ := slotsOk
      exact validators_advanceSlots_sameEpoch positive advanced same
    · cases run
      rfl
  constructor
  · simp only [getTotalActiveBalance, getActiveValidatorIndicesChecked, getTotalBalance,
      validators, same]
  · intro v
    simp only [NotSlashed, validators]

/-- Updating a validator preserves any unchanged projection of the registry. -/
private theorem registryMap_setValidatorAt {α : Type} (project : Validator → α)
    {state after : BeaconState preset fork} {position : Nat} {v old : Validator}
    (found : getValidatorAt state position = .ok old)
    (set : state.setValidatorAt position v = .ok after) (same : project v = project old) :
    after.validators.data.toList.map project = state.validators.data.toList.map project := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldEq : state.validators.data[position] = old := by
    simpa [getValidatorAt, inside] using found
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.toList_set, List.map_set]
  rw [same, ← oldEq]
  have atValue : (state.validators.data.toList.map project)[position]'(by simpa using inside) =
      project state.validators.data[position] := by simp
  rw [← atValue]
  exact List.set_getElem_self _

/-- Exit scheduling does not change effective balances or slashing flags. -/
private theorem balanceFlags_initiateValidatorExit {state after : BeaconState preset fork}
    {index : ValidatorIndex}
    (run : initiateValidatorExit config state index = .ok after) :
    after.validators.data.toList.map (fun v => (v.effectiveBalance, v.slashed)) =
      state.validators.data.toList.map (fun v => (v.effectiveBalance, v.slashed)) := by
  obtain ⟨v, found, unchanged | ⟨_, queued, epoch, withdrawal, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok run
  · rw [unchanged.2]
  · have same := (exitQueue_validators queue).1
    have kept := registryMap_setValidatorAt (fun v => (v.effectiveBalance, v.slashed))
      (by rw [← getValidator_eq_getValidatorAt, getValidator_of_validators_eq same]; exact found)
      (by rwa [← setValidator_eq_setValidatorAt]) (by rfl)
    exact kept.trans (by rw [same])

/-- Registry updates schedule future activity without changing balances or slashing flags. -/
private theorem balanceFlags_processRegistryUpdates {state after : BeaconState preset fork}
    (run : processRegistryUpdates config state = .ok after) :
    after.validators.data.toList.map (fun v => (v.effectiveBalance, v.slashed)) =
      state.validators.data.toList.map (fun v => (v.effectiveBalance, v.slashed)) := by
  let R (s t : BeaconState preset fork) :=
    t.validators.data.toList.map (fun v => (v.effectiveBalance, v.slashed)) =
      s.validators.data.toList.map (fun v => (v.effectiveBalance, v.slashed))
  have folded {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
      {xs : List α} {s t : BeaconState preset fork}
      (keeps : ∀ s x t, step s x = .ok t → R s t)
      (ok : xs.foldlM step s = .ok t) : R s t :=
    foldlM_ok_invariant (R s) (fun _ _ _ before ok => (keeps _ _ _ ok).trans before) rfl ok
  have update {s t : BeaconState preset fork} {i : Nat}
      (ok : updateRegistryEntry config s i = .ok t) : R s t := by
    simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨v, found, queued, queue, marked, set, ok⟩ := ok
    have fields : (queued.effectiveBalance, queued.slashed) = (v.effectiveBalance, v.slashed) := by
      unfold queueForActivation at queue
      split at queue
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queue
        obtain ⟨_, _, rfl⟩ := queue
        rfl
      · cases queue; rfl
    have first := registryMap_setValidatorAt (fun v => (v.effectiveBalance, v.slashed))
      found set fields
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, exited⟩ := ok
      exact (balanceFlags_initiateValidatorExit exited).trans first
    · cases ok; exact first
  have activate {s t : BeaconState preset fork} {i : ValidatorIndex}
      (ok : activateValidator s i = .ok t) : R s t := by
    simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, found, _, _, set⟩ := ok
    rw [setValidator_eq_setValidatorAt] at set
    rw [getValidator_eq_getValidatorAt] at found
    exact registryMap_setValidatorAt (fun v => (v.effectiveBalance, v.slashed))
      found set rfl
  have updateElectra {s t : BeaconState preset fork} {epoch : Epoch} {i : Nat}
      (ok : updateRegistryEntryElectra config epoch s i = .ok t) : R s t := by
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, found, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, set⟩ := ok
      exact registryMap_setValidatorAt _ found set rfl
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, exited⟩ := ok
      exact balanceFlags_initiateValidatorExit exited
    split at ok
    · exact registryMap_setValidatorAt _ found (liftAccessor_ok.mp ok) rfl
    · cases ok; rfl
  unfold processRegistryUpdates at run
  split at run
  · simp only [bind_ok_iff, liftAccessor_ok] at run
    obtain ⟨_, _, run⟩ := run
    exact folded (fun _ _ _ ok => updateElectra ok) run
  · simp only [bind_ok_iff] at run
    obtain ⟨_, updated, activated⟩ := run
    exact (folded (fun _ _ _ ok => activate ok) activated).trans
      (folded (fun _ _ _ ok => update ok) updated)

/-- Rewards change actual balances, not the validator records used by the active total. -/
private theorem validators_processRewardsAndPenalties {state after : BeaconState preset fork}
    (run : processRewardsAndPenalties config state = .ok after) :
    after.validators = state.validators := by
  have deltas {s t : BeaconState preset fork} {rewards penalties : Array Gwei} {index : Nat}
      (ok : applyDeltas rewards penalties s index = .ok t) : t.validators = s.validators := by
    simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, raised, lowered⟩ := ok
    exact (decreaseBalance_validators lowered).trans (increaseBalance_validators raised)
  have allDeltas {s t : BeaconState preset fork} {ds : Array Gwei × Array Gwei}
      (ok : applyAllDeltas s ds = .ok t) : t.validators = s.validators :=
    foldlM_ok_invariant (fun t => t.validators = s.validators)
      (fun _ _ _ before ok => (deltas ok).trans before) rfl ok
  unfold processRewardsAndPenalties at run
  split at run
  · cases run; rfl
  split at run
  · simp only [bind_ok_iff] at run
    obtain ⟨_, _, _, _, applied⟩ := run
    exact foldlM_ok_invariant (fun t => t.validators = state.validators)
      (fun _ _ _ before ok => (allDeltas ok).trans before) rfl applied
  · simp only [bind_ok_iff] at run
    obtain ⟨_, _, applied⟩ := run
    exact allDeltas applied

/-- Inactivity scoring changes only the inactivity scores. -/
private theorem validators_processInactivityUpdates {state after : BeaconState preset fork}
    {altair : .altair ≤ fork}
    (run : processInactivityUpdates config state altair = .ok after) :
    after.validators = state.validators := by
  unfold processInactivityUpdates at run
  split at run
  · cases run; rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at run
    obtain ⟨_, _, _, _, rfl⟩ := run
    rfl

/-- The epoch prefix before slashings preserves effective balances and slashing flags.

Registry updates may schedule activation and exit, but neither changes these fields. -/
private theorem balanceFlags_epochPrefix {state justified scored rewarded registered :
    BeaconState preset fork}
    (justifiedOk : processJustificationAndFinalization state = .ok justified)
    (scoredOk : (if altair : .altair ≤ fork then
      processInactivityUpdates config justified altair else pure justified) = .ok scored)
    (rewardedOk : processRewardsAndPenalties config scored = .ok rewarded)
    (registeredOk : processRegistryUpdates config rewarded = .ok registered) :
    registered.validators.data.toList.map (fun v => (v.effectiveBalance, v.slashed)) =
      state.validators.data.toList.map (fun v => (v.effectiveBalance, v.slashed)) := by
  have scored : scored.validators = justified.validators := by
    split at scoredOk
    · exact validators_processInactivityUpdates scoredOk
    · cases scoredOk; rfl
  rw [balanceFlags_processRegistryUpdates registeredOk,
    validators_processRewardsAndPenalties rewardedOk, scored,
    (processJustificationAndFinalization_keeps justifiedOk).2.2.2.2.2.1]

/-- The active total checked by slashings is also a checked total before the epoch prefix. -/
private theorem activeTotal_before_epochPrefix {state justified scored rewarded registered :
    BeaconState preset fork} {total : Gwei}
    (within : state.RegistryWithinLimit)
    (justifiedOk : processJustificationAndFinalization state = .ok justified)
    (scoredOk : (if altair : .altair ≤ fork then
      processInactivityUpdates config justified altair else pure justified) = .ok scored)
    (rewardedOk : processRewardsAndPenalties config scored = .ok rewarded)
    (registeredOk : processRegistryUpdates config rewarded = .ok registered)
    (read : getTotalActiveBalance registered = .ok total) :
    getTotalActiveBalance state = .ok total := by
  have scoredFrame : ActiveStep justified scored := by
    split at scoredOk
    · exact (stepKeeps_processInactivityUpdates scoredOk).2
    · cases scoredOk; exact ActiveStep.refl _
  have frame : ActiveStep state registered :=
    (stepKeeps_processJustificationAndFinalization justifiedOk).2.trans <|
      scoredFrame.trans <| (activeStep_processRewardsAndPenalties rewardedOk).trans
        (stepKeeps_processRegistryUpdates registeredOk).2
  have epoch : getCurrentEpoch registered = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.1]
  have fields := balanceFlags_epochPrefix justifiedOk scoredOk rewardedOk registeredOk
  apply activeTotal_transfer within read
  · intro i
    rw [epoch]
    exact (frame.2 _ (getCurrentEpoch_le_activityFixedEpoch state) i).symm
  · intro v _
    have atIndex := congrArg (fun xs => xs[v.toNat]?) fields
    have weights := congrArg (fun x => (x.map (fun p => p.1.toNat)).getD 0) atIndex
    simpa only [List.getElem?_map, Array.getElem?_toList, Option.map_map,
      Function.comp_def, balanceAt] using weights.symm

/-- Every successful epoch transition checks its incoming active total, including epoch zero.

The slashings step reads the total before effective balances change. -/
private theorem activeTotal_of_processEpoch {state after : BeaconState preset fork}
    (within : state.RegistryWithinLimit)
    (run : processEpoch config checks state = .ok after) :
    ∃ total, getTotalActiveBalance state = .ok total := by
  have slashings {s t : BeaconState preset fork}
      (ok : processSlashings s = .ok t) : ∃ total, getTotalActiveBalance s = .ok total := by
    unfold processSlashings at ok
    simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨total, read, _⟩ := ok
    exact ⟨total, read⟩
  unfold processEpoch at run
  split at run
  · unfold processEpochAltair at run
    simp only [bind_ok_iff] at run
    obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk,
      registered, registeredOk, slashed, slashedOk, _⟩ := run
    obtain ⟨total, read⟩ := slashings slashedOk
    refine ⟨total, activeTotal_before_epochPrefix within justifiedOk ?_
      rewardedOk registeredOk read⟩
    simp only [dite_eq_left ‹.altair ≤ fork›]
    exact scoredOk
  · simp only [bind_ok_iff] at run
    obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk,
      slashed, slashedOk, _⟩ := run
    obtain ⟨total, read⟩ := slashings slashedOk
    refine ⟨total, activeTotal_before_epochPrefix within justifiedOk ?_
      rewardedOk registeredOk read⟩
    simp only [dite_eq_right ‹¬ .altair ≤ fork›, pure, Except.pure]

/-- A slot run that leaves its starting epoch has checked the starting active total. -/
private theorem activeTotal_of_advanceSlots_epoch_lt {state after : BeaconState preset fork}
    {count : Nat} (preGloas : fork < .glamsterdam)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (run : advanceSlots config checks count state = .ok after)
    (later : getCurrentEpoch state < getCurrentEpoch after) :
    ∃ total, getTotalActiveBalance state = .ok total := by
  induction count generalizing state with
  | zero =>
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at run
    subst after
    exact False.elim ((UInt64.lt_irrefl _) later)
  | succ count ih =>
    obtain ⟨middle, first, rest⟩ := bind_ok_iff.mp run
    by_cases same : getCurrentEpoch middle = getCurrentEpoch state
    · obtain ⟨total, read⟩ := ih rest (by rwa [same])
      have validators := validators_advanceSlot_sameEpoch positive first same
      refine ⟨total, ?_⟩
      simpa only [getTotalActiveBalance, getActiveValidatorIndicesChecked, getTotalBalance,
        validators, same] using read
    · obtain ⟨next, cached, epoched, nextNat, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok first
      obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
      unfold epochIfLast at epochedOk
      split at epochedOk
      · obtain ⟨total, read⟩ := activeTotal_of_processEpoch (cached.validators.bound preGloas)
          epochedOk
        refine ⟨total, ?_⟩
        rw [cachedEq] at read
        exact read
      · rename_i noBoundary
        cases epochedOk
        have quotient : next.toNat / preset.SLOTS_PER_EPOCH.toNat =
            state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
          have rem : next.toNat % preset.SLOTS_PER_EPOCH.toNat ≠ 0 := by
            intro eq
            apply noBoundary
            apply UInt64.toNat_inj.mp
            simpa only [UInt64.toNat_mod, UInt64.toNat_zero] using eq
          rw [nextNat] at rem ⊢
          exact Nat.succ_div_of_mod_ne_zero rem
        apply False.elim
        apply same
        apply UInt64.toNat_inj.mp
        simpa only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div] using quotient

/-- A lookahead into a later epoch supplies a checked total for its held starting state. -/
private theorem activeTotal_of_lookahead_epoch_lt {state after : BeaconState preset fork}
    {slot : Slot} (preGloas : fork < .glamsterdam)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (run : lookaheadState config checks state slot = .ok after)
    (later : getCurrentEpoch state < getCurrentEpoch after) :
    ∃ total, getTotalActiveBalance state = .ok total := by
  unfold lookaheadState at run
  split at run
  · have slotsOk := mapError_ok_iff.mp run
    simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
    obtain ⟨_, _, advanced⟩ := slotsOk
    exact activeTotal_of_advanceSlots_epoch_lt preGloas positive advanced later
  · cases run
    exact False.elim ((UInt64.lt_irrefl _) later)

/-- Slot processing preserves the slashing flag at every index, including absent indices. -/
private def SlashFlagsKept (state after : BeaconState preset fork) : Prop :=
  ∀ i : Nat, (after.validators.data[i]?.map (·.slashed)).getD false =
    (state.validators.data[i]?.map (·.slashed)).getD false

private theorem slashFlags_of_validators {state after : BeaconState preset fork}
    (same : after.validators.data = state.validators.data := by rfl) :
    SlashFlagsKept state after := by intro i; simp only [same]

private theorem slashFlags_of_map {state after : BeaconState preset fork}
    (same : after.validators.data.toList.map (·.slashed) =
      state.validators.data.toList.map (·.slashed)) : SlashFlagsKept state after := by
  intro i
  have atIndex := congrArg (fun xs => (xs[i]?).getD false) same
  simpa only [List.getElem?_map, Array.getElem?_toList] using atIndex

private theorem SlashFlagsKept.trans {first second third : BeaconState preset fork}
    (one : SlashFlagsKept first second) (two : SlashFlagsKept second third) :
    SlashFlagsKept first third := fun i => (two i).trans (one i)

private theorem slashFlags_fold {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    {xs : List α} {state after : BeaconState preset fork}
    (keeps : ∀ s x t, step s x = .ok t → SlashFlagsKept s t)
    (ok : xs.foldlM step state = .ok after) : SlashFlagsKept state after :=
  foldlM_ok_invariant (SlashFlagsKept state)
    (fun _ _ _ before ok => before.trans (keeps _ _ _ ok)) (fun _ => rfl) ok

/-- Slashings collect balance penalties without changing any validator record. -/
private theorem validators_processSlashings {state after : BeaconState preset fork}
    (run : processSlashings state = .ok after) : after.validators = state.validators := by
  have penalty {s t : BeaconState preset fork} {total adjusted : Gwei} {i : Nat}
      (ok : applySlashingPenalty s total adjusted i = .ok t) : t.validators = s.validators := by
    simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, _, _, _, _, lowered⟩ := ok
        exact decreaseBalance_validators lowered
      · cases ok; rfl
    · cases ok; rfl
  have penaltyElectra {s t : BeaconState preset fork} {perIncrement : Gwei} {i : Nat}
      (ok : applySlashingPenaltyElectra s perIncrement i = .ok t) :
      t.validators = s.validators := by
    simp only [applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, _, _, lowered⟩ := ok
        exact decreaseBalance_validators lowered
      · cases ok; rfl
    · cases ok; rfl
  unfold processSlashings at run
  simp only [bind_ok_iff] at run
  obtain ⟨_, _, _, _, _, _, run⟩ := run
  split at run
  · simp only [bind_ok_iff] at run
    obtain ⟨_, _, applied⟩ := run
    exact foldlM_ok_invariant (fun s => s.validators = state.validators)
      (fun _ _ _ before ok => (penaltyElectra ok).trans before) rfl applied
  · exact foldlM_ok_invariant (fun s => s.validators = state.validators)
      (fun _ _ _ before ok => (penalty ok).trans before) rfl run

/-- A newly deposited validator is unslashed, so absence and insertion have the same flag. -/
private theorem slashFlags_addValidator {state after : BeaconState preset fork}
    {pubkey : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (run : addValidatorToRegistry state pubkey credentials amount = .ok after) :
    SlashFlagsKept state after := by
  have added := addValidatorToRegistry_validators_eq_push run
  intro i
  rw [added]
  by_cases before : i < state.validators.data.size
  · simp [Array.getElem?_push, before, Nat.ne_of_lt before]
  · by_cases atEnd : i = state.validators.data.size
    · subst i
      simp [getValidatorFromDeposit]
    · simp [Array.getElem?_push, before, atEnd]

/-- Pending deposits either credit a balance or append an unslashed validator. -/
private theorem slashFlags_applyPendingDeposit {state after : BeaconState preset fork}
    {deposit : PendingDeposit}
    (run : applyPendingDeposit config checks state deposit = .ok after) :
    SlashFlagsKept state after := by
  unfold applyPendingDeposit at run
  split at run
  · split at run
    · cases run; exact slashFlags_of_validators
    simp only [bind_ok_iff] at run
    obtain ⟨_, _, run⟩ := run
    split at run
    · exact slashFlags_addValidator run
    · cases run; exact slashFlags_of_validators
  · simp only [liftAccessor_ok, bind_ok_iff] at run
    obtain ⟨_, _, run⟩ := run
    exact slashFlags_of_validators (congrArg (·.data) (increaseBalance_validators run))

/-- Passing pending deposits preserves the default-false flag even when the registry grows. -/
private theorem slashFlags_passPendingDeposits {stop : PendingDeposit → Bool}
    {nextEpoch : Epoch} {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count
        postponed deposits = .ok pass → SlashFlagsKept state pass.1.state
  | [], _, _, _, _, _, ok => by
    cases ok; exact slashFlags_of_validators
  | deposit :: rest, state, processed, count, postponed, pass, ok => by
    unfold passPendingDeposits at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    split at ok
    · cases ok; exact slashFlags_of_validators
    split at ok
    · cases ok
    split at ok
    · split at ok
      · cases ok
      rename_i credited
      split at ok
      · cases ok
      cases ok
      exact (slashFlags_applyPendingDeposit credited).trans
        (slashFlags_passPendingDeposits (deposits := rest) ‹_›)
    split at ok
    · split at ok
      · cases ok
      cases ok
      exact slashFlags_passPendingDeposits (deposits := rest) ‹_›
    split at ok
    · cases ok
    split at ok
    · cases ok; exact slashFlags_of_validators
    split at ok
    · cases ok
    rename_i credited
    split at ok
    · cases ok
    cases ok
    exact (slashFlags_applyPendingDeposit credited).trans
      (slashFlags_passPendingDeposits (deposits := rest) ‹_›)

private theorem slashFlags_processPendingBalances {state after : BeaconState preset fork}
    (run : processPendingBalances config checks state = .ok after) :
    SlashFlagsKept state after := by
  unfold processPendingBalances at run
  split at run
  · simp only [bind_ok_iff] at run
    obtain ⟨middle, deposited, consolidated⟩ := run
    have deposits : SlashFlagsKept state middle := by
      unfold processPendingDeposits at deposited
      simp only [bind, Except.bind, pure, Except.pure] at deposited
      repeat' (split at deposited <;> try cases deposited)
      all_goals exact (slashFlags_passPendingDeposits ‹_›).trans slashFlags_of_validators
    exact deposits.trans
      (slashFlags_of_validators (by rw [(processPendingConsolidations_kept consolidated).1]))
  · cases run; exact slashFlags_of_validators

private theorem slashFlags_processEffectiveBalanceUpdates {state after : BeaconState preset fork}
    (run : processEffectiveBalanceUpdates state = .ok after) : SlashFlagsKept state after := by
  apply slashFlags_fold (fun _ _ _ ok => ?_) run
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, _, _, _, _, set⟩ := ok
  exact slashFlags_of_map (registryMap_setValidatorAt (·.slashed) found set rfl)

private theorem slashFlags_epochTail {rooted synced looked after : BeaconState preset fork}
    {altair : .altair ≤ fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair)
      altair = .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : SlashFlagsKept rooted after := by
  have syncedStep : SlashFlagsKept rooted synced := by
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals exact slashFlags_of_validators
  have lookedStep : SlashFlagsKept synced looked := by
    split at lookedOk
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at lookedOk
      obtain ⟨_, _, _, _, rfl⟩ := lookedOk
      exact slashFlags_of_validators
    · cases lookedOk; exact slashFlags_of_validators
  have windowedStep : SlashFlagsKept looked after := by
    split at windowed
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at windowed
      obtain ⟨_, _, _, _, rfl⟩ := windowed
      exact slashFlags_of_validators
    · cases windowed; exact slashFlags_of_validators
  exact syncedStep.trans (lookedStep.trans windowedStep)

/-- Epoch processing cannot slash a validator, and newly appended validators are unslashed. -/
private theorem slashFlags_processEpoch {state after : BeaconState preset fork}
    (run : processEpoch config checks state = .ok after) : SlashFlagsKept state after := by
  have initial {s j c r t : BeaconState preset fork}
      (justified : processJustificationAndFinalization s = .ok j)
      (scored : (if altair : .altair ≤ fork then processInactivityUpdates config j altair
        else pure j) = .ok c)
      (rewarded : processRewardsAndPenalties config c = .ok r)
      (registered : processRegistryUpdates config r = .ok t) : SlashFlagsKept s t := by
    apply slashFlags_of_map
    have fields := congrArg (List.map Prod.snd)
      (balanceFlags_epochPrefix justified scored rewarded registered)
    simpa only [List.map_map, Function.comp_def] using fields
  have reset {s t : BeaconState preset fork} {before : fork < .hegota}
      (ok : processEth1DataReset before s = .ok t) : SlashFlagsKept s t := by
    simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok <;> cases ok <;> exact slashFlags_of_validators
  have clear {s t : BeaconState preset fork}
      (ok : processSlashingsReset s = .ok t) : SlashFlagsKept s t := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq ok
    exact slashFlags_of_validators
  have mix {s t : BeaconState preset fork}
      (ok : processRandaoMixesReset s = .ok t) : SlashFlagsKept s t := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq ok
    exact slashFlags_of_validators
  have roots {s t : BeaconState preset fork}
      (ok : processHistoricalRootsUpdate s = .ok t) : SlashFlagsKept s t := by
    unfold processHistoricalRootsUpdate at ok
    split at ok
    · cases ok
    simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨_, _, _, _, rfl⟩ := ok
      exact slashFlags_of_validators
    · cases ok; exact slashFlags_of_validators
  unfold processEpoch at run
  split at run
  · unfold processEpochAltair at run
    simp only [bind_ok_iff] at run
    obtain ⟨_, justified, _, scored, _, rewarded, _, registered, slashedState, slashed,
      resetState, resetOk, pending, pendingOk, paid, paidOk, _, balanced, _, cleared,
      mixed, mixedOk, run⟩ := run
    have resetStep : SlashFlagsKept slashedState resetState := by
      split at resetOk
      · exact reset resetOk
      · cases resetOk; exact slashFlags_of_validators
    have paidStep : SlashFlagsKept pending paid := by
      split at paidOk
      · simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff,
          pure, Except.pure, Except.ok.injEq] at paidOk
        obtain ⟨_, _, rfl⟩ := paidOk
        exact slashFlags_of_validators
      · cases paidOk; exact slashFlags_of_validators
    have first : SlashFlagsKept state mixed :=
      (initial justified (by simpa only [dite_eq_left ‹.altair ≤ fork›] using scored)
        rewarded registered).trans <|
      (slashFlags_of_validators (congrArg (·.data) (validators_processSlashings slashed))).trans <|
      resetStep.trans <| (slashFlags_processPendingBalances pendingOk).trans <| paidStep.trans <|
      (slashFlags_processEffectiveBalanceUpdates balanced).trans <| (clear cleared).trans <|
      mix mixedOk
    split at run <;> simp only [bind_ok_iff] at run <;>
      obtain ⟨rootedState, rooted, _, synced, _, looked, windowed⟩ := run
    · have rootedStep : SlashFlagsKept mixed rootedState := by
        unfold processHistoricalSummariesUpdate at rooted
        simp only [bind, Except.bind, pure, Except.pure] at rooted
        repeat' (split at rooted <;> try cases rooted)
        all_goals exact slashFlags_of_validators
      exact first.trans (rootedStep.trans (slashFlags_epochTail synced looked windowed))
    · exact first.trans ((roots rooted).trans (slashFlags_epochTail synced looked windowed))
  · simp only [bind_ok_iff] at run
    obtain ⟨_, justified, _, rewarded, _, registered, _, slashed, _, resetOk, _, balanced,
      _, cleared, _, mixed, rooted, rootedOk, rotated⟩ := run
    have last : SlashFlagsKept rooted after := by
      unfold processParticipationRecordUpdates at rotated
      split at rotated
      · cases rotated
      · cases rotated; exact slashFlags_of_validators
    exact (initial justified (by simp only [dite_eq_right ‹¬ .altair ≤ fork›]; rfl)
      rewarded registered).trans <|
      (slashFlags_of_validators (congrArg (·.data) (validators_processSlashings slashed))).trans <|
      (reset resetOk).trans <| (slashFlags_processEffectiveBalanceUpdates balanced).trans <|
      (clear cleared).trans <| (mix mixed).trans <| (roots rootedOk).trans last

/-- Slot-only lookahead preserves unslashedness at every index, across any number of epochs. -/
private theorem notSlashed_lookahead {state after : BeaconState preset fork} {slot : Slot}
    (run : lookaheadState config checks state slot = .ok after) :
    ∀ v, NotSlashed after v ↔ NotSlashed state v := by
  have step {s t : BeaconState preset fork}
      (ok : advanceSlot config checks s = .ok t) : SlashFlagsKept s t := by
    obtain ⟨_, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
    obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
    have first : SlashFlagsKept s cached := slashFlags_of_validators (by rw [cachedEq])
    have middle : SlashFlagsKept cached epoched := by
      unfold epochIfLast at epochedOk
      split at epochedOk
      · exact slashFlags_processEpoch epochedOk
      · cases epochedOk; exact slashFlags_of_validators
    exact (first.trans middle).trans slashFlags_of_validators
  have steps {count : Nat} {s t : BeaconState preset fork}
      (ok : advanceSlots config checks count s = .ok t) : SlashFlagsKept s t := by
    induction count generalizing s with
    | zero => cases ok; exact slashFlags_of_validators
    | succ count ih =>
      obtain ⟨_, first, rest⟩ := bind_ok_iff.mp ok
      exact (step first).trans (ih rest)
  have flags : SlashFlagsKept state after := by
    unfold lookaheadState at run
    split at run
    · have slotsOk := mapError_ok_iff.mp run
      simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
      obtain ⟨_, _, advanced⟩ := slotsOk
      exact steps advanced
    · cases run; exact slashFlags_of_validators
  intro v
  unfold NotSlashed
  rw [flags v.toNat]

/-- After the first two epochs, a successful justification step has checked the active total. -/
private theorem activeTotal_of_justification {state after : BeaconState preset fork}
    (late : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1)
    (run : processJustificationAndFinalization state = .ok after) :
    ∃ total, getTotalActiveBalance state = .ok total := by
  unfold processJustificationAndFinalization at run
  split at run
  · simp only [processJustificationAndFinalizationAltair, late, ↓reduceIte,
      bind_ok_iff, liftAccessor_ok] at run
    obtain ⟨_, _, _, _, total, totalOk, _⟩ := run
    exact ⟨total, totalOk⟩
  · simp only [bind_ok_iff, liftAccessor_ok] at run
    obtain ⟨_, _, _, _, total, totalOk, _⟩ := run
    exact ⟨total, totalOk⟩

/-- The cached anchor checkpoint remains exactly the anchor state, not an arbitrary lookahead. -/
private theorem anchor_checkpointState {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {last : ℕ}
    (oneBlock : OneBlockPerRoot e last)
    {w : ValidatorIndex} (honest : w ∈ J) {k : Nat} (bounded : (e.world k).time ≤ last)
    {state : BeaconState preset fork}
    (read : ((e.world k).state w).checkpointState anchor.justifiedCheckpoint = .ok state) :
    state = anchorState := by
  obtain ⟨root, rootOk, cached⟩ := getForkchoiceStore_checkpointStates anchored
  obtain ⟨other, otherOk, _, _, justified, _, _, _⟩ := getForkchoiceStore_anchor anchored
  have roots : other = root := Except.ok.inj (otherOk.symm.trans rootOk)
  subst other
  have initial : ((e.world 0).state w).checkpointStates[anchor.justifiedCheckpoint]? =
      some anchorState := by
    simp [Execution.world_zero, World.initial, start w honest, justified, cached]
  exact e.checkpointStates_eq_of_oneBlock anchored start oneBlock honest honest bounded
    ((e.monotone_time (Nat.zero_le k)).trans bounded)
    (Store.checkpointState_ok_iff.mp read) initial

variable [DecidablePred (· ∈ J)]

/-- Step 5, the initial transport: the bound of step 4 holds in each honest store at a later time.

The caller is an honest validator whose store is up to date and holds the bound of step 4.

Its ranges of committees end at the slot before its own, and at the slot before the block.

The call is at the start of its slot.

Its source of balances is the state of a checkpoint of its store, as `sourceOk` says.

So every honest vote of an earlier slot of the current epoch falls in the window below.

The block is on the chain of the head of the caller.

The historical block is on the chain of the parent of the block.

It is of the current epoch of the caller or of the epoch before.

It is safe at each time from the start of the current epoch to just before the call.

The receiver is an honest validator whose store is up to date at the later time.

Its head descends from the parent of the block.

Its current epoch is at most two epochs after the epoch of the parent.

Its finalized checkpoints up to that time agree with the block, as `rootFinal` says.

No honest validator is slashed in a state that an honest store counts, as `unslashed` says.

The tally state of the receiver is a lookahead of a held state, and need not be a counting state.

The window of the receiver is the committees of its head between the parent and its own slot.

The conclusion bounds the active members of that window, as `HeadFollowsSupport` reads it.

The preset bounds are sufficient for this argument; they are not claimed to be necessary.

The proof follows three lemmas of [verified-fast-confirmation][vfc].

Two are `honest_supporters_sum_le_Sval_window` and `weak_base_discharged_window`.

The third is `bval_endpoint_strip_window_uniform`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem Execution.honest_support_of_historical_anchor {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (lookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat ∧ 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat ∧
      preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam) {time : ℕ} (admitted : BlocksAdmitted e 0 Δ time)
    (oneBlock : OneBlockPerRoot e time)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (votes : Votes e.startTime time e) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e time) (committees : CommitteesFollow e time) {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (anchored : ∀ w ∈ J, e.start w = anchor) (noVotes : anchor.latestMessages.isEmpty)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (upToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    {head root : Root} {balanceSource : BeaconState preset fork}
    {slot firstSlot lastSlot beforeBlock : Slot} {block parentBlock : BeaconBlock preset fork}
    {parentParticipants : Std.TreeSet ValidatorIndex} {proposerScore maximumSupport : Gwei}
    (callerHead : ∃ node, ((e.world n).state u).getHead config = .ok node ∧ node.root = head)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    {begin : UInt64} (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (atSlot : (e.world n).time = begin.toNat)
    (blockOk : ((e.world n).state u).block root = .ok block)
    (parentOk : ((e.world n).state u).block block.parentRoot = .ok parentBlock)
    {sourceCheckpoint : Checkpoint}
    (sourceOk : ((e.world n).state u).checkpointState sourceCheckpoint = .ok balanceSource)
    (boostOk : computeProposerScore config balanceSource = .ok proposerScore)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked slot 1 = .ok lastSlot)
    (beforeOk : subChecked block.slot 1 = .ok beforeBlock)
    (maximumOk : ((e.world n).state u).computeCommitteeWeightBetweenSlots head balanceSource
      firstSlot lastSlot = .ok maximumSupport)
    (parentParticipantsOk : ((e.world n).state u).getCommitteesBetweenSlots head firstSlot
      beforeBlock = .ok parentParticipants)
    {shift : ℕ} {support discount adversary : Gwei}
    (within : balanceSource.RegistryWithinLimit) (aligned : EffectiveBalancesAligned balanceSource)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (supportOk : ((e.world n).state u).scoreFromTally
      (((e.world n).state u).tallyVotes balanceSource) ⟨root, .pending⟩ = .ok support)
    (discountOk : ((e.world n).state u).computeEmptySlotSupportDiscount config head balanceSource
      root = .ok discount)
    (adversaryOk : ((e.world n).state u).getAdversarialWeight config head balanceSource root =
      .ok adversary)
    (confirmed : ((e.world n).state u).isOneConfirmed config head balanceSource
      (((e.world n).state u).tallyVotes balanceSource) root = .ok true)
    (base : maximumSupport.toNat + proposerScore.toNat + 2 * adversary.toNat + shift <
      discount.toNat + 2 * support.toNat)
    (later : (e.world n).time ≤ time)
    (weights : WeightBounds e balanceSource (e.world n).time time shift)
    {horizon : Epoch} (chain : FinalizedPrefix e horizon time)
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ time →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      (e.world k).time ≤ time → ((e.world k).state w).Counts config state →
      getCurrentEpoch state ≤ horizon →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (few : ∀ w ∈ J, ∀ k (state : BeaconState preset fork) total,
      (e.world k).time ≤ time → ((e.world k).state w).Counts config state →
      getCurrentEpoch state ≤ horizon → getTotalActiveBalance state = .ok total →
      3 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | v ∉ J} <
        2 * total.toNat)
    (unslashed : ∀ w ∈ J, ∀ k (state : BeaconState preset fork), (e.world k).time ≤ time →
      ((e.world k).state w).Counts config state → ∀ v ∈ J, NotSlashed state v)
    (supply : ∀ w ∈ J, ∀ k (checkpoint : Checkpoint) (state : BeaconState preset fork),
      (e.world k).time ≤ time → ((e.world k).state w).checkpointState checkpoint = .ok state →
      stake (fun v => balanceAt state v.toNat) (activeVoters state) ≤ stakeCapGwei)
    (safe : ∀ earlier, (e.world n).time ≤ earlier → earlier < time → SafeAt e earlier root)
    (rootOnHead : ((e.world n).state u).isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true)
    {historical : Root} {callerEpoch historicalEpoch : Epoch} {epochStart : Slot}
    {epochStartTime : UInt64}
    (below : ((e.world n).state u).isAncestor ⟨block.parentRoot, .pending⟩
      ⟨historical, .pending⟩ = .ok true)
    (callerEpochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok callerEpoch)
    (historicalEpochOk : ((e.world n).state u).getBlockEpoch historical = .ok historicalEpoch)
    (recent : callerEpoch.toNat ≤ historicalEpoch.toNat + 1)
    (epochStartOk : computeStartSlotAtEpoch preset callerEpoch = .ok epochStart)
    (epochStartTimeOk : computeTimeAtSlotMs config genesisTimeMs epochStart = .ok epochStartTime)
    (historicalSafe : ∀ earlier, epochStartTime.toNat ≤ earlier → earlier < (e.world n).time →
      SafeAt e earlier historical)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (atTime : (e.world k).time = time)
    (receiverUpToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (known : ((e.world k).state w).blocks[root]? = some block)
    (rootFinal : ∀ k' ≤ k,
      UpToDate config checks sources (e.world k').time ((e.world k').view w)
        ((e.world k').state w) →
      (∃ boundary,
        computeStartSlotAtEpoch preset ((e.world k').state w).finalizedCheckpoint.epoch =
          .ok boundary ∧ boundary ≤ block.slot ∧
        ((e.world k).state w).getCheckpointBlock root
          ((e.world k').state w).finalizedCheckpoint.epoch =
            .ok ((e.world k').state w).finalizedCheckpoint.root) ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k').state w).finalizedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true)
    {receiverHead : ForkChoiceNode} {state : BeaconState preset fork}
    {current last : Slot} {receiverEpoch : Epoch} {score : Gwei}
    {receiverWindow receiverParticipants : Std.TreeSet ValidatorIndex}
    (headOk : ((e.world k).state w).getHead config = .ok receiverHead)
    (receiverAbove : ((e.world k).state w).isAncestor receiverHead ⟨block.parentRoot, .pending⟩ =
      .ok true)
    (stateOk : ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint =
      .ok state)
    (currentOk : ((e.world k).state w).getCurrentSlot config = .ok current)
    (receiverEpochOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok receiverEpoch)
    (age : receiverEpoch.toNat ≤ (computeEpochAtSlot preset parentBlock.slot).toNat + 2)
    (receiverLastOk : subChecked current 1 = .ok last)
    (receiverWindowOk : ((e.world k).state w).getCommitteesBetweenSlots receiverHead.root
      firstSlot last = .ok receiverWindow)
    (scoreOk : computeProposerScore config state = .ok score)
    (receiverParticipantsOk : ((e.world k).state w).getCommitteesBetweenSlots receiverHead.root
      firstSlot beforeBlock = .ok receiverParticipants) :
    stake (fun v => balanceAt state v.toNat) (Store.activeMembers state receiverWindow) +
        score.toNat <
      stake (fun v => balanceAt state v.toNat)
          {v ∈ ((e.world k).state w).parentVotersOf state receiverParticipants block
            parentBlock | v ∈ J} +
        2 * stake (fun v => balanceAt state v.toNat)
          {v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ | v ∈ J} ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true := by
  obtain ⟨receiverTotal, receiverTotalOk⟩ := activeTotal_of_stake_bound
    (state.validators.bound preGloas)
    (Nat.lt_of_le_of_lt (supply w receiver k _ state (by omega) stateOk) stakeCapGwei_lt)
  have receiverIndices : ∀ v ∈ receiverWindow, ∃ validator,
      validatorAt state v = .ok validator := by
    intro v member
    exact validatorAt_of_mem_committeeWindow anchorStore sound anchorSlot anchorBoundary
      anchored preGloas slots chain receiver (by omega) receiverEpochOk
      (inHorizon w receiver k receiverEpoch (by omega) receiverEpochOk)
      (nonzero w receiver k (by omega)) headOk stateOk receiverWindowOk member
  obtain ⟨receiverActive, receiverWeight, receiverActiveOk, receiverWeightOk⟩ :=
    filteredTotal_exists receiverTotalOk receiverIndices
  have clocks := (e.clock_bounds u n).1
  have receiverClocks := (e.clock_bounds w k).1
  rw [anchored u caller] at clocks
  rw [anchored w receiver] at receiverClocks
  have currentLe : slot ≤ current := by
    apply computeSlotAtTimeMs_mono (laterMs := ((e.world k).state w).timeMs)
      (UInt64.le_iff_toNat_le.mpr (by
        rw [upToDate.1, receiverUpToDate.1, atTime]
        exact later)) (mapError_ok_iff.mp slotOk)
    simpa only [Store.getCurrentSlot, receiverClocks.trans clocks.symm] using
      (mapError_ok_iff.mp currentOk)
  have oldLastLe : lastSlot ≤ last := by
    have callerLast := (subChecked_ok_iff.mp lastOk).2
    have receiverLast := (subChecked_ok_iff.mp receiverLastOk).2
    have slotsLe := UInt64.le_iff_toNat_le.mp currentLe
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  obtain ⟨receiverMaximum, receiverMaximumOk⟩ := receiver_oldMaximum maximumOk
    receiverWindowOk oldLastLe receiverTotalOk receiverIndices
  have oldLastPast : lastSlot < current := by
    have lastValue := subChecked_ok_iff.mp lastOk
    have slotsLe := UInt64.le_iff_toNat_le.mp currentLe
    exact UInt64.lt_iff_toNat_lt.mpr (by simp only [UInt64.toNat_one] at lastValue; omega)
  obtain ⟨sourceMaximum, sourceScore, sourceMaximumOk, sourceScoreOk⟩ :=
    weights.reads w receiver k receiverHead state current firstSlot lastSlot receiverMaximum
      (by omega) (by omega) headOk currentOk oldLastPast stateOk receiverMaximumOk
  have sourceScoreEq : sourceScore = proposerScore :=
    Except.ok.inj (sourceScoreOk.symm.trans boostOk)
  subst sourceScore
  let oldSupporters := {v ∈ ((e.world n).state u).supportersOf balanceSource
    ⟨root, .pending⟩ | v ∈ J}
  let oldParents := {v ∈ ((e.world n).state u).parentVotersOf balanceSource
    parentParticipants block parentBlock | v ∈ J}
  have parentDiscount : discount.toNat ≤
      stake (fun v => balanceAt balanceSource v.toNat) oldParents :=
    Store.le_honest_parentVotersOf_of_computeEmptySlotSupportDiscount blockOk parentOk
      firstOk beforeOk parentParticipantsOk discountOk aligned increment
      (weights.dishonest u caller n later)
      (weights.sourceByzantine u caller n head firstSlot beforeBlock parentParticipants
        rfl parentParticipantsOk)
  have transferred := weights.margin w receiver k receiverHead state score proposerScore
    firstSlot lastSlot receiverMaximum sourceMaximum (by omega) (by omega) headOk stateOk
    scoreOk boostOk receiverMaximumOk sourceMaximumOk oldSupporters oldParents
    (fun _ member => (Finset.mem_filter.mp member).2)
    (fun _ member => (Finset.mem_filter.mp member).2)
  have supportersActive : ∀ v ∈ oldSupporters,
      v ∈ ((unslashedActiveBalances balanceSource).map (·.1)).toFinset := by
    intro v member
    have supports := (Finset.mem_filter.mp member).1
    simp only [Store.supportersOf, List.mem_toFinset, List.mem_map, List.mem_filter] at supports
    obtain ⟨entry, ⟨present, _⟩, rfl⟩ := supports
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨entry, present, rfl⟩)
  have parentsActive : ∀ v ∈ oldParents,
      v ∈ ((unslashedActiveBalances balanceSource).map (·.1)).toFinset := by
    intro v member
    have parent := (Finset.mem_filter.mp member).1
    obtain ⟨_, ⟨validator, found, flag, _⟩, _⟩ := Store.mem_parentVotersOf.mp parent
    apply tallyActive_of_activeMember (Finset.mem_filter.mp parent).1
    simp only [NotSlashed, found, Option.map_some, Option.getD_some, flag]
  have supportersWeight := stake_congr (w := fun v =>
    if v ∈ ((unslashedActiveBalances balanceSource).map (·.1)).toFinset
    then balanceAt balanceSource v.toNat else 0)
    (fun v member => ite_eq_left (supportersActive v member))
  have parentsWeight := stake_congr (w := fun v =>
    if v ∈ ((unslashedActiveBalances balanceSource).map (·.1)).toFinset
    then balanceAt balanceSource v.toNat else 0)
    (fun v member => ite_eq_left (parentsActive v member))
  dsimp only at transferred
  rw [supportersWeight, parentsWeight] at transferred
  have receiverUnslashed : ∀ v ∈ J, NotSlashed state v := by
    obtain ⟨held, boundary, stored, _, advanced⟩ :=
      e.checkpointStates_fixedChecks anchorStore (anchored w receiver)
        (Store.checkpointState_ok_iff.mp stateOk)
    intro v honest
    apply (notSlashed_lookahead advanced v).mpr
    exact unslashed w receiver k held (by omega)
      (Store.counts_of_fixedChecks (checks := checks) stored (.inl rfl)) v honest
  have receiverHonestActive : ∀ v ∈ Store.activeMembers state receiverWindow, v ∈ J →
      v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset := by
    intro v member honest
    exact tallyActive_of_activeMember member (receiverUnslashed v honest)
  have receiverReachable := e.reachable
    (fun w hw => (anchored w hw) ▸ Store.Reachable.anchor anchorStore) k w receiver
  have rootAboveAnchor := receiverReachable.anchorSlot_le_block known
  have equalRankSupport : ∀ v ∈ oldSupporters, ∀ first second,
      ((e.world n).state u).latestMessages[v]? = some first →
      ((e.world k).state w).latestMessages[v]? = some second →
      first.rank = second.rank →
      v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset →
      v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ := by
    intro v member first second firstOk secondOk rank active
    obtain ⟨supporter, honest⟩ := Finset.mem_filter.mp member
    have same := latest_eq_of_rank_eq slots preGloas anchorStore anchored caller receiver honest
      firstOk secondOk rank
    exact supporter_of_same_latest anchorStore anchored oneBlock preGloas caller receiver later
      (by omega) (Store.block_ok_iff.mp blockOk) known rootAboveAnchor supporter
      (by rw [firstOk, secondOk, same])
      (fun equivocated => weights.dishonest w receiver k (by omega) v equivocated honest) active
  have freshSlotSupport : ∀ v ∈ J, ∀ attestation : Attestation preset fork,
      ((e.world k).state w).latestMessages[v]? =
        some (LatestMessage.ofAttestation attestation) →
      slot ≤ attestation.data.slot →
      ((e.world k).state w).VoteOrigin config v attestation →
      (∃ signedAt < k,
        MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
          (e.world signedAt).time ((e.world signedAt).view v) ((e.world signedAt).state v)
          attestation.data) →
      v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset →
      v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ := by
    intro v honest attestation latest floor origin signed active
    obtain ⟨due, dueOk⟩ := fits.1
    -- The preceding caller slot is complete, so its boundary bounds the attestation offset.
    have lastValue := subChecked_ok_iff.mp lastOk
    have nextOk : addChecked lastSlot 1 = .ok slot := by
      apply addChecked_ok_iff.mpr
      constructor <;> simp only [UInt64.toNat_one] at lastValue ⊢ <;>
        have := slot.toNat_lt <;> omega
    have beforeSlot : lastSlot ≤ slot := UInt64.le_iff_toNat_le.mpr (by
      simp only [UInt64.toNat_one] at lastValue; omega)
    obtain ⟨previousTime, previousOk, _, _⟩ := exists_timeAtSlotMs_of_le beforeSlot beginOk
    have dueLt := fits.due_lt_slot nextOk previousOk beginOk dueOk
    exact supporter_of_latest_slot anchorStore anchored oneBlock preGloas honest receiver
      (by omega) latest
      (fun equivocated => weights.dishonest w receiver k (by omega) v equivocated honest)
      receiverUpToDate dueOk dueLt beginOk floor
      (fun earlier low high => safe earlier (by omega) (by omega)) known rootAboveAnchor active
      signed origin
  sorry


end EthLib.Consensus.Models.Network
