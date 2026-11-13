module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationResets
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationCommittees
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSupporters
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

/-- The caller's finalized boundary is no later than a recent held historical block. -/
private theorem finalized_boundary_le_historical {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchored : ∀ u ∈ J, e.start u = anchor)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    {epoch historicalEpoch : Epoch} {historical : Root}
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (historicalEpochOk : ((e.world n).state u).getBlockEpoch historical = .ok historicalEpoch)
    (recent : epoch.toNat ≤ historicalEpoch.toNat + 1) :
    ∃ block boundary, ((e.world n).state u).blocks[historical]? = some block ∧
      computeStartSlotAtEpoch preset ((e.world n).state u).finalizedCheckpoint.epoch =
        .ok boundary ∧ boundary ≤ block.slot := by
  have reachable := e.reachable
    (fun u hu => (anchored u hu) ▸ Store.Reachable.anchor anchorStore) n u caller
  unfold Store.getBlockEpoch at historicalEpochOk
  obtain ⟨block, blockOk, epochEq⟩ := bind_ok_iff.mp historicalEpochOk
  have known := Store.block_ok_iff.mp blockOk
  have epochEq : historicalEpoch = computeEpochAtSlot preset block.slot :=
    (Except.ok.inj epochEq).symm
  have finalizedLe : ((e.world n).state u).finalizedCheckpoint.epoch.toNat ≤
      historicalEpoch.toNat := by
    rcases e.finalizedCheckpoint_eq_or_add_two_le anchorStore sound
      (anchored u caller) epochOk with same | older
    · obtain ⟨_, _, _, _, _, initial, _, _⟩ := getForkchoiceStore_anchor anchorStore
      rw [same, initial]
      change (computeEpochAtSlot preset anchorState.slot).toNat ≤ historicalEpoch.toNat
      rw [← anchorSlot, epochEq]
      simp only [computeEpochAtSlot, UInt64.toNat_div]
      exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp
        (reachable.anchorSlot_le_block known))
    · omega
  have productLe := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat finalizedLe
  rw [epochEq] at productLe
  simp only [computeEpochAtSlot, UInt64.toNat_div] at productLe
  have rounded := Nat.div_mul_le_self block.slot.toNat preset.SLOTS_PER_EPOCH.toNat
  have bound : ((e.world n).state u).finalizedCheckpoint.epoch.toNat *
      preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 :=
    lt_of_le_of_lt (productLe.trans rounded) block.slot.toNat_lt
  have made := mulChecked_of_lt bound
  refine ⟨block, _, known, made, UInt64.le_iff_toNat_le.mpr ?_⟩
  rw [(mulChecked_ok_iff.mp made).2]
  exact productLe.trans rounded

/-- Finality at an earlier ready event is below a slot recent at the caller. -/
private theorem finalized_boundary_le_slot_of_earlier {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (slots : 0 < config.SLOT_DURATION_MS)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchored : ∀ u ∈ J, e.start u = anchor)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n j : ℕ}
    (upToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    (ready : UpToDate config checks sources (e.world j).time ((e.world j).view w)
      ((e.world j).state w))
    (earlier : (e.world j).time ≤ (e.world n).time)
    {slot recent : Slot} {epoch : Epoch}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (age : epoch.toNat ≤ (computeEpochAtSlot preset recent).toNat + 1)
    (above : anchorBlock.slot ≤ recent) :
    ∃ boundary,
      computeStartSlotAtEpoch preset ((e.world j).state w).finalizedCheckpoint.epoch =
        .ok boundary ∧ boundary ≤ recent := by
  have forward := e.forwardReachable
    (fun u hu => (anchored u hu) ▸ Store.ForwardReachable.anchor anchorStore) j w receiver
  obtain ⟨current, currentOk, _, _⟩ :=
    forward.slots_le_current slots (UInt64.le_of_eq anchorSlot)
  have firstClock := (e.clock_bounds u n).1
  have secondClock := (e.clock_bounds w j).1
  rw [anchored u caller] at firstClock
  rw [anchored w receiver] at secondClock
  have currentLe : current ≤ slot := by
    apply computeSlotAtTimeMs_mono (laterMs := ((e.world n).state u).timeMs)
      (UInt64.le_iff_toNat_le.mpr (by rw [ready.1, upToDate.1]; exact earlier))
      (mapError_ok_iff.mp currentOk)
    simpa only [Store.getCurrentSlot, firstClock.trans secondClock.symm] using
      (mapError_ok_iff.mp slotOk)
  have epochEq : epoch = computeEpochAtSlot preset slot := by
    simpa [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure] using
      epochOk.symm
  have currentEpochOk : ((e.world j).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset current) := by
    simp [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
  have currentEpochLe : (computeEpochAtSlot preset current).toNat ≤ epoch.toNat := by
    rw [epochEq]
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp currentLe)
  have finalizedLe : ((e.world j).state w).finalizedCheckpoint.epoch.toNat ≤
      (computeEpochAtSlot preset recent).toNat := by
    rcases e.finalizedCheckpoint_eq_or_add_two_le anchorStore sound
      (anchored w receiver) currentEpochOk with same | older
    · obtain ⟨_, _, _, _, _, initial, _, _⟩ := getForkchoiceStore_anchor anchorStore
      rw [same, initial]
      change (computeEpochAtSlot preset anchorState.slot).toNat ≤ _
      rw [← anchorSlot]
      simp only [computeEpochAtSlot, UInt64.toNat_div]
      exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp above)
    · omega
  have productLe := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat finalizedLe
  simp only [computeEpochAtSlot, UInt64.toNat_div] at productLe
  have rounded := Nat.div_mul_le_self recent.toNat preset.SLOTS_PER_EPOCH.toNat
  have bound : ((e.world j).state w).finalizedCheckpoint.epoch.toNat *
      preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 :=
    lt_of_le_of_lt (productLe.trans rounded) recent.toNat_lt
  have made := mulChecked_of_lt bound
  refine ⟨_, made, UInt64.le_iff_toNat_le.mpr ?_⟩
  rw [(mulChecked_ok_iff.mp made).2]
  exact productLe.trans rounded

/-- A recent historical block on the caller's head agrees with caller finality. -/
private theorem checkpoint_of_recent_historical {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (anchored : ∀ u ∈ J, e.start u = anchor)
    (slots : 0 < config.SLOT_DURATION_MS) (preGloas : fork < .glamsterdam)
    {horizon : Epoch} {time : ℕ} (chain : FinalizedPrefix e horizon time)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (bounded : (e.world n).time ≤ time)
    {epoch historicalEpoch : Epoch} {historical : Root} {head : ForkChoiceNode}
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (inHorizon : epoch ≤ horizon)
    (historicalEpochOk : ((e.world n).state u).getBlockEpoch historical = .ok historicalEpoch)
    (recent : epoch.toNat ≤ historicalEpoch.toNat + 1)
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (descends : ((e.world n).state u).isAncestor head ⟨historical, .pending⟩ = .ok true) :
    ∃ block boundary, ((e.world n).state u).blocks[historical]? = some block ∧
      computeStartSlotAtEpoch preset ((e.world n).state u).finalizedCheckpoint.epoch =
        .ok boundary ∧ boundary ≤ block.slot ∧
      ((e.world n).state u).getCheckpointBlock historical
        ((e.world n).state u).finalizedCheckpoint.epoch =
          .ok ((e.world n).state u).finalizedCheckpoint.root := by
  obtain ⟨block, boundary, known, boundaryOk, below⟩ := finalized_boundary_le_historical
    anchorStore sound anchorSlot anchored caller epochOk historicalEpochOk recent
  have forward := e.forwardReachable
    (fun u hu => (anchored u hu) ▸ Store.ForwardReachable.anchor anchorStore) n u caller
  have justifiedHorizon := UInt64.le_trans
    (forward.justified_epoch_le_current sound slots (UInt64.le_of_eq anchorSlot) epochOk).1
    inHorizon
  have justifiedRead := chain u caller u caller n n bounded bounded
    ((e.world n).state u).justifiedCheckpoint (Or.inl rfl)
    (forward.reachable.finalized_le_justified sound) justifiedHorizon
  refine ⟨block, boundary, known, boundaryOk, below, ?_⟩
  by_cases genesis : ((e.world n).state u).finalizedCheckpoint.epoch = GENESIS_EPOCH
  · have above := e.anchorSlot_le_finalized_boundary anchorStore anchorSlot anchorBoundary
      (anchored u caller) boundaryOk
    have zeroBoundary : boundary = 0 := by
      apply UInt64.toNat_inj.mp
      simpa [genesis, GENESIS_EPOCH] using
        (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
    have zeroAnchor : anchorBlock.slot = 0 :=
      UInt64.le_zero_iff.mp (zeroBoundary ▸ above)
    obtain ⟨r, hashed, anchorKnown, _, justified, final, _, _⟩ :=
      getForkchoiceStore_anchor anchorStore
    have initialKnown : ((e.world 0).state u).blocks[r]? = some anchorBlock := by
      simpa only [Execution.world_zero, World.initial, anchored u caller] using anchorKnown
    have rootRead := chain u caller u caller n 0 bounded
      ((e.monotone_time (Nat.zero_le n)).trans bounded)
      anchor.justifiedCheckpoint
      (by change (e.start u).Justified anchor.justifiedCheckpoint
          rw [anchored u caller]
          exact .inl rfl)
      (by rw [genesis]; exact UInt64.zero_le)
      (by simp [justified, getCurrentEpoch, computeEpochAtSlot, ← anchorSlot, zeroAnchor])
    have initialWalk := Store.getAncestor_of_le (node := ⟨r, .pending⟩) initialKnown
      (show anchorBlock.slot ≤ boundary by rw [zeroAnchor, zeroBoundary]; exact UInt64.le_refl _)
    have initialRead : ((e.world 0).state u).getCheckpointBlock r
        ((e.world n).state u).finalizedCheckpoint.epoch = .ok r := by
      simp [Store.getCheckpointBlock, boundaryOk, initialWalk, Except.mapError,
        bind, Except.bind, pure, Except.pure]
    rw [justified] at rootRead
    have finalRoot : ((e.world n).state u).finalizedCheckpoint.root = r :=
      (Except.ok.inj (rootRead.symm.trans initialRead))
    have historicalAbove := e.isAncestor_anchor_of_known anchorStore anchored caller known
    obtain ⟨r', hashed', held⟩ := forward.reachable.anchor_known
    rw [hashed, Except.ok.injEq] at hashed'
    subst r'
    rw [final] at historicalAbove
    have walk := Store.getAncestor_of_isAncestor_of_lt preGloas held historicalAbove
    simp [Store.getCheckpointBlock, boundaryOk, zeroBoundary, ← zeroAnchor, walk,
      Except.mapError, bind, Except.bind, pure, Except.pure, finalRoot]
  have headRead : ((e.world n).state u).getCheckpointBlock head.root
      ((e.world n).state u).finalizedCheckpoint.epoch =
        .ok ((e.world n).state u).finalizedCheckpoint.root := by
    rcases Store.getHead_viable headOk with viable | ⟨_, fallback⟩
    · exact (Store.isViableLeaf_finalized viable).resolve_left genesis
    · simpa only [fallback] using justifiedRead
  have walk := Store.getAncestor_of_isAncestor_of_lt preGloas known descends
  have through := Store.getAncestor_trans below walk
  have rootWalk := Store.getAncestor_root (store := (e.world n).state u) head .pending boundary
  simp only [Store.getCheckpointBlock, boundaryOk, Except.mapError, bind, Except.bind,
    pure, Except.pure] at headRead ⊢
  change (·.root) <$> ((e.world n).state u).getAncestor ⟨head.root, .pending⟩ boundary =
    .ok ((e.world n).state u).finalizedCheckpoint.root at headRead
  rw [← rootWalk, through] at headRead
  exact headRead

/-- A delivered safe duty with a recent target is recorded at a compatible ready endpoint. -/
private theorem recorded_duty_of_endpoint_checkpoint {Δ time : ℕ}
    (sync : e.Synchronous Δ) (preGloas : fork < .glamsterdam)
    (oneBlock : OneBlockPerRoot e time) (admitted : BlocksAdmitted e 0 Δ time)
    {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (anchored : ∀ u ∈ J, e.start u = anchor)
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J)
    {dutySlot current : Slot} {committeeIndex : CommitteeIndex} {deadline n k : ℕ}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v dutySlot committeeIndex deadline n attestation indexed)
    (due : IsAttestationDeadline fork config genesisTimeMs dutySlot deadline)
    {dueMs : UInt64} (dueOk : getAttestationDueMs config fork = .ok dueMs)
    (inSlot : dueMs < config.SLOT_DURATION_MS)
    (bounded : (e.world k).time ≤ time)
    (late : deadline + Δ ≤ (e.world k).time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (counted : v ∉ ((e.world k).state w).equivocatingIndices)
    (currentOk : ((e.world k).state w).getCurrentSlot config = .ok current)
    (recent : computeEpochAtSlot preset dutySlot = computeEpochAtSlot preset current ∨
      computeEpochAtSlot preset dutySlot = saturatingSub (computeEpochAtSlot preset current) 1)
    (past : dutySlot < current) {root : Root} {block : BeaconBlock preset fork}
    (safe : SafeAt e deadline root)
    (nonzero : ∀ (r : Root) (b : BeaconBlock preset fork),
      ((e.world n).state v).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (known : ((e.world k).state w).blocks[root]? = some block)
    (finalizedKnown : ∃ b, ((e.world k).state w).blocks[
      ((e.world k).state w).finalizedCheckpoint.root]? = some b)
    {boundary : Slot}
    (boundaryOk : computeStartSlotAtEpoch preset ((e.world k).state w).finalizedCheckpoint.epoch =
      .ok boundary)
    (below : boundary ≤ block.slot)
    (checkpoint : ((e.world k).state w).getCheckpointBlock root
      ((e.world k).state w).finalizedCheckpoint.epoch =
        .ok ((e.world k).state w).finalizedCheckpoint.root) :
    ∃ message, ((e.world k).state w).latestMessages[v]? = some message ∧
      attestation.data.target.epoch ≤ message.rank := by
  have sourceBound : (e.world n).time ≤ time := by rw [vote.atTime]; omega
  obtain ⟨dataSlot, dataEpoch, head, headBlock, headOk, headKnown, dataRoot, notFuture⟩ :=
    vote.data_head anchorStore (UInt64.le_of_eq anchorSlot) anchored honest due dueOk inSlot
  have supports := safe v honest n head vote.atTime (vote.atTime.symm ▸ vote.upToDate) headOk
  have sourceKnown : ((e.world n).state v).blocks[root]? = some block := by
    have test := supports
    unfold Store.isAncestor at test
    obtain ⟨other, read, _⟩ := bind_ok_iff.mp test
    have held := Store.block_ok_iff.mp read
    exact oneBlock v honest w receiver n k sourceBound bounded root other block held known ▸ held
  have votedKnown := e.blocks_of_endpoint_checkpoint sync preGloas oneBlock admitted
    anchorStore anchored honest receiver bounded bounded (by simpa [vote.atTime] using late)
    upToDate finalizedKnown headKnown sourceKnown supports boundaryOk
    (e.anchorSlot_le_finalized_boundary anchorStore anchorSlot anchorBoundary
      (anchored w receiver) boundaryOk) below checkpoint
  have votedKnown : ((e.world k).state w).blocks[attestation.data.beaconBlockRoot]? =
      some headBlock := dataRoot ▸ votedKnown
  have targetRead := vote.data_target anchorStore anchorSlot anchorBoundary anchored honest
    nonzero
  obtain ⟨targetBoundary, targetBlock, targetBoundaryOk, targetKnown, targetLe, _⟩ :=
    Store.isAncestor_of_getCheckpointBlock preGloas targetRead
  have sourceReachable := e.reachable
    (fun u hu => (anchored u hu) ▸ Store.Reachable.anchor anchorStore) n v honest
  have receiverReachable := e.reachable
    (fun u hu => (anchored u hu) ▸ Store.Reachable.anchor anchorStore) k w receiver
  have receiverRead := Store.getCheckpointBlock_of_same_blocks receiverReachable
    (oneBlock v honest w receiver n k sourceBound bounded) targetBoundaryOk
    (UInt64.le_trans (sourceReachable.anchorSlot_le_block targetKnown) targetLe)
    ⟨headBlock, votedKnown⟩ targetRead
  obtain ⟨_, receiverTarget, _, receiverTargetKnown, _, _⟩ :=
    Store.isAncestor_of_getCheckpointBlock preGloas receiverRead
  have valid := Store.validateOnAttestation_of_facts currentOk (dataEpoch ▸ recent)
    (by simpa only [dataSlot] using dataEpoch) receiverTargetKnown votedKnown
    (dataSlot ▸ notFuture) (fun gloas => (Nat.not_le_of_lt preGloas gloas).elim)
    receiverRead (dataSlot ▸ past)
  obtain ⟨⟨after, accepted⟩, reads⟩ := vote.accepted_of_target_known anchorStore anchored oneBlock
    honest receiver sourceBound bounded receiverTargetKnown valid
  obtain ⟨message, latest, rank⟩ :=
    vote.recorded sync honest receiver late upToDate accepted reads counted
  refine ⟨message, latest, ?_⟩
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
  simpa [LatestMessage.rank, LatestMessage.ofAttestation, notGloas] using rank

/-- A newer signed vote from before the call cannot replace a recent caller vote unnoticed. -/
private theorem rank_le_of_stale_slot {Δ time : ℕ}
    (sync : e.Synchronous Δ) (preGloas : fork < .glamsterdam)
    (oneBlock : OneBlockPerRoot e time) (admitted : BlocksAdmitted e 0 Δ time)
    (votes : Votes e.startTime time e) (fits : DelayFits fork config genesisTimeMs Δ)
    {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (anchored : ∀ u ∈ J, e.start u = anchor)
    {v u : ValidatorIndex} (honest : v ∈ J) (caller : u ∈ J) {signedAt n : ℕ}
    {data : AttestationData}
    (signed : MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
      (e.world signedAt).time ((e.world signedAt).view v) ((e.world signedAt).state v) data)
    (targetEpoch : data.target.epoch = computeEpochAtSlot preset data.slot)
    {current epochStart : Slot} {begin epochBegin : UInt64}
    (currentOk : ((e.world n).state u).getCurrentSlot config = .ok current)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs current = .ok begin)
    (atBegin : (e.world n).time = begin.toNat)
    (bounded : (e.world n).time ≤ time)
    (epochStartOk : computeStartSlotAtEpoch preset (computeEpochAtSlot preset current) =
      .ok epochStart)
    (epochBeginOk : computeTimeAtSlotMs config genesisTimeMs epochStart = .ok epochBegin)
    (past : data.slot < current)
    (upToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    (counted : v ∉ ((e.world n).state u).equivocatingIndices)
    {old : LatestMessage fork}
    (latest : ((e.world n).state u).latestMessages[v]? = some old)
    (floor : (computeEpochAtSlot preset current).toNat ≤ old.rank.toNat + 1)
    {root : Root} {block : BeaconBlock preset fork}
    (safe : ∀ earlier, epochBegin.toNat ≤ earlier → earlier < (e.world n).time →
      SafeAt e earlier root)
    (nonzero : ∀ j, (e.world j).time ≤ time → ∀ (r : Root) (b : BeaconBlock preset fork),
      ((e.world j).state v).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (known : ((e.world n).state u).blocks[root]? = some block)
    (finalizedKnown : ∃ b, ((e.world n).state u).blocks[
      ((e.world n).state u).finalizedCheckpoint.root]? = some b)
    {boundary : Slot}
    (boundaryOk : computeStartSlotAtEpoch preset ((e.world n).state u).finalizedCheckpoint.epoch =
      .ok boundary)
    (below : boundary ≤ block.slot)
    (checkpoint : ((e.world n).state u).getCheckpointBlock root
      ((e.world n).state u).finalizedCheckpoint.epoch =
        .ok ((e.world n).state u).finalizedCheckpoint.root) :
    data.target.epoch ≤ old.rank := by
  by_contra high
  have epochLe : (computeEpochAtSlot preset data.slot).toNat ≤
      (computeEpochAtSlot preset current).toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp (UInt64.le_of_lt past))
  have sameEpoch : computeEpochAtSlot preset data.slot = computeEpochAtSlot preset current := by
    apply UInt64.toNat_inj.mp
    have higher := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp high)
    rw [targetEpoch] at higher
    omega
  obtain ⟨committeeIndex, assigned, due, _, _, _, _⟩ := signed
  have nextBound : data.slot.toNat + (1 : UInt64).toNat < 2 ^ 64 := by
    have := current.toNat_lt
    have := UInt64.lt_iff_toNat_lt.mp past
    simp only [UInt64.toNat_one]
    omega
  have nextOk := addChecked_of_lt nextBound
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  have nextLe : data.slot + 1 ≤ current := UInt64.le_iff_toNat_le.mpr (by
    have := UInt64.lt_iff_toNat_lt.mp past
    simp only [UInt64.toNat_one] at nextNat
    omega)
  obtain ⟨following, followingOk, _, followingLe⟩ := exists_timeAtSlotMs_of_le nextLe beginOk
  obtain ⟨start, startOk, _, _⟩ :=
    exists_timeAtSlotMs_of_le (UInt64.le_of_lt past) beginOk
  have delivered := fits.before_boundary nextOk startOk followingOk due
  have deliveredCaller : (e.world signedAt).time + Δ < (e.world n).time := by
    have := UInt64.le_iff_toNat_le.mp followingLe
    omega
  have before : (e.world signedAt).time < (e.world n).time := by
    omega
  have lowSlot : epochStart ≤ data.slot := by
    rw [UInt64.le_iff_toNat_le, (computeStartSlotAtEpoch_ok_iff.mp epochStartOk).2,
      ← sameEpoch]
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_mul_le_self _ _
  obtain ⟨sameBegin, sameBeginOk, _, lowTime⟩ := exists_timeAtSlotMs_of_le lowSlot startOk
  have sameBeginEq := Except.ok.inj (sameBeginOk.symm.trans epochBeginOk)
  subst sameBegin
  have afterBegin : epochBegin.toNat ≤ (e.world signedAt).time := by
    obtain ⟨start', dueMs, startOk', _, timeEq⟩ := due
    rw [startOk, Except.ok.injEq] at startOk'
    subst start'
    have := UInt64.le_iff_toNat_le.mp lowTime
    omega
  have started := e.monotone_time (Nat.zero_le signedAt)
  obtain ⟨j, attestation, indexed, vote⟩ := votes v honest data.slot committeeIndex
    (e.world signedAt).time assigned due started started (before.le.trans bounded)
  obtain ⟨dueMs, dueOk⟩ := fits.1
  have inSlot := fits.due_lt_slot nextOk startOk followingOk dueOk
  obtain ⟨_, dataEpoch, _⟩ :=
    vote.data_head anchorStore (UInt64.le_of_eq anchorSlot) anchored honest due dueOk inSlot
  obtain ⟨message, recorded, rank⟩ := recorded_duty_of_endpoint_checkpoint sync preGloas
    oneBlock admitted anchorStore anchorSlot anchorBoundary anchored honest caller vote due
    dueOk inSlot bounded deliveredCaller.le upToDate counted currentOk (Or.inl sameEpoch) past
    (safe _ afterBegin before) (nonzero j (by rw [vote.atTime]; omega)) known finalizedKnown
    boundaryOk below checkpoint
  rw [latest, Option.some.injEq] at recorded
  subst message
  exact high (by simpa only [targetEpoch, dataEpoch] using rank)

/-- A completed duty supporting a compatible root is recorded at its next slot boundary. -/
private theorem recorded_duty_of_supporting_vote {Δ time : ℕ}
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (preGloas : fork < .glamsterdam) (oneBlock : OneBlockPerRoot e time)
    (admitted : BlocksAdmitted e 0 Δ time)
    (prompt : Prompt e time)
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
    {v w : ValidatorIndex} (honest : v ∈ J) (receiver : w ∈ J) {k : ℕ}
    (atTime : (e.world k).time = time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (counted : ∀ j, (e.world j).time ≤ time →
      v ∉ ((e.world j).state w).equivocatingIndices)
    {root : Root} {block : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some block)
    {following : UInt64} {covered : Prop}
    (rootFinal : ∀ j ≤ k,
      (e.world j).time < following.toNat →
      UpToDate config checks sources (e.world j).time ((e.world j).view w)
        ((e.world j).state w) →
      (∃ boundary,
        computeStartSlotAtEpoch preset ((e.world j).state w).finalizedCheckpoint.epoch =
          .ok boundary ∧ boundary ≤ block.slot ∧
        ((e.world k).state w).getCheckpointBlock root
          ((e.world j).state w).finalizedCheckpoint.epoch =
            .ok ((e.world j).state w).finalizedCheckpoint.root) ∨ covered)
    {slot next : Slot} {start : UInt64}
    {committeeIndex : CommitteeIndex} {deadline n : ℕ}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex deadline n attestation indexed)
    (nextOk : addChecked slot 1 = .ok next)
    (startOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok start)
    (followingOk : computeTimeAtSlotMs config genesisTimeMs next = .ok following)
    (deadlineOk : IsAttestationDeadline fork config genesisTimeMs slot deadline)
    (started : e.startTime ≤ deadline) (complete : following.toNat ≤ time)
    (supportsHead : ∀ head, ((e.world n).state v).getHead config = .ok head →
      ((e.world n).state v).isAncestor head ⟨root, .pending⟩ = .ok true) :
    (∃ message,
      ((e.world k).state w).latestMessages[v]? = some message ∧
      attestation.data.target.epoch ≤ message.rank) ∨ covered := by
  obtain ⟨⟨pre, preTime, delivered, preReady⟩, ⟨post, postTime, postReady⟩⟩ :=
    e.exists_duty_boundaries fits (prompt.of_le complete) receiver nextOk startOk followingOk
      deadlineOk started
  have completePost : (e.world post).time ≤ time := by omega
  obtain ⟨due, dueOk⟩ := fits.1
  have dueLt := fits.due_lt_slot nextOk startOk followingOk dueOk
  obtain ⟨dataSlot, dataEpoch, head, headBlock, headOk, headKnown, dataRoot, notFuture⟩ :=
    vote.data_head anchorStore (UInt64.le_of_eq anchorSlot) anchored honest deadlineOk dueOk dueLt
  have supports := supportsHead head headOk
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
  rcases rootFinal pre preLe (by omega) preReady with
    ⟨boundary, boundaryOk, below, checkpoint⟩ | covered
  swap
  · exact .inr covered
  have held := e.blocks_of_endpoint_checkpoint sync preGloas oneBlock admitted anchorStore
    anchored honest receiver (by omega) (by omega)
    (by simpa [vote.atTime] using delivered) preReady
    (e.finalized_known_of_prefix anchorStore sound anchored slots anchorSlot preGloas chain
      receiver (by omega) preEpochOk (inHorizon w receiver pre preEpoch (by omega) preEpochOk))
    headKnown sourceKnown supports boundaryOk
    (e.anchorSlot_le_finalized_boundary anchorStore anchorSlot anchorBoundary
      (anchored w receiver) boundaryOk) below checkpoint
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
    (nonzero v honest n (by rw [vote.atTime]; omega))
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
  exact .inl ⟨message, latest, rank⟩

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
    delivered, _, completePost, _, _,
    next, start, following, nextOk, startOk, followingOk, deadlineOk, postTime⟩ :=
    duty_delivery_before_receiver votes prompt fits beginOk endOk started fresh complete
      honest receiver low high duty
  obtain ⟨due, dueOk⟩ := fits.1
  have dueLt := fits.due_lt_slot nextOk startOk followingOk dueOk
  obtain ⟨dataSlot, dataEpoch, _⟩ :=
    vote.data_head anchorStore (UInt64.le_of_eq anchorSlot) anchored honest deadlineOk dueOk dueLt
  have forward := e.forwardReachable
    (fun u hu => (anchored u hu) ▸ Store.ForwardReachable.anchor anchorStore) k w receiver
  obtain ⟨current, currentOk, _, _⟩ :=
    forward.slots_le_current slots (UInt64.le_of_eq anchorSlot)
  have epochOk : ((e.world k).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset current) := by
    simp [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
  have justifiedHorizon := UInt64.le_trans
    (forward.justified_epoch_le_current sound slots (UInt64.le_of_eq anchorSlot) epochOk).1
    (inHorizon w receiver k _ (by omega) epochOk)
  rcases recorded_duty_of_supporting_vote sync slots preGloas oneBlock admitted prompt fits
      anchorStore sound anchorSlot anchorBoundary anchored chain inHorizon nonzero honest receiver
      atTime upToDate counted known (fun j le _ ready =>
        (rootFinal j le ready).imp_right fun covered =>
          e.justified_covers_of_finalized_covers anchorStore sound anchored preGloas chain
            receiver le (by omega) justifiedHorizon known covered)
      vote nextOk startOk followingOk deadlineOk
      (started.trans firstLe) (by omega)
      (fun head headOk => safe deadline firstLe before v honest n head vote.atTime
        (vote.atTime.symm ▸ vote.upToDate) headOk) with ⟨message, latest, rank⟩ | covered
  · exact .inl ⟨deadline, n, attestation, indexed, message, vote, dataSlot, dataEpoch,
      by omega, latest, rank⟩
  · exact .inr covered

/-- A duty attestation carries its sole voter's signed data. -/
private theorem signed_of_voteAt {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ u ∈ J, e.start u = anchor)
    {v : ValidatorIndex} (honest : v ∈ J) {slot : Slot}
    {committeeIndex : CommitteeIndex} {deadline n : ℕ}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex deadline n attestation indexed) :
    (v, attestation.data) ∈
      statements config checks anchorState anchorBlock (.attestation attestation) := by
  have reachable := e.reachable
    (fun u hu => (anchored u hu) ▸ Store.Reachable.anchor anchorStore) n v honest
  obtain ⟨stored, target, storedOk, targetOk, indexedOk, valid⟩ := vote.reads
  obtain ⟨indices, indicesOk, _⟩ := getAttestingIndices_of_getIndexedAttestation indexedOk
  obtain ⟨other, otherOk, _, sameData, _⟩ :=
    getIndexedAttestation_of_getAttestingIndices indicesOk
  have same := Except.ok.inj (indexedOk.symm.trans otherOk)
  have dataEq : indexed.data = attestation.data := same ▸ sameData
  refine ⟨_, indexed, reachable, ⟨stored, target, storedOk, targetOk, indexedOk, valid⟩, ?_⟩
  simp [indexedStatements, ← dataEq, ← Array.mem_toList_iff, vote.alone]

/-- A counted honest vote is delivered by its next boundary and retained at the endpoint. -/
private theorem recorded_rank_of_counted_vote {Δ time : ℕ}
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
    {u v w : ValidatorIndex} (caller : u ∈ J) (honest : v ∈ J) (receiver : w ∈ J)
    {n k : ℕ} {slot : Slot} {begin : UInt64}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (atSlot : (e.world n).time = begin.toNat) (bounded : (e.world n).time ≤ time)
    (atTime : (e.world k).time = time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (counted : ∀ j, (e.world j).time ≤ time →
      v ∉ ((e.world j).state w).equivocatingIndices)
    {root : Root} {block : BeaconBlock preset fork}
    (sourceKnown : ((e.world n).state u).blocks[root]? = some block)
    (known : ((e.world k).state w).blocks[root]? = some block)
    {covered : Prop}
    (rootFinal : ∀ j ≤ k, (e.world j).time < (e.world n).time →
      UpToDate config checks sources (e.world j).time ((e.world j).view w)
        ((e.world j).state w) →
      (∃ boundary,
        computeStartSlotAtEpoch preset ((e.world j).state w).finalizedCheckpoint.epoch =
          .ok boundary ∧ boundary ≤ block.slot ∧
        ((e.world k).state w).getCheckpointBlock root
          ((e.world j).state w).finalizedCheckpoint.epoch =
            .ok ((e.world j).state w).finalizedCheckpoint.root) ∨ covered)
    {first : LatestMessage fork}
    (firstOk : ((e.world n).state u).latestMessages[v]? = some first)
    (supports : ((e.world n).state u).voteCountsFor ⟨root, .pending⟩ v = true) :
    (∃ second, ((e.world k).state w).latestMessages[v]? = some second ∧
      first.rank ≤ second.rank) ∨ covered := by
  obtain ⟨message, supported, latest, _, supportedOk, descends⟩ :=
    Store.exists_of_voteCountsFor _ supports
  rw [firstOk, Option.some.injEq] at latest
  subst message
  obtain ⟨old, source, seen, same, signed, origin⟩ :=
    e.exists_signed_origin_of_latestMessages anchorStore anchored caller firstOk
  have supportedEq : supported = ⟨old.data.beaconBlockRoot, .pending⟩ := by
    simpa only [Store.getSupportedNode_of_lt preGloas, same, LatestMessage.ofAttestation,
      Except.ok.injEq] using supportedOk.symm
  subst supported
  obtain ⟨signedAt, _, maySign⟩ :=
    e.exists_maySign_of_signed (e.view_subset_sent n u seen) signed honest
  obtain ⟨committeeIndex, assigned, deadline, _⟩ := maySign
  obtain ⟨current, currentOk, past⟩ := origin.past
  rw [slotOk, Except.ok.injEq] at currentOk
  subst current
  have nextBound : old.data.slot.toNat + (1 : UInt64).toNat < 2 ^ 64 := by
    have := slot.toNat_lt
    have := UInt64.lt_iff_toNat_lt.mp past
    simp only [UInt64.toNat_one]
    omega
  have nextOk := addChecked_of_lt nextBound
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  have nextLe : old.data.slot + 1 ≤ slot := UInt64.le_iff_toNat_le.mpr (by
    have := UInt64.lt_iff_toNat_lt.mp past
    simp only [UInt64.toNat_one] at nextNat
    omega)
  obtain ⟨start, startOk, _, _⟩ :=
    exists_timeAtSlotMs_of_le (UInt64.le_of_lt past) beginOk
  obtain ⟨following, followingOk, _, followingLe⟩ :=
    exists_timeAtSlotMs_of_le nextLe beginOk
  have followingBound := UInt64.le_iff_toNat_le.mp followingLe
  have delivered := fits.before_boundary nextOk startOk followingOk deadline
  have started := e.monotone_time (Nat.zero_le signedAt)
  obtain ⟨j, attestation, indexed, vote⟩ := votes v honest old.data.slot committeeIndex
    (e.world signedAt).time assigned deadline started started (by omega)
  obtain ⟨due, dueOk⟩ := fits.1
  have dueLt := fits.due_lt_slot nextOk startOk followingOk dueOk
  obtain ⟨_, dataEpoch, head, headBlock, headOk, headKnown, dataRoot, _⟩ :=
    vote.data_head anchorStore (UInt64.le_of_eq anchorSlot) anchored honest deadline dueOk dueLt
  have signedVote := signed_of_voteAt anchorStore anchored honest vote
  have dataEq := e.data_eq_of_signed_of_target_epoch slots (e.view_subset_sent n u seen)
    (e.view_subset_sent k w (vote.mem_view sync honest receiver (by omega))) signed signedVote
    honest (origin.targetEpoch.trans dataEpoch.symm)
  have reached := fun u hu j => e.reachable
    (fun u hu => (anchored u hu) ▸ Store.Reachable.anchor anchorStore) j u hu
  have walk := Store.getAncestor_of_isAncestor_of_lt preGloas sourceKnown descends
  have tipKnown : ((e.world j).state v).blocks[old.data.beaconBlockRoot]? = some headBlock := by
    simpa only [dataEq, dataRoot] using headKnown
  obtain ⟨rootBlock, rootKnown⟩ := (reached u caller n).known_of_ancestor_walk
    (reached v honest j) (oneBlock u caller v honest n j bounded (by rw [vote.atTime]; omega))
    ⟨headBlock, tipKnown⟩ walk
  have rootEq := oneBlock u caller v honest n j bounded (by rw [vote.atTime]; omega)
    root block rootBlock sourceKnown rootKnown
  subst rootBlock
  have voteSupports := Store.isAncestor_of_same_blocks (reached v honest j) preGloas
    (oneBlock u caller v honest n j bounded (by rw [vote.atTime]; omega)) sourceKnown rootKnown
    ((reached u caller n).anchorSlot_le_block sourceKnown) ⟨headBlock, tipKnown⟩ descends
  have pending := Store.getHead_pending preGloas headOk
  have headEq : head = ⟨old.data.beaconBlockRoot, .pending⟩ := by
    cases head with
    | mk r status =>
      change status = .pending at pending
      change attestation.data.beaconBlockRoot = r at dataRoot
      simp only [pending, ← dataRoot, ← dataEq]
  rcases recorded_duty_of_supporting_vote sync slots preGloas oneBlock admitted prompt fits
      anchorStore sound anchorSlot anchorBoundary anchored chain inHorizon nonzero honest receiver
      atTime upToDate counted known
      (fun j le before ready => rootFinal j le (by omega) ready) vote nextOk startOk followingOk
      deadline started (by omega)
      (fun other otherOk => by
        have eq := Except.ok.inj (otherOk.symm.trans headOk)
        simpa only [eq, headEq] using voteSupports) with ⟨second, secondOk, rank⟩ | covered
  · left
    refine ⟨second, secondOk, ?_⟩
    have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
    simpa only [same, LatestMessage.rank, LatestMessage.ofAttestation, notGloas, ↓reduceDIte,
      dataEq] using rank
  · exact .inr covered

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

/-- The state at a held ancestor starts a committee-preserving run to each held descendant. -/
private theorem runKept_of_ancestor_walk {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    {ancestor : Root} {baseBlock : BeaconBlock preset fork}
    {base state : BeaconState preset fork} {node : ForkChoiceNode}
    (baseKnown : store.blocks[ancestor]? = some baseBlock)
    (baseHeld : store.blockStates[ancestor]? = some base)
    (held : store.blockStates[node.root]? = some state)
    (walk : store.getAncestor node baseBlock.slot = .ok ⟨ancestor, .pending⟩) :
    RunKept base state := by
  obtain ⟨block, known⟩ := reachable.known_of_blockState held
  by_cases low : block.slot ≤ baseBlock.slot
  · rw [Store.getAncestor_of_le known low, Except.ok.injEq] at walk
    subst node
    rw [baseHeld, Option.some.injEq] at held
    subst state
    exact RunKept.refl _
  have other : block ≠ anchorBlock := by
    intro same
    exact low (same ▸ reachable.anchorSlot_le_block baseKnown)
  obtain ⟨post, postHeld, _, produced⟩ := reachable.blockStatesFromParents known
  rw [held, Option.some.injEq] at postHeld
  subst post
  obtain ⟨parent, checks, engine, signed, message, parentHeld, transition⟩ := produced other
  obtain ⟨parentBlock, parentKnown⟩ := reachable.known_of_blockState parentHeld
  have lower : parentBlock.slot < block.slot := by
    have bounds := (stateTransition_slot transition).1
    rw [message] at bounds
    exact UInt64.lt_of_le_of_lt (reachable.blockState_slot_le anchorSlot parentKnown parentHeld)
      bounds
  rw [Store.getAncestor_step known low parentKnown lower] at walk
  exact (runKept_of_ancestor_walk reachable anchorSlot baseKnown baseHeld parentHeld walk).trans
    (runKept_stateTransition transition)
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transition
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

/-- Two head states with the same active indices and committees read the same slot members. -/
private theorem slotCommittee_eq_of_kept {left right : Store preset fork}
    {first second : Root} {source state : BeaconState preset fork} {slot : Slot}
    (sourceOk : left.blockState first = .ok source)
    (stateOk : right.blockState second = .ok state)
    (active : getActiveValidatorIndices source (computeEpochAtSlot preset slot) =
      getActiveValidatorIndices state (computeEpochAtSlot preset slot))
    (kept : ∀ index, getBeaconCommittee source slot index = getBeaconCommittee state slot index) :
    left.getSlotCommittee first slot = right.getSlotCommittee second slot := by
  have count : getCommitteeCountPerSlot source (computeEpochAtSlot preset slot) =
      getCommitteeCountPerSlot state (computeEpochAtSlot preset slot) := by
    simp only [getCommitteeCountPerSlot, active]
  simp only [Store.getSlotCommittee, sourceOk, stateOk, bind, Except.bind, count, kept]

/-- A partial window after a parent ends no later than the epoch after that parent. -/
private theorem epoch_le_of_partial_parent_window {parent first last current : Slot}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (firstOk : addChecked parent 1 = .ok first)
    (lastOk : subChecked current 1 = .ok last)
    (uncovered : isFullValidatorSetCovered preset first last = .ok false) :
    (computeEpochAtSlot preset current).toNat ≤
      (computeEpochAtSlot preset parent).toNat + 1 := by
  simp only [isFullValidatorSetCovered, bind_ok_iff, mapError_ok_iff] at uncovered
  obtain ⟨afterFirst, afterFirstOk, lastFirst, lastFirstOk, afterLast, afterLastOk, notFull⟩ :=
    uncovered
  have firstNat := (addChecked_ok_iff.mp firstOk).2
  have afterFirstNat := (addChecked_ok_iff.mp afterFirstOk).2
  have lastFirstNat := (subChecked_ok_iff.mp lastFirstOk).2
  have lastNat := subChecked_ok_iff.mp lastOk
  have afterLastNat := (addChecked_ok_iff.mp afterLastOk).2
  simp only [UInt64.toNat_one] at lastNat afterLastNat
  have endpoint : afterLast = current := UInt64.toNat_inj.mp (by omega)
  have boundary : lastFirst.toNat = parent.toNat + preset.SLOTS_PER_EPOCH.toNat := by
    simp only [UInt64.toNat_one] at firstNat lastFirstNat
    omega
  have notLater : ¬computeEpochAtSlot preset lastFirst < computeEpochAtSlot preset afterLast := by
    simpa only [pure, Except.pure, Except.ok.injEq, decide_eq_false_iff_not] using notFull
  rw [endpoint] at notLater
  have le := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp notLater)
  simpa only [computeEpochAtSlot, UInt64.toNat_div, boundary,
    Nat.add_div_right _ positive] using le

/-- A covered range holds a whole epoch, with checked boundaries. -/
private theorem epoch_of_covered {first last : Slot}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (covered : isFullValidatorSetCovered preset first last = .ok true) :
    ∃ epoch epochStart next epochEnd,
      computeStartSlotAtEpoch preset epoch = .ok epochStart ∧
      addChecked epochStart preset.SLOTS_PER_EPOCH = .ok next ∧
      subChecked next 1 = .ok epochEnd ∧ first ≤ epochStart ∧ epochEnd ≤ last ∧
      epochStart.toNat = epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ∧
      epochEnd.toNat + 1 = epochStart.toNat + preset.SLOTS_PER_EPOCH.toNat := by
  simp only [isFullValidatorSetCovered, bind_ok_iff, mapError_ok_iff] at covered
  obtain ⟨afterFirst, afterFirstOk, lastFirst, lastFirstOk, afterLast, afterLastOk, full⟩ :=
    covered
  have afterFirstNat := addChecked_ok_iff.mp afterFirstOk
  have lastFirstNat := subChecked_ok_iff.mp lastFirstOk
  have afterLastNat := addChecked_ok_iff.mp afterLastOk
  simp only [UInt64.toNat_one] at lastFirstNat afterLastNat
  have later : computeEpochAtSlot preset lastFirst < computeEpochAtSlot preset afterLast := by
    simpa only [pure, Except.pure, Except.ok.injEq, decide_eq_true_eq] using full
  have laterNat := UInt64.lt_iff_toNat_lt.mp later
  simp only [computeEpochAtSlot, UInt64.toNat_div] at laterNat
  generalize sizeEq : preset.SLOTS_PER_EPOCH.toNat = size at *
  generalize epochEq : lastFirst.toNat / size = E at *
  have below : E * size ≤ lastFirst.toNat := epochEq ▸ Nat.div_mul_le_self _ _
  have above : lastFirst.toNat < E * size + size := by
    have := Nat.lt_mul_div_succ lastFirst.toNat positive
    rw [epochEq, Nat.mul_add, Nat.mul_one, Nat.mul_comm] at this
    exact this
  have reach : E * size + size ≤ afterLast.toNat := by
    have := (Nat.le_div_iff_mul_le positive).mp laterNat
    rwa [Nat.succ_mul] at this
  have startBound : E * size < 2 ^ 64 := Nat.lt_of_le_of_lt below lastFirst.toNat_lt
  have nextBound : E * size + size < 2 ^ 64 := Nat.lt_of_le_of_lt reach afterLast.toNat_lt
  have epochBound : E < 2 ^ 64 := by
    have := Nat.le_mul_of_pos_right E positive
    omega
  have epochNat : E.toUInt64.toNat = E := UInt64.toNat_ofNat_of_lt' epochBound
  have startNat : (E * size).toUInt64.toNat = E * size := UInt64.toNat_ofNat_of_lt' startBound
  have nextNat : (E * size + size).toUInt64.toNat = E * size + size :=
    UInt64.toNat_ofNat_of_lt' nextBound
  have endBound : E * size + size - 1 < 2 ^ 64 := by omega
  have endNat : (E * size + size - 1).toUInt64.toNat = E * size + size - 1 :=
    UInt64.toNat_ofNat_of_lt' endBound
  refine ⟨E.toUInt64, (E * size).toUInt64, (E * size + size).toUInt64,
    (E * size + size - 1).toUInt64, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact computeStartSlotAtEpoch_ok_iff.mpr ⟨by rw [epochNat, sizeEq]; exact startBound,
      by rw [epochNat, startNat, sizeEq]⟩
  · exact addChecked_ok_iff.mpr ⟨by rw [startNat, sizeEq]; exact nextBound,
      by rw [startNat, nextNat, sizeEq]⟩
  · exact subChecked_ok_iff.mpr ⟨by rw [nextNat, UInt64.toNat_one]; omega,
      by rw [nextNat, endNat, UInt64.toNat_one]⟩
  · exact UInt64.le_iff_toNat_le.mpr (by rw [startNat]; omega)
  · exact UInt64.le_iff_toNat_le.mpr (by rw [endNat]; omega)
  · rw [startNat, epochNat]
  · rw [endNat, startNat]
    omega

/-- The whole epoch of a covered receiver window ends at or after the call, within the seed. -/
private theorem epoch_bounds_of_covered {size epoch parent slot current epochStart epochEnd : Nat}
    (positive : 0 < size) (startNat : epochStart = epoch * size)
    (endNat : epochEnd + 1 = epochStart + size) (startLow : parent + 1 ≤ epochStart)
    (endHigh : epochEnd + 1 ≤ current) (callerAge : slot / size ≤ parent / size + 1)
    (receiverAge : current / size ≤ parent / size + 2) :
    slot ≤ epochEnd ∧ epochEnd / size ≤ parent / size + 1 := by
  have parentBelow : parent / size < epoch := by
    apply Nat.lt_of_mul_lt_mul_right (a := size)
    have := Nat.div_mul_le_self parent size
    omega
  have slotBelow : slot < size * (slot / size) + size := by
    have := Nat.lt_mul_div_succ slot positive
    rwa [Nat.mul_add, Nat.mul_one] at this
  have scaled : size * (slot / size) ≤ size * epoch := Nat.mul_le_mul_left size (by omega)
  have endValue : epochEnd / size < epoch + 1 := by
    apply (Nat.div_lt_iff_lt_mul positive).mpr
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have reach : epoch + 1 ≤ current / size := by
    apply (Nat.le_div_iff_mul_le positive).mpr
    rw [Nat.add_mul, Nat.one_mul]
    omega
  rw [Nat.mul_comm] at startNat
  constructor <;> omega

/-- Recent heads above a common parent read the same committees through its next epoch. -/
private theorem slotCommittee_eq_of_recent_parent {anchor : Store preset fork} {limit : Nat}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (oneBlock : OneBlockPerRoot e limit) (slots : 0 < config.SLOT_DURATION_MS)
    (preGloas : fork < .glamsterdam)
    (lookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat ∧ 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat ∧
      preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : Nat}
    (callerBound : (e.world n).time ≤ limit) (receiverBound : (e.world k).time ≤ limit)
    {parent : Root} {parentBlock : BeaconBlock preset fork}
    (callerParentKnown : ((e.world n).state u).blocks[parent]? = some parentBlock)
    (receiverParentKnown : ((e.world k).state w).blocks[parent]? = some parentBlock)
    {firstHead secondHead : ForkChoiceNode}
    (firstAbove : ((e.world n).state u).isAncestor firstHead ⟨parent, .pending⟩ = .ok true)
    (secondAbove : ((e.world k).state w).isAncestor secondHead ⟨parent, .pending⟩ = .ok true)
    {callerEpoch receiverEpoch : Epoch}
    (callerEpochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok callerEpoch)
    (receiverEpochOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok receiverEpoch)
    (recent : callerEpoch.toNat ≤ (computeEpochAtSlot preset parentBlock.slot).toNat + 1)
    (age : receiverEpoch.toNat ≤ (computeEpochAtSlot preset parentBlock.slot).toNat + 2)
    {dutySlot : Slot} (low : parentBlock.slot ≤ dutySlot)
    (high : (computeEpochAtSlot preset dutySlot).toNat ≤
      (computeEpochAtSlot preset parentBlock.slot).toNat + 1) :
    ((e.world n).state u).getSlotCommittee firstHead.root dutySlot =
      ((e.world k).state w).getSlotCommittee secondHead.root dutySlot := by
  have callerForward := e.forwardReachable
    (fun w hw => (anchored w hw) ▸ Store.ForwardReachable.anchor anchorStore) n u caller
  have receiverForward := e.forwardReachable
    (fun w hw => (anchored w hw) ▸ Store.ForwardReachable.anchor anchorStore) k w receiver
  have callerReachable := callerForward.reachable
  have receiverReachable := receiverForward.reachable
  obtain ⟨parentState, parentStateKnown, initial, _⟩ :=
    callerReachable.blockStatesFromParents callerParentKnown
  have parentStateSlot : parentState.slot = parentBlock.slot := by
    by_cases atAnchor : parentBlock = anchorBlock
    · rw [initial atAnchor, atAnchor, anchorSlot]
    · exact (callerReachable.blockState_header callerParentKnown parentStateKnown atAnchor).1
  obtain ⟨firstBlock, firstKnown, _⟩ := Store.slot_le_of_isAncestor callerParentKnown firstAbove
  obtain ⟨firstState, firstStateKnown, _⟩ := callerReachable.blockStatesFromParents firstKnown
  obtain ⟨secondBlock, secondKnown, _⟩ :=
    Store.slot_le_of_isAncestor receiverParentKnown secondAbove
  obtain ⟨secondState, secondStateKnown, _⟩ := receiverReachable.blockStatesFromParents secondKnown
  obtain ⟨receiverParentState, receiverParentStateKnown, _⟩ :=
    receiverReachable.blockStatesFromParents receiverParentKnown
  have sameParentState := e.blockStates_eq anchorStore caller receiver
    (anchored u caller) (anchored w receiver)
    (oneBlock u caller w receiver n k callerBound receiverBound)
    parentStateKnown receiverParentStateKnown
  subst receiverParentState
  have firstRun := runKept_of_ancestor_walk callerReachable (UInt64.le_of_eq anchorSlot)
    callerParentKnown parentStateKnown firstStateKnown
    (Store.getAncestor_of_isAncestor_of_lt preGloas callerParentKnown firstAbove)
  have secondRun := runKept_of_ancestor_walk receiverReachable (UInt64.le_of_eq anchorSlot)
    receiverParentKnown receiverParentStateKnown secondStateKnown
    (Store.getAncestor_of_isAncestor_of_lt preGloas receiverParentKnown secondAbove)
  have headEpochLe {v : ValidatorIndex} {i : Nat} {epoch : Epoch}
      {r : Root} {state : BeaconState preset fork}
      (forward : Store.ForwardReachable config anchorState anchorBlock ((e.world i).state v))
      (epochOk : ((e.world i).state v).getCurrentStoreEpoch config = .ok epoch)
      (held : ((e.world i).state v).blockStates[r]? = some state) :
      (getCurrentEpoch state).toNat ≤ epoch.toNat := by
    obtain ⟨current, currentOk, _, statesLe⟩ :=
      forward.slots_le_current slots (UInt64.le_of_eq anchorSlot)
    have epochEq : epoch = computeEpochAtSlot preset current := by
      simpa [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure] using
        epochOk.symm
    rw [epochEq]
    simp only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp (statesLe _ _ held))
  have firstEpochLe := headEpochLe callerForward callerEpochOk firstStateKnown
  have secondEpochLe := headEpochLe receiverForward receiverEpochOk secondStateKnown
  have epochLow : (computeEpochAtSlot preset parentBlock.slot).toNat ≤
      (computeEpochAtSlot preset dutySlot).toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp low)
  have parentEpochEq : getCurrentEpoch parentState =
      computeEpochAtSlot preset parentBlock.slot := by
    simp only [getCurrentEpoch, parentStateSlot]
  have final : (computeEpochAtSlot preset dutySlot).toNat ≤
      (getCurrentEpoch parentState).toNat + preset.MIN_SEED_LOOKAHEAD.toNat := by
    rw [parentEpochEq]
    omega
  have fixed : computeEpochAtSlot preset dutySlot ≤ activityFixedEpoch parentState := by
    rw [UInt64.le_iff_toNat_le, activityFixedEpoch_toNat, parentEpochEq]
    have := (computeEpochAtSlot preset dutySlot).toNat_lt
    omega
  have firstKept := firstRun.committeesKept final fixed (by omega)
  have secondKept := secondRun.committeesKept final fixed (by omega)
  exact slotCommittee_eq_of_kept (Store.blockState_ok_iff.mpr firstStateKnown)
    (Store.blockState_ok_iff.mpr secondStateKnown)
    ((firstRun.active.getActiveValidatorIndices_eq fixed).trans
      (secondRun.active.getActiveValidatorIndices_eq fixed).symm)
    (fun index => (firstKept dutySlot index rfl).trans (secondKept dutySlot index rfl).symm)

/-- Equality of slot committees transfers every successful read of a finite window. -/
private theorem committeeWindow_transfer {left right : Store preset fork}
    {first second : Root} {low high : Slot} {members : Std.TreeSet ValidatorIndex}
    (read : left.getCommitteesBetweenSlots first low high = .ok members)
    (same : ∀ slot, low ≤ slot → slot ≤ high →
      left.getSlotCommittee first slot = right.getSlotCommittee second slot) :
    right.getCommitteesBetweenSlots second low high = .ok members := by
  unfold Store.getCommitteesBetweenSlots at read ⊢
  obtain ⟨afterHigh, afterOk, folded⟩ := bind_ok_iff.mp read
  rw [afterOk]
  dsimp only [bind, Except.bind]
  have afterNat := (addChecked_ok_iff.mp (mapError_ok_iff.mp afterOk)).2
  have steps : ∀ offset ∈ List.range (afterHigh.toNat - low.toNat),
      left.getSlotCommittee first (low + offset.toUInt64) =
        right.getSlotCommittee second (low + offset.toUInt64) := by
    intro offset member
    have bound := List.mem_range.mp member
    have offsetLt : offset < 2 ^ 64 := by
      have := afterHigh.toNat_lt
      omega
    have offsetNat : offset.toUInt64.toNat = offset := by
      simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' offsetLt]
    have slotNat : (low + offset.toUInt64).toNat = low.toNat + offset := by
      rw [UInt64.toNat_add, offsetNat, Nat.mod_eq_of_lt]
      have := afterHigh.toNat_lt
      omega
    apply same <;> rw [UInt64.le_iff_toNat_le, slotNat]
    · omega
    · simp only [UInt64.toNat_one] at afterNat
      omega
  have transfer : ∀ (indices : List Nat) (initial result : Std.TreeSet ValidatorIndex),
      (∀ offset ∈ indices, left.getSlotCommittee first (low + offset.toUInt64) =
        right.getSlotCommittee second (low + offset.toUInt64)) →
      indices.foldlM (fun (participants : Std.TreeSet ValidatorIndex) offset => do
        let committee : Std.TreeSet ValidatorIndex ←
          left.getSlotCommittee first (low + offset.toUInt64)
        Except.ok (committee.foldl Std.TreeSet.insert participants)) initial =
          Except.ok (ε := ForkChoiceError) result →
      indices.foldlM (fun (participants : Std.TreeSet ValidatorIndex) offset => do
        let committee : Std.TreeSet ValidatorIndex ←
          right.getSlotCommittee second (low + offset.toUInt64)
        Except.ok (committee.foldl Std.TreeSet.insert participants)) initial =
          Except.ok (ε := ForkChoiceError) result := by
    intro indices
    induction indices with
    | nil => intro initial result agrees folded; exact folded
    | cons offset rest ih =>
      intro initial result agrees folded
      simp only [List.foldlM_cons, bind_ok_iff] at folded ⊢
      obtain ⟨next, nextOk, restOk⟩ := folded
      refine ⟨next, ?_, ih next result (fun i member => agrees i (by simp [member])) restOk⟩
      simpa only [← agrees offset (by simp)] using nextOk
  exact transfer _ _ _ steps folded

/-- A successful window reads every slot it contains. -/
private theorem slotCommittee_exists_of_window {store : Store preset fork} {head : Root}
    {first last slot : Slot} {members : Std.TreeSet ValidatorIndex}
    (read : store.getCommitteesBetweenSlots head first last = .ok members)
    (low : first ≤ slot) (high : slot ≤ last) :
    ∃ committee, store.getSlotCommittee head slot = .ok committee := by
  simp only [Store.getCommitteesBetweenSlots, bind_ok_iff, mapError_ok_iff] at read
  obtain ⟨afterLast, afterOk, folded⟩ := read
  have afterNat := (addChecked_ok_iff.mp afterOk).2
  have lowNat := UInt64.le_iff_toNat_le.mp low
  have highNat := UInt64.le_iff_toNat_le.mp high
  have inRange : slot.toNat - first.toNat ∈ List.range (afterLast.toNat - first.toNat) := by
    rw [List.mem_range]
    simp only [UInt64.toNat_one] at afterNat
    omega
  have back : first + (slot.toNat - first.toNat).toUInt64 = slot := by
    rw [← UInt64.toNat_sub_of_le _ _ low, Nat.toUInt64_eq, UInt64.ofNat_toNat,
      UInt64.add_comm, UInt64.sub_add_cancel]
  obtain ⟨committee, committeeOk⟩ := foldlM_forall_of_ok
    (fun _ _ _ step => (bind_ok_iff.mp step).imp fun _ found => found.1) _ _ _ folded _ inRange
  exact ⟨committee, back ▸ committeeOk⟩

/-- Successful slot reads suffice to read their finite window. -/
private theorem committeeWindow_exists_of_slots {store : Store preset fork} {head : Root}
    {first last afterLast : Slot} (afterOk : addChecked last 1 = .ok afterLast)
    (slots : ∀ slot, first ≤ slot → slot ≤ last →
      ∃ committee, store.getSlotCommittee head slot = .ok committee) :
    ∃ members, store.getCommitteesBetweenSlots head first last = .ok members := by
  simp only [Store.getCommitteesBetweenSlots, afterOk, Except.mapError, bind, Except.bind]
  apply foldlM_exists_ok_of_invariant (fun _ => True) _ _ trivial
  intro acc offset inRange _
  have offsetLt := List.mem_range.mp inRange
  have afterNat := (addChecked_ok_iff.mp afterOk).2
  have offsetBound : offset < 2 ^ 64 := by
    have := afterLast.toNat_lt
    omega
  have offsetNat : offset.toUInt64.toNat = offset := by
    simp [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' offsetBound]
  have slotNat : (first + offset.toUInt64).toNat = first.toNat + offset := by
    rw [UInt64.toNat_add, offsetNat, Nat.mod_eq_of_lt]
    have := afterLast.toNat_lt
    omega
  obtain ⟨committee, committeeOk⟩ := slots (first + offset.toUInt64)
    (UInt64.le_iff_toNat_le.mpr (by rw [slotNat]; omega))
    (UInt64.le_iff_toNat_le.mpr (by
      rw [slotNat]
      simp only [UInt64.toNat_one] at afterNat
      omega))
  exact ⟨committee.foldl Std.TreeSet.insert acc,
    by simp [committeeOk, pure, Except.pure], trivial⟩

/-- A successful window supplies every subrange's successful read. -/
private theorem committeeWindow_subrange {store : Store preset fork} {head : Root}
    {first last low high : Slot} {members : Std.TreeSet ValidatorIndex}
    (read : store.getCommitteesBetweenSlots head first last = .ok members)
    (lowIn : first ≤ low) (highIn : high ≤ last) :
    ∃ subrange, store.getCommitteesBetweenSlots head low high = .ok subrange := by
  have original := read
  simp only [Store.getCommitteesBetweenSlots, bind_ok_iff, mapError_ok_iff] at read
  obtain ⟨_, afterOk, _⟩ := read
  have afterNat := (addChecked_ok_iff.mp afterOk).1
  have highNat := UInt64.le_iff_toNat_le.mp highIn
  exact committeeWindow_exists_of_slots (addChecked_of_lt (by omega))
    (fun slot lowLe highLe => slotCommittee_exists_of_window original
      (UInt64.le_trans lowIn lowLe) (UInt64.le_trans highLe highIn))

/-- A window contains precisely the members of its successful slot reads. -/
private theorem mem_committeeWindow_iff {store : Store preset fork} {head : Root}
    {first last : Slot} {members : Std.TreeSet ValidatorIndex} {v : ValidatorIndex}
    (read : store.getCommitteesBetweenSlots head first last = .ok members) :
    v ∈ members ↔ ∃ slot committee, first ≤ slot ∧ slot ≤ last ∧
      store.getSlotCommittee head slot = .ok committee ∧ v ∈ committee := by
  simp only [Store.getCommitteesBetweenSlots, bind_ok_iff, mapError_ok_iff] at read
  obtain ⟨afterLast, afterOk, folded⟩ := read
  have afterNat := (addChecked_ok_iff.mp afterOk).2
  constructor
  · intro member
    rcases (mem_foldlM_committees_iff folded).mp member with empty |
        ⟨offset, inRange, committee, committeeOk, inside⟩
    · exact False.elim (Std.TreeSet.not_mem_emptyc empty)
    have offsetLt := List.mem_range.mp inRange
    have offsetBound : offset < 2 ^ 64 := by
      have := afterLast.toNat_lt
      omega
    have offsetNat : offset.toUInt64.toNat = offset := by
      simp [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' offsetBound]
    have slotNat : (first + offset.toUInt64).toNat = first.toNat + offset := by
      rw [UInt64.toNat_add, offsetNat, Nat.mod_eq_of_lt]
      have := afterLast.toNat_lt
      omega
    refine ⟨first + offset.toUInt64, committee, ?_, ?_, committeeOk, inside⟩
    · rw [UInt64.le_iff_toNat_le, slotNat]
      omega
    · rw [UInt64.le_iff_toNat_le, slotNat]
      simp only [UInt64.toNat_one] at afterNat
      omega
  · rintro ⟨slot, committee, low, high, committeeOk, inside⟩
    have lowNat := UInt64.le_iff_toNat_le.mp low
    have highNat := UInt64.le_iff_toNat_le.mp high
    have back : first + (slot.toNat - first.toNat).toUInt64 = slot := by
      rw [← UInt64.toNat_sub_of_le _ _ low, Nat.toUInt64_eq, UInt64.ofNat_toNat,
        UInt64.add_comm, UInt64.sub_add_cancel]
    refine (mem_foldlM_committees_iff folded).mpr (.inr
      ⟨slot.toNat - first.toNat, ?_, committee, ?_, inside⟩)
    · rw [List.mem_range]
      simp only [UInt64.toNat_one] at afterNat
      omega
    · rw [back]
      exact committeeOk

/-- Adjacent successful windows have the union of their active members. -/
private theorem activeMembers_window_union {store : Store preset fork} {head : Root}
    {state : BeaconState preset fork} {first middle before last : Slot}
    {left right whole : Std.TreeSet ValidatorIndex}
    (beforeOk : subChecked middle 1 = .ok before) (low : first ≤ middle) (high : before ≤ last)
    (leftOk : store.getCommitteesBetweenSlots head first before = .ok left)
    (rightOk : store.getCommitteesBetweenSlots head middle last = .ok right)
    (wholeOk : store.getCommitteesBetweenSlots head first last = .ok whole) :
    Store.activeMembers state whole =
      Store.activeMembers state left ∪ Store.activeMembers state right := by
  have beforeNat := (subChecked_ok_iff.mp beforeOk).2
  ext v
  simp only [Store.mem_activeMembers, Finset.mem_union]
  constructor
  · rintro ⟨member, validator, found, active⟩
    obtain ⟨slot, committee, firstLe, lastLe, committeeOk, inside⟩ :=
      (mem_committeeWindow_iff wholeOk).mp member
    by_cases old : slot < middle
    · left
      refine ⟨(mem_committeeWindow_iff leftOk).mpr
        ⟨slot, committee, firstLe, ?_, committeeOk, inside⟩, validator, found, active⟩
      have := UInt64.lt_iff_toNat_lt.mp old
      exact UInt64.le_iff_toNat_le.mpr (by
        simp only [UInt64.toNat_one] at beforeNat
        omega)
    · exact .inr ⟨(mem_committeeWindow_iff rightOk).mpr
        ⟨slot, committee, UInt64.not_lt.mp old, lastLe, committeeOk, inside⟩,
          validator, found, active⟩
  · rintro (⟨member, validator, found, active⟩ | ⟨member, validator, found, active⟩)
    · obtain ⟨slot, committee, firstLe, lastLe, committeeOk, inside⟩ :=
        (mem_committeeWindow_iff leftOk).mp member
      exact ⟨(mem_committeeWindow_iff wholeOk).mpr
        ⟨slot, committee, firstLe, UInt64.le_trans lastLe high, committeeOk, inside⟩,
          validator, found, active⟩
    · obtain ⟨slot, committee, firstLe, lastLe, committeeOk, inside⟩ :=
        (mem_committeeWindow_iff rightOk).mp member
      exact ⟨(mem_committeeWindow_iff wholeOk).mpr
        ⟨slot, committee, UInt64.le_trans low firstLe, lastLe, committeeOk, inside⟩,
          validator, found, active⟩

/-- A covered receiver window holds a whole epoch after the call and within the parent's seed.

The source stake outside that epoch's committees fits the reserve.

So the active source stake exceeds the members of a window through the epoch by at most it. -/
private theorem full_window_epoch {store : Store preset fork} {head : Root}
    {source : BeaconState preset fork} {parent slot lastSlot firstSlot current last : Slot}
    {window : Std.TreeSet ValidatorIndex} {receiverEpoch : Epoch} {reserve : Nat}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) (within : source.RegistryWithinLimit)
    (firstOk : addChecked parent 1 = .ok firstSlot) (lastOk : subChecked slot 1 = .ok lastSlot)
    (currentOk : store.getCurrentSlot config = .ok current)
    (receiverEpochOk : store.getCurrentStoreEpoch config = .ok receiverEpoch)
    (receiverLastOk : subChecked current 1 = .ok last)
    (covered : isFullValidatorSetCovered preset firstSlot last = .ok true)
    (windowOk : store.getCommitteesBetweenSlots head firstSlot last = .ok window)
    (callerAge : (computeEpochAtSlot preset slot).toNat ≤
      (computeEpochAtSlot preset parent).toNat + 1)
    (age : receiverEpoch.toNat ≤ (computeEpochAtSlot preset parent).toNat + 2)
    (exited : ∀ epoch epochStart next epochEnd epochMembers,
      computeStartSlotAtEpoch preset epoch = .ok epochStart →
      addChecked epochStart preset.SLOTS_PER_EPOCH = .ok next →
      subChecked next 1 = .ok epochEnd →
      firstSlot ≤ epochStart → epochEnd ≤ last →
      store.getCommitteesBetweenSlots head epochStart epochEnd = .ok epochMembers →
      stake (fun v => balanceAt source v.toNat) {v ∈ activeVoters source | v ∉ epochMembers} ≤
        reserve) :
    ∃ epochEnd, lastSlot ≤ epochEnd ∧ slot ≤ epochEnd ∧ epochEnd ≤ last ∧
      (computeEpochAtSlot preset epochEnd).toNat ≤ (computeEpochAtSlot preset parent).toNat + 1 ∧
      ∀ wide, store.getCommitteesBetweenSlots head firstSlot epochEnd = .ok wide →
        stake (fun v => balanceAt source v.toNat) (activeVoters source) ≤
          stake (fun v => balanceAt source v.toNat) (Store.activeMembers source wide) +
            reserve := by
  obtain ⟨epoch, epochStart, next, epochEnd, epochStartOk, nextOk, epochEndOk, startIn, endIn,
    startNat, endNat⟩ := epoch_of_covered positive covered
  have receiverEpochEq : receiverEpoch = computeEpochAtSlot preset current := by
    simpa [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
      using receiverEpochOk.symm
  rw [receiverEpochEq] at age
  simp only [computeEpochAtSlot, UInt64.toNat_div] at age callerAge ⊢
  have finish := subChecked_ok_iff.mp receiverLastOk
  have start := (addChecked_ok_iff.mp firstOk).2
  have low := UInt64.le_iff_toNat_le.mp startIn
  have high := UInt64.le_iff_toNat_le.mp endIn
  have lastNat := (subChecked_ok_iff.mp lastOk).2
  simp only [UInt64.toNat_one] at finish start lastNat
  have bounds := epoch_bounds_of_covered positive startNat endNat (by omega) (by omega)
    callerAge age
  obtain ⟨epochMembers, epochMembersOk⟩ := committeeWindow_subrange windowOk startIn endIn
  have outside := exited epoch epochStart next epochEnd epochMembers epochStartOk nextOk
    epochEndOk startIn endIn epochMembersOk
  refine ⟨epochEnd, UInt64.le_iff_toNat_le.mpr (by omega), UInt64.le_iff_toNat_le.mpr bounds.1,
    endIn, bounds.2, fun wide wideOk => ?_⟩
  have split : stake (fun v => balanceAt source v.toNat)
        {v ∈ activeVoters source | v ∈ epochMembers} +
      stake (fun v => balanceAt source v.toNat) {v ∈ activeVoters source | v ∉ epochMembers} =
      stake (fun v => balanceAt source v.toNat) (activeVoters source) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have inside : stake (fun v => balanceAt source v.toNat)
      {v ∈ activeVoters source | v ∈ epochMembers} ≤
      stake (fun v => balanceAt source v.toNat) (Store.activeMembers source wide) := by
    apply stake_mono
    intro v member
    obtain ⟨active, epochMember⟩ := Finset.mem_filter.mp member
    obtain ⟨validator, found, isActive⟩ := (mem_getActiveValidatorIndices within).mp
      (List.mem_toFinset.mp active)
    obtain ⟨dutySlot, committee, dutyLow, dutyHigh, committeeOk, inCommittee⟩ :=
      (mem_committeeWindow_iff epochMembersOk).mp epochMember
    exact Store.mem_activeMembers.mpr ⟨(mem_committeeWindow_iff wideOk).mpr
      ⟨dutySlot, committee, UInt64.le_trans startIn dutyLow, dutyHigh, committeeOk,
        inCommittee⟩, validator, found, isActive⟩
  omega

/-- The adversary window starts after the parent and no later than the block. -/
private theorem adversary_window_bounds {store : Store preset fork} {head root : Root}
    {source : BeaconState preset fork} {slot first last : Slot}
    {block parent : BeaconBlock preset fork} {adversary : Gwei}
    (slotOk : store.getCurrentSlot config = .ok slot)
    (blockOk : store.block root = .ok block)
    (parentOk : store.block block.parentRoot = .ok parent)
    (firstOk : addChecked parent.slot 1 = .ok first)
    (lastOk : subChecked slot 1 = .ok last) (earlier : parent.slot < block.slot)
    (read : store.getAdversarialWeight config head source root = .ok adversary) :
    ∃ start, first ≤ start ∧ start ≤ block.slot ∧
      store.computeAdversarialWeight config head source start last = .ok adversary := by
  simp only [Store.getAdversarialWeight, Store.getBlockEpoch, slotOk, blockOk, parentOk,
    lastOk, Except.mapError, bind, Except.bind, pure, Except.pure] at read
  have firstNat := (addChecked_ok_iff.mp firstOk).2
  have earlierNat := UInt64.lt_iff_toNat_lt.mp earlier
  split at read
  · rename_i across
    obtain ⟨start, startOk, rangeOk⟩ := bind_ok_iff.mp read
    have startNat := (computeStartSlotAtEpoch_ok_iff.mp (mapError_ok_iff.mp startOk)).2
    have epochs := UInt64.lt_iff_toNat_lt.mp across
    simp only [computeEpochAtSlot, UInt64.toNat_div] at startNat epochs
    refine ⟨start, UInt64.le_iff_toNat_le.mpr ?_, UInt64.le_iff_toNat_le.mpr ?_, rangeOk⟩
    · have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by
        by_contra zero
        simp [Nat.eq_zero_of_not_pos zero] at epochs
      have parentBefore := Nat.lt_mul_of_div_lt epochs positive
      simp only [UInt64.toNat_one] at firstNat
      omega
    · have := Nat.div_mul_le_self block.slot.toNat preset.SLOTS_PER_EPOCH.toNat
      omega
  · exact ⟨block.slot, UInt64.le_iff_toNat_le.mpr (by
      simp only [UInt64.toNat_one] at firstNat
      omega), UInt64.le_refl _, read⟩

/-- Partial receiver windows transfer their readable subranges to the caller's Byzantine bound. -/
private theorem sourceByzantine_of_partial_parent_window
    [DecidablePred (· ∈ J)] {anchor : Store preset fork} {limit : Nat}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (oneBlock : OneBlockPerRoot e limit) (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) (preGloas : fork < .glamsterdam)
    (lookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat ∧ 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat ∧
      preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : Nat}
    (callerBound : (e.world n).time ≤ limit) (receiverBound : (e.world k).time ≤ limit)
    {parent : Root} {parentBlock : BeaconBlock preset fork}
    (callerParentKnown : ((e.world n).state u).blocks[parent]? = some parentBlock)
    (receiverParentKnown : ((e.world k).state w).blocks[parent]? = some parentBlock)
    {firstHead secondHead : ForkChoiceNode}
    (firstAbove : ((e.world n).state u).isAncestor firstHead ⟨parent, .pending⟩ = .ok true)
    (secondAbove : ((e.world k).state w).isAncestor secondHead ⟨parent, .pending⟩ = .ok true)
    {callerEpoch receiverEpoch : Epoch}
    (callerEpochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok callerEpoch)
    (receiverEpochOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok receiverEpoch)
    (recent : callerEpoch.toNat ≤ (computeEpochAtSlot preset parentBlock.slot).toNat + 1)
    (age : receiverEpoch.toNat ≤ (computeEpochAtSlot preset parentBlock.slot).toNat + 2)
    {source : BeaconState preset fork}
    (sourceBound : ∀ low high members,
      ((e.world n).state u).getCommitteesBetweenSlots firstHead.root low high = .ok members →
      ByzantineStakeAtMost (fun v => balanceAt source v.toNat)
        (Store.activeMembers source members) J
        config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100)
    {first last current low high : Slot} {members : Std.TreeSet ValidatorIndex}
    (firstOk : addChecked parentBlock.slot 1 = .ok first)
    (lastOk : subChecked current 1 = .ok last)
    (uncovered : isFullValidatorSetCovered preset first last = .ok false)
    (lowIn : first ≤ low) (highIn : high ≤ last)
    (read : ((e.world k).state w).getCommitteesBetweenSlots secondHead.root low high =
      .ok members) :
    ByzantineStakeAtMost (fun v => balanceAt source v.toNat)
      (Store.activeMembers source members) J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100 := by
  have epochBound := epoch_le_of_partial_parent_window positive firstOk lastOk uncovered
  apply sourceBound low high members
  apply committeeWindow_transfer read
  intro dutySlot lowLe highLe
  have parentLow : parentBlock.slot ≤ dutySlot := by
    have start := (addChecked_ok_iff.mp firstOk).2
    have lower := UInt64.le_iff_toNat_le.mp (UInt64.le_trans lowIn lowLe)
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  have currentHigh : dutySlot ≤ current := by
    have finish := (subChecked_ok_iff.mp lastOk).2
    have upper := UInt64.le_iff_toNat_le.mp (UInt64.le_trans highLe highIn)
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  have highEpoch : (computeEpochAtSlot preset dutySlot).toNat ≤
      (computeEpochAtSlot preset parentBlock.slot).toNat + 1 := by
    apply Nat.le_trans _ epochBound
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp currentHigh)
  exact (slotCommittee_eq_of_recent_parent anchorStore anchorSlot anchored oneBlock slots
    preGloas lookahead caller receiver callerBound receiverBound callerParentKnown
    receiverParentKnown firstAbove secondAbove callerEpochOk receiverEpochOk recent age
    parentLow highEpoch).symm

/-- A receiver window from the parent through its next epoch is also the caller's window. -/
private theorem callerWindow_of_recent_parent {anchor : Store preset fork} {limit : Nat}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (oneBlock : OneBlockPerRoot e limit) (slots : 0 < config.SLOT_DURATION_MS)
    (preGloas : fork < .glamsterdam)
    (lookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat ∧ 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat ∧
      preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : Nat}
    (callerBound : (e.world n).time ≤ limit) (receiverBound : (e.world k).time ≤ limit)
    {parent : Root} {parentBlock : BeaconBlock preset fork}
    (callerParentKnown : ((e.world n).state u).blocks[parent]? = some parentBlock)
    (receiverParentKnown : ((e.world k).state w).blocks[parent]? = some parentBlock)
    {firstHead secondHead : ForkChoiceNode}
    (firstAbove : ((e.world n).state u).isAncestor firstHead ⟨parent, .pending⟩ = .ok true)
    (secondAbove : ((e.world k).state w).isAncestor secondHead ⟨parent, .pending⟩ = .ok true)
    {callerEpoch receiverEpoch : Epoch}
    (callerEpochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok callerEpoch)
    (receiverEpochOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok receiverEpoch)
    (recent : callerEpoch.toNat ≤ (computeEpochAtSlot preset parentBlock.slot).toNat + 1)
    (age : receiverEpoch.toNat ≤ (computeEpochAtSlot preset parentBlock.slot).toNat + 2)
    {low high : Slot} {members : Std.TreeSet ValidatorIndex}
    (lowIn : parentBlock.slot ≤ low)
    (highEpoch : (computeEpochAtSlot preset high).toNat ≤
      (computeEpochAtSlot preset parentBlock.slot).toNat + 1)
    (read : ((e.world k).state w).getCommitteesBetweenSlots secondHead.root low high =
      .ok members) :
    ((e.world n).state u).getCommitteesBetweenSlots firstHead.root low high = .ok members := by
  apply committeeWindow_transfer read
  intro dutySlot lowLe highLe
  have dutyEpoch : (computeEpochAtSlot preset dutySlot).toNat ≤
      (computeEpochAtSlot preset parentBlock.slot).toNat + 1 := by
    have lower := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
      (UInt64.le_iff_toNat_le.mp highLe)
    simp only [computeEpochAtSlot, UInt64.toNat_div] at highEpoch ⊢
    omega
  exact (slotCommittee_eq_of_recent_parent anchorStore anchorSlot anchored oneBlock slots
    preGloas lookahead caller receiver callerBound receiverBound callerParentKnown
    receiverParentKnown firstAbove secondAbove callerEpochOk receiverEpochOk recent age
    (UInt64.le_trans lowIn lowLe) dutyEpoch).symm

/-- Equal slot committees transfer a maximum read under the same balance state. -/
private theorem maximum_of_same_slotCommittees {left right : Store preset fork}
    {first second : Root} {source : BeaconState preset fork} {low high : Slot} {maximum : Gwei}
    (read : left.computeCommitteeWeightBetweenSlots first source low high = .ok maximum)
    (same : ∀ slot, low ≤ slot → slot ≤ high →
      left.getSlotCommittee first slot = right.getSlotCommittee second slot) :
    right.computeCommitteeWeightBetweenSlots second source low high = .ok maximum := by
  by_cases empty : high < low
  · rw [Store.computeCommitteeWeightBetweenSlots_of_gt empty] at read ⊢
    exact read
  simp only [Store.computeCommitteeWeightBetweenSlots, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at read ⊢
  obtain ⟨⟨total, members⟩, read, rfl⟩ := read
  refine ⟨(total, members), ?_, rfl⟩
  simp only [Store.computeCommitteeWeightAndMembers, empty, ↓reduceIte, bind_ok_iff] at read ⊢
  obtain ⟨covered, coveredOk, read⟩ := read
  refine ⟨covered, coveredOk, ?_⟩
  cases covered
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok_iff] at read ⊢
    obtain ⟨participants, windowRead, rest⟩ := read
    refine ⟨participants, ?_, rest⟩
    exact committeeWindow_transfer windowRead same
  · exact read

/-- A recent counted supporter belongs to every head-committee window containing its vote. -/
private theorem supporters_mem_committeeWindow {limit : Nat}
    (committees : CommitteesFollow e limit)
    {u : ValidatorIndex} (caller : u ∈ J) {n : Nat} (bounded : (e.world n).time ≤ limit)
    {head : ForkChoiceNode} {headState source : BeaconState preset fork}
    {current : Epoch} {root : Root} {block : BeaconBlock preset fork}
    {slot first last : Slot} {participants : Std.TreeSet ValidatorIndex}
    (origins : ((e.world n).state u).VotesHaveOrigins config)
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (stateOk : ((e.world n).state u).blockState head.root = .ok headState)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok current)
    (blockOk : ((e.world n).state u).block root = .ok block)
    (recent : current.toNat ≤ (computeEpochAtSlot preset block.slot).toNat + 1)
    (firstLe : first ≤ block.slot) (lastOk : subChecked slot 1 = .ok last)
    (windowOk : ((e.world n).state u).getCommitteesBetweenSlots head.root first last =
      .ok participants) :
    ∀ v ∈ ((e.world n).state u).supportersOf source ⟨root, .pending⟩,
      v ∈ participants := by
  intro v supporter
  obtain ⟨attestation, _, origin, blockLe, high⟩ :=
    origins.slot_mem_range_of_mem_supportersOf blockOk (UInt64.le_refl _) slotOk lastOk supporter
  have epochEq : current = computeEpochAtSlot preset slot := by
    simpa [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure] using
      epochOk.symm
  have monotone {a b : Slot} (le : a ≤ b) :
      (computeEpochAtSlot preset a).toNat ≤ (computeEpochAtSlot preset b).toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp le)
  obtain ⟨readSlot, readOk, past⟩ := origin.past
  rw [slotOk, Except.ok.injEq] at readOk
  subst readSlot
  have targetPast : attestation.data.target.epoch.toNat ≤ current.toNat := by
    rw [origin.targetEpoch, epochEq]
    exact monotone (UInt64.le_of_lt past)
  have targetRecent : current.toNat ≤ attestation.data.target.epoch.toNat + 1 := by
    rw [origin.targetEpoch]
    exact recent.trans (Nat.add_le_add_right (monotone blockLe) 1)
  obtain ⟨targetState, index, committee, targetOk, below, committeeOk, member⟩ :=
    origin.exists_mem_committee
  obtain ⟨common, headRun, targetRun, final, fixed, headRing, targetRing⟩ :=
    committees.common u caller n bounded head headState current v attestation targetState
      headOk stateOk epochOk targetPast targetRecent origin targetOk
  have headKept := headRun.committeesKept final fixed headRing
  have targetKept := targetRun.committeesKept final fixed targetRing
  have same := (headKept attestation.data.slot index origin.targetEpoch.symm).trans
    (targetKept attestation.data.slot index origin.targetEpoch.symm).symm
  have active := (headRun.active.getActiveValidatorIndices_eq fixed).trans
    (targetRun.active.getActiveValidatorIndices_eq fixed).symm
  have count :
      getCommitteeCountPerSlot headState (computeEpochAtSlot preset attestation.data.slot) =
      getCommitteeCountPerSlot targetState (computeEpochAtSlot preset attestation.data.slot) := by
    simp only [← origin.targetEpoch, getCommitteeCountPerSlot, active]
  exact Store.mem_getCommitteesBetweenSlots windowOk (UInt64.le_trans firstLe blockLe) high
    stateOk (count ▸ below) (same.trans committeeOk) member

/-- Removing Byzantine counted votes preserves the raw confirmation margin, including its shift. -/
private theorem honest_margin_of_raw_bound {store : Store preset fork}
    [DecidablePred (· ∈ J)] {head root : Root} {source : BeaconState preset fork}
    {first last : Slot} {participants : Std.TreeSet ValidatorIndex}
    {maximum score support discount adversary : Gwei} {shift : Nat}
    (within : source.RegistryWithinLimit)
    (supportOk : store.scoreFromTally (store.tallyVotes source) ⟨root, .pending⟩ = .ok support)
    (rangeOk : store.computeAdversarialWeight config head source first last = .ok adversary)
    (participantsOk : store.getCommitteesBetweenSlots head first last = .ok participants)
    (supportersIn : ∀ v ∈ store.supportersOf source ⟨root, .pending⟩, v ∈ participants)
    (aligned : EffectiveBalancesAligned source)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (dishonest : ∀ v ∈ store.equivocatingIndices, v ∉ J)
    (byzantine : ByzantineStakeAtMost (fun v => balanceAt source v.toNat)
      (Store.activeMembers source participants) J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100)
    (base : maximum.toNat + score.toNat + 2 * adversary.toNat + shift <
      discount.toNat + 2 * support.toNat) :
    maximum.toNat + score.toNat + shift < discount.toNat +
      2 * stake (fun v => balanceAt source v.toNat)
        {v ∈ store.supportersOf source ⟨root, .pending⟩ | v ∈ J} := by
  obtain ⟨weight, equivocation, weightOk, equivocationOk⟩ :=
    Store.computeAdversarialWeight_eq_ok rangeOk
  obtain ⟨found, foundOk, equivocators⟩ :=
    Store.exists_stake_equivocatorsOf_of_getEquivocationScore equivocationOk
  rw [participantsOk, Except.ok.injEq] at foundOk
  subst found
  have cover := Store.threshold_mul_stake_le_of_computeAdversarialWeight weightOk equivocationOk
    rangeOk (Store.stake_le_computeCommitteeWeightBetweenSlots participantsOk weightOk
      fun v member => Store.mem_activeMembers.mp member)
    (fun v _ => Nat.mod_eq_zero_of_dvd (dvd_balanceAt_of_aligned aligned
      (Nat.dvd_of_mod_eq_zero increment) v.toNat))
  rw [← equivocators] at cover
  have clean := Models.ForkChoice.sub_le_honest_support byzantine
    (fun v member => Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
      (Std.TreeSet.mem_toList.mpr (supportersIn v member)),
        Store.isActiveAt_of_mem_supportersOf within member⟩)
    Store.equivocatorsOf_subset_activeMembers Store.disjoint_supportersOf_equivocatorsOf
    (fun v member => dishonest v (Finset.mem_filter.mp member).2) cover
  rw [Store.stake_supportersOf within supportOk] at clean
  omega

/-- The raw check of a recent block gives an honest margin at the caller, with its shift. -/
private theorem honest_margin_of_recent_check {limit : Nat}
    [DecidablePred (· ∈ J)] (committees : CommitteesFollow e limit)
    {u : ValidatorIndex} (caller : u ∈ J) {n : Nat} (bounded : (e.world n).time ≤ limit)
    {head : ForkChoiceNode} {headState source : BeaconState preset fork}
    {current : Epoch} {root : Root} {block : BeaconBlock preset fork}
    {slot last : Slot} {maximum score support discount adversary : Gwei}
    {shift parentStake : Nat}
    (origins : ((e.world n).state u).VotesHaveOrigins config)
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (stateOk : ((e.world n).state u).blockState head.root = .ok headState)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok current)
    (blockOk : ((e.world n).state u).block root = .ok block)
    (recent : current.toNat ≤ (computeEpochAtSlot preset block.slot).toNat + 1)
    (lastOk : subChecked slot 1 = .ok last)
    (within : source.RegistryWithinLimit)
    (supportOk : ((e.world n).state u).scoreFromTally
      (((e.world n).state u).tallyVotes source) ⟨root, .pending⟩ = .ok support)
    (adversaryOk : ((e.world n).state u).getAdversarialWeight config head.root source root =
      .ok adversary)
    (aligned : EffectiveBalancesAligned source)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (dishonest : ∀ v ∈ ((e.world n).state u).equivocatingIndices, v ∉ J)
    (byzantine : ∀ first last participants,
      ((e.world n).state u).getCommitteesBetweenSlots head.root first last = .ok participants →
      ByzantineStakeAtMost (fun v => balanceAt source v.toNat)
        (Store.activeMembers source participants) J
        config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100)
    (base : maximum.toNat + score.toNat + 2 * adversary.toNat + shift <
      discount.toNat + 2 * support.toNat)
    (parentBound : discount.toNat ≤ parentStake) :
    maximum.toNat + score.toNat + shift < parentStake +
      2 * stake (fun v => balanceAt source v.toNat)
        {v ∈ ((e.world n).state u).supportersOf source ⟨root, .pending⟩ | v ∈ J} := by
  obtain ⟨readSlot, readBlock, start, readLast, readSlotOk, readBlockOk, readLastOk,
    startOk, rangeOk⟩ := Store.getAdversarialWeight_eq_ok adversaryOk
  rw [slotOk, Except.ok.injEq] at readSlotOk
  subst readSlot
  rw [blockOk, Except.ok.injEq] at readBlockOk
  subst readBlock
  rw [lastOk, Except.ok.injEq] at readLastOk
  subst readLast
  obtain ⟨weight, equivocation, _, equivocationOk⟩ := Store.computeAdversarialWeight_eq_ok rangeOk
  obtain ⟨participants, participantsOk, _⟩ :=
    Store.exists_stake_equivocatorsOf_of_getEquivocationScore equivocationOk
  have startLe : start ≤ block.slot := by
    rcases startOk with rfl | boundary
    · exact UInt64.le_refl _
    · apply UInt64.le_iff_toNat_le.mpr
      rw [(computeStartSlotAtEpoch_ok_iff.mp boundary).2]
      exact Nat.div_mul_le_self _ _
  have inside := supporters_mem_committeeWindow committees caller bounded origins headOk stateOk
    slotOk epochOk blockOk recent startLe lastOk participantsOk (source := source)
  exact (honest_margin_of_raw_bound within supportOk rangeOk participantsOk inside aligned
    increment dishonest (byzantine _ _ _ participantsOk) base).trans_le
    (Nat.add_le_add_right parentBound _)

/-- The caller reserve pays for new Byzantine duties after honest gains are counted.

Fresh members lie outside the old support window.

Prefix members lie in that window but outside its adversary window.

Honest fresh members gain two units of support weight.

Honest prefix members gain at least one.

All weights use the caller's balance source. -/
private theorem margin_of_fresh_duty_partition
    {share adversary equivocators countedByzantine oldByzantine adversaryMaximum : Nat}
    {freshHonest prefixHonest freshByzantine prefixByzantine reserve : Nat}
    {maximum laterMaximum score shift parents supporters laterParents laterSupporters : Nat}
    (half : 2 * share ≤ 100)
    (unionBound : 100 * (oldByzantine + freshByzantine + prefixByzantine) + 50 * reserve ≤
      share * (adversaryMaximum + freshHonest + prefixHonest +
        freshByzantine + prefixByzantine))
    (adversaryBound : share * adversaryMaximum ≤ 100 * (adversary + equivocators))
    (apart : equivocators + countedByzantine ≤ oldByzantine)
    (base : maximum + score + 2 * adversary + shift < parents +
      2 * supporters + 2 * countedByzantine)
    (growth : laterMaximum ≤ maximum + freshHonest + freshByzantine + reserve)
    (gain : parents + 2 * supporters + 2 * freshHonest + prefixHonest ≤
      laterParents + 2 * laterSupporters) :
    laterMaximum + score + shift < laterParents + 2 * laterSupporters := by
  have paid : freshByzantine + prefixByzantine + 2 * countedByzantine + reserve ≤
      freshHonest + prefixHonest + 2 * adversary := by
    have scaledHalf := Nat.mul_le_mul_right
      (freshHonest + prefixHonest + freshByzantine + prefixByzantine) half
    have scaledApart := Nat.mul_le_mul_left 100 apart
    nlinarith
  omega

/-- Fresh honest duties gain two votes outside the old window and one outside its reserve. -/
private theorem stake_gain_of_fresh_duties {α : Type} [DecidableEq α]
    (weight : α → Nat) (A W G S P : Finset α) (honest : Set α)
    [DecidablePred (· ∈ honest)] (nested : A ⊆ W)
    (supportersIn : S ⊆ A) (parentsIn : P ⊆ W)
    (apart : Disjoint S P) :
    stake weight P + 2 * stake weight S +
        2 * stake weight {v ∈ G \ W | v ∈ honest} +
        stake weight {v ∈ (G ∩ W) \ A | v ∈ honest} ≤
      stake weight (P \ {v ∈ G | v ∈ honest}) +
        2 * stake weight (S ∪ {v ∈ G | v ∈ honest}) := by
  let all := S ∪ P ∪ G
  have indicator (members : Finset α) (inside : members ⊆ all) :
      (∑ v ∈ all, if v ∈ members then weight v else 0) = stake weight members := by
    rw [← Finset.sum_filter]
    have filtered : all.filter (fun v => v ∈ members) = members := by
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨inside h, h⟩⟩
    rw [filtered]
    rfl
  have pointwise := Finset.sum_le_sum (s := all)
    (f := fun v => (if v ∈ P then weight v else 0) +
      2 * (if v ∈ S then weight v else 0) +
      2 * (if v ∈ G \ W ∧ v ∈ honest then weight v else 0) +
      (if v ∈ (G ∩ W) \ A ∧ v ∈ honest then weight v else 0))
    (g := fun v => (if v ∈ P \ {v ∈ G | v ∈ honest} then weight v else 0) +
      2 * (if v ∈ S ∪ {v ∈ G | v ∈ honest} then weight v else 0)) (fun v _ => by
      have inA := fun h => supportersIn (x := v) h
      have inW := fun h => parentsIn (x := v) h
      have aInW := fun h => nested (x := v) h
      have distinct : v ∈ S → v ∈ P → False := fun hs hp =>
        Finset.disjoint_left.mp apart hs hp
      by_cases hs : v ∈ S <;> by_cases hp : v ∈ P <;>
        by_cases hg : v ∈ G <;> by_cases hw : v ∈ W <;>
        by_cases ha : v ∈ A <;> by_cases hj : v ∈ honest <;>
        simp_all <;> omega)
  simpa only [← Finset.mem_filter, Finset.sum_add_distrib, ← Finset.mul_sum,
    indicator P (by intro v h; simp [all, h]),
    indicator S (by intro v h; simp [all, h]),
    indicator {v ∈ G \ W | v ∈ honest} (by
      intro v h; have := (Finset.mem_sdiff.mp (Finset.mem_filter.mp h).1).1; simp [all, this]),
    indicator {v ∈ (G ∩ W) \ A | v ∈ honest} (by
      intro v h
      have := (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp h).1).1).1
      simp [all, this]),
    indicator (P \ {v ∈ G | v ∈ honest}) (by
      intro v h; have := (Finset.mem_sdiff.mp h).1; simp [all, this]),
    indicator (S ∪ {v ∈ G | v ∈ honest}) (by
      intro v h
      rcases Finset.mem_union.mp h with h | h
      · simp [all, h]
      · simp [all, (Finset.mem_filter.mp h).1])] using pointwise

/-- The actual duty-set partition discharges the scalar transport certificate. -/
private theorem margin_of_fresh_duty_sets {α : Type} [DecidableEq α]
    (weight : α → Nat) (A W G S P : Finset α) (honest : Set α)
    [DecidablePred (· ∈ honest)] {share adversary equivocation countedByzantine : Nat}
    {maximum laterMaximum score shift : Nat}
    (nested : A ⊆ W) (supportersIn : S ⊆ A) (parentsIn : P ⊆ W) (apart : Disjoint S P)
    (half : 2 * share ≤ 100)
    {reserve : Nat}
    (byzantine : 100 * stake weight {v ∈ A ∪ G | v ∉ honest} + 50 * reserve ≤
      share * stake weight (A ∪ G))
    (cover : share * stake weight A ≤ 100 * (adversary + equivocation))
    (oldByzantine : equivocation + countedByzantine ≤ stake weight {v ∈ A | v ∉ honest})
    (base : maximum + score + 2 * adversary + shift <
      stake weight P + 2 * stake weight S + 2 * countedByzantine)
    (growth : laterMaximum ≤ maximum + stake weight (G \ W) + reserve) :
    laterMaximum + score + shift < stake weight (P \ {v ∈ G | v ∈ honest}) +
      2 * stake weight (S ∪ {v ∈ G | v ∈ honest}) := by
  let T := G \ W
  let I := (G ∩ W) \ A
  have partition : A ∪ G = A ∪ T ∪ I := by
    ext v
    have inside := fun h => nested (x := v) h
    simp only [T, I, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have firstApart : Disjoint A T := by
    apply Finset.disjoint_left.mpr
    intro v ha ht
    exact (Finset.mem_sdiff.mp ht).2 (nested ha)
  have lastApart : Disjoint (A ∪ T) I := by
    apply Finset.disjoint_left.mpr
    intro v hat hi
    have inI := Finset.mem_sdiff.mp hi
    rcases Finset.mem_union.mp hat with ha | ht
    · exact inI.2 ha
    · exact (Finset.mem_sdiff.mp ht).2 (Finset.mem_inter.mp inI.1).2
  have sumParts (value : α → Nat) :
      stake value (A ∪ G) = stake value A + stake value T + stake value I := by
    rw [partition]
    exact (Finset.sum_union lastApart).trans
      (congrArg (· + stake value I) (Finset.sum_union firstApart))
  let bad := fun v => if v ∉ honest then weight v else 0
  have badFilter (V : Finset α) : stake bad V = stake weight {v ∈ V | v ∉ honest} := by
    simp only [stake, bad, Finset.sum_filter]
  have badParts := sumParts bad
  rw [badFilter, badFilter, badFilter, badFilter] at badParts
  have totalParts := sumParts weight
  have splitT : stake weight {v ∈ T | v ∈ honest} +
      stake weight {v ∈ T | v ∉ honest} = stake weight T :=
    Finset.sum_filter_add_sum_filter_not T (· ∈ honest) weight
  have splitI : stake weight {v ∈ I | v ∈ honest} +
      stake weight {v ∈ I | v ∉ honest} = stake weight I :=
    Finset.sum_filter_add_sum_filter_not I (· ∈ honest) weight
  apply margin_of_fresh_duty_partition half (oldByzantine :=
    stake weight {v ∈ A | v ∉ honest})
    (freshHonest := stake weight {v ∈ T | v ∈ honest})
    (prefixHonest := stake weight {v ∈ I | v ∈ honest})
    (freshByzantine := stake weight {v ∈ T | v ∉ honest})
    (prefixByzantine := stake weight {v ∈ I | v ∉ honest})
    (adversaryMaximum := stake weight A)
  · have bound := byzantine
    rw [badParts, totalParts, ← splitT, ← splitI] at bound
    exact le_of_le_of_eq bound (by ring)
  · exact cover
  · exact oldByzantine
  · exact base
  · change laterMaximum ≤ maximum + stake weight T + reserve at growth
    omega
  · exact stake_gain_of_fresh_duties weight A W G S P honest nested supportersIn parentsIn apart

/-- A partial-window margin separates counted Byzantine support from honest promotion. -/
private theorem honest_margin_of_partial_sets {store : Store preset fork}
    [DecidablePred (· ∈ J)] {source : BeaconState preset fork} {node : ForkChoiceNode}
    {A W G P : Finset ValidatorIndex} {participants : Std.TreeSet ValidatorIndex}
    {share maximum laterMaximum score shift discount adversary equivocation : Nat}
    {support : Gwei}
    (within : source.RegistryWithinLimit) (nested : A ⊆ W)
    (supportersIn : store.supportersOf source node ⊆ A) (parentsIn : P ⊆ W)
    (apart : Disjoint {v ∈ store.supportersOf source node | v ∈ J} P)
    (equivocatorsIn : store.equivocatorsOf source participants ⊆ A)
    (dishonest : ∀ v ∈ store.equivocatingIndices, v ∉ J)
    (equivocationValue : stake (fun v => balanceAt source v.toNat)
      (store.equivocatorsOf source participants) = equivocation)
    (supportOk : store.scoreFromTally (store.tallyVotes source) node = .ok support)
    (half : 2 * share ≤ 100)
    {reserve : Nat}
    (byzantine : 100 * stake (fun v => balanceAt source v.toNat) {v ∈ A ∪ G | v ∉ J} +
      50 * reserve ≤ share * stake (fun v => balanceAt source v.toNat) (A ∪ G))
    (cover : share * stake (fun v => balanceAt source v.toNat) A ≤
      100 * (adversary + equivocation))
    (base : maximum + score + 2 * adversary + shift < discount + 2 * support.toNat)
    (parentDiscount : discount ≤ stake (fun v => balanceAt source v.toNat) P)
    (growth : laterMaximum ≤ maximum + stake (fun v => balanceAt source v.toNat) (G \ W) +
      reserve) :
    laterMaximum + score + shift <
      stake (fun v => balanceAt source v.toNat) (P \ {v ∈ G | v ∈ J}) +
      2 * stake (fun v => balanceAt source v.toNat)
        ({v ∈ store.supportersOf source node | v ∈ J} ∪ {v ∈ G | v ∈ J}) := by
  let badSupporters := {v ∈ store.supportersOf source node | v ∉ J}
  have badApart : Disjoint (store.equivocatorsOf source participants) badSupporters :=
    (Store.disjoint_supportersOf_equivocatorsOf (store := store) (state := source)
      (balanceSource := source) (node := node) (participants := participants)).symm.mono
      (Finset.Subset.refl _) (Finset.filter_subset _ _)
  have badCover : equivocation + stake (fun v => balanceAt source v.toNat) badSupporters ≤
      stake (fun v => balanceAt source v.toNat) {v ∈ A | v ∉ J} := by
    rw [← equivocationValue]
    change (∑ v ∈ store.equivocatorsOf source participants, balanceAt source v.toNat) +
      (∑ v ∈ badSupporters, balanceAt source v.toNat) ≤ _
    rw [← Finset.sum_union badApart]
    apply stake_mono
    intro v member
    rcases Finset.mem_union.mp member with equivocated | supports
    · exact Finset.mem_filter.mpr ⟨equivocatorsIn equivocated,
        dishonest v (Finset.mem_filter.mp equivocated).2⟩
    · exact Finset.mem_filter.mpr ⟨supportersIn (Finset.mem_filter.mp supports).1,
        (Finset.mem_filter.mp supports).2⟩
  have rawSupport := Store.stake_supportersOf (store := store) (node := node) within supportOk
  have splitSupport :
      stake (fun v => balanceAt source v.toNat) {v ∈ store.supportersOf source node | v ∈ J} +
      stake (fun v => balanceAt source v.toNat) badSupporters = support.toNat := by
    rw [← rawSupport]
    exact Finset.sum_filter_add_sum_filter_not _ (· ∈ J) _
  have checked : maximum + score + 2 * adversary + shift <
      stake (fun v => balanceAt source v.toNat) P +
        2 * stake (fun v => balanceAt source v.toNat)
          {v ∈ store.supportersOf source node | v ∈ J} +
        2 * stake (fun v => balanceAt source v.toNat) badSupporters := by omega
  have honestSupportersIn : {v ∈ store.supportersOf source node | v ∈ J} ⊆ A :=
    (Finset.filter_subset _ _).trans supportersIn
  have certificate := margin_of_fresh_duty_sets (fun v => balanceAt source v.toNat) A W G
    {v ∈ store.supportersOf source node | v ∈ J} P J
    (share := share) (adversary := adversary) (equivocation := equivocation)
    (countedByzantine := stake (fun v => balanceAt source v.toNat) badSupporters)
    (maximum := maximum) (laterMaximum := laterMaximum) (score := score) (shift := shift)
    (reserve := reserve) nested
    honestSupportersIn parentsIn apart half
  have certificate := certificate byzantine cover badCover
  exact certificate checked growth

/-- Disjoint child supporters and parent voters can move to child support without losing weight. -/
private theorem stake_le_of_supporter_parent_transport {α : Type} [DecidableEq α]
    (weight targetWeight : α → Nat) (supporters parents targetSupporters targetParents : Finset α)
    (apart : Disjoint supporters parents)
    (weights : ∀ v, weight v ≤ targetWeight v)
    (support : ∀ v ∈ supporters, 0 < weight v → v ∈ targetSupporters)
    (parent : ∀ v ∈ parents, 0 < weight v → v ∈ targetSupporters ∨ v ∈ targetParents) :
    2 * stake weight supporters + stake weight parents ≤
      2 * stake targetWeight targetSupporters + stake targetWeight targetParents := by
  let all := supporters ∪ parents ∪ targetSupporters ∪ targetParents
  have indicator (members : Finset α) (value : α → Nat) (inside : members ⊆ all) :
      (∑ v ∈ all, if v ∈ members then value v else 0) = stake value members := by
    rw [← Finset.sum_filter]
    have filtered : all.filter (fun v => v ∈ members) = members := by
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨inside h, h⟩⟩
    rw [filtered]
    rfl
  have pointwise := Finset.sum_le_sum (s := all)
    (f := fun v => 2 * (if v ∈ supporters then weight v else 0) +
      (if v ∈ parents then weight v else 0))
    (g := fun v => 2 * (if v ∈ targetSupporters then targetWeight v else 0) +
      (if v ∈ targetParents then targetWeight v else 0)) (fun v _ => by
      have disjoint : v ∈ supporters → v ∈ parents → False :=
        fun hs hp => Finset.disjoint_left.mp apart hs hp
      have bounded := weights v
      by_cases zero : weight v = 0
      · simp only [zero, ite_self, Nat.mul_zero, Nat.zero_add]
        exact Nat.zero_le _
      have positive : 0 < weight v := Nat.pos_of_ne_zero zero
      by_cases hs : v ∈ supporters
      · have child := support v hs positive
        simp only [ite_eq_left hs, ite_eq_right (disjoint hs), ite_eq_left child]
        omega
      by_cases hp : v ∈ parents
      · rcases parent v hp positive with child | stays
        · simp only [ite_eq_right hs, ite_eq_left hp, ite_eq_left child]
          omega
        · simp only [ite_eq_right hs, ite_eq_left hp, ite_eq_left stays]
          omega
      · simp only [ite_eq_right hs, ite_eq_right hp, Nat.mul_zero, Nat.zero_add]
        exact Nat.zero_le _)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
    indicator supporters weight (by intro v h; simp [all, h]),
    indicator parents weight (by intro v h; simp [all, h]),
    indicator targetSupporters targetWeight (by intro v h; simp [all, h]),
    indicator targetParents targetWeight (by intro v h; simp [all, h])] using pointwise

/-- A counted child supporter cannot have its latest vote at the strictly earlier parent. -/
private theorem disjoint_supporters_parentVoters {store : Store preset fork}
    {source : BeaconState preset fork} {root : Root} {block parentBlock : BeaconBlock preset fork}
    {participants : Std.TreeSet ValidatorIndex}
    (known : store.blocks[root]? = some block)
    (parentKnown : store.blocks[block.parentRoot]? = some parentBlock)
    (earlier : parentBlock.slot < block.slot) :
    Disjoint (store.supportersOf source ⟨root, .pending⟩)
      (store.parentVotersOf source participants block parentBlock) := by
  apply Finset.disjoint_left.mpr
  intro v supporter parent
  obtain ⟨message, supported, latest, _, supportedOk, descends⟩ :=
    Store.exists_of_voteCountsFor _ (Store.voteCountsFor_of_mem_supportersOf supporter)
  obtain ⟨_, _, _, other, otherSupported, otherLatest, otherOk, which⟩ :=
    Store.mem_parentVotersOf.mp parent
  rw [latest, Option.some.injEq] at otherLatest
  subst other
  rw [supportedOk, Except.ok.injEq] at otherOk
  subst otherSupported
  have rootEq : supported.root = block.parentRoot := by
    rcases which with rfl | rfl <;> rfl
  obtain ⟨found, foundOk, le⟩ := Store.slot_le_of_isAncestor known descends
  rw [rootEq, parentKnown, Option.some.injEq] at foundOk
  subst found
  exact (UInt64.not_le.mpr earlier) le

/-- Positive honest support or parent weight requires a nonempty caller window. -/
private theorem window_nonempty_of_honest_weight {store : Store preset fork}
    [DecidablePred (· ∈ J)] {source : BeaconState preset fork} {root head : Root}
    {block parentBlock : BeaconBlock preset fork} {first last before slot : Slot}
    {participants : Std.TreeSet ValidatorIndex}
    (origins : store.VotesHaveOrigins config)
    (blockOk : store.block root = .ok block)
    (earlier : parentBlock.slot < block.slot)
    (firstOk : addChecked parentBlock.slot 1 = .ok first)
    (slotOk : store.getCurrentSlot config = .ok slot)
    (lastOk : subChecked slot 1 = .ok last) (beforeLe : before ≤ last)
    (participantsOk : store.getCommitteesBetweenSlots head first before = .ok participants)
    (positive : 0 < stake (fun v => balanceAt source v.toNat)
        {v ∈ store.parentVotersOf source participants block parentBlock | v ∈ J} +
      2 * stake (fun v => balanceAt source v.toNat)
        {v ∈ store.supportersOf source ⟨root, .pending⟩ | v ∈ J}) : first ≤ last := by
  by_contra notLe
  have empty := UInt64.not_le.mp notLe
  have parentEmpty : participants = ∅ := Except.ok.inj
    (participantsOk.symm.trans (Store.getCommitteesBetweenSlots_of_gt
      (UInt64.lt_of_le_of_lt beforeLe empty)))
  have parentsEmpty :
      {v ∈ store.parentVotersOf source participants block parentBlock | v ∈ J} = ∅ :=
    Finset.eq_empty_of_forall_notMem fun v member => by
      have participant := (Store.mem_parentVotersOf.mp (Finset.mem_filter.mp member).1).1
      rw [parentEmpty] at participant
      exact Std.TreeSet.not_mem_emptyc participant
  have supportersEmpty : {v ∈ store.supportersOf source ⟨root, .pending⟩ | v ∈ J} = ∅ :=
    Finset.eq_empty_of_forall_notMem fun v member => by
      obtain ⟨attestation, _, _, blockLe, lastLe⟩ :=
        origins.slot_mem_range_of_mem_supportersOf blockOk (UInt64.le_refl _)
          slotOk lastOk (Finset.mem_filter.mp member).1
      have firstNat := (addChecked_ok_iff.mp firstOk).2
      have parentNat := UInt64.lt_iff_toNat_lt.mp earlier
      have emptyNat := UInt64.lt_iff_toNat_lt.mp empty
      have blockNat := UInt64.le_iff_toNat_le.mp blockLe
      have lastNat := UInt64.le_iff_toNat_le.mp lastLe
      simp only [UInt64.toNat_one] at firstNat
      omega
  simp only [parentsEmpty, supportersEmpty, stake_empty, Nat.mul_zero, Nat.zero_add] at positive
  exact Nat.not_lt_zero _ positive

/-- A balance margin and vote transport preserve a strict bound on the window weight. -/
private theorem lt_of_transported_margin
    {sourceMaximum sourceScore shift sourceParents sourceSupport maximum score : Nat}
    {receiverParents receiverSupport parents support windowWeight : Nat}
    (sourceMargin : sourceMaximum + sourceScore + shift < sourceParents + 2 * sourceSupport)
    (margin : 2 * sourceSupport + sourceParents + maximum + score ≤
      2 * receiverSupport + receiverParents + sourceMaximum + sourceScore + shift)
    (transported : 2 * receiverSupport + receiverParents ≤ 2 * support + parents)
    (windowBound : windowWeight ≤ maximum) :
    windowWeight + score < parents + 2 * support := by
  omega

/-- Source weights of active validators lose nothing to the margin's activity mask. -/
private theorem margin_of_active_sets {source : BeaconState preset fork}
    {p q : Finset ValidatorIndex} {maximum score rest : Nat}
    (pActive : ∀ v ∈ p, v ∈ ((unslashedActiveBalances source).map (·.1)).toFinset)
    (qActive : ∀ v ∈ q, v ∈ ((unslashedActiveBalances source).map (·.1)).toFinset)
    (margin : 2 * stake (fun v => if v ∈ ((unslashedActiveBalances source).map (·.1)).toFinset
        then balanceAt source v.toNat else 0) p +
      stake (fun v => if v ∈ ((unslashedActiveBalances source).map (·.1)).toFinset
        then balanceAt source v.toNat else 0) q + maximum + score ≤ rest) :
    2 * stake (fun v => balanceAt source v.toNat) p +
      stake (fun v => balanceAt source v.toNat) q + maximum + score ≤ rest := by
  rwa [stake_congr (fun v member => ite_eq_left (pActive v member)),
    stake_congr (fun v member => ite_eq_left (qActive v member))] at margin

/-- A complete caller window preserves its honest margin through balance and vote transport. -/
private theorem honest_support_of_complete_window {store : Store preset fork}
    [DecidablePred (· ∈ J)] {source state : BeaconState preset fork}
    {root : Root} {block parentBlock : BeaconBlock preset fork}
    {participants window : Std.TreeSet ValidatorIndex} {supporters parents : Finset ValidatorIndex}
    {sourceMaximum sourceScore maximum score : Gwei} {shift : Nat} {head : Root}
    {first last : Slot}
    (apart : Disjoint supporters parents)
    (supporterHonest : ∀ v ∈ supporters, v ∈ J)
    (parentHonest : ∀ v ∈ parents, v ∈ J)
    (sourceMargin : sourceMaximum.toNat + sourceScore.toNat + shift <
      stake (fun v => balanceAt source v.toNat) parents +
        2 * stake (fun v => balanceAt source v.toNat) supporters)
    (margin : 2 * stake (fun v => balanceAt source v.toNat) supporters +
        stake (fun v => balanceAt source v.toNat) parents + maximum.toNat + score.toNat ≤
      2 * stake (fun v => if v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset
        then balanceAt state v.toNat else 0) supporters +
      stake (fun v => if v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset
        then balanceAt state v.toNat else 0) parents +
      sourceMaximum.toNat + sourceScore.toNat + shift)
    (within : state.RegistryWithinLimit)
    (complete : isFullValidatorSetCovered preset first last = .ok true)
    (maximumOk : store.computeCommitteeWeightBetweenSlots head state first last = .ok maximum)
    (support : ∀ v ∈ supporters,
      v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset →
      v ∈ store.supportersOf state ⟨root, .pending⟩ ∨
      store.isAncestor ⟨store.justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (parent : ∀ v ∈ parents,
      v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset →
      (v ∈ store.parentVotersOf state participants block parentBlock ∨
        v ∈ store.supportersOf state ⟨root, .pending⟩) ∨
      store.isAncestor ⟨store.justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true) :
    stake (fun v => balanceAt state v.toNat) (Store.activeMembers state window) + score.toNat <
      stake (fun v => balanceAt state v.toNat)
        {v ∈ store.parentVotersOf state participants block parentBlock | v ∈ J} +
      2 * stake (fun v => balanceAt state v.toNat)
        {v ∈ store.supportersOf state ⟨root, .pending⟩ | v ∈ J} ∨
      store.isAncestor ⟨store.justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true := by
  by_cases covered : store.isAncestor ⟨store.justifiedCheckpoint.root, .pending⟩
      ⟨root, .pending⟩ = .ok true
  · exact .inr covered
  left
  have windowBound := (stake_mono (w := fun v => balanceAt state v.toNat)
    (show Store.activeMembers state window ⊆
      (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset from by
        intro v member
        exact List.mem_toFinset.mpr ((mem_getActiveValidatorIndices within).mpr
          (Store.mem_activeMembers.mp member).2))).trans
      (Store.stake_le_computeCommitteeWeightBetweenSlots_of_covered complete maximumOk)
  have transported := stake_le_of_supporter_parent_transport
    (fun v => if v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset
      then balanceAt state v.toNat else 0) (fun v => balanceAt state v.toNat)
    supporters parents
    {v ∈ store.supportersOf state ⟨root, .pending⟩ | v ∈ J}
    {v ∈ store.parentVotersOf state participants block parentBlock | v ∈ J}
    apart (fun v => by split <;> omega)
    (fun v member positive => by
      have active : v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset := by
        by_contra absent
        simp only [ite_eq_right absent, Nat.lt_irrefl] at positive
      exact Finset.mem_filter.mpr
        ⟨(support v member active).resolve_right covered, supporterHonest v member⟩)
    (fun v member positive => by
      have active : v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset := by
        by_contra absent
        simp only [ite_eq_right absent, Nat.lt_irrefl] at positive
      rcases (parent v member active).resolve_right covered with stays | promotes
      · exact .inr (Finset.mem_filter.mpr ⟨stays, parentHonest v member⟩)
      · exact .inl (Finset.mem_filter.mpr ⟨promotes, parentHonest v member⟩))
  omega

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

/-- A tally-active participant passes the activity filter of its committee window. -/
private theorem activeMember_of_tallyActive {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) {members : Std.TreeSet ValidatorIndex}
    {v : ValidatorIndex}
    (active : v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset)
    (member : v ∈ members) : v ∈ Store.activeMembers state members := by
  simp only [List.mem_toFinset, List.mem_map, unslashedActiveBalances, List.mem_filterMap,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, Prod.exists] at active
  obtain ⟨index, balance, ⟨validator, i, inZip, flags, rfl, rfl⟩, rfl⟩ := active
  have found := List.mem_zipIdx_iff_getElem?.mp inZip
  have lt : i < state.validators.data.size := by
    simpa using (List.getElem?_eq_some_iff.mp found).1
  refine Store.mem_activeMembers.mpr ⟨member, validator, ?_, (Bool.and_eq_true_iff.mp flags).1⟩
  simpa only [toNat_toUInt64_of_lt within lt, Array.getElem?_toList] using found

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

/-- A nonempty partial window weighs its active members, with the increment floor. -/
private theorem maximum_eq_max_stake_of_partial {store : Store preset fork} {head : Root}
    {state : BeaconState preset fork} {first last : Slot}
    {participants : Std.TreeSet ValidatorIndex} {maximum : Gwei}
    (nonempty : first ≤ last)
    (uncovered : isFullValidatorSetCovered preset first last = .ok false)
    (windowOk : store.getCommitteesBetweenSlots head first last = .ok participants)
    (maximumOk : store.computeCommitteeWeightBetweenSlots head state first last = .ok maximum) :
    maximum.toNat = max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (stake (fun v => balanceAt state v.toNat) (Store.activeMembers state participants)) := by
  simp only [Store.computeCommitteeWeightBetweenSlots, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at maximumOk
  obtain ⟨⟨_, members⟩, read, rfl⟩ := maximumOk
  simp only [Store.computeCommitteeWeightAndMembers, UInt64.not_lt.mpr nonempty,
    ↓reduceIte, bind_ok_iff] at read
  obtain ⟨covered, coverage, read⟩ := read
  rw [uncovered, Except.ok.injEq] at coverage
  subst covered
  simp only [Bool.false_eq_true, ↓reduceIte, bind_ok_iff, mapError_ok_iff,
    pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at read
  obtain ⟨found, foundOk, active, filtered, total, totalOk, rfl, _⟩ := read
  rw [windowOk, Except.ok.injEq] at foundOk
  subst found
  have same : active.toFinset = Store.activeMembers state participants := by
    ext v
    rw [List.mem_toFinset, Store.mem_activeMembers]
    constructor
    · intro member
      have pass := passes_of_mem_filterM_ok filtered member
      simp only [bind_ok_iff, Except.ok.injEq] at pass
      obtain ⟨validator, found, active⟩ := pass
      exact ⟨Std.TreeSet.mem_toList.mp (mem_of_filterM_ok filtered member), validator,
        validatorAt_ok_iff.mp found, active⟩
    · rintro ⟨member, validator, found, active⟩
      exact mem_filterM_ok_of_test filtered (Std.TreeSet.mem_toList.mpr member)
        (by simp [validatorAt_ok_iff.mpr found, active, bind, Except.bind])
  exact same ▸ (getTotalBalance_ok_iff_stake.mp totalOk).2.2

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

/-- A non-complete successful maximum and window have a successful partial-coverage read. -/
private theorem coverage_false_of_maximum {store : Store preset fork} {head : Root}
    {state : BeaconState preset fork} {first last : Slot} {maximum : Gwei}
    {members : Std.TreeSet ValidatorIndex} (nonempty : first ≤ last)
    (read : store.computeCommitteeWeightBetweenSlots head state first last = .ok maximum)
    (windowOk : store.getCommitteesBetweenSlots head first last = .ok members)
    (notFull : isFullValidatorSetCovered preset first last ≠ .ok true) :
    isFullValidatorSetCovered preset first last = .ok false := by
  unfold Store.getCommitteesBetweenSlots at windowOk
  obtain ⟨afterLast, afterOk, _⟩ := bind_ok_iff.mp windowOk
  obtain ⟨covered, coverage⟩ := coverage_exists_of_maximum nonempty read
    (mapError_ok_iff.mp afterOk)
  cases covered
  · exact coverage
  · exact False.elim (notFull coverage)

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

/-- A partial receiver window transports old support and promotes completed honest duties. -/
private theorem honest_support_of_partial_window
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (lookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat ∧ 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat ∧
      preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam) {time : Nat} (oneBlock : OneBlockPerRoot e time)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (committees : CommitteesFollow e time) {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot) (anchored : ∀ w ∈ J, e.start w = anchor)
    {u : ValidatorIndex} (caller : u ∈ J) {n : Nat} {head root : Root}
    {balanceSource : BeaconState preset fork} {slot firstSlot lastSlot beforeBlock : Slot}
    {block parentBlock : BeaconBlock preset fork}
    {parentParticipants : Std.TreeSet ValidatorIndex} {proposerScore maximumSupport : Gwei}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (blockOk : ((e.world n).state u).block root = .ok block)
    (parentOk : ((e.world n).state u).block block.parentRoot = .ok parentBlock)
    {sourceCheckpoint : Checkpoint}
    (sourceOk : ((e.world n).state u).checkpointState sourceCheckpoint = .ok balanceSource)
    (boostOk : computeProposerScore config balanceSource = .ok proposerScore)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked slot 1 = .ok lastSlot)
    (maximumOk : ((e.world n).state u).computeCommitteeWeightBetweenSlots head balanceSource
      firstSlot lastSlot = .ok maximumSupport)
    (parentParticipantsOk : ((e.world n).state u).getCommitteesBetweenSlots head firstSlot
      beforeBlock = .ok parentParticipants)
    {shift : Nat} {support discount adversary : Gwei}
    (within : balanceSource.RegistryWithinLimit) (aligned : EffectiveBalancesAligned balanceSource)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (supportOk : ((e.world n).state u).scoreFromTally
      (((e.world n).state u).tallyVotes balanceSource) ⟨root, .pending⟩ = .ok support)
    (adversaryOk : ((e.world n).state u).getAdversarialWeight config head balanceSource root =
      .ok adversary)
    (base : maximumSupport.toNat + proposerScore.toNat + 2 * adversary.toNat + shift <
      discount.toNat + 2 * support.toNat)
    (later : (e.world n).time ≤ time)
    (weights : WeightBounds e balanceSource (e.world n).time time shift)
    (unslashed : ∀ w ∈ J, ∀ k (state : BeaconState preset fork), (e.world k).time ≤ time →
      ((e.world k).state w).Counts config state → ∀ v ∈ J, NotSlashed state v)
    {callerEpoch : Epoch}
    (callerEpochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok callerEpoch)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : Nat} (atTime : (e.world k).time = time)
    (receiverUpToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
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
    (scoreOk : computeProposerScore config state = .ok score) {receiverTotal : Gwei}
    (receiverTotalOk : getTotalActiveBalance state = .ok receiverTotal)
    (receiverIndices : ∀ v ∈ receiverWindow, ∃ validator, validatorAt state v = .ok validator)
    (oldLastLe : lastSlot ≤ last)
    (parentLower : parentBlock.slot < block.slot)
    (callerHeadOk : ((e.world n).state u).getHead config = .ok ⟨head, .pending⟩)
    (parentOnHead : ((e.world n).state u).isAncestor ⟨head, .pending⟩
      ⟨block.parentRoot, .pending⟩ = .ok true)
    (callerEpochEq : callerEpoch = computeEpochAtSlot preset slot)
    (callerOrigins : ((e.world n).state u).VotesHaveOrigins config)
    (callerParentAge : callerEpoch.toNat ≤ (computeEpochAtSlot preset parentBlock.slot).toNat + 1)
    (receiverParentKnown : ((e.world k).state w).blocks[block.parentRoot]? = some parentBlock)
    (callerBlocksLe : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world n).state u).blocks[root]? = some block →
      block.slot ≤ slot)
    (oldSlotCommittees : ∀ dutySlot, firstSlot ≤ dutySlot → dutySlot ≤ lastSlot →
      ((e.world n).state u).getSlotCommittee head dutySlot =
        ((e.world k).state w).getSlotCommittee receiverHead.root dutySlot)
    (beforeBlockLe : beforeBlock ≤ lastSlot) {callerHeadState : BeaconState preset fork}
    (callerHeadStateOk : ((e.world n).state u).blockState head = .ok callerHeadState)
    (callerBlockAge : callerEpoch.toNat ≤ (computeEpochAtSlot preset block.slot).toNat + 1)
    (oldComplete : isFullValidatorSetCovered preset firstSlot lastSlot ≠ .ok true)
    (uncovered : isFullValidatorSetCovered preset firstSlot last = .ok false)
    (oldSupporters oldParents : Finset ValidatorIndex)
    (supportersEq : oldSupporters = {v ∈ ((e.world n).state u).supportersOf balanceSource
      ⟨root, .pending⟩ | v ∈ J})
    (parentsEq : oldParents = {v ∈ ((e.world n).state u).parentVotersOf balanceSource
      parentParticipants block parentBlock | v ∈ J})
    (parentDiscount : discount.toNat ≤ stake (fun v => balanceAt balanceSource v.toNat) oldParents)
    (supportersActive : ∀ (v : ValidatorIndex), v ∈ oldSupporters →
      v ∈ ((unslashedActiveBalances balanceSource).map (·.1)).toFinset)
    (parentsActive : ∀ (v : ValidatorIndex), v ∈ oldParents →
      v ∈ ((unslashedActiveBalances balanceSource).map (·.1)).toFinset)
    (positiveHonest : 0 < stake (fun v => balanceAt balanceSource v.toNat) oldParents +
      2 * stake (fun v => balanceAt balanceSource v.toNat) oldSupporters)
    (oldSupportTransport : ∀ (v : ValidatorIndex), v ∈ oldSupporters →
      v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset →
      v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (oldParentTransport : ∀ (v : ValidatorIndex), v ∈ oldParents →
      v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset →
      (v ∈ ((e.world k).state w).parentVotersOf state receiverParticipants block parentBlock ∨
        v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩) ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (freshDutySupport : ∀ endTime,
      computeTimeAtSlotMs config genesisTimeMs current = .ok endTime → endTime.toNat ≤ time →
      ∀ v ∈ J, ∀ dutySlot committeeIndex, slot ≤ dutySlot → dutySlot < current →
      assignment.committee v dutySlot = some committeeIndex →
      v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset →
      v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true) :
    stake (fun v => balanceAt state v.toNat) (Store.activeMembers state receiverWindow) +
        score.toNat <
      stake (fun v => balanceAt state v.toNat)
        {v ∈ ((e.world k).state w).parentVotersOf state receiverParticipants block parentBlock |
          v ∈ J} +
      2 * stake (fun v => balanceAt state v.toNat)
        {v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ | v ∈ J} ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true := by
  subst oldSupporters oldParents
  let oldSupporters := {v ∈ ((e.world n).state u).supportersOf balanceSource
    ⟨root, .pending⟩ | v ∈ J}
  let oldParents := {v ∈ ((e.world n).state u).parentVotersOf balanceSource
    parentParticipants block parentBlock | v ∈ J}
  change 0 < stake (fun v => balanceAt balanceSource v.toNat) oldParents +
    2 * stake (fun v => balanceAt balanceSource v.toNat) oldSupporters at positiveHonest
  have callerKnown := Store.block_ok_iff.mp blockOk
  have callerParentKnown := Store.block_ok_iff.mp parentOk
  have receiverForward := e.forwardReachable
    (fun w hw => (anchored w hw) ▸ Store.ForwardReachable.anchor anchorStore) k w receiver
  have oldNonempty := window_nonempty_of_honest_weight callerOrigins blockOk parentLower
    firstOk slotOk lastOk beforeBlockLe parentParticipantsOk positiveHonest
  obtain ⟨oldWindow, oldWindowOk, _⟩ := committeeWindow_prefix receiverWindowOk oldLastLe
  have callerWindowOk := committeeWindow_transfer oldWindowOk
    (fun dutySlot low high => (oldSlotCommittees dutySlot low high).symm)
  have oldPartial := coverage_false_of_maximum oldNonempty maximumOk callerWindowOk oldComplete
  have oldValue := maximum_eq_max_stake_of_partial oldNonempty oldPartial callerWindowOk maximumOk
  obtain ⟨adversaryStart, startLow, startHigh, rangeOk⟩ :=
    adversary_window_bounds slotOk blockOk parentOk firstOk lastOk parentLower adversaryOk
  obtain ⟨adversaryMaximum, equivocation, adversaryMaximumOk, equivocationOk⟩ :=
    Store.computeAdversarialWeight_eq_ok rangeOk
  obtain ⟨adversaryMembers, adversaryMembersOk, equivocationValue⟩ :=
    Store.exists_stake_equivocatorsOf_of_getEquivocationScore equivocationOk
  have receiverAdversaryMembersOk := committeeWindow_transfer adversaryMembersOk
    (fun dutySlot low high => oldSlotCommittees dutySlot (UInt64.le_trans startLow low) high)
  have firstLeSlot : firstSlot ≤ slot := UInt64.le_trans
    (UInt64.le_trans startLow startHigh) (callerBlocksLe _ _ callerKnown)
  have startLeSlot : adversaryStart ≤ slot :=
    UInt64.le_trans startHigh (callerBlocksLe _ _ callerKnown)
  obtain ⟨freshMembers, freshMembersOk⟩ := committeeWindow_subrange receiverWindowOk
    firstLeSlot (UInt64.le_refl last)
  obtain ⟨unionMembers, unionMembersOk⟩ := committeeWindow_subrange receiverWindowOk
    startLow (UInt64.le_refl last)
  -- The partial receiver window keeps every duty within the common parent's seed lookahead.
  have unionBound := sourceByzantine_of_partial_parent_window anchorStore anchorSlot anchored
    oneBlock slots positive preGloas lookahead caller receiver later (Nat.le_of_eq atTime)
    callerParentKnown receiverParentKnown parentOnHead receiverAbove callerEpochOk receiverEpochOk
    callerParentAge age
    (fun low high members read => weights.sourceByzantine u caller n head low high members rfl read)
    firstOk receiverLastOk uncovered startLow (UInt64.le_refl last) unionMembersOk
  -- All three sets use source activity; repeated duties contribute only once to each union.
  let A := Store.activeMembers balanceSource adversaryMembers
  let W := Store.activeMembers balanceSource oldWindow
  let G := Store.activeMembers balanceSource freshMembers
  have unionA : Store.activeMembers balanceSource unionMembers = A ∪ G :=
    activeMembers_window_union lastOk startLeSlot oldLastLe
      receiverAdversaryMembersOk freshMembersOk unionMembersOk
  have unionW : Store.activeMembers balanceSource receiverWindow = W ∪ G :=
    activeMembers_window_union lastOk firstLeSlot oldLastLe
      oldWindowOk freshMembersOk receiverWindowOk
  rw [unionA] at unionBound
  have nested : A ⊆ W := by
    intro v member
    obtain ⟨inside, validator, found, active⟩ := Store.mem_activeMembers.mp member
    obtain ⟨dutySlot, committee, low, high, committeeOk, inCommittee⟩ :=
      (mem_committeeWindow_iff adversaryMembersOk).mp inside
    exact Store.mem_activeMembers.mpr
      ⟨(mem_committeeWindow_iff callerWindowOk).mpr
        ⟨dutySlot, committee, UInt64.le_trans startLow low, high, committeeOk, inCommittee⟩,
        validator, found, active⟩
  have supportersIn : ((e.world n).state u).supportersOf balanceSource ⟨root, .pending⟩ ⊆ A := by
    intro v member
    apply Store.mem_activeMembers.mpr
    refine ⟨?_, isActiveAt_eq_true_iff.mp (Store.isActiveAt_of_mem_supportersOf within member)⟩
    exact supporters_mem_committeeWindow committees caller later callerOrigins callerHeadOk
      callerHeadStateOk slotOk callerEpochOk blockOk callerBlockAge startHigh lastOk
      adversaryMembersOk v member
  have parentsIn : oldParents ⊆ W := by
    intro v member
    apply activeMember_of_tallyActive within (parentsActive v member)
    obtain ⟨dutySlot, committee, low, high, committeeOk, inside⟩ :=
      (mem_committeeWindow_iff parentParticipantsOk).mp
        (Store.mem_parentVotersOf.mp (Finset.mem_filter.mp member).1).1
    exact (mem_committeeWindow_iff callerWindowOk).mpr
      ⟨dutySlot, committee, low, UInt64.le_trans high beforeBlockLe, committeeOk, inside⟩
  have cover := Store.threshold_mul_stake_le_of_computeAdversarialWeight
    adversaryMaximumOk equivocationOk rangeOk
    (Store.stake_le_computeCommitteeWeightBetweenSlots adversaryMembersOk adversaryMaximumOk
      fun v member => Store.mem_activeMembers.mp member)
    (fun v _ => Nat.mod_eq_zero_of_dvd (dvd_balanceAt_of_aligned aligned
      (Nat.dvd_of_mod_eq_zero increment) v.toNat))
  obtain ⟨newMaximum, newMaximumOk⟩ := maximum_exists_of_total uncovered receiverWindowOk
    receiverTotalOk receiverIndices
  have lastPast : last < current := UInt64.lt_iff_toNat_lt.mpr (by
    have finish := subChecked_ok_iff.mp receiverLastOk
    simp only [UInt64.toNat_one] at finish
    omega)
  obtain ⟨newSourceMaximum, newSourceScore, newSourceMaximumOk, newSourceScoreOk⟩ :=
    weights.reads w receiver k receiverHead state current firstSlot last newMaximum
      (atTime ▸ later) (Nat.le_of_eq atTime) headOk currentOk lastPast stateOk newMaximumOk
  have newValue := maximum_eq_max_stake_of_partial (UInt64.le_trans oldNonempty oldLastLe)
    uncovered receiverWindowOk newSourceMaximumOk
  have growth : newSourceMaximum.toNat ≤ maximumSupport.toNat +
      stake (fun v => balanceAt balanceSource v.toNat) (G \ W) := by
    have unionSum : stake (fun v => balanceAt balanceSource v.toNat) (W ∪ G) =
        stake (fun v => balanceAt balanceSource v.toNat) W +
          stake (fun v => balanceAt balanceSource v.toNat) (G \ W) := by
      rw [← Finset.union_sdiff_self_eq_union]
      exact Finset.sum_union Finset.disjoint_sdiff
    rw [unionW, unionSum] at newValue
    change maximumSupport.toNat = max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (stake (fun v => balanceAt balanceSource v.toNat) W) at oldValue
    omega
  -- The caller's reserve pays for Byzantine growth after honest promotion is counted.
  have sourceMargin := honest_margin_of_partial_sets within nested supportersIn parentsIn
    ((disjoint_supporters_parentVoters callerKnown callerParentKnown parentLower).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    Store.equivocatorsOf_subset_activeMembers (weights.dishonest u caller n later)
    equivocationValue supportOk half (laterMaximum := newSourceMaximum.toNat) (reserve := 0)
    (by simpa only [Nat.mul_zero, Nat.add_zero] using unionBound.2) cover base parentDiscount
    (by simpa only [Nat.add_zero] using growth)
  have sourceUnslashed : ∀ v ∈ J, NotSlashed balanceSource v := by
    obtain ⟨held, boundary, stored, _, advanced⟩ :=
      e.checkpointStates_fixedChecks anchorStore (anchored u caller)
        (Store.checkpointState_ok_iff.mp sourceOk)
    intro v honest
    apply (notSlashed_lookahead advanced v).mpr
    exact unslashed u caller n held later
      (Store.counts_of_fixedChecks (checks := checks) stored (.inl rfl)) v honest
  let newSupporters := oldSupporters ∪ {v ∈ G | v ∈ J}
  let newParents := oldParents \ {v ∈ G | v ∈ J}
  have supportersHonest : ∀ v ∈ newSupporters, v ∈ J := by
    intro v member
    rcases Finset.mem_union.mp member with old | fresh
    · exact (Finset.mem_filter.mp old).2
    · exact (Finset.mem_filter.mp fresh).2
  have parentsHonest : ∀ v ∈ newParents, v ∈ J :=
    fun _ member => (Finset.mem_filter.mp (Finset.mem_sdiff.mp member).1).2
  have sourceSupportersActive : ∀ v ∈ newSupporters,
      v ∈ ((unslashedActiveBalances balanceSource).map (·.1)).toFinset := by
    intro v member
    rcases Finset.mem_union.mp member with old | fresh
    · exact supportersActive v old
    · exact tallyActive_of_activeMember (Finset.mem_filter.mp fresh).1
        (sourceUnslashed v (Finset.mem_filter.mp fresh).2)
  -- Apply the larger-window margin once, preserving its receiver activity masks.
  have newMargin := margin_of_active_sets sourceSupportersActive
    (fun v member => parentsActive v (Finset.mem_sdiff.mp member).1)
    (weights.margin w receiver k receiverHead state score newSourceScore
      firstSlot last newMaximum newSourceMaximum (atTime ▸ later) (Nat.le_of_eq atTime) headOk
      stateOk scoreOk newSourceScoreOk newMaximumOk newSourceMaximumOk newSupporters newParents
      supportersHonest parentsHonest)
  have newScoreEq : newSourceScore = proposerScore :=
    Except.ok.inj (newSourceScoreOk.symm.trans boostOk)
  subst newSourceScore
  have honestLatest : ∃ v message, v ∈ J ∧
      ((e.world n).state u).latestMessages[v]? = some message := by
    by_cases child : oldSupporters.Nonempty
    · obtain ⟨v, member⟩ := child
      obtain ⟨message, _, latest, _⟩ := Store.exists_of_voteCountsFor _
        (Store.voteCountsFor_of_mem_supportersOf (Finset.mem_filter.mp member).1)
      exact ⟨v, message, (Finset.mem_filter.mp member).2, latest⟩
    · have parent : oldParents.Nonempty := by
        by_contra absent
        have noParents := Finset.not_nonempty_iff_eq_empty.mp absent
        have noSupporters := Finset.not_nonempty_iff_eq_empty.mp child
        rw [noParents, noSupporters, stake_empty, Nat.mul_zero, Nat.zero_add] at positiveHonest
        exact Nat.not_lt_zero _ positiveHonest
      obtain ⟨v, member⟩ := parent
      obtain ⟨_, _, _, message, _, latest, _⟩ :=
        Store.mem_parentVotersOf.mp (Finset.mem_filter.mp member).1
      exact ⟨v, message, (Finset.mem_filter.mp member).2, latest⟩
  obtain ⟨v, message, honest, latest⟩ := honestLatest
  obtain ⟨attestation, signedMessage, seen, _, signed, _⟩ :=
    e.exists_signed_origin_of_latestMessages anchorStore anchored caller latest
  obtain ⟨signedAt, _, maySign⟩ :=
    e.exists_maySign_of_signed (e.view_subset_sent n u seen) signed honest
  obtain ⟨_, _, _, genesis, _, _, _⟩ := maySign
  have receiverGenesis : ((e.world k).state w).genesisTimeMs = genesisTimeMs := by
    rw [(e.clock_bounds w k).1, anchored w receiver, ← anchored v honest,
      ← (e.clock_bounds v signedAt).1, genesis]
  have currentRead := mapError_ok_iff.mp currentOk
  change computeSlotAtTimeMs config ((e.world k).state w).genesisTimeMs
    ((e.world k).state w).timeMs = .ok current at currentRead
  rw [receiverGenesis] at currentRead
  obtain ⟨endTime, endTimeOk, endTimeLe⟩ := boundary_of_current_slot currentRead
  have endBound : endTime.toNat ≤ time :=
    (UInt64.le_iff_toNat_le.mp endTimeLe).trans_eq (receiverUpToDate.1.trans atTime)
  have parentEpochLe :
      (computeEpochAtSlot preset parentBlock.slot).toNat ≤ callerEpoch.toNat := by
    rw [callerEpochEq]
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp
      (callerBlocksLe _ _ callerParentKnown))
  have freshAssigned := committees.assigned w receiver k (Nat.le_of_eq atTime)
    receiverHead current slot last freshMembers headOk currentOk lastPast
    (fun headState headStateOk => by
      obtain ⟨readSlot, readSlotOk, _, statesLe⟩ :=
        receiverForward.slots_le_current slots (UInt64.le_of_eq anchorSlot)
      rw [currentOk, Except.ok.injEq] at readSlotOk
      subst readSlot
      have stateSlotLe := statesLe _ _ (Store.blockState_ok_iff.mp headStateOk)
      have epochLe := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
        (UInt64.le_iff_toNat_le.mp stateSlotLe)
      have receiverEpochEq : receiverEpoch = computeEpochAtSlot preset current := by
        simpa [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
          using receiverEpochOk.symm
      simp only [receiverEpochEq, computeEpochAtSlot, UInt64.toNat_div] at age
      simp only [getCurrentEpoch, callerEpochEq, computeEpochAtSlot, UInt64.toNat_div]
        at parentEpochLe ⊢
      omega) freshMembersOk
  by_cases covered : ((e.world k).state w).isAncestor
      ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true
  · exact .inr covered
  left
  have transported := stake_le_of_supporter_parent_transport
    (fun v => if v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset
      then balanceAt state v.toNat else 0) (fun v => balanceAt state v.toNat)
    newSupporters newParents
    {v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ | v ∈ J}
    {v ∈ ((e.world k).state w).parentVotersOf state receiverParticipants block parentBlock | v ∈ J}
    (by
      apply Finset.disjoint_left.mpr
      intro v supporter parent
      have parentOld := (Finset.mem_sdiff.mp parent).1
      rcases Finset.mem_union.mp supporter with old | fresh
      · exact Finset.disjoint_left.mp
          (disjoint_supporters_parentVoters callerKnown callerParentKnown parentLower)
          (Finset.mem_filter.mp old).1 (Finset.mem_filter.mp parentOld).1
      · exact (Finset.mem_sdiff.mp parent).2 fresh)
    (fun v => by split <;> omega)
    (fun v member positive => by
      have active : v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset := by
        by_contra absent
        simp only [ite_eq_right absent, Nat.lt_irrefl] at positive
      refine Finset.mem_filter.mpr ⟨?_, supportersHonest v member⟩
      rcases Finset.mem_union.mp member with old | fresh
      · exact (oldSupportTransport v old active).resolve_right covered
      · have freshHonest := (Finset.mem_filter.mp fresh).2
        obtain ⟨dutySlot, committeeIndex, low, high, duty⟩ :=
          (freshAssigned v freshHonest).mp
            (Store.mem_activeMembers.mp (Finset.mem_filter.mp fresh).1).1
        exact (freshDutySupport endTime endTimeOk endBound v freshHonest dutySlot committeeIndex
          low (UInt64.lt_of_le_of_lt high lastPast) duty active).resolve_right covered)
    (fun v member positive => by
      have active : v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset := by
        by_contra absent
        simp only [ite_eq_right absent, Nat.lt_irrefl] at positive
      have old := (Finset.mem_sdiff.mp member).1
      rcases (oldParentTransport v old active).resolve_right covered with parent | child
      · exact .inr (Finset.mem_filter.mpr ⟨parent, parentsHonest v member⟩)
      · exact .inl (Finset.mem_filter.mpr ⟨child, parentsHonest v member⟩))
  have windowBound := Store.stake_le_computeCommitteeWeightBetweenSlots receiverWindowOk
    newMaximumOk (fun v member => Store.mem_activeMembers.mp member)
  change newSourceMaximum.toNat + proposerScore.toNat + shift <
    stake (fun v => balanceAt balanceSource v.toNat) newParents +
      2 * stake (fun v => balanceAt balanceSource v.toNat) newSupporters at sourceMargin
  exact lt_of_transported_margin sourceMargin newMargin transported windowBound

/-- A receiver window with a whole epoch transports old support and promotes honest duties.

The epoch starts after the parent, so its committees are those of the caller's head.

The receiver weighs the total active balance of its state, and the caller's source does too.

Source-active validators outside the committees of that epoch fit the exit reserve.

The caller's source reserve on the range from its adversary window through the epoch pays it. -/
private theorem honest_support_of_full_window
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (lookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat ∧ 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat ∧
      preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam) {time : Nat} (oneBlock : OneBlockPerRoot e time)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (committees : CommitteesFollow e time) {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot) (anchored : ∀ w ∈ J, e.start w = anchor)
    {u : ValidatorIndex} (caller : u ∈ J) {n : Nat} {head root : Root}
    {balanceSource : BeaconState preset fork} {slot firstSlot lastSlot beforeBlock : Slot}
    {block parentBlock : BeaconBlock preset fork}
    {parentParticipants : Std.TreeSet ValidatorIndex} {proposerScore maximumSupport : Gwei}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (blockOk : ((e.world n).state u).block root = .ok block)
    (parentOk : ((e.world n).state u).block block.parentRoot = .ok parentBlock)
    {sourceCheckpoint : Checkpoint}
    (sourceOk : ((e.world n).state u).checkpointState sourceCheckpoint = .ok balanceSource)
    (boostOk : computeProposerScore config balanceSource = .ok proposerScore)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked slot 1 = .ok lastSlot)
    (maximumOk : ((e.world n).state u).computeCommitteeWeightBetweenSlots head balanceSource
      firstSlot lastSlot = .ok maximumSupport)
    (parentParticipantsOk : ((e.world n).state u).getCommitteesBetweenSlots head firstSlot
      beforeBlock = .ok parentParticipants)
    {shift : Nat} {support discount adversary : Gwei}
    (within : balanceSource.RegistryWithinLimit) (aligned : EffectiveBalancesAligned balanceSource)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (supportOk : ((e.world n).state u).scoreFromTally
      (((e.world n).state u).tallyVotes balanceSource) ⟨root, .pending⟩ = .ok support)
    (adversaryOk : ((e.world n).state u).getAdversarialWeight config head balanceSource root =
      .ok adversary)
    (base : maximumSupport.toNat + proposerScore.toNat + 2 * adversary.toNat + shift <
      discount.toNat + 2 * support.toNat)
    (later : (e.world n).time ≤ time)
    (weights : WeightBounds e balanceSource (e.world n).time time shift)
    (unslashed : ∀ w ∈ J, ∀ k (state : BeaconState preset fork), (e.world k).time ≤ time →
      ((e.world k).state w).Counts config state → ∀ v ∈ J, NotSlashed state v)
    {callerEpoch : Epoch}
    (callerEpochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok callerEpoch)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : Nat} (atTime : (e.world k).time = time)
    (receiverUpToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
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
    (scoreOk : computeProposerScore config state = .ok score) {receiverTotal : Gwei}
    (receiverTotalOk : getTotalActiveBalance state = .ok receiverTotal)
    (oldLastLe : lastSlot ≤ last)
    (parentLower : parentBlock.slot < block.slot)
    (callerHeadOk : ((e.world n).state u).getHead config = .ok ⟨head, .pending⟩)
    (parentOnHead : ((e.world n).state u).isAncestor ⟨head, .pending⟩
      ⟨block.parentRoot, .pending⟩ = .ok true)
    (callerEpochEq : callerEpoch = computeEpochAtSlot preset slot)
    (callerOrigins : ((e.world n).state u).VotesHaveOrigins config)
    (callerParentAge : callerEpoch.toNat ≤ (computeEpochAtSlot preset parentBlock.slot).toNat + 1)
    (receiverParentKnown : ((e.world k).state w).blocks[block.parentRoot]? = some parentBlock)
    (callerBlocksLe : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world n).state u).blocks[root]? = some block →
      block.slot ≤ slot)
    (oldSlotCommittees : ∀ dutySlot, firstSlot ≤ dutySlot → dutySlot ≤ lastSlot →
      ((e.world n).state u).getSlotCommittee head dutySlot =
        ((e.world k).state w).getSlotCommittee receiverHead.root dutySlot)
    (beforeBlockLe : beforeBlock ≤ lastSlot) {callerHeadState : BeaconState preset fork}
    (callerHeadStateOk : ((e.world n).state u).blockState head = .ok callerHeadState)
    (callerBlockAge : callerEpoch.toNat ≤ (computeEpochAtSlot preset block.slot).toNat + 1)
    (oldComplete : isFullValidatorSetCovered preset firstSlot lastSlot ≠ .ok true)
    (notUncovered : isFullValidatorSetCovered preset firstSlot last ≠ .ok false)
    (oldSupporters oldParents : Finset ValidatorIndex)
    (supportersEq : oldSupporters = {v ∈ ((e.world n).state u).supportersOf balanceSource
      ⟨root, .pending⟩ | v ∈ J})
    (parentsEq : oldParents = {v ∈ ((e.world n).state u).parentVotersOf balanceSource
      parentParticipants block parentBlock | v ∈ J})
    (parentDiscount : discount.toNat ≤ stake (fun v => balanceAt balanceSource v.toNat) oldParents)
    (supportersActive : ∀ (v : ValidatorIndex), v ∈ oldSupporters →
      v ∈ ((unslashedActiveBalances balanceSource).map (·.1)).toFinset)
    (parentsActive : ∀ (v : ValidatorIndex), v ∈ oldParents →
      v ∈ ((unslashedActiveBalances balanceSource).map (·.1)).toFinset)
    (positiveHonest : 0 < stake (fun v => balanceAt balanceSource v.toNat) oldParents +
      2 * stake (fun v => balanceAt balanceSource v.toNat) oldSupporters)
    (oldSupportTransport : ∀ (v : ValidatorIndex), v ∈ oldSupporters →
      v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset →
      v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (oldParentTransport : ∀ (v : ValidatorIndex), v ∈ oldParents →
      v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset →
      (v ∈ ((e.world k).state w).parentVotersOf state receiverParticipants block parentBlock ∨
        v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩) ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (freshDutySupport : ∀ endTime,
      computeTimeAtSlotMs config genesisTimeMs current = .ok endTime → endTime.toNat ≤ time →
      ∀ v ∈ J, ∀ dutySlot committeeIndex, slot ≤ dutySlot → dutySlot < current →
      assignment.committee v dutySlot = some committeeIndex →
      v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset →
      v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (exited : ∀ epoch epochStart next epochEnd epochMembers,
      computeStartSlotAtEpoch preset epoch = .ok epochStart →
      addChecked epochStart preset.SLOTS_PER_EPOCH = .ok next →
      subChecked next 1 = .ok epochEnd →
      firstSlot ≤ epochStart → epochEnd ≤ last →
      ((e.world k).state w).getCommitteesBetweenSlots receiverHead.root epochStart epochEnd =
        .ok epochMembers →
      stake (fun v => balanceAt balanceSource v.toNat)
          {v ∈ activeVoters balanceSource | v ∉ epochMembers} ≤
        exitReserve config balanceSource) :
    stake (fun v => balanceAt state v.toNat) (Store.activeMembers state receiverWindow) +
        score.toNat <
      stake (fun v => balanceAt state v.toNat)
        {v ∈ ((e.world k).state w).parentVotersOf state receiverParticipants block parentBlock |
          v ∈ J} +
      2 * stake (fun v => balanceAt state v.toNat)
        {v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ | v ∈ J} ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true := by
  subst oldSupporters oldParents
  let oldSupporters := {v ∈ ((e.world n).state u).supportersOf balanceSource
    ⟨root, .pending⟩ | v ∈ J}
  let oldParents := {v ∈ ((e.world n).state u).parentVotersOf balanceSource
    parentParticipants block parentBlock | v ∈ J}
  change 0 < stake (fun v => balanceAt balanceSource v.toNat) oldParents +
    2 * stake (fun v => balanceAt balanceSource v.toNat) oldSupporters at positiveHonest
  have callerKnown := Store.block_ok_iff.mp blockOk
  have callerParentKnown := Store.block_ok_iff.mp parentOk
  have receiverForward := e.forwardReachable
    (fun w hw => (anchored w hw) ▸ Store.ForwardReachable.anchor anchorStore) k w receiver
  have oldNonempty := window_nonempty_of_honest_weight callerOrigins blockOk parentLower
    firstOk slotOk lastOk beforeBlockLe parentParticipantsOk positiveHonest
  obtain ⟨oldWindow, oldWindowOk, _⟩ := committeeWindow_prefix receiverWindowOk oldLastLe
  have callerWindowOk := committeeWindow_transfer oldWindowOk
    (fun dutySlot low high => (oldSlotCommittees dutySlot low high).symm)
  have oldPartial := coverage_false_of_maximum oldNonempty maximumOk callerWindowOk oldComplete
  have oldValue := maximum_eq_max_stake_of_partial oldNonempty oldPartial callerWindowOk maximumOk
  obtain ⟨adversaryStart, startLow, startHigh, rangeOk⟩ :=
    adversary_window_bounds slotOk blockOk parentOk firstOk lastOk parentLower adversaryOk
  obtain ⟨adversaryMaximum, equivocation, adversaryMaximumOk, equivocationOk⟩ :=
    Store.computeAdversarialWeight_eq_ok rangeOk
  obtain ⟨adversaryMembers, adversaryMembersOk, equivocationValue⟩ :=
    Store.exists_stake_equivocatorsOf_of_getEquivocationScore equivocationOk
  have receiverAdversaryMembersOk := committeeWindow_transfer adversaryMembersOk
    (fun dutySlot low high => oldSlotCommittees dutySlot (UInt64.le_trans startLow low) high)
  have firstLeSlot : firstSlot ≤ slot := UInt64.le_trans
    (UInt64.le_trans startLow startHigh) (callerBlocksLe _ _ callerKnown)
  have startLeSlot : adversaryStart ≤ slot :=
    UInt64.le_trans startHigh (callerBlocksLe _ _ callerKnown)
  have covered : isFullValidatorSetCovered preset firstSlot last = .ok true := by
    have afterRead := receiverWindowOk
    unfold Store.getCommitteesBetweenSlots at afterRead
    obtain ⟨afterLast, afterOk, _⟩ := bind_ok_iff.mp afterRead
    obtain ⟨coverage, coverageOk⟩ := coverage_exists_of_maximum oldNonempty maximumOk
      (mapError_ok_iff.mp afterOk)
    cases coverage
    · exact absurd coverageOk notUncovered
    · exact coverageOk
  have lastPast : last < current := UInt64.lt_iff_toNat_lt.mpr (by
    have finish := subChecked_ok_iff.mp receiverLastOk
    simp only [UInt64.toNat_one] at finish
    omega)
  -- The receiver window holds a whole epoch after the call, within the parent's seed.
  obtain ⟨epochEnd, lastLeEnd, slotLeEnd, endIn, endEpoch, wideBound⟩ := full_window_epoch
    positive within firstOk lastOk currentOk receiverEpochOk receiverLastOk covered
    receiverWindowOk (callerEpochEq ▸ callerParentAge) age exited
  have endPast : epochEnd < current := UInt64.lt_of_le_of_lt endIn lastPast
  obtain ⟨freshMembers, freshMembersOk⟩ := committeeWindow_subrange receiverWindowOk
    firstLeSlot endIn
  obtain ⟨unionMembers, unionMembersOk⟩ := committeeWindow_subrange receiverWindowOk
    startLow endIn
  obtain ⟨wideMembers, wideMembersOk⟩ := committeeWindow_subrange receiverWindowOk
    (UInt64.le_refl firstSlot) endIn
  -- The caller reads the same committees through the epoch, so its source reserve applies.
  have callerUnionOk := callerWindow_of_recent_parent anchorStore anchorSlot anchored oneBlock
    slots preGloas lookahead caller receiver later (Nat.le_of_eq atTime) callerParentKnown
    receiverParentKnown parentOnHead receiverAbove callerEpochOk receiverEpochOk callerParentAge
    age (UInt64.le_trans (UInt64.le_iff_toNat_le.mpr (by
      have start := (addChecked_ok_iff.mp firstOk).2
      simp only [UInt64.toNat_one] at start
      omega)) startLow) endEpoch unionMembersOk
  have unionBound := weights.sourceReserve u caller n head adversaryStart epochEnd unionMembers
    rfl (UInt64.le_trans startLeSlot slotLeEnd) callerUnionOk
  -- All three sets use source activity; repeated duties contribute only once to each union.
  let A := Store.activeMembers balanceSource adversaryMembers
  let W := Store.activeMembers balanceSource oldWindow
  let G := Store.activeMembers balanceSource freshMembers
  have unionA : Store.activeMembers balanceSource unionMembers = A ∪ G :=
    activeMembers_window_union lastOk startLeSlot lastLeEnd
      receiverAdversaryMembersOk freshMembersOk unionMembersOk
  have unionW : Store.activeMembers balanceSource wideMembers = W ∪ G :=
    activeMembers_window_union lastOk firstLeSlot lastLeEnd
      oldWindowOk freshMembersOk wideMembersOk
  rw [unionA] at unionBound
  have nested : A ⊆ W := by
    intro v member
    obtain ⟨inside, validator, found, active⟩ := Store.mem_activeMembers.mp member
    obtain ⟨dutySlot, committee, low, high, committeeOk, inCommittee⟩ :=
      (mem_committeeWindow_iff adversaryMembersOk).mp inside
    exact Store.mem_activeMembers.mpr
      ⟨(mem_committeeWindow_iff callerWindowOk).mpr
        ⟨dutySlot, committee, UInt64.le_trans startLow low, high, committeeOk, inCommittee⟩,
        validator, found, active⟩
  have supportersIn : ((e.world n).state u).supportersOf balanceSource ⟨root, .pending⟩ ⊆ A := by
    intro v member
    apply Store.mem_activeMembers.mpr
    refine ⟨?_, isActiveAt_eq_true_iff.mp (Store.isActiveAt_of_mem_supportersOf within member)⟩
    exact supporters_mem_committeeWindow committees caller later callerOrigins callerHeadOk
      callerHeadStateOk slotOk callerEpochOk blockOk callerBlockAge startHigh lastOk
      adversaryMembersOk v member
  have parentsIn : oldParents ⊆ W := by
    intro v member
    apply activeMember_of_tallyActive within (parentsActive v member)
    obtain ⟨dutySlot, committee, low, high, committeeOk, inside⟩ :=
      (mem_committeeWindow_iff parentParticipantsOk).mp
        (Store.mem_parentVotersOf.mp (Finset.mem_filter.mp member).1).1
    exact (mem_committeeWindow_iff callerWindowOk).mpr
      ⟨dutySlot, committee, low, UInt64.le_trans high beforeBlockLe, committeeOk, inside⟩
  have cover := Store.threshold_mul_stake_le_of_computeAdversarialWeight
    adversaryMaximumOk equivocationOk rangeOk
    (Store.stake_le_computeCommitteeWeightBetweenSlots adversaryMembersOk adversaryMaximumOk
      fun v member => Store.mem_activeMembers.mp member)
    (fun v _ => Nat.mod_eq_zero_of_dvd (dvd_balanceAt_of_aligned aligned
      (Nat.dvd_of_mod_eq_zero increment) v.toNat))
  have newMaximumOk : ((e.world k).state w).computeCommitteeWeightBetweenSlots
      receiverHead.root state firstSlot last = .ok receiverTotal := by
    rw [Store.computeCommitteeWeightBetweenSlots_of_covered covered, receiverTotalOk]
    rfl
  obtain ⟨newSourceMaximum, newSourceScore, newSourceMaximumOk, newSourceScoreOk⟩ :=
    weights.reads w receiver k receiverHead state current firstSlot last receiverTotal
      (atTime ▸ later) (Nat.le_of_eq atTime) headOk currentOk lastPast stateOk newMaximumOk
  have sourceTotalOk : getTotalActiveBalance balanceSource = .ok newSourceMaximum := by
    rw [Store.computeCommitteeWeightBetweenSlots_of_covered covered] at newSourceMaximumOk
    exact mapError_ok_iff.mp newSourceMaximumOk
  have newValue :=
    (getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok sourceTotalOk)).2.2
  have growth : newSourceMaximum.toNat ≤ maximumSupport.toNat +
      stake (fun v => balanceAt balanceSource v.toNat) (G \ W) +
      exitReserve config balanceSource := by
    have bound := wideBound wideMembers wideMembersOk
    have unionSum : stake (fun v => balanceAt balanceSource v.toNat) (W ∪ G) =
        stake (fun v => balanceAt balanceSource v.toNat) W +
          stake (fun v => balanceAt balanceSource v.toNat) (G \ W) := by
      rw [← Finset.union_sdiff_self_eq_union]
      exact Finset.sum_union Finset.disjoint_sdiff
    rw [unionW, unionSum] at bound
    change newSourceMaximum.toNat = max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (stake (fun v => balanceAt balanceSource v.toNat) (activeVoters balanceSource)) at newValue
    change maximumSupport.toNat = max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (stake (fun v => balanceAt balanceSource v.toNat) W) at oldValue
    omega
  -- The caller's reserve pays for Byzantine growth after honest promotion is counted.
  have sourceMargin := honest_margin_of_partial_sets within nested supportersIn parentsIn
    ((disjoint_supporters_parentVoters callerKnown callerParentKnown parentLower).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    Store.equivocatorsOf_subset_activeMembers (weights.dishonest u caller n later)
    equivocationValue supportOk half unionBound cover base parentDiscount growth
  have sourceUnslashed : ∀ v ∈ J, NotSlashed balanceSource v := by
    obtain ⟨held, boundary, stored, _, advanced⟩ :=
      e.checkpointStates_fixedChecks anchorStore (anchored u caller)
        (Store.checkpointState_ok_iff.mp sourceOk)
    intro v honest
    apply (notSlashed_lookahead advanced v).mpr
    exact unslashed u caller n held later
      (Store.counts_of_fixedChecks (checks := checks) stored (.inl rfl)) v honest
  let newSupporters := oldSupporters ∪ {v ∈ G | v ∈ J}
  let newParents := oldParents \ {v ∈ G | v ∈ J}
  have supportersHonest : ∀ v ∈ newSupporters, v ∈ J := by
    intro v member
    rcases Finset.mem_union.mp member with old | fresh
    · exact (Finset.mem_filter.mp old).2
    · exact (Finset.mem_filter.mp fresh).2
  have parentsHonest : ∀ v ∈ newParents, v ∈ J :=
    fun _ member => (Finset.mem_filter.mp (Finset.mem_sdiff.mp member).1).2
  have sourceSupportersActive : ∀ v ∈ newSupporters,
      v ∈ ((unslashedActiveBalances balanceSource).map (·.1)).toFinset := by
    intro v member
    rcases Finset.mem_union.mp member with old | fresh
    · exact supportersActive v old
    · exact tallyActive_of_activeMember (Finset.mem_filter.mp fresh).1
        (sourceUnslashed v (Finset.mem_filter.mp fresh).2)
  -- Apply the larger-window margin once, preserving its receiver activity masks.
  have newMargin := margin_of_active_sets sourceSupportersActive
    (fun v member => parentsActive v (Finset.mem_sdiff.mp member).1)
    (weights.margin w receiver k receiverHead state score newSourceScore
      firstSlot last receiverTotal newSourceMaximum (atTime ▸ later) (Nat.le_of_eq atTime) headOk
      stateOk scoreOk newSourceScoreOk newMaximumOk newSourceMaximumOk newSupporters newParents
      supportersHonest parentsHonest)
  have newScoreEq : newSourceScore = proposerScore :=
    Except.ok.inj (newSourceScoreOk.symm.trans boostOk)
  subst newSourceScore
  have honestLatest : ∃ v message, v ∈ J ∧
      ((e.world n).state u).latestMessages[v]? = some message := by
    by_cases child : oldSupporters.Nonempty
    · obtain ⟨v, member⟩ := child
      obtain ⟨message, _, latest, _⟩ := Store.exists_of_voteCountsFor _
        (Store.voteCountsFor_of_mem_supportersOf (Finset.mem_filter.mp member).1)
      exact ⟨v, message, (Finset.mem_filter.mp member).2, latest⟩
    · have parent : oldParents.Nonempty := by
        by_contra absent
        have noParents := Finset.not_nonempty_iff_eq_empty.mp absent
        have noSupporters := Finset.not_nonempty_iff_eq_empty.mp child
        rw [noParents, noSupporters, stake_empty, Nat.mul_zero, Nat.zero_add] at positiveHonest
        exact Nat.not_lt_zero _ positiveHonest
      obtain ⟨v, member⟩ := parent
      obtain ⟨_, _, _, message, _, latest, _⟩ :=
        Store.mem_parentVotersOf.mp (Finset.mem_filter.mp member).1
      exact ⟨v, message, (Finset.mem_filter.mp member).2, latest⟩
  obtain ⟨v, message, honest, latest⟩ := honestLatest
  obtain ⟨attestation, signedMessage, seen, _, signed, _⟩ :=
    e.exists_signed_origin_of_latestMessages anchorStore anchored caller latest
  obtain ⟨signedAt, _, maySign⟩ :=
    e.exists_maySign_of_signed (e.view_subset_sent n u seen) signed honest
  obtain ⟨_, _, _, genesis, _, _, _⟩ := maySign
  have receiverGenesis : ((e.world k).state w).genesisTimeMs = genesisTimeMs := by
    rw [(e.clock_bounds w k).1, anchored w receiver, ← anchored v honest,
      ← (e.clock_bounds v signedAt).1, genesis]
  have currentRead := mapError_ok_iff.mp currentOk
  change computeSlotAtTimeMs config ((e.world k).state w).genesisTimeMs
    ((e.world k).state w).timeMs = .ok current at currentRead
  rw [receiverGenesis] at currentRead
  obtain ⟨endTime, endTimeOk, endTimeLe⟩ := boundary_of_current_slot currentRead
  have endBound : endTime.toNat ≤ time :=
    (UInt64.le_iff_toNat_le.mp endTimeLe).trans_eq (receiverUpToDate.1.trans atTime)
  have parentEpochLe :
      (computeEpochAtSlot preset parentBlock.slot).toNat ≤ callerEpoch.toNat := by
    rw [callerEpochEq]
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp
      (callerBlocksLe _ _ callerParentKnown))
  have freshAssigned := committees.assigned w receiver k (Nat.le_of_eq atTime)
    receiverHead current slot epochEnd freshMembers headOk currentOk endPast
    (fun headState headStateOk => by
      obtain ⟨readSlot, readSlotOk, _, statesLe⟩ :=
        receiverForward.slots_le_current slots (UInt64.le_of_eq anchorSlot)
      rw [currentOk, Except.ok.injEq] at readSlotOk
      subst readSlot
      have stateSlotLe := statesLe _ _ (Store.blockState_ok_iff.mp headStateOk)
      have epochLe := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
        (UInt64.le_iff_toNat_le.mp stateSlotLe)
      have receiverEpochEq : receiverEpoch = computeEpochAtSlot preset current := by
        simpa [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
          using receiverEpochOk.symm
      simp only [receiverEpochEq, computeEpochAtSlot, UInt64.toNat_div] at age
      simp only [getCurrentEpoch, callerEpochEq, computeEpochAtSlot, UInt64.toNat_div]
        at parentEpochLe ⊢
      omega) freshMembersOk
  by_cases covered : ((e.world k).state w).isAncestor
      ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true
  · exact .inr covered
  left
  have transported := stake_le_of_supporter_parent_transport
    (fun v => if v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset
      then balanceAt state v.toNat else 0) (fun v => balanceAt state v.toNat)
    newSupporters newParents
    {v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ | v ∈ J}
    {v ∈ ((e.world k).state w).parentVotersOf state receiverParticipants block parentBlock | v ∈ J}
    (by
      apply Finset.disjoint_left.mpr
      intro v supporter parent
      have parentOld := (Finset.mem_sdiff.mp parent).1
      rcases Finset.mem_union.mp supporter with old | fresh
      · exact Finset.disjoint_left.mp
          (disjoint_supporters_parentVoters callerKnown callerParentKnown parentLower)
          (Finset.mem_filter.mp old).1 (Finset.mem_filter.mp parentOld).1
      · exact (Finset.mem_sdiff.mp parent).2 fresh)
    (fun v => by split <;> omega)
    (fun v member positive => by
      have active : v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset := by
        by_contra absent
        simp only [ite_eq_right absent, Nat.lt_irrefl] at positive
      refine Finset.mem_filter.mpr ⟨?_, supportersHonest v member⟩
      rcases Finset.mem_union.mp member with old | fresh
      · exact (oldSupportTransport v old active).resolve_right covered
      · have freshHonest := (Finset.mem_filter.mp fresh).2
        obtain ⟨dutySlot, committeeIndex, low, high, duty⟩ :=
          (freshAssigned v freshHonest).mp
            (Store.mem_activeMembers.mp (Finset.mem_filter.mp fresh).1).1
        exact (freshDutySupport endTime endTimeOk endBound v freshHonest dutySlot committeeIndex
          low (UInt64.lt_of_le_of_lt high endPast) duty active).resolve_right covered)
    (fun v member positive => by
      have active : v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset := by
        by_contra absent
        simp only [ite_eq_right absent, Nat.lt_irrefl] at positive
      have old := (Finset.mem_sdiff.mp member).1
      rcases (oldParentTransport v old active).resolve_right covered with parent | child
      · exact .inr (Finset.mem_filter.mpr ⟨parent, parentsHonest v member⟩)
      · exact .inl (Finset.mem_filter.mpr ⟨child, parentsHonest v member⟩))
  have windowBound := Store.stake_le_computeCommitteeWeightBetweenSlots receiverWindowOk
    newMaximumOk (fun v member => Store.mem_activeMembers.mp member)
  change newSourceMaximum.toNat + proposerScore.toNat + shift <
    stake (fun v => balanceAt balanceSource v.toNat) newParents +
      2 * stake (fun v => balanceAt balanceSource v.toNat) newSupporters at sourceMargin
  exact lt_of_transported_margin sourceMargin newMargin transported windowBound

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

A validator active in the source may sit in no committee of a whole epoch of the receiver window.

The source stake of such validators fits the exit reserve, as `exited` says.

The window of the receiver is the committees of its head between the parent and its own slot.

The conclusion bounds the active members of that window, as `HeadFollowsSupport` reads it.

The preset bounds are sufficient for this argument; they are not claimed to be necessary.

The proof follows three lemmas of [verified-fast-confirmation][vfc].

Two are `honest_supporters_sum_le_Sval_window` and `weak_base_discharged_window`.

The third is `bval_endpoint_strip_window_uniform`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem Execution.honest_support_of_historical_anchor {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
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
    (anchored : ∀ w ∈ J, e.start w = anchor)
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
    (unslashed : ∀ w ∈ J, ∀ k (state : BeaconState preset fork), (e.world k).time ≤ time →
      ((e.world k).state w).Counts config state → ∀ v ∈ J, NotSlashed state v)
    (supply : ∀ w ∈ J, ∀ k (checkpoint : Checkpoint) (state : BeaconState preset fork),
      (e.world k).time ≤ time → ((e.world k).state w).checkpointState checkpoint = .ok state →
      ActiveStakeAtMost stakeCapGwei state)
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
      firstSlot beforeBlock = .ok receiverParticipants)
    (exited : ∀ epoch epochStart next epochEnd epochMembers,
      computeStartSlotAtEpoch preset epoch = .ok epochStart →
      addChecked epochStart preset.SLOTS_PER_EPOCH = .ok next →
      subChecked next 1 = .ok epochEnd →
      firstSlot ≤ epochStart → epochEnd ≤ last →
      ((e.world k).state w).getCommitteesBetweenSlots receiverHead.root epochStart epochEnd =
        .ok epochMembers →
      stake (fun v => balanceAt balanceSource v.toNat)
          {v ∈ activeVoters balanceSource | v ∉ epochMembers} ≤
        exitReserve config balanceSource) :
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
  obtain ⟨receiverTotal, receiverTotalOk⟩ := getTotalActiveBalance_exists_ok_of_activeStakeAtMost
    (state.validators.bound preGloas)
    (supply w receiver k _ state (by omega) stateOk) stakeCapGwei_lt
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
  have receiverForward := e.forwardReachable
    (fun w hw => (anchored w hw) ▸ Store.ForwardReachable.anchor anchorStore) k w receiver
  have receiverJustifiedHorizon := UInt64.le_trans
    (receiverForward.justified_epoch_le_current sound slots (UInt64.le_of_eq anchorSlot)
      receiverEpochOk).1 (inHorizon w receiver k receiverEpoch (by omega) receiverEpochOk)
  have rootFinalReady := fun j le ready => (rootFinal j le ready).imp_right fun covered =>
    e.justified_covers_of_finalized_covers anchorStore sound anchored preGloas chain
      receiver le (by omega) receiverJustifiedHorizon known covered
  by_cases rootAnchor : root = anchor.finalizedCheckpoint.root
  · right
    have justifiedTest := Store.isAncestor_getHead headOk
    unfold Store.isAncestor at justifiedTest
    obtain ⟨justifiedBlock, justifiedOk, _⟩ := bind_ok_iff.mp justifiedTest
    rw [rootAnchor]
    exact e.isAncestor_anchor_of_known anchorStore anchored receiver
      (Store.block_ok_iff.mp justifiedOk)
  have callerReachable := e.reachable
    (fun w hw => (anchored w hw) ▸ Store.Reachable.anchor anchorStore) n u caller
  have callerKnown := Store.block_ok_iff.mp blockOk
  have callerParentKnown := Store.block_ok_iff.mp parentOk
  have blockOther : block ≠ anchorBlock := by
    intro same
    obtain ⟨r, hashed, _, _, _, final, _, _⟩ := getForkchoiceStore_anchor anchorStore
    have rootHash := callerReachable.root callerKnown
    rw [same, hashed, Except.ok.injEq] at rootHash
    exact rootAnchor (by simpa only [final] using rootHash.symm)
  obtain ⟨rootState, _, _, produced⟩ :=
    callerReachable.blockStatesFromParents callerKnown
  obtain ⟨parentState, _, _, signedBlock, messageEq, parentStateKnown, transition⟩ :=
    produced blockOther
  have parentLower : parentBlock.slot < block.slot := by
    have stateLower := (stateTransition_slot transition).1
    rw [messageEq] at stateLower
    exact UInt64.lt_of_le_of_lt (callerReachable.blockState_slot_le
      (UInt64.le_of_eq anchorSlot) callerParentKnown parentStateKnown) stateLower
  have rootOnParent : ((e.world n).state u).isAncestor ⟨root, .pending⟩
      ⟨block.parentRoot, .pending⟩ = .ok true := by
    have walk := Store.getAncestor_parent_of_slot_lt (node := ⟨root, .pending⟩)
      callerKnown callerParentKnown parentLower
    have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
    simp [Store.isAncestor, parentOk, walk, Store.parentPayloadStatus_of_lt preGloas,
      notGloas, bind, Except.bind, pure, Except.pure]
  obtain ⟨callerNode, callerHeadOk, callerRoot⟩ := callerHead
  have pending := Store.getHead_pending preGloas callerHeadOk
  have nodeEq : callerNode = ⟨head, .pending⟩ := by
    cases callerNode with
    | mk r status =>
      change r = head at callerRoot
      change status = .pending at pending
      simp only [callerRoot, pending]
  have parentOnHead := Store.isAncestor_trans_of_lt preGloas callerKnown callerParentKnown
    (by simpa only [nodeEq] using rootOnHead) rootOnParent
  have historicalFound : ∃ b, ((e.world n).state u).blocks[historical]? = some b := by
    unfold Store.getBlockEpoch at historicalEpochOk
    obtain ⟨b, found, _⟩ := bind_ok_iff.mp historicalEpochOk
    exact ⟨b, Store.block_ok_iff.mp found⟩
  obtain ⟨historicalBlock, historicalFound⟩ := historicalFound
  have historicalOnHead := Store.isAncestor_trans_of_lt preGloas callerParentKnown
    historicalFound parentOnHead below
  obtain ⟨historicalBlock', historicalBoundary, historicalKnown, historicalBoundaryOk,
      historicalBelow, historicalRead⟩ :=
    checkpoint_of_recent_historical anchorStore sound anchorSlot anchorBoundary anchored
      slots preGloas chain caller later callerEpochOk
      (inHorizon u caller n callerEpoch later callerEpochOk) historicalEpochOk recent
      callerHeadOk (by simpa only [nodeEq] using historicalOnHead)
  rw [historicalFound, Option.some.injEq] at historicalKnown
  subst historicalBlock'
  have historicalKnown := historicalFound
  have callerEpochEq : callerEpoch = computeEpochAtSlot preset slot := by
    simpa [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure] using
      callerEpochOk.symm
  have callerFinalizedKnown := e.finalized_known_of_prefix anchorStore sound anchored slots
    anchorSlot preGloas chain caller later callerEpochOk
    (inHorizon u caller n callerEpoch later callerEpochOk)
  have callerOrigins : ((e.world n).state u).VotesHaveOrigins config := by
    intro v message latest
    obtain ⟨attestation, _, _, same, _, origin⟩ :=
      e.exists_signed_origin_of_latestMessages anchorStore anchored caller latest
    exact ⟨attestation, same, origin⟩
  have historicalEpochEq : historicalEpoch = computeEpochAtSlot preset historicalBlock.slot := by
    simpa [Store.getBlockEpoch, Store.block_ok_iff.mpr historicalKnown, bind, Except.bind,
      pure, Except.pure] using historicalEpochOk.symm
  have historicalSlotLe : historicalBlock.slot ≤ parentBlock.slot := by
    obtain ⟨b, held, lower⟩ := Store.slot_le_of_isAncestor historicalKnown below
    rw [callerParentKnown, Option.some.injEq] at held
    exact held ▸ lower
  have callerParentAge : callerEpoch.toNat ≤
      (computeEpochAtSlot preset parentBlock.slot).toNat + 1 := by
    have lower := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
      (UInt64.le_iff_toNat_le.mp historicalSlotLe)
    rw [historicalEpochEq] at recent
    simp only [computeEpochAtSlot, UInt64.toNat_div] at recent ⊢
    omega
  have receiverParentKnown : ((e.world k).state w).blocks[block.parentRoot]? =
      some parentBlock := by
    have test := receiverAbove
    unfold Store.isAncestor at test
    obtain ⟨other, read, _⟩ := bind_ok_iff.mp test
    have held := Store.block_ok_iff.mp read
    have same := oneBlock u caller w receiver n k later (by omega)
      block.parentRoot parentBlock other callerParentKnown held
    exact same ▸ held
  have callerForward := e.forwardReachable
    (fun w hw => (anchored w hw) ▸ Store.ForwardReachable.anchor anchorStore) n u caller
  obtain ⟨callerCurrent, callerCurrentOk, callerBlocksLe, _⟩ :=
    callerForward.slots_le_current slots (UInt64.le_of_eq anchorSlot)
  rw [slotOk, Except.ok.injEq] at callerCurrentOk
  subst callerCurrent
  have oldSlotCommittees : ∀ dutySlot, firstSlot ≤ dutySlot → dutySlot ≤ lastSlot →
      ((e.world n).state u).getSlotCommittee head dutySlot =
        ((e.world k).state w).getSlotCommittee receiverHead.root dutySlot := by
    intro dutySlot low high
    have parentLow : parentBlock.slot ≤ dutySlot := by
      have start := (addChecked_ok_iff.mp firstOk).2
      have lower := UInt64.le_iff_toNat_le.mp low
      exact UInt64.le_iff_toNat_le.mpr (by omega)
    have callerHigh : dutySlot ≤ slot := by
      have finish := (subChecked_ok_iff.mp lastOk).2
      have upper := UInt64.le_iff_toNat_le.mp high
      exact UInt64.le_iff_toNat_le.mpr (by omega)
    have epochHigh : (computeEpochAtSlot preset dutySlot).toNat ≤ callerEpoch.toNat := by
      rw [callerEpochEq]
      simp only [computeEpochAtSlot, UInt64.toNat_div]
      exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp callerHigh)
    exact slotCommittee_eq_of_recent_parent anchorStore anchorSlot anchored oneBlock slots
      preGloas lookahead caller receiver later (by omega) callerParentKnown receiverParentKnown
      parentOnHead receiverAbove callerEpochOk receiverEpochOk callerParentAge age
      parentLow (epochHigh.trans callerParentAge)
  have sourceMaximumRead := maximum_of_same_slotCommittees maximumOk oldSlotCommittees
  have sourceMaximumEq := Except.ok.inj (sourceMaximumOk.symm.trans sourceMaximumRead)
  rw [sourceMaximumEq] at transferred
  have beforeBlockLe : beforeBlock ≤ lastSlot := by
    have rootLe := UInt64.le_iff_toNat_le.mp (callerBlocksLe _ _ callerKnown)
    have beforeNat := (subChecked_ok_iff.mp beforeOk).2
    have lastNat := (subChecked_ok_iff.mp lastOk).2
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  have parentWindows := committeeWindow_transfer parentParticipantsOk
    (fun dutySlot low high => oldSlotCommittees dutySlot low (UInt64.le_trans high beforeBlockLe))
  have sameParentParticipants := Except.ok.inj (receiverParticipantsOk.symm.trans parentWindows)
  have parentFinalReady : ∀ j ≤ k, (e.world j).time < (e.world n).time →
      UpToDate config checks sources (e.world j).time ((e.world j).view w)
        ((e.world j).state w) →
      (∃ boundary,
        computeStartSlotAtEpoch preset ((e.world j).state w).finalizedCheckpoint.epoch =
          .ok boundary ∧ boundary ≤ parentBlock.slot ∧
        ((e.world k).state w).getCheckpointBlock block.parentRoot
          ((e.world j).state w).finalizedCheckpoint.epoch =
            .ok ((e.world j).state w).finalizedCheckpoint.root) ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true := by
    intro j le before ready
    obtain ⟨boundary, boundaryOk, lower⟩ := finalized_boundary_le_slot_of_earlier anchorStore
      sound slots anchorSlot anchored caller receiver upToDate ready before.le slotOk callerEpochOk
      callerParentAge (callerReachable.anchorSlot_le_block callerParentKnown)
    rcases rootFinalReady j le ready with ⟨other, otherOk, _, checkpoint⟩ | covered
    · have same := Except.ok.inj (otherOk.symm.trans boundaryOk)
      subst other
      refine .inl ⟨boundary, boundaryOk, lower, ?_⟩
      have walk := Store.getAncestor_of_gt (node := ⟨root, .pending⟩) preGloas known
        (UInt64.not_le.mpr (UInt64.lt_of_le_of_lt lower parentLower))
        receiverParentKnown parentLower
      simpa only [Store.getCheckpointBlock, boundaryOk, Except.mapError, bind, Except.bind,
        walk] using checkpoint
    · exact .inr covered
  have oldSupportFloor : ∀ v ∈ oldSupporters, ∀ message,
      ((e.world n).state u).latestMessages[v]? = some message →
      callerEpoch.toNat ≤ message.rank.toNat + 1 := by
    intro v member message latest
    obtain ⟨attestation, latest', origin, lowSlot⟩ :=
      Store.VotesHaveOrigins.exists_attestation_of_mem_supportersOf callerOrigins callerKnown
        (Finset.mem_filter.mp member).1
    have same := Option.some.inj (latest.symm.trans latest')
    have lower := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
      (UInt64.le_iff_toNat_le.mp (UInt64.le_trans historicalSlotLe
        (UInt64.le_trans (UInt64.le_of_lt parentLower) lowSlot)))
    have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
    have rankEpoch : message.rank = computeEpochAtSlot preset attestation.data.slot := by
      simpa [same, LatestMessage.rank, LatestMessage.ofAttestation, notGloas] using
        origin.targetEpoch
    rw [historicalEpochEq] at recent
    rw [rankEpoch]
    simp only [computeEpochAtSlot, UInt64.toNat_div] at recent ⊢
    omega
  have oldParentFloor : ∀ v ∈ oldParents, ∀ message,
      ((e.world n).state u).latestMessages[v]? = some message →
      callerEpoch.toNat ≤ message.rank.toNat + 1 := by
    intro v member message latest
    obtain ⟨_, _, _, parentMessage, supported, parentLatest, supportedOk, which⟩ :=
      Store.mem_parentVotersOf.mp (Finset.mem_filter.mp member).1
    obtain ⟨attestation, same, origin⟩ := callerOrigins parentLatest
    have sameMessage := Option.some.inj (latest.symm.trans parentLatest)
    have supportedRoot : supported.root = block.parentRoot := by
      rcases which with rfl | rfl <;> rfl
    have rootEq : attestation.data.beaconBlockRoot = block.parentRoot := by
      have eq := Store.getSupportedNode_root supportedOk
      simpa only [same, LatestMessage.ofAttestation, supportedRoot] using eq.symm
    obtain ⟨tip, held, lowSlot⟩ := origin.voted
    rw [rootEq, callerParentKnown, Option.some.injEq] at held
    subst tip
    have lower := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
      (UInt64.le_iff_toNat_le.mp (UInt64.le_trans historicalSlotLe lowSlot))
    have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
    have rankEpoch : message.rank = computeEpochAtSlot preset attestation.data.slot := by
      simpa [sameMessage, same, LatestMessage.rank, LatestMessage.ofAttestation, notGloas] using
        origin.targetEpoch
    rw [historicalEpochEq] at recent
    rw [rankEpoch]
    simp only [computeEpochAtSlot, UInt64.toNat_div] at recent ⊢
    omega
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
  have newerRankSupport : ∀ v ∈ J, ∀ first second,
      ((e.world n).state u).latestMessages[v]? = some first →
      ((e.world k).state w).latestMessages[v]? = some second →
      first.rank < second.rank → callerEpoch.toNat ≤ first.rank.toNat + 1 →
      v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset →
      v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ := by
    intro v honest first second firstOk secondOk higher floor active
    obtain ⟨attestation, source, seen, same, signed, origin⟩ :=
      e.exists_signed_origin_of_latestMessages anchorStore anchored receiver secondOk
    obtain ⟨signedAt, earlier, maySign⟩ :=
      e.exists_maySign_of_signed (e.view_subset_sent k w seen) signed honest
    have latest : ((e.world k).state w).latestMessages[v]? =
        some (LatestMessage.ofAttestation attestation) := by simpa only [same] using secondOk
    by_cases fresh : slot ≤ attestation.data.slot
    · exact freshSlotSupport v honest attestation latest fresh origin
        ⟨signedAt, earlier, maySign⟩ active
    have oldRank := rank_le_of_stale_slot sync preGloas oneBlock admitted votes fits
      anchorStore anchorSlot anchorBoundary anchored honest caller maySign origin.targetEpoch
      slotOk beginOk atSlot later (callerEpochEq ▸ epochStartOk) epochStartTimeOk
      (UInt64.not_le.mp fresh) upToDate
      (fun equivocated => weights.dishonest u caller n later v equivocated honest) firstOk
      (by simpa only [callerEpochEq] using floor) historicalSafe
      (fun j bounded => nonzero v honest j bounded) historicalKnown callerFinalizedKnown
      historicalBoundaryOk historicalBelow historicalRead
    have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
    have targetHigher : first.rank < attestation.data.target.epoch := by
      simpa [same, LatestMessage.rank, LatestMessage.ofAttestation, notGloas] using higher
    exact ((UInt64.not_lt.mpr oldRank) targetHigher).elim
  have oldSupportOfRank : ∀ v ∈ oldSupporters, ∀ first second,
      ((e.world n).state u).latestMessages[v]? = some first →
      ((e.world k).state w).latestMessages[v]? = some second →
      first.rank ≤ second.rank →
      v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset →
      v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ := by
    intro v member first second firstOk secondOk rank active
    by_cases same : first.rank = second.rank
    · exact equalRankSupport v member first second firstOk secondOk same active
    · exact newerRankSupport v (Finset.mem_filter.mp member).2 first second firstOk secondOk
        (UInt64.lt_of_le_of_ne rank same) (oldSupportFloor v member first firstOk) active
  have oldSupportTransport : ∀ v ∈ oldSupporters,
      v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset →
      v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true := by
    intro v member active
    have honest := (Finset.mem_filter.mp member).2
    have counts := Store.voteCountsFor_of_mem_supportersOf (Finset.mem_filter.mp member).1
    obtain ⟨first, _, firstOk, _⟩ := Store.exists_of_voteCountsFor _ counts
    rcases recorded_rank_of_counted_vote sync slots preGloas oneBlock admitted votes prompt fits
        anchorStore sound anchorSlot anchorBoundary anchored chain inHorizon nonzero caller honest
        receiver slotOk beginOk atSlot later atTime receiverUpToDate
        (fun j bounded equivocated => weights.dishonest w receiver j bounded v equivocated honest)
        callerKnown known (fun j le _ => rootFinalReady j le) firstOk counts
        with ⟨second, secondOk, rank⟩ | covered
    · exact .inl (oldSupportOfRank v member first second firstOk secondOk rank active)
    · exact .inr covered
  have oldParentTransport : ∀ v ∈ oldParents, v ∈ receiverParticipants →
      v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset →
      (v ∈ ((e.world k).state w).parentVotersOf state receiverParticipants block parentBlock ∨
        v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩) ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true := by
    intro v member participant active
    have honest := (Finset.mem_filter.mp member).2
    obtain ⟨_, _, notKnown, first, supported, firstOk, supportedOk, which⟩ :=
      Store.mem_parentVotersOf.mp (Finset.mem_filter.mp member).1
    have supportedEq : supported = ⟨block.parentRoot, .pending⟩ := by
      rcases which with rfl | rfl
      · rfl
      · rw [Store.parentPayloadStatus_of_lt preGloas]
    have counts : ((e.world n).state u).voteCountsFor ⟨block.parentRoot, .pending⟩ v = true := by
      apply Store.voteCountsFor_of_check _ firstOk (by simpa using notKnown)
      simpa only [supportedOk, supportedEq, bind, Except.bind] using
        (Store.isAncestor_self (node := ⟨block.parentRoot, .pending⟩) callerParentKnown)
    rcases recorded_rank_of_counted_vote sync slots preGloas oneBlock admitted votes prompt fits
        anchorStore sound anchorSlot anchorBoundary anchored chain inHorizon nonzero caller honest
        receiver slotOk beginOk atSlot later atTime receiverUpToDate
        (fun j bounded equivocated => weights.dishonest w receiver j bounded v equivocated honest)
        callerParentKnown receiverParentKnown parentFinalReady firstOk counts
        with ⟨second, secondOk, rank⟩ | covered
    · left
      by_cases equal : first.rank = second.rank
      · left
        have same := latest_eq_of_rank_eq slots preGloas anchorStore anchored caller receiver
          honest firstOk secondOk equal
        obtain ⟨_, validator, found, isActive⟩ := Store.mem_activeMembers.mp
          (activeMember_of_tallyActive (state.validators.bound preGloas) active participant)
        have flag : validator.slashed = false := by
          simpa only [NotSlashed, found, Option.map_some, Option.getD_some] using
            receiverUnslashed v honest
        refine Store.mem_parentVotersOf.mpr ⟨participant, ⟨validator, found, flag, isActive⟩,
          (fun equivocated => weights.dishonest w receiver k (by omega) v equivocated honest),
          second, ⟨block.parentRoot, .pending⟩, secondOk, ?_, .inl rfl⟩
        simpa only [Store.getSupportedNode_of_lt preGloas, supportedEq, same] using supportedOk
      · right
        exact newerRankSupport v honest first second firstOk secondOk
          (UInt64.lt_of_le_of_ne rank equal) (oldParentFloor v member first firstOk) active
    · exact .inr covered
  have freshRecordedSupport : ∀ v ∈ J, ∀ dutySlot committeeIndex deadline signedAt
      (attestation : Attestation preset fork) indexed message,
      VoteAt e v dutySlot committeeIndex deadline signedAt attestation indexed →
      attestation.data.slot = dutySlot →
      attestation.data.target.epoch = computeEpochAtSlot preset dutySlot →
      deadline + Δ ≤ time → slot ≤ dutySlot →
      ((e.world k).state w).latestMessages[v]? = some message →
      attestation.data.target.epoch ≤ message.rank →
      v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset →
      v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ := by
    intro v honest dutySlot committeeIndex deadline signedAt attestation indexed message
      vote dataSlot dataEpoch delivered floor latest rank active
    have seen := vote.mem_view sync honest receiver (k := k) (by omega)
    have signedVote := signed_of_voteAt anchorStore anchored honest vote
    obtain ⟨other, source, sourceSeen, rfl, signedOther, origin⟩ :=
      e.exists_signed_origin_of_latestMessages anchorStore anchored receiver latest
    have fresh := latest_slot_floor_of_signed_rank slots preGloas honest
      (e.view_subset_sent k w seen) (e.view_subset_sent k w sourceSeen) signedVote signedOther
      origin (by simpa [dataSlot] using dataEpoch) rank (dataSlot ▸ floor)
    exact freshSlotSupport v honest other latest fresh origin
      (e.exists_maySign_of_signed (e.view_subset_sent k w sourceSeen) signedOther honest) active
  have freshDutySupport : ∀ endTime,
      computeTimeAtSlotMs config genesisTimeMs current = .ok endTime →
      endTime.toNat ≤ time → ∀ v ∈ J, ∀ dutySlot committeeIndex,
      slot ≤ dutySlot → dutySlot < current →
      assignment.committee v dutySlot = some committeeIndex →
      v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset →
      v ∈ ((e.world k).state w).supportersOf state ⟨root, .pending⟩ ∨
      ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩
        ⟨root, .pending⟩ = .ok true := by
    intro endTime endOk complete v honest dutySlot committeeIndex low high duty active
    have started : e.startTime ≤ (e.world n).time := e.monotone_time (Nat.zero_le n)
    rcases recorded_duty_of_safe_interval sync slots preGloas oneBlock admitted votes prompt fits
        anchorStore sound anchorSlot anchorBoundary anchored chain inHorizon nonzero
        beginOk endOk started (by omega) complete safe honest receiver atTime receiverUpToDate
        (fun j bounded equivocated => weights.dishonest w receiver j bounded v equivocated honest)
        known rootFinal low high duty with recorded | covered
    · obtain ⟨deadline, signedAt, attestation, indexed, message, vote, dataSlot, dataEpoch,
        delivered, latest, rank⟩ := recorded
      exact .inl (freshRecordedSupport v honest dutySlot committeeIndex deadline signedAt
        attestation indexed message vote dataSlot dataEpoch delivered low latest rank active)
    · exact .inr covered
  obtain ⟨callerHeadBlock, callerHeadKnown, _⟩ :=
    Store.slot_le_of_isAncestor callerParentKnown parentOnHead
  obtain ⟨callerHeadState, callerHeadStateKnown, _⟩ :=
    callerReachable.blockStatesFromParents callerHeadKnown
  have callerBlockAge : callerEpoch.toNat ≤
      (computeEpochAtSlot preset block.slot).toNat + 1 := by
    have lower := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
      (UInt64.le_iff_toNat_le.mp (UInt64.le_of_lt parentLower))
    simp only [computeEpochAtSlot, UInt64.toNat_div] at callerParentAge ⊢
    omega
  have sourceHonestParents := honest_margin_of_recent_check committees caller later callerOrigins
    callerHeadOk
    (show ((e.world n).state u).blockState callerNode.root = .ok callerHeadState by
      simpa only [nodeEq] using Store.blockState_ok_iff.mpr callerHeadStateKnown)
    slotOk callerEpochOk blockOk callerBlockAge lastOk within supportOk
    (show ((e.world n).state u).getAdversarialWeight config callerNode.root balanceSource root =
      .ok adversary by simpa only [nodeEq] using adversaryOk)
    aligned increment (weights.dishonest u caller n later)
    (fun first last participants read => weights.sourceByzantine u caller n callerNode.root
      first last participants rfl read) base parentDiscount
  change maximumSupport.toNat + proposerScore.toNat + shift <
    stake (fun v => balanceAt balanceSource v.toNat) oldParents +
      2 * stake (fun v => balanceAt balanceSource v.toNat) oldSupporters at sourceHonestParents
  by_cases oldComplete : isFullValidatorSetCovered preset firstSlot lastSlot = .ok true
  · exact honest_support_of_complete_window
      ((disjoint_supporters_parentVoters callerKnown callerParentKnown parentLower).mono
        (Finset.filter_subset _ _) (Finset.filter_subset _ _))
      (fun _ member => (Finset.mem_filter.mp member).2)
      (fun _ member => (Finset.mem_filter.mp member).2)
      sourceHonestParents transferred (state.validators.bound preGloas) oldComplete
      receiverMaximumOk oldSupportTransport
      (fun v member active => oldParentTransport v member (by
        rw [sameParentParticipants]
        exact (Store.mem_parentVotersOf.mp (Finset.mem_filter.mp member).1).1) active)
  by_cases uncovered : isFullValidatorSetCovered preset firstSlot last = .ok false
  · exact honest_support_of_partial_window slots positive lookahead preGloas oneBlock half
      committees anchorStore anchorSlot anchored caller slotOk blockOk parentOk sourceOk boostOk
      firstOk lastOk maximumOk parentParticipantsOk within aligned increment supportOk adversaryOk
      base later weights unslashed callerEpochOk receiver atTime receiverUpToDate headOk
      receiverAbove
      stateOk currentOk receiverEpochOk age receiverLastOk receiverWindowOk scoreOk receiverTotalOk
      receiverIndices oldLastLe parentLower (by simpa only [nodeEq] using callerHeadOk) parentOnHead
      callerEpochEq callerOrigins callerParentAge receiverParentKnown callerBlocksLe
      oldSlotCommittees
      beforeBlockLe (Store.blockState_ok_iff.mpr callerHeadStateKnown) callerBlockAge oldComplete
      uncovered oldSupporters oldParents rfl rfl parentDiscount supportersActive parentsActive
      ((Nat.zero_le _).trans_lt sourceHonestParents) oldSupportTransport
      (fun v member active => oldParentTransport v member (by
        rw [sameParentParticipants]
        exact (Store.mem_parentVotersOf.mp (Finset.mem_filter.mp member).1).1) active)
      freshDutySupport
  exact honest_support_of_full_window slots positive lookahead preGloas oneBlock half
    committees anchorStore anchorSlot anchored caller slotOk blockOk parentOk sourceOk boostOk
    firstOk lastOk maximumOk parentParticipantsOk within aligned increment supportOk adversaryOk
    base later weights unslashed callerEpochOk receiver atTime receiverUpToDate headOk
    receiverAbove stateOk currentOk receiverEpochOk age receiverLastOk receiverWindowOk scoreOk
    receiverTotalOk oldLastLe parentLower (by simpa only [nodeEq] using callerHeadOk)
    parentOnHead callerEpochEq callerOrigins callerParentAge receiverParentKnown callerBlocksLe
    oldSlotCommittees beforeBlockLe (Store.blockState_ok_iff.mpr callerHeadStateKnown)
    callerBlockAge oldComplete uncovered oldSupporters oldParents rfl rfl parentDiscount
    supportersActive parentsActive ((Nat.zero_le _).trans_lt sourceHonestParents)
    oldSupportTransport
    (fun v member active => oldParentTransport v member (by
      rw [sameParentParticipants]
      exact (Store.mem_parentVotersOf.mp (Finset.mem_filter.mp member).1).1) active)
    freshDutySupport exited


end EthLib.Consensus.Models.Network
