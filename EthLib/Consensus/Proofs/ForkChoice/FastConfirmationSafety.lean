module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.ConfirmedCallStep
import EthLib.Consensus.Proofs.ForkChoice.Ghost
import EthLib.Consensus.Proofs.Time

/-!
# The end of a confirming walk of the fast confirmation rule

An honest call of the rule stores a root on later up-to-date honest heads.

This holds at every fork before Gloas, Phase 0 included.

It covers them from the start of the following slot through the inclusive time limit.

Otherwise two honest stores collide, or accountable-safety evidence holds.
-/

@[expose] public section
namespace EthLib.Consensus.Models.Network
open Base Uint64 Models Serialization.Ssz SszType ConfirmedCalls

variable {preset : Preset} {fork : Fork} {config : Config}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config .bls sources anchorState anchorBlock assignment
    genesisTimeMs) J}

section
set_option hygiene false
local notation "S" i:arg x:arg => ((e.world i).state x)
local notation "T" i:arg => ((e.world i).time)
local notation "Ready" i:arg x:arg =>
  UpToDate config .bls sources (T i) ((e.world i).view x) (S i x)

/-- Before Gloas, the root stored by an honest call lies on each up-to-date honest head.

This holds at every fork before Gloas, Phase 0 included.

It covers heads from the start of the call's following slot through the inclusive time limit.

The alternatives are an honest-store block collision or one of four kinds of safety evidence.

The call is any one of the validator's consecutive calls.

Its slot has a checked successor, whose start time is representable.

Only before Electra it assumes that the quorum drift is within each call's reserve.

That assumption allows a collision of two honest stores in place of the bound.

The run starts from genesis, verifies signatures with BLS and reaches the anchor state.

The model's genesis time is the anchor state's genesis time.

The anchor store is built from that state and its block, which share a slot at an epoch boundary.

Every honest store starts at the anchor store.

The anchor state's latest header has the anchor block's slot, proposer and parent root.

Its body root is the root of the anchor block's body, and its state root is zero.

Timing assumes synchrony, a positive slot duration, fitting delays and prompt processing.

Blocks are admitted after the delay, duty votes are validated and honest duty windows agree.

The parameter facts are the committee windows, the seed lookahead and the ring of RANDAO mixes.

They also include the direct-safety parameters, multi-slot epochs, the upward band and increment.

They also include the threshold, the aligned maximum balances and the cap order.

They also include the inclusion and withdrawal delays and the proposer score fit.

The activation balance is at most the largest effective balance before Electra.

The horizon precedes the next scheduled fork.

The store bounds are the epoch horizon, nonzero held state roots and unslashed counted states.

Through the limit, no honest store holds the anchor's parent, and checkpoint stakes are capped.

The stake floors hold for the held runs and for the terminal states.

The run assumptions are the pinned justification, the Byzantine bound and target inclusion.

They also include stale head voters in the committees that the rule reads.

Some honest store is up to date at or after the limit, and its slot has a checked predecessor.

The calls are at the starts of consecutive slots from a first slot.

The first slot's epoch is at least two, and strictly after the epoch of the anchor state.

The validator is honest, it is up to date at each call, and each call assumes its obligations. -/
theorem Execution.confirmedWalk_end_on_honest_heads [DecidablePred (· ∈ J)]
    {Δ limit : ℕ} {horizon : Epoch} {anchor : Store preset fork} {g : ForkedBeaconState preset}
    (before : fork < .glamsterdam)
    (drift : fork < .pectra → QuorumDriftWithin (e := e) horizon limit)
    (pre : Run config .bls g ⟨fork, anchorState⟩) (genesis : Genesis config .bls g)
    (anchorGenesis : secondsToMilliseconds anchorState.genesisTime = genesisTimeMs)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (initial : ∀ x ∈ J, e.start x = anchor)
    (anchorHeader : anchorState.latestBlockHeader.slot = anchorBlock.slot ∧
      anchorState.latestBlockHeader.proposerIndex = anchorBlock.proposerIndex ∧
      anchorState.latestBlockHeader.parentRoot = anchorBlock.parentRoot ∧
      SszType.hashTreeRoot anchorBlock.body = .ok anchorState.latestBlockHeader.bodyRoot)
    (anchorZero : anchorState.latestBlockHeader.stateRoot = Vector.replicate 32 0)
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (fits : DelayFits fork config genesisTimeMs Δ) (admitted : BlocksAdmitted e 0 Δ limit)
    (votes : ValidatedDutyVotes (e := e) limit) (prompt : Prompt e limit)
    (windows : AssignmentWindowAgreement (e := e) limit) (fit : config.CommitteeWindowsFit preset)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (exitWindow : preset.SeedLookaheadAtLeastThree)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (long : 1 < preset.SLOTS_PER_EPOCH) (parameters : DirectSafety.Parameters preset)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (maxAligned : MaxEffectiveBalancesAligned preset)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (band : preset.IncrementWithinUpwardBand) (delay : preset.InclusionDelayPositive)
    (withdrawDelay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (caps : CapOrder preset) (activation : ActivationWithinMaxEffective preset)
    (forkWindow : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat)
    (bounded : HonestStoreEpochsBounded (e := e) horizon limit)
    (roots : HeldBlockStateRootsNonzero (e := e) limit) (absent : AnchorParentAbsent (e := e) limit)
    (unslashed : HonestCountedStatesUnslashed (e := e) limit)
    (ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) limit)
    (scoreFits : config.ProposerScoreFits preset (2 * 10 ^ 17))
    (enough : HeldRunStakeFloor (e := e) pre horizon limit)
    (terminal : HeldTerminalStakeFloor (e := e) horizon limit)
    (pinned : JustifiedPinned (e := e) anchor.justifiedCheckpoint.epoch 0 0 limit)
    (byzantine : ByzantineCountedStake (e := e) anchor.justifiedCheckpoint.epoch 0 limit)
    (included : TargetIncluded (e := e) limit) (stale : StaleHeadVotersInWindow (e := e) limit)
    (reference : ∃ x ∈ J, ∃ m, ∃ ref finish : Slot, limit ≤ T m ∧ Ready m x ∧
      (S m x).getCurrentSlot config = .ok ref ∧ subChecked ref 1 = .ok finish)
    {u : ValidatorIndex} (caller : u ∈ J) {events : List ℕ} {firstSlot : Slot}
    (confirmationEpoch : 2 ≤ computeEpochAtSlot preset firstSlot)
    (anchorEpochBefore : getCurrentEpoch anchorState < computeEpochAtSlot preset firstSlot)
    (upToDate : ∀ n ∈ events, Ready n u)
    (atSlots : ∀ i n, events[i]? = some n → ∃ slot begin,
      (S n u).getCurrentSlot config = .ok slot ∧ slot.toNat = firstSlot.toNat + i ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧ T n = begin.toNat)
    {i n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    (obligations : ∀ j m input out,
      CallAt (e := e) u events (getFastConfirmationStore anchor) j m input out →
      CallObligations (e := e) 0 limit u m input out)
    {slot next : Slot} {following : UInt64}
    (slotOk : (S n u).getCurrentSlot config = .ok slot) (nextOk : addChecked slot 1 = .ok next)
    (followingOk : computeTimeAtSlotMs config genesisTimeMs next = .ok following) :
    (∀ w ∈ J, ∀ k hd, following.toNat ≤ T k → T k ≤ limit → Ready k w →
      (S k w).getHead config = .ok hd →
      (S k w).isAncestor ⟨hd.root, .pending⟩ ⟨after.confirmedRoot, .pending⟩ = .ok true) ∨
      HonestCollision (e := e) limit ∨ HistoricalDirectSafetyEvidence (e := e) pre limit ∨
      CrossStoreDirectSafetyEvidence (e := e) pre limit ∨
      CrossStoreJustifiedEvidence (e := e) pre limit ∨
        HeldStateFinalityEvidence (e := e) pre limit := by
  -- A receiver after the limit is not asked about, so a late following slot is vacuous.
  by_cases late : limit < following.toNat
  · exact .inl fun _ _ _ _ low high _ _ => absurd (low.trans high) (Nat.not_le_of_lt late)
  -- The call is at the start of its slot, so it is no later than the following slot.
  have followingLe : following.toNat ≤ limit := Nat.le_of_not_lt late
  obtain ⟨atSlot, begin, atSlotOk, -, beginOk, timeEq⟩ := atSlots i n calls.1
  rw [slotOk] at atSlotOk
  cases atSlotOk
  have nextEq := (addChecked_ok_iff.mp nextOk).2
  have le : slot ≤ next := UInt64.le_iff_toNat_le.mpr (by simp at nextEq; omega)
  obtain ⟨start, startOk, -, startLe⟩ := exists_timeAtSlotMs_of_le le followingOk
  rw [beginOk] at startOk
  cases startOk
  have bound : T n ≤ limit := by
    rw [timeEq]
    exact (UInt64.le_iff_toNat_le.mp startLe).trans followingLe
  -- Before Gloas the three assumptions from Gloas say nothing.
  have early : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  rcases e.callInvariant_of_run pre rfl anchorGenesis sync slots minLookahead exitWindow ring
      (fun gloas => absurd gloas early) (fun gloas => absurd gloas early)
      (fun gloas => absurd gloas early) admitted half long maxAligned votes fits prompt windows
      fit anchored anchorSlot anchorBoundary initial rfl increment bounded roots unslashed ceiling
      scoreFits parameters genesis enough terminal absent pinned anchorHeader anchorZero delay
      byzantine drift band withdrawDelay caps activation forkWindow included stale reference
      caller confirmationEpoch anchorEpochBefore upToDate atSlots obligations calls bound with
      holds | bad
  · -- The first clause of the call invariant covers the heads, whose ancestry reads their roots.
    refine .inl fun w member k hd low high ready headOk => ?_
    rw [← Store.isAncestor_getHead_root headOk]
    exact holds.1 slot next following slotOk nextOk followingOk (T k) low
      (Nat.lt_succ_of_le high) w member k hd rfl ready headOk
  · exact .inr bad
end

end EthLib.Consensus.Models.Network
