module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSupport

/-!
# The head of an honest store

The store of an honest validator computes a head at each event up to a last time.

Before Gloas the head computation reads the cached state of the justified checkpoint.

It reads the filtered block tree, the tally of the latest votes in that state, and the boost.

Each read succeeds in a store that honest moves build from an anchor.

The justified checkpoint state is cached, because an honest store imports a block together with
its votes, and each vote caches the state of its target.

Every walk down the parents of a block stops at or above the anchor.

A held block has its parent held, at a lower slot, and the anchor's parent is not held.

The sums of balances stay below `2^64` because each checkpoint state that an honest store reads
has at most `stakeCapGwei` of active stake.

The boost is at most a committee's weight, because its percentage is at most 100.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}

/-- The boost of a timely block fits below the cap when the active stake does.

The total that the boost reads is that of the unslashed active validators, or one increment.

The active stake bounds the first, and the increment is at most the cap.

At least two slots split the total, and the percentage of the boost is at most 100. -/
theorem computeProposerScore_le_stakeCap {state : BeaconState preset fork}
    (stakeLe : ActiveStakeAtMost stakeCapGwei state)
    (floor : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ stakeCapGwei)
    (long : 1 < preset.SLOTS_PER_EPOCH) (boost : config.PROPOSER_SCORE_BOOST.toNat ≤ 100) :
    ∃ score, computeProposerScore config state = .ok score ∧ score.toNat ≤ stakeCapGwei := by
  classical
  let indices := (unslashedActiveBalances state).map (·.1)
  have members : ∀ index ∈ indices,
      index.toNat < state.validators.data.size ∧
        index ∈ getActiveValidatorIndices state (getCurrentEpoch state) := by
    intro index member
    simp only [indices, List.mem_map, unslashedActiveBalances, List.mem_filterMap,
      Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq,
      Prod.exists] at member
    obtain ⟨i, balance, ⟨validator, position, inZip, active, rfl, rfl⟩, rfl⟩ := member
    have positionLt := (List.getElem?_eq_some_iff.mp
      (List.mem_zipIdx_iff_getElem?.mp inZip)).1
    have reduced : position.toUInt64.toNat ≤ position := by
      simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
      exact Nat.mod_le _ _
    refine ⟨by simpa using reduced.trans_lt positionLt, ?_⟩
    simp only [getActiveValidatorIndices, List.mem_filterMap,
      Option.ite_none_right_eq_some, Option.some.injEq, Prod.exists]
    exact ⟨validator, position, inZip, (Bool.and_eq_true_iff.mp active).1, rfl⟩
  have stakeBound : stake (fun v => balanceAt state v.toNat) indices.toFinset ≤
      stakeCapGwei := by
    apply le_trans (stake_mono (fun v member => ?_)) stakeLe
    exact List.mem_toFinset.mpr (members v (List.mem_toFinset.mp member)).2
  let amount := max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (stake (fun v => balanceAt state v.toNat) indices.toFinset)
  have amountLe : amount ≤ stakeCapGwei := max_le floor stakeBound
  have amountFits := amountLe.trans_lt stakeCapGwei_lt
  have totalOk : getTotalBalance state indices = .ok amount.toUInt64 := by
    apply getTotalBalance_ok_iff_stake.mpr
    exact ⟨fun i member => (members i member).1,
      stakeBound.trans_lt stakeCapGwei_lt, UInt64.toNat_ofNat_of_lt' amountFits⟩
  have slotsLong : 2 ≤ preset.SLOTS_PER_EPOCH.toNat := by
    have := UInt64.lt_iff_toNat_lt.mp long
    change 1 < preset.SLOTS_PER_EPOCH.toNat at this
    omega
  have nonzero : preset.SLOTS_PER_EPOCH ≠ 0 := by
    intro zero
    simp [zero] at slotsLong
  have quotient : amount / preset.SLOTS_PER_EPOCH.toNat ≤ stakeCapGwei / 2 :=
    Nat.div_le_div amountLe slotsLong (by decide)
  have productLe : amount / preset.SLOTS_PER_EPOCH.toNat *
      config.PROPOSER_SCORE_BOOST.toNat ≤ stakeCapGwei / 2 * 100 :=
    Nat.mul_le_mul quotient boost
  have productFits : amount / preset.SLOTS_PER_EPOCH.toNat *
      config.PROPOSER_SCORE_BOOST.toNat < 2 ^ 64 := by
    exact productLe.trans_lt (by norm_num [stakeCapGwei])
  have committeeOk : divChecked amount.toUInt64 preset.SLOTS_PER_EPOCH =
      .ok (amount.toUInt64 / preset.SLOTS_PER_EPOCH) :=
    divChecked_ok_iff.mpr ⟨nonzero, UInt64.toNat_div _ _⟩
  have productOk := mulChecked_of_lt (a := amount.toUInt64 / preset.SLOTS_PER_EPOCH)
    (b := config.PROPOSER_SCORE_BOOST) (by
      simpa only [UInt64.toNat_div, UInt64.toNat_ofNat_of_lt' amountFits] using productFits)
  refine ⟨((amount.toUInt64 / preset.SLOTS_PER_EPOCH) * config.PROPOSER_SCORE_BOOST) / 100,
    ?_, ?_⟩
  · unfold computeProposerScore calculateCommitteeFraction
    simp only [bind_ok_iff, mapError_ok_iff, pure, Except.pure, Except.ok.injEq]
    exact ⟨_, totalOk, _, committeeOk, _, productOk, rfl⟩
  · rw [UInt64.toNat_div, UInt64.toNat_mul, UInt64.toNat_div,
      UInt64.toNat_ofNat_of_lt' amountFits, Nat.mod_eq_of_lt productFits]
    exact (Nat.div_le_div_right (Nat.mul_le_mul_left _ boost)).trans
      (by simpa using (Nat.div_le_self amount preset.SLOTS_PER_EPOCH.toNat).trans amountLe)

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J}

/-- A store replaces the anchor justification only with a strictly later checkpoint. -/
private theorem justifiedRoot_fields_after_anchor {anchor store : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (reached : Store.Reachable config anchorState anchorBlock store) :
    (store.justifiedCheckpoint = anchor.justifiedCheckpoint ∨
      anchor.justifiedCheckpoint.epoch < store.justifiedCheckpoint.epoch) ∧
    (store.unrealizedJustifiedCheckpoint = anchor.justifiedCheckpoint ∨
      anchor.justifiedCheckpoint.epoch < store.unrealizedJustifiedCheckpoint.epoch) := by
  let P := fun (c : Checkpoint) => c = anchor.justifiedCheckpoint ∨
    anchor.justifiedCheckpoint.epoch < c.epoch
  have newer {c j : Checkpoint} (old : P c) (gt : c.epoch < j.epoch) : P j := by
    rcases old with rfl | lt
    · exact .inr gt
    · exact .inr (UInt64.lt_trans lt gt)
  have update (s : Store preset fork) (j f : Checkpoint)
      (old : P s.justifiedCheckpoint ∧ P s.unrealizedJustifiedCheckpoint) :
      P (s.updateCheckpoints j f).justifiedCheckpoint ∧
        P (s.updateCheckpoints j f).unrealizedJustifiedCheckpoint := by
    unfold Store.updateCheckpoints
    split <;> dsimp only <;> split
    all_goals exact ⟨by first | exact newer old.1 ‹_› | exact old.1, old.2⟩
  have updateUn (s : Store preset fork) (j f : Checkpoint)
      (old : P s.justifiedCheckpoint ∧ P s.unrealizedJustifiedCheckpoint) :
      P (s.updateUnrealizedCheckpoints j f).justifiedCheckpoint ∧
        P (s.updateUnrealizedCheckpoints j f).unrealizedJustifiedCheckpoint := by
    unfold Store.updateUnrealizedCheckpoints
    split <;> dsimp only <;> split
    all_goals exact ⟨old.1, by first | exact newer old.2 ‹_› | exact old.2⟩
  have pull {s t : Store preset fork} {root : Root}
      (old : P s.justifiedCheckpoint ∧ P s.unrealizedJustifiedCheckpoint)
      (computed : s.computePulledUpTip config root = .ok t) :
      P t.justifiedCheckpoint ∧ P t.unrealizedJustifiedCheckpoint := by
    unfold Store.computePulledUpTip at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, p, _, _, _, _, _, computed⟩ := computed
    have pending := updateUn {s with unrealizedJustifications :=
      s.unrealizedJustifications.insert root p.currentJustifiedCheckpoint}
      p.currentJustifiedCheckpoint p.finalizedCheckpoint old
    split at computed <;> cases Except.ok.inj computed
    · exact update _ _ _ pending
    · exact pending
  change P store.justifiedCheckpoint ∧ P store.unrealizedJustifiedCheckpoint
  induction reached with
  | anchor made =>
    have eq := Except.ok.inj (anchored.symm.trans made)
    subst eq
    obtain ⟨_, _, _, _, justified, _, pending, _⟩ := getForkchoiceStore_anchor made
    exact ⟨.inl rfl, .inl (pending.trans justified.symm)⟩
  | block _ added ih =>
    unfold Store.onBlock at added
    simp only [bind_ok_iff] at added
    obtain ⟨_, _, added⟩ := added
    split at added
    · cases added
      exact ih
    · unfold Store.addBlock at added
      simp only [bind_ok_iff] at added
      obtain ⟨state, _, _, _, _, vote, recorded, record, boosted, boost, added⟩ := added
      obtain ⟨_, _, rfl⟩ := Store.recordBlockPtcVotes_onlyPtcVotes vote
      have kept : P recorded.justifiedCheckpoint ∧ P recorded.unrealizedJustifiedCheckpoint := by
        unfold Store.recordBlockTimeliness at record
        simp only [bind_ok_iff, pure, Except.pure] at record
        obtain ⟨_, _, _, _, _, _, _, _, record⟩ := record
        split at record
        · simp only [bind_ok_iff, Except.ok.injEq] at record
          obtain ⟨_, _, rfl⟩ := record
          exact ih
        · cases record
          exact ih
      have boostedKept : P boosted.justifiedCheckpoint ∧
          P boosted.unrealizedJustifiedCheckpoint := by
        unfold Store.updateProposerBoostRoot at boost
        split at boost
        rotate_left
        · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at boost
        simp only [bind_ok_iff, pure_bind] at boost
        obtain ⟨_, _, _, _, _, _, boost⟩ := boost
        split at boost <;> cases Except.ok.inj boost <;> exact kept
      exact pull (update _ state.currentJustifiedCheckpoint state.finalizedCheckpoint boostedKept)
        added
  | tick _ ticked ih =>
    exact Store.justified_properties_of_onTick P ih.1 ih.2 ticked
  | attestation _ attested ih =>
    unfold Store.onAttestation at attested
    simp only [bind_ok_iff] at attested
    obtain ⟨_, _, stored, storing, _, _, _, _, _, _, _, _, attested⟩ := attested
    have kept : P stored.justifiedCheckpoint ∧ P stored.unrealizedJustifiedCheckpoint := by
      unfold Store.storeTargetCheckpointState at storing
      split at storing
      · cases Except.ok.inj storing
        exact ih
      · simp only [bind_ok_iff] at storing
        obtain ⟨_, _, storing⟩ := storing
        cases Except.ok.inj storing
        exact ih
    split at attested
    · cases Except.ok.inj attested
      exact kept
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested
  | attesterSlashing _ slashed ih =>
    unfold Store.onAttesterSlashing at slashed
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at slashed
    obtain ⟨_, _, rfl⟩ := slashed
    exact ih
  | payloadAttestation _ voted ih =>
    obtain ⟨_, _, rfl⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes voted
    exact ih
  | envelope _ accepted ih =>
    obtain ⟨_, _, _, _, _, record, rfl⟩ := Store.onExecutionPayloadEnvelope_ok accepted
    obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
    exact ih
  | inclusionList _ accepted ih =>
    obtain ⟨_, _, rfl⟩ := Store.onInclusionList_ok _ accepted
    exact ih

/-- An honest store holds the block of its justified checkpoint, up to a last time.

The checkpoint is the anchor's, or the root that a held state records for its epoch.

That root is the root of a held block, the latest of that chain at or before the first slot.

A nonzero state root fills the header of each held block only once. -/
theorem Execution.justifiedRoot_known {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (start : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (preGloas : fork < .glamsterdam) {limit : ℕ}
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit) :
    ∃ block, ((e.world k).state w).blocks[((e.world k).state w).justifiedCheckpoint.root]? =
      some block := by
  have reached := e.reachable
    (fun u hu => (start u hu).symm ▸ Store.Reachable.anchor anchored) k w honest
  obtain ⟨anchorRoot, hashed, _, _, justified, _⟩ := getForkchoiceStore_anchor anchored
  rcases (justifiedRoot_fields_after_anchor anchored reached).1 with same | later
  · obtain ⟨root, rootOk, held⟩ := reached.anchor_known
    rw [hashed, Except.ok.injEq] at rootOk
    subst root
    exact ⟨anchorBlock, by simpa only [same, justified] using held⟩
  have recent : getCurrentEpoch anchorState <
      ((e.world k).state w).justifiedCheckpoint.epoch := by
    simpa only [justified] using later
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by
    by_contra absent
    have zero : preset.SLOTS_PER_EPOCH = 0 := UInt64.toNat_inj.mp (by
      change preset.SLOTS_PER_EPOCH.toNat = 0
      omega)
    have epochs (s : BeaconState preset fork) : getCurrentEpoch s = 0 := by
      simp [getCurrentEpoch, computeEpochAtSlot, zero]
    rw [epochs] at recent
    rcases reached.justified_origins _ (.inl rfl) with
      ⟨r, _, eq⟩ | ⟨r, s, held, eq⟩ | ⟨r, s, p, held, pulled, eq⟩
    · simp [eq, epochs] at recent
    · have bound := UInt64.le_trans ((reached.ordered sound).2 held).settled
        (getPreviousEpoch_le s)
      rw [epochs, ← eq] at bound
      exact UInt64.not_le.mpr recent bound
    · have invariant := (reached.ordered sound).2 held
      have bound := (processJustificationAndFinalization_invariant invariant.ordered
        invariant.settled pulled).2.2.1
      rw [epochs, ← eq] at bound
      exact UInt64.not_le.mpr recent bound
  have child : ∃ (r : Root) (b : BeaconBlock preset fork),
      ((e.world k).state w).blocks[r]? = some b ∧ b ≠ anchorBlock := by
    by_contra absent
    have allAnchor {r : Root} {s : BeaconState preset fork}
        (held : ((e.world k).state w).blockStates[r]? = some s) : s = anchorState := by
      obtain ⟨b, known⟩ := reached.known_of_blockState held
      have same : b = anchorBlock := by
        by_contra other
        exact absent ⟨r, b, known, other⟩
      obtain ⟨post, found, anchored, _⟩ := reached.blockStatesFromParents known
      rw [held, Option.some.injEq] at found
      subst post
      exact anchored same
    have upper : ((e.world k).state w).justifiedCheckpoint.epoch ≤
        getCurrentEpoch anchorState := by
      rcases reached.justified_origins _ (.inl rfl) with
        ⟨r, _, eq⟩ | ⟨r, s, held, eq⟩ | ⟨r, s, p, held, pulled, eq⟩
      · exact eq ▸ UInt64.le_refl _
      · rw [eq, allAnchor held]
        exact UInt64.le_trans sound.settled (getPreviousEpoch_le _)
      · rw [allAnchor held] at pulled
        rw [eq]
        exact (processJustificationAndFinalization_invariant sound.ordered sound.settled
          pulled).2.2.1
    exact UInt64.not_le.mpr recent upper
  rcases reached.justified_origins _ (.inl rfl) with
    ⟨root, _, same⟩ | ⟨root, state, held, same⟩ |
    ⟨root, state, pulled, held, run, same⟩
  · rw [same] at recent
    exact (UInt64.lt_irrefl _ recent).elim
  · have roots := walk_checkpoint_ancestor reached sound preGloas positive window
      (UInt64.le_of_eq anchorSlot) (nonzero w honest k bounded) child held
    rcases roots.2.1 with old | ⟨_, _, _, _, _, _, read⟩
    · exact (UInt64.not_le.mpr recent (same ▸ old)).elim
    · obtain ⟨_, block, _, found, _⟩ := Store.isAncestor_of_getCheckpointBlock preGloas read
      exact ⟨block, same ▸ found⟩
  · have roots := walk_pulled_checkpoint_ancestor reached sound preGloas positive window
      (UInt64.le_of_eq anchorSlot) (nonzero w honest k bounded) child held run
    rcases roots.2.1 with old | ⟨_, _, _, _, _, _, read⟩
    · exact (UInt64.not_le.mpr recent (same ▸ old)).elim
    · obtain ⟨_, block, _, found, _⟩ := Store.isAncestor_of_getCheckpointBlock preGloas read
      exact ⟨block, same ▸ found⟩

/-- An honest store caches the state of its justified checkpoint, and can count with it.

The anchor's checkpoint is cached when the store is built.

A later justified checkpoint has an epoch above the anchor's, so a vote of a held block targets it.

The store imported that block with its votes, and each vote cached the state of its target.

The state is that of the checkpoint block, or its slots up to a held child, so the store counts
with it.

A positive increment makes the count of a justified checkpoint positive. -/
theorem Execution.exists_justified_checkpointState {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (start : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (preGloas : fork < .glamsterdam) (positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    {limit : ℕ}
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit) :
    ∃ state, ((e.world k).state w).checkpointState
        ((e.world k).state w).justifiedCheckpoint = .ok state ∧
      ((e.world k).state w).Counts config state := by
  sorry

private theorem p2_exists_getAncestor {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (aligned : anchorBlock.slot ≤ anchorState.slot)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    (preGloas : fork < .glamsterdam) {root : Root} {block : BeaconBlock preset fork}
    (known : store.blocks[root]? = some block) {slot : Slot}
    (above : anchorBlock.slot ≤ slot) :
    ∃ ancestor, store.getAncestor ⟨root, .pending⟩ slot = .ok ancestor := by
  by_cases below : block.slot ≤ slot
  · exact ⟨_, Store.getAncestor_of_le known below⟩
  · have different : block ≠ anchorBlock := by
      rintro rfl
      exact below above
    obtain ⟨_, _, _, produced⟩ := reachable.blockStatesFromParents known
    obtain ⟨_, _, _, _, _, parentState, _⟩ := produced different
    obtain ⟨parent, parentKnown⟩ := reachable.known_of_blockState parentState
    have lower := reachable.parentsBelow aligned unknown root block parent known parentKnown
    -- Strictly descending slots make this recursive walk finite.
    obtain ⟨ancestor, walked⟩ := p2_exists_getAncestor reachable aligned unknown preGloas
      parentKnown above
    refine ⟨ancestor, ?_⟩
    rw [Store.getAncestor_step known below parentKnown lower,
      Store.parentPayloadStatus_of_lt preGloas]
    exact walked
termination_by block.slot.toNat
decreasing_by exact UInt64.lt_iff_toNat_lt.mp lower

/-- An honest store reads whether one held block descends from another.

The walk goes down the parents of the first block while they are above the second one's slot.

Each parent is held and at a lower slot, and the anchor's parent is not held. -/
theorem Execution.exists_isAncestor_of_held {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (preGloas : fork < .glamsterdam) {limit : ℕ}
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit)
    {root ancestor : Root} {block ancestorBlock : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some block)
    (ancestorKnown : ((e.world k).state w).blocks[ancestor]? = some ancestorBlock) :
    ∃ result, ((e.world k).state w).isAncestor ⟨root, .pending⟩ ⟨ancestor, .pending⟩ =
      .ok result := by
  have reachable := e.reachable
    (fun v member => (start v member).symm ▸ Store.Reachable.anchor anchored) k w honest
  have aligned : anchorBlock.slot ≤ anchorState.slot := anchorSlot ▸ UInt64.le_refl _
  -- A non-anchor block follows a transition from a state at or after the anchor.
  have above : anchorBlock.slot ≤ ancestorBlock.slot := by
    by_cases same : ancestorBlock = anchorBlock
    · exact same ▸ UInt64.le_refl _
    · obtain ⟨_, _, _, produced⟩ := reachable.blockStatesFromParents ancestorKnown
      obtain ⟨_, _, _, signed, message, parentState, transitioned⟩ := produced same
      have afterAnchor := reachable.anchorSlot_le_blockState parentState
      have later := (stateTransition_slot transitioned).1
      rw [message] at later
      exact UInt64.le_trans aligned (UInt64.le_trans afterAnchor (UInt64.le_of_lt later))
  obtain ⟨found, walked⟩ := p2_exists_getAncestor reachable aligned
    (anchorParent w honest k bounded) preGloas known above
  have before : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
  refine ⟨found == ⟨ancestor, .pending⟩, ?_⟩
  simp [Store.isAncestor, Store.block_ok_iff.mpr ancestorKnown, walked,
    before, bind, Except.bind, pure, Except.pure]

/-- An honest store reads the checkpoint block of a held block at an epoch after the anchor's slot.

The walk stops at the first slot of the epoch, at or above the anchor. -/
theorem Execution.exists_getCheckpointBlock_of_held {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (preGloas : fork < .glamsterdam) {limit : ℕ}
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit)
    {root : Root} {block : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some block)
    {epoch : Epoch} {first : Slot} (firstOk : computeStartSlotAtEpoch preset epoch = .ok first)
    (above : anchorBlock.slot ≤ first) :
    ∃ checkpointRoot, ((e.world k).state w).getCheckpointBlock root epoch = .ok checkpointRoot := by
  have reachable := e.reachable
    (fun v member => (start v member).symm ▸ Store.Reachable.anchor anchored) k w honest
  have aligned : anchorBlock.slot ≤ anchorState.slot := anchorSlot ▸ UInt64.le_refl _
  obtain ⟨ancestor, walked⟩ := p2_exists_getAncestor reachable aligned
    (anchorParent w honest k bounded) preGloas known above
  exact ⟨ancestor.root, by
    simp [Store.getCheckpointBlock, firstOk, walked, Except.mapError,
      bind, Except.bind, pure, Except.pure]⟩

private theorem p6_update_cache (store : Store preset fork) (j f : Checkpoint) :
    (store.updateCheckpoints j f).unrealizedJustifications = store.unrealizedJustifications ∧
      (store.updateUnrealizedCheckpoints j f).unrealizedJustifications =
        store.unrealizedJustifications := by
  constructor
  · unfold Store.updateCheckpoints
    split <;> dsimp only <;> split <;> rfl
  · unfold Store.updateUnrealizedCheckpoints
    split <;> dsimp only <;> split <;> rfl

private theorem p6_tick_cache {store after : Store preset fork} {time : UInt64}
    (ticked : store.onTick config time = .ok after) :
    after.unrealizedJustifications = store.unrealizedJustifications := by
  have step : ∀ {store after : Store preset fork} {time : UInt64},
      store.onTickPerSlot config time = .ok after →
      after.unrealizedJustifications = store.unrealizedJustifications := by
    intro store after time ticked
    unfold Store.onTickPerSlot at ticked
    simp only [bind_ok_iff] at ticked
    obtain ⟨previous, _, current, _, ticked⟩ := ticked
    split at ticked <;>
      · obtain ⟨_, _, ticked⟩ := ticked
        split at ticked <;> simp only [pure, Except.pure, Except.ok.injEq] at ticked <;>
          subst after <;> try rfl
        exact (p6_update_cache _ _ _).1
  have catchup : ∀ {start after : Store preset fork} {slot : Slot},
      Store.catchUp config start slot = .ok after →
      after.unrealizedJustifications = start.unrealizedJustifications := by
    intro start after slot caught
    induction start using Store.catchUp.induct config slot with
    | _ start ih =>
      rw [Store.catchUp.eq_1] at caught
      simp only [bind_ok_iff] at caught
      obtain ⟨current, _, caught⟩ := caught
      split at caught
      · simp only [bind_ok_iff] at caught
        obtain ⟨next, _, nextTime, _, ticked, tick, caught⟩ := caught
        split at caught
        · exact (ih ticked ‹_› caught).trans (step tick)
        · cases caught
      · cases Except.ok.inj caught
        rfl
  unfold Store.onTick at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨slot, _, caught, caughtOk, ticked⟩ := ticked
  exact (step ticked).trans (catchup caughtOk)

private theorem p6_attestation_cache {store after : Store preset fork}
    {attestation : Attestation preset fork} {fromBlock : Bool}
    (attested : store.onAttestation config checks attestation fromBlock = .ok after) :
    after.unrealizedJustifications = store.unrealizedJustifications := by
  unfold Store.onAttestation at attested
  simp only [bind_ok_iff] at attested
  obtain ⟨_, _, cached, caching, _, _, _, _, _, _, _, _, attested⟩ := attested
  have kept : cached.unrealizedJustifications = store.unrealizedJustifications := by
    unfold Store.storeTargetCheckpointState at caching
    split at caching
    · cases Except.ok.inj caching
      rfl
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at caching
      obtain ⟨_, _, rfl⟩ := caching
      rfl
  split at attested
  · cases Except.ok.inj attested
    exact kept
  · cases attested

private theorem p6_pulled_cache {store after : Store preset fork} {root : Root}
    (computed : store.computePulledUpTip config root = .ok after) :
    ∃ state pulled, store.blockStates[root]? = some state ∧
      processJustificationAndFinalization state = .ok pulled ∧
      after.unrealizedJustifications =
        store.unrealizedJustifications.insert root pulled.currentJustifiedCheckpoint := by
  unfold Store.computePulledUpTip at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨state, found, pulled, processed, block, _, epoch, _, computed⟩ := computed
  refine ⟨state, pulled, Store.blockState_ok_iff.mp found, mapError_ok_iff.mp processed, ?_⟩
  split at computed <;> simp only [pure, Except.pure, Except.ok.injEq] at computed <;>
    subst after
  · rw [(p6_update_cache _ _ _).1, (p6_update_cache _ _ _).2]
  · exact (p6_update_cache _ _ _).2

private theorem p6_block_cache {store after : Store preset fork}
    {signed : SignedBeaconBlock preset fork}
    (added : store.onBlock config checks sources signed = .ok after) :
    after = store ∨ ∃ root state pulled,
      store.blocks[root]? = none ∧
      after.blocks = store.blocks.insert root signed.message ∧
      after.blockStates[root]? = some state ∧ state.slot = signed.message.slot ∧
      processJustificationAndFinalization state = .ok pulled ∧
      after.unrealizedJustifications =
        store.unrealizedJustifications.insert root pulled.currentJustifiedCheckpoint := by
  rcases Store.onBlock_same_or_insert added with same |
    ⟨root, hashed, fresh, blocks, pre, post, _, transitioned, states⟩
  · exact .inl same
  right
  have unknown : ¬ store.blocks.contains root := by
    simp [Std.TreeMap.contains_eq_isSome_getElem?, fresh]
  simp only [Store.onBlock, hashed, unknown, bind, Except.bind, Except.mapError,
    ↓reduceIte, Bool.false_eq_true] at added
  unfold Store.addBlock at added
  simp only [bind_ok_iff] at added
  obtain ⟨state, _, head, _, voted, vote, recorded, record, boosted, boost, added⟩ := added
  obtain ⟨_, _, rfl⟩ := Store.recordBlockPtcVotes_onlyPtcVotes vote
  have recordedCache : recorded.unrealizedJustifications = store.unrealizedJustifications := by
    unfold Store.recordBlockTimeliness at record
    simp only [bind_ok_iff, pure, Except.pure] at record
    obtain ⟨_, _, _, _, _, _, _, _, record⟩ := record
    split at record
    · simp only [bind_ok_iff, Except.ok.injEq] at record
      obtain ⟨_, _, rfl⟩ := record
      rfl
    · cases record
      rfl
  have boostedCache : boosted.unrealizedJustifications = store.unrealizedJustifications := by
    unfold Store.updateProposerBoostRoot at boost
    split at boost
    rotate_left
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at boost
    simp only [bind_ok_iff, pure_bind] at boost
    obtain ⟨_, _, _, _, _, _, boost⟩ := boost
    split at boost <;> simp only [pure, Except.pure, Except.ok.injEq] at boost <;>
      subst boosted <;> exact recordedCache
  obtain ⟨cached, pulled, held, run, cache⟩ := p6_pulled_cache added
  have heldAfter : after.blockStates[root]? = some cached := by
    rwa [(Store.computePulledUpTip_frame added).2.2.1]
  have postHeld : after.blockStates[root]? = some post := by
    rw [states, getElem?_insert_root]
    simp
  have same : cached = post := Option.some.inj (heldAfter.symm.trans postHeld)
  refine ⟨root, cached, pulled, fresh, blocks, heldAfter, ?_, run, ?_⟩
  · rw [same]
    exact (stateTransition_slot transitioned).2
  · rw [(p6_update_cache _ _ _).1, boostedCache] at cache
    exact cache

private theorem p6_cache_of_held {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (preGloas : fork < .glamsterdam) :
    ∀ {root : Root} {block : BeaconBlock preset fork}, store.blocks[root]? = some block →
      ∃ checkpoint, store.unrealizedJustifications[root]? = some checkpoint ∧
        checkpoint.epoch ≤ computeEpochAtSlot preset block.slot := by
  induction reachable with
  | anchor made =>
    unfold getForkchoiceStore at made
    simp only [bind_ok_iff] at made
    obtain ⟨stateRoot, _, made⟩ := made
    split at made
    · cases made
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at made
      obtain ⟨root, _, time, _, rfl⟩ := made
      intro key block found
      rw [getElem?_insert_root] at found
      split at found
      · cases Option.some.inj found
        refine ⟨⟨getCurrentEpoch anchorState, root⟩, ?_, ?_⟩
        · rw [getElem?_insert_root]
          simp [‹root = key›]
        · rw [anchorSlot]
          exact UInt64.le_refl _
      · simp at found
  | tick prior ticked ih =>
    intro root block held
    rw [(Store.onTick_frame ticked).2.2.1] at held
    rw [p6_tick_cache ticked]
    exact ih held
  | @block before after c s signed prior added ih =>
    rcases p6_block_cache added with rfl |
      ⟨root, state, pulled, fresh, blocks, held, atSlot, run, cache⟩
    · exact ih
    intro key block found
    rw [blocks, getElem?_insert_root] at found
    rw [cache, getElem?_insert_root]
    by_cases same : root = key
    · simp only [same, ↓reduceIte, Option.some.injEq] at found
      subst block
      refine ⟨pulled.currentJustifiedCheckpoint, by simp [same], ?_⟩
      have inv := ((prior.block added).ordered sound).2 held
      have bound :=
        (processJustificationAndFinalization_invariant inv.ordered inv.settled run).2.2.1
      simpa only [getCurrentEpoch, atSlot] using bound
    · simp only [same, ↓reduceIte] at found ⊢
      exact ih found
  | attestation prior attested ih =>
    intro root block held
    rw [(Store.onAttestation_frame attested).2.1] at held
    rw [p6_attestation_cache attested]
    exact ih held
  | attesterSlashing prior slashed ih =>
    unfold Store.onAttesterSlashing at slashed
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at slashed
    obtain ⟨_, _, rfl⟩ := slashed
    exact ih
  | payloadAttestation => exact False.elim (Nat.not_le_of_lt preGloas ‹.glamsterdam ≤ fork›)
  | envelope => exact False.elim (Nat.not_le_of_lt preGloas ‹.glamsterdam ≤ fork›)
  | inclusionList =>
    exact False.elim (Nat.not_le_of_lt preGloas
      (Nat.le_trans (by decide : Fork.glamsterdam ≤ Fork.hegota) ‹.hegota ≤ fork›))

/-- An honest store reads its filtered block tree, up to a last time.

Each leaf has a voting source, from the state or the unrealized justification of its block.

The source epoch is at most the current epoch, which two more epochs leave within 64 bits.

Each leaf reads its checkpoint block at the finalized epoch, at or above the anchor. -/
theorem Execution.exists_getFilteredNodeTree {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (start : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (slots : 0 < config.SLOT_DURATION_MS) (long : 1 < preset.SLOTS_PER_EPOCH)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (preGloas : fork < .glamsterdam) {limit : ℕ}
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit) :
    ∃ nodes, ((e.world k).state w).getFilteredNodeTree config = .ok nodes := by
  classical
  let store := (e.world k).state w
  have forward : Store.ForwardReachable config anchorState anchorBlock store :=
    e.forwardReachable (fun v hv => (start v hv) ▸ .anchor anchored) k w honest
  have reachable := forward.reachable
  obtain ⟨current, currentOk, blockBound, stateBound⟩ :=
    forward.slots_le_current slots (UInt64.le_of_eq anchorSlot)
  let epoch := computeEpochAtSlot preset current
  have epochOk : store.getCurrentStoreEpoch config = .ok epoch := by
    simp [Store.getCurrentStoreEpoch, currentOk, epoch, bind, Except.bind, pure, Except.pure]
  have source : ∀ {root : Root} {block : BeaconBlock preset fork},
      store.blocks[root]? = some block →
      ∃ checkpoint, store.getVotingSource config root = .ok checkpoint ∧
        checkpoint.epoch ≤ epoch := by
    intro root block held
    have blockEpoch : computeEpochAtSlot preset block.slot ≤ epoch := by
      exact UInt64.le_iff_toNat_le.mpr
        (Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp (blockBound root block held)))
    obtain ⟨state, stateOk, _, _⟩ := reachable.blockStatesFromParents held
    by_cases earlier : computeEpochAtSlot preset block.slot < epoch
    · obtain ⟨checkpoint, cached, bound⟩ :=
        p6_cache_of_held reachable sound anchorSlot preGloas held
      refine ⟨checkpoint, ?_, UInt64.le_trans bound blockEpoch⟩
      simp [Store.getVotingSource, Store.block, held, epochOk, earlier, cached,
        bind, Except.bind, pure, Except.pure]
    · refine ⟨state.currentJustifiedCheckpoint, ?_, ?_⟩
      · simp [Store.getVotingSource, Store.block, held, epochOk, earlier, stateOk,
          bind, Except.bind, pure, Except.pure]
      · exact UInt64.le_trans
          (UInt64.le_trans ((reachable.ordered sound).2 stateOk).settled (getPreviousEpoch_le _))
          (UInt64.le_iff_toNat_le.mpr
            (Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp (stateBound root state stateOk))))
  have finalizedLe : store.finalizedCheckpoint.epoch ≤ epoch :=
    UInt64.le_trans (reachable.ordered sound).1.1
      (forward.justified_epoch_le_current sound slots (UInt64.le_of_eq anchorSlot) epochOk).1
  have fits : store.finalizedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat <
      2 ^ 64 := by
    have le := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat
      (UInt64.le_iff_toNat_le.mp finalizedLe)
    exact Nat.lt_of_le_of_lt (le.trans (Nat.div_mul_le_self _ _)) current.toNat_lt
  let boundary := store.finalizedCheckpoint.epoch * preset.SLOTS_PER_EPOCH
  have boundaryOk : computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch =
      .ok boundary := by
    exact computeStartSlotAtEpoch_ok_iff.mpr ⟨fits,
      by simp only [boundary, UInt64.toNat_mul, Nat.mod_eq_of_lt fits]⟩
  have above : anchorBlock.slot ≤ boundary :=
    e.anchorSlot_le_finalized_boundary anchored anchorSlot anchorAtBoundary
      (start w honest) boundaryOk
  have viable : ∀ {root : Root} {block : BeaconBlock preset fork},
      store.blocks[root]? = some block → ∃ result,
        store.isViableLeaf config ⟨root, .pending⟩ = .ok result := by
    intro root block held
    obtain ⟨checkpoint, sourceOk, sourceLe⟩ := source held
    obtain ⟨finalizedRoot, finalizedOk⟩ := e.exists_getCheckpointBlock_of_held anchored start
      anchorSlot preGloas anchorParent honest bounded held boundaryOk above
    change store.getCheckpointBlock root store.finalizedCheckpoint.epoch = .ok finalizedRoot
      at finalizedOk
    have nextFits : checkpoint.epoch.toNat + 2 < 2 ^ 64 := by
      have sourceNat := UInt64.le_iff_toNat_le.mp sourceLe
      have longNat : 2 ≤ preset.SLOTS_PER_EPOCH.toNat := by
        have := UInt64.lt_iff_toNat_lt.mp long
        change 1 < preset.SLOTS_PER_EPOCH.toNat at this
        omega
      have half := Nat.div_le_div_left (a := current.toNat) longNat (by decide)
      have currentFits := current.toNat_lt
      change checkpoint.epoch.toNat ≤ current.toNat / preset.SLOTS_PER_EPOCH.toNat at sourceNat
      omega
    have nextOk := addChecked_of_lt (a := checkpoint.epoch) (b := 2) nextFits
    unfold Store.isViableLeaf
    rw [epochOk, sourceOk]
    simp only [bind, Except.bind]
    split
    · simp only [pure, Except.pure, finalizedOk]
      exact ⟨_, rfl⟩
    · simp only [nextOk, Except.mapError, pure, Except.pure, finalizedOk]
      exact ⟨_, rfl⟩
  have parents := reachable.parentsBelow (UInt64.le_of_eq anchorSlot)
    (anchorParent w honest k bounded)
  have walk : ∀ (node : ForkChoiceNode) (block : BeaconBlock preset fork),
      node.payloadStatus = .pending → store.blocks[node.root]? = some block →
      ∃ nodes, store.filterNodeTree config node = .ok nodes := by
    intro node
    induction rank : store.nodeRank node using Nat.strong_induction_on generalizing node with
    | _ n ih =>
      intro block pending held
      have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
      let children := (store.blocks.toList.filter fun (_, b) => b.parentRoot = node.root).map
        fun (r, _) => (⟨r, .pending⟩ : ForkChoiceNode)
      have childrenOk : store.getNodeChildren node = .ok children := by
        simp [Store.getNodeChildren, later, children, pure, Except.pure]
      rw [Store.filterNodeTree, childrenOk]
      simp only [bind, Except.bind]
      split
      · obtain ⟨result, resultOk⟩ := viable held
        have same : node = ⟨node.root, .pending⟩ := by cases node; simp_all
        rw [← same] at resultOk
        simp only [resultOk, pure, Except.pure]
        exact ⟨_, rfl⟩
      · have each : ∀ child ∈ children, ∃ below,
            (if store.nodeRank child < store.nodeRank node then
              store.filterNodeTree config child else
              throw (.parentSlotNotLower child.root)) = .ok below := by
          intro child member
          obtain ⟨childPending, childBlock, childHeld, parent⟩ :=
            (Store.mem_getNodeChildren preGloas childrenOk).mp member
          have lowerSlot := parents _ _ _ childHeld (parent ▸ held)
          have lower : store.nodeRank child < store.nodeRank node := by
            simp only [Store.nodeRank, held, childHeld, pending, childPending, ↓reduceIte]
            have := UInt64.lt_iff_toNat_lt.mp lowerSlot
            have := block.slot.toNat_lt
            have := childBlock.slot.toNat_lt
            omega
          obtain ⟨below, belowOk⟩ := ih _ (rank ▸ lower) child rfl childBlock childPending childHeld
          exact ⟨below, by simp [lower, belowOk]⟩
        have flat : ∀ xs : List ForkChoiceNode,
            (∀ child ∈ xs, ∃ below,
              (if store.nodeRank child < store.nodeRank node then
                store.filterNodeTree config child else
                throw (.parentSlotNotLower child.root)) = .ok below) →
            ∃ below, xs.flatMapM (fun child =>
              if store.nodeRank child < store.nodeRank node then
                store.filterNodeTree config child else
                throw (.parentSlotNotLower child.root)) = .ok below := by
          intro xs all
          induction xs with
          | nil => exact ⟨[], rfl⟩
          | cons x xs ih =>
            obtain ⟨first, firstOk⟩ := all x (by simp)
            obtain ⟨rest, restOk⟩ := ih (fun x hx => all x (by simp [hx]))
            exact ⟨first ++ rest, by
              rw [List.flatMapM_cons, firstOk]
              simp [restOk, bind, Except.bind, pure, Except.pure]⟩
        obtain ⟨below, belowOk⟩ := flat children each
        simp only [dite_eq_ite]
        rw [belowOk]
        exact ⟨_, rfl⟩
  obtain ⟨justified, justifiedOk⟩ := e.justifiedRoot_known anchored sound start anchorSlot
    anchorAtBoundary window preGloas nonzero honest bounded
  exact walk _ justified rfl justifiedOk

/-- An honest store counts the latest votes for a held block in a state with capped stake.

Before Gloas each vote supports the pending node of its block, which the store holds.

The sum is that of active validators, so it stays within the cap. -/
theorem Execution.exists_scoreFromTally {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (preGloas : fork < .glamsterdam) {limit : ℕ}
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit)
    {state : BeaconState preset fork} (stakeLe : ActiveStakeAtMost stakeCapGwei state)
    {root : Root} {block : BeaconBlock preset fork}
    (known : ((e.world k).state w).blocks[root]? = some block) :
    ∃ score, ((e.world k).state w).scoreFromTally (((e.world k).state w).tallyVotes state)
      ⟨root, .pending⟩ = .ok score ∧ score.toNat ≤ stakeCapGwei := by
  sorry

/-- The store of an honest validator computes a head at each event up to a last time.

The justified checkpoint state is cached and counts, so its active stake is at most the cap.

The bound on counting states then puts one increment below the cap too.

The filtered tree, each tally and the boost are then read, and each weight fits in 64 bits.

The boosted block, when there is one, is held. -/
theorem Execution.exists_getHead {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (start : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (slots : 0 < config.SLOT_DURATION_MS) (long : 1 < preset.SLOTS_PER_EPOCH)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (preGloas : fork < .glamsterdam) (positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    (boost : config.PROPOSER_SCORE_BOOST.toNat ≤ 100) {limit : ℕ} {horizon : Epoch}
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).Counts config state →
      getCurrentEpoch state ≤ horizon →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (supply : ∀ w ∈ J, ∀ k (checkpoint : Checkpoint) (state : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).checkpointState checkpoint = .ok state →
      ActiveStakeAtMost stakeCapGwei state)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit) :
    ∃ head, ((e.world k).state w).getHead config = .ok head := by
  sorry

end EthLib.Consensus.Models.Network
