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
  sorry

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

/-- Block attestations supply target provenance without comparing their committees. -/
private theorem justifiedState_flags_block {anchorEpoch : Epoch}
    {votes : Set (ValidatorIndex × AttestationData)} {state after : BeaconState preset fork}
    {block : BeaconBlock preset fork}
    (holds : CountedFlags anchorEpoch votes state)
    (computed : processBlock config checks sources.engine state block = .ok after)
    (cached : ∀ a ∈ block.body.attestations.data, ∀ v, (v, a.data) ∈ votes) :
    CountedFlags anchorEpoch votes after := by
  have frame {s t : BeaconState preset fork} (old : CountedFlags anchorEpoch votes s)
      (kept : BlockFrame s t) : CountedFlags anchorEpoch votes t :=
    countedFlags_voteFrame old (VoteFrame.of_blockFrame kept)
      (fun _ absent _ _ => absent.elim)
  obtain ⟨first, last, head, operations, tail⟩ := processBlock_split computed
  obtain ⟨before, done, leading, attestations, trailing⟩ := processOperations_split operations
  apply frame (kept := tail)
  apply frame (kept := trailing)
  have each : ∀ (xs : List (Attestation preset fork)) s t,
      CountedFlags anchorEpoch votes s →
      (∀ a ∈ xs, ∀ v, (v, a.data) ∈ votes) →
      xs.foldlM (processAttestation config checks · state.latestBlockHeader.slot ·) s = .ok t →
      CountedFlags anchorEpoch votes t := by
    intro xs
    induction xs with
    | nil =>
      intro s t old _ ran
      cases Except.ok.inj ran
      exact old
    | cons a xs ih =>
      intro s t old all ran
      simp only [List.foldlM_cons, bind_ok_iff] at ran
      obtain ⟨middle, processed, rest⟩ := ran
      apply ih middle t ?_ (fun item member => all item (by simp [member])) rest
      apply countedFlags_voteFrame old (voteFrame_processAttestation processed)
      intro vote member _ _
      obtain ⟨same, _⟩ := member
      rcases vote with ⟨v, data⟩
      dsimp only at same
      subst data
      exact all a (by simp) v
  exact each _ _ _ (frame (frame holds head) leading)
    (fun a member => cached a (Array.mem_toList_iff.mp member)) attestations

/-- Flags for epochs after the anchor name targets whose states the honest handlers cached. -/
private theorem justifiedState_flags_held {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    {root : Root} {state : BeaconState preset fork}
    (found : ((e.world k).state w).blockStates[root]? = some state) :
    CountedFlags (getCurrentEpoch anchorState)
      {vote | ∃ cached, ((e.world k).state w).checkpointStates[vote.2.target]? = some cached}
      state := by
  have reached : Store.Reachable config anchorState anchorBlock ((e.world k).state w) := by
    have all : ∀ n, Store.Reachable config anchorState anchorBlock ((e.world n).state w) := by
      intro n
      induction n with
      | zero =>
        change Store.Reachable config anchorState anchorBlock (e.start w)
        exact start.symm ▸ Store.Reachable.anchor anchored
      | succ n ih =>
        rcases e.state_succ n w with same | ⟨_, moved⟩
        · exact same ▸ ih
        · exact moved.reachable ih
    exact all k
  obtain ⟨block, held⟩ := reached.known_of_blockState found
  by_cases same : block = anchorBlock
  · obtain ⟨post, postOk, atAnchor, _⟩ := reached.blockStatesFromParents held
    rw [found, Option.some.injEq] at postOk
    subst post
    rw [atAnchor same]
    intro _ recent _ _ later
    cases recent
    · exact (UInt64.not_lt.mpr (getPreviousEpoch_le anchorState) later).elim
    · exact (UInt64.lt_irrefl _ later).elim
  · obtain ⟨parent, signed, message, parentFound, transitioned⟩ :=
      e.exists_transition_of_nonanchor_block anchored honest start held found same
    obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok transitioned
    have old := justifiedState_flags_held anchored sound positive window honest start parentFound
    have advancedHolds := slotsOk
    simp only [processSlots, bind_ok_iff, ensure_ok_iff] at advancedHolds
    obtain ⟨_, _, run⟩ := advancedHolds
    apply justifiedState_flags_block
      (countedFlags_advanceSlots positive window ((reached.ordered sound).2 parentFound) old run)
      blockOk
    intro a member v
    obtain ⟨cached, _, cachedOk, _⟩ :=
      blockVote_read_of_held anchored start held same (message ▸ member)
    exact ⟨cached, cachedOk⟩
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

/-- A passing count above the balance floor contains a validator. -/
private theorem justifiedState_nonempty {state : BeaconState preset fork}
    {indices : List ValidatorIndex} {total balance threshold weight : Gwei}
    (totalOk : getTotalActiveBalance state = .ok total)
    (balanceOk : getTotalBalance state indices = .ok balance)
    (thresholdOk : mulChecked total 2 = .ok threshold)
    (weightOk : mulChecked balance 3 = .ok weight) (passed : threshold ≤ weight)
    (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun v => balanceAt state v.toNat) (activeVoters state)) :
    ∃ v, v ∈ indices := by
  cases indices with
  | cons v rest => exact ⟨v, by simp⟩
  | nil =>
    obtain ⟨_, _, totalEq⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok totalOk)
    obtain ⟨_, _, balanceEq⟩ := getTotalBalance_ok_iff_stake.mp balanceOk
    change total.toNat = max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (stake (fun v => balanceAt state v.toNat) (activeVoters state)) at totalEq
    simp only [List.toFinset_nil, stake_empty, Nat.max_zero] at balanceEq
    have thresholdEq := (mulChecked_ok_iff.mp thresholdOk).2
    have weightEq := (mulChecked_ok_iff.mp weightOk).2
    simp only [UInt64.reduceToNat] at thresholdEq weightEq
    have bound := UInt64.le_iff_toNat_le.mp passed
    omega

/-- A counted post-anchor target has a cached state, at every fork. -/
private theorem justifiedState_cached_of_counted {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (start : ∀ u ∈ J, e.start u = anchor)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ}
    {root : Root} {base state : BeaconState preset fork}
    (found : ((e.world k).state w).blockStates[root]? = some base)
    (advanced : state = base ∨ ∃ (slot : Slot) (childRoot : Root)
      (child : BeaconBlock preset fork), ((e.world k).state w).blocks[childRoot]? = some child ∧
        child.parentRoot = root ∧ slot ≤ child.slot ∧
        processSlots config checks base slot = .ok state)
    (late : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1) (recent : Bool)
    {indices : List ValidatorIndex}
    (counted : (∃ altair : .altair ≤ fork,
      getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
        (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok indices) ∨
      ∃ (before : fork < .altair) (attestations : Array (PendingAttestation preset)),
        getMatchingTargetAttestations state before
          (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok attestations ∧
        getUnslashedAttestingIndices state attestations = .ok indices)
    {v : ValidatorIndex} (member : v ∈ indices) {checkpoint : Checkpoint}
    (later : getCurrentEpoch anchorState < checkpoint.epoch)
    (epoch : checkpoint.epoch = (if recent then getCurrentEpoch state else getPreviousEpoch state))
    (read : getBlockRoot state checkpoint.epoch = .ok checkpoint.root) :
    ∃ cached, ((e.world k).state w).checkpointStates[checkpoint]? = some cached := by
  have reached := e.reachable
    (fun u hu => (start u hu).symm ▸ Store.Reachable.anchor anchored) k w honest
  have invariant := (reached.ordered sound).2 found
  have targetEq {data : AttestationData}
      (targetEpoch : data.target.epoch =
        (if recent then getCurrentEpoch state else getPreviousEpoch state))
      (targetRoot : getBlockRoot state data.target.epoch = .ok data.target.root) :
      data.target = checkpoint := by
    have sameEpoch := targetEpoch.trans epoch.symm
    rw [sameEpoch, read, Except.ok.injEq] at targetRoot
    cases target : data.target
    cases checkpoint
    simp_all
  rcases counted with ⟨altair, flags⟩ | ⟨before, attestations, matching, indicesOk⟩
  · have old := justifiedState_flags_held anchored sound positive window honest
      (start w honest) found
    have holds : CountedFlags (getCurrentEpoch anchorState)
        {vote | ∃ cached, ((e.world k).state w).checkpointStates[vote.2.target]? = some cached}
        state := by
      rcases advanced with rfl | ⟨_, _, _, _, _, _, processed⟩
      · exact old
      · simp only [processSlots, bind_ok_iff, ensure_ok_iff] at processed
        obtain ⟨_, _, run⟩ := processed
        exact countedFlags_advanceSlots positive window invariant old run
    obtain ⟨_, data, cached, targetEpoch, targetRoot, _⟩ :=
      countedFlags_quorum holds altair late recent (epoch ▸ later) flags member
    exact targetEq targetEpoch targetRoot ▸ cached
  · have old := countedPending_held anchored sound honest (start w honest) found
    have holds : CountedPending (getCurrentEpoch anchorState)
        (fun pending => ∃ (r : Root) (block : BeaconBlock preset fork)
          (a : Attestation preset fork), ((e.world k).state w).blocks[r]? = some block ∧
          block ≠ anchorBlock ∧ a ∈ block.body.attestations.data ∧ pending.data = a.data ∧
          pending.aggregationBits.bits = a.aggregationBits.bits) state := by
      rcases advanced with rfl | ⟨_, _, _, _, _, _, processed⟩
      · exact old
      · simp only [processSlots, bind_ok_iff, ensure_ok_iff] at processed
        obtain ⟨_, _, run⟩ := processed
        exact countedPending_advanceSlots invariant old run
    obtain ⟨pending, _, ⟨r, block, a, held, other, included, same, _⟩,
      _, _, targetEpoch, _, targetRoot, _⟩ :=
      countedPending_member before holds late recent (epoch ▸ later) matching indicesOk member
    obtain ⟨cached, _, cachedOk, _⟩ :=
      blockVote_read_of_held anchored (start w honest) held other included
    have target := targetEq targetEpoch targetRoot
    rw [same] at target
    exact ⟨cached, target ▸ cachedOk⟩

/-- The checkpoint state reconstructed from a held history lies before a held child. -/
private theorem justifiedState_history_counts {store : Store preset fork}
    (reached : Store.Reachable config anchorState anchorBlock store)
    (transitions : ∀ (root : Root) (block : BeaconBlock preset fork)
      (state : BeaconState preset fork), store.blocks[root]? = some block →
      store.blockStates[root]? = some state → block ≠ anchorBlock →
      ∃ parent signed, signed.message = block ∧
        store.blockStates[block.parentRoot]? = some parent ∧
        stateTransition config checks sources.engine parent signed true = .ok state)
    (nonzero : ∀ (root : Root) (block : BeaconBlock preset fork), store.blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0)
    {root readRoot : Root} {state : BeaconState preset fork} {query : Slot}
    (stored : store.blockStates[root]? = some state)
    (read : getBlockRootAtSlot state query = .ok readRoot)
    (later : anchorState.slot ≤ query) :
    ∃ base cached, store.blockStates[readRoot]? = some base ∧
      lookaheadState config checks base query = .ok cached ∧ store.Counts config cached := by
  obtain ⟨block, held⟩ := reached.known_of_blockState stored
  by_cases same : block = anchorBlock
  · obtain ⟨post, postOk, atAnchor, _⟩ := reached.blockStatesFromParents held
    rw [stored, Option.some.injEq] at postOk
    subst post
    rw [atAnchor same] at read
    have before := (getBlockRootAtSlot_ok_iff.mp read).1
    have bound := UInt64.le_iff_toNat_le.mp later
    omega
  · obtain ⟨parent, signed, message, parentFound, transitioned⟩ :=
      transitions root block state held stored same
    obtain ⟨advanced, slotsOk, atSlot, _, blockOk, _⟩ := stateTransition_ok transitioned
    have advancedRead : getBlockRootAtSlot advanced query = .ok readRoot := by
      unfold getBlockRootAtSlot at read ⊢
      rwa [processBlock_slot blockOk, (processBlock_blockRoots_latestBlockHeader blockOk).1]
        at read
    by_cases old : query < parent.slot
    · have run := slotsOk
      simp only [processSlots, bind_ok_iff, ensure_ok_iff] at run
      obtain ⟨_, _, ran⟩ := run
      exact justifiedState_history_counts reached transitions nonzero parentFound
        (getBlockRootAtSlot_of_advanceSlots ran advancedRead old) later
    · obtain ⟨parentBlock, parentKnown⟩ := reached.known_of_blockState parentFound
      have cachedRoot := getBlockRootAtSlot_processSlots_header
        (reached.blockState_root parentKnown parentFound) (nonzero _ _ parentKnown)
        slotsOk advancedRead (UInt64.not_lt.mp old)
      have parentHash := processBlock_parentRoot blockOk
      rw [message] at parentHash
      have eq := Except.ok.inj (cachedRoot.symm.trans parentHash)
      have high : query < signed.message.slot := by
        rw [← atSlot]
        exact UInt64.lt_iff_toNat_lt.mpr (getBlockRootAtSlot_ok_iff.mp advancedRead).1
      obtain ⟨cached, made, _, _⟩ :=
        lookaheadState_of_processSlots slotsOk (UInt64.not_lt.mp old) high
      refine ⟨parent, cached, eq ▸ parentFound, made, ?_⟩
      unfold lookaheadState at made
      split at made
      · exact ⟨block.parentRoot, parent, parentFound,
          .inr ⟨checks, query, root, block, held, rfl,
            UInt64.le_of_lt (message ▸ high), mapError_ok_iff.mp made⟩⟩
      · cases Except.ok.inj made
        exact ⟨block.parentRoot, parent, parentFound, .inl rfl⟩
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

/-- A cached target read in a counting state is itself a counting state. -/
private theorem justifiedState_cached_counts {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ}
    (nonzero : ∀ (r : Root) (b : BeaconBlock preset fork),
      ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    {root : Root} {base state cached : BeaconState preset fork}
    (found : ((e.world k).state w).blockStates[root]? = some base)
    (advanced : state = base ∨ ∃ (slot : Slot) (childRoot : Root)
      (child : BeaconBlock preset fork), ((e.world k).state w).blocks[childRoot]? = some child ∧
        child.parentRoot = root ∧ slot ≤ child.slot ∧
        processSlots config checks base slot = .ok state)
    {checkpoint : Checkpoint} {query : Slot}
    (cachedOk : ((e.world k).state w).checkpointStates[checkpoint]? = some cached)
    (queryOk : computeStartSlotAtEpoch preset checkpoint.epoch = .ok query)
    (read : getBlockRootAtSlot state query = .ok checkpoint.root)
    (later : anchorState.slot ≤ query) : ((e.world k).state w).Counts config cached := by
  have reached := e.reachable
    (fun u hu => (start u hu).symm ▸ Store.Reachable.anchor anchored) k w honest
  obtain ⟨cacheBase, boundary, cacheFound, boundaryOk, made⟩ :=
    e.checkpointStates_fixedChecks anchored (start w honest) cachedOk
  rw [queryOk, Except.ok.injEq] at boundaryOk
  subst boundary
  have history {r : Root} {s : BeaconState preset fork}
      (held : ((e.world k).state w).blockStates[r]? = some s)
      (rootRead : getBlockRootAtSlot s query = .ok checkpoint.root) :
      ((e.world k).state w).Counts config cached := by
    obtain ⟨parent, reconstructed, parentFound, computed, counts⟩ :=
      justifiedState_history_counts reached
        (fun r b s held stored other => e.exists_transition_of_nonanchor_block anchored
          honest (start w honest) (root := r) (block := b) (state := s) held stored other)
        nonzero held rootRead later
    rw [cacheFound, Option.some.injEq] at parentFound
    subst parent
    rw [made, Except.ok.injEq] at computed
    exact computed ▸ counts
  rcases advanced with rfl | ⟨slot, childRoot, child, held, parent, before, processed⟩
  · exact history found read
  · by_cases old : query < base.slot
    · have run := processed
      simp only [processSlots, bind_ok_iff, ensure_ok_iff] at run
      obtain ⟨_, _, ran⟩ := run
      exact history found (getBlockRootAtSlot_of_advanceSlots ran read old)
    · obtain ⟨baseBlock, baseHeld⟩ := reached.known_of_blockState found
      have eq : checkpoint.root = root := by
        by_cases same : baseBlock = anchorBlock
        · obtain ⟨post, stored, atAnchor, _⟩ := reached.blockStatesFromParents baseHeld
          rw [found, Option.some.injEq] at stored
          subst post
          obtain ⟨readBlock, readHeld⟩ := reached.known_of_blockState cacheFound
          rw [atAnchor same] at processed
          exact reached.anchor_processSlots_root (same ▸ nonzero _ _ baseHeld)
            (same ▸ baseHeld) readHeld processed read later
        · exact reached.blockState_processSlots_root baseHeld found same
            (nonzero _ _ baseHeld) processed read
            ((reached.blockState_header baseHeld found same).1 ▸ UInt64.not_lt.mp old)
      rw [eq, found, Option.some.injEq] at cacheFound
      subst cacheBase
      unfold lookaheadState at made
      split at made
      · have below : query ≤ child.slot := by
          have high := (getBlockRootAtSlot_ok_iff.mp read).1
          have atSlot := (processSlots_slot processed).2
          exact UInt64.le_trans (UInt64.le_of_lt (atSlot ▸ UInt64.lt_iff_toNat_lt.mpr high)) before
        exact ⟨root, base, found, .inr ⟨checks, query, childRoot, child, held, parent,
          below, mapError_ok_iff.mp made⟩⟩
      · cases Except.ok.inj made
        exact ⟨root, base, found, .inl rfl⟩

/-- The anchor's cached state survives every handler. -/
private theorem justifiedState_anchor_cache {anchor store : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (reached : Store.Reachable config anchorState anchorBlock store) :
    store.checkpointStates[anchor.justifiedCheckpoint]? = some anchorState := by
  induction reached with
  | anchor made =>
    have same := Except.ok.inj (anchored.symm.trans made)
    subst same
    obtain ⟨root, rootOk, states⟩ := getForkchoiceStore_checkpointStates made
    obtain ⟨other, otherOk, _, _, justified, _⟩ := getForkchoiceStore_anchor made
    rw [rootOk, Except.ok.injEq] at otherOk
    subst other
    simp [justified, states]
  | tick _ step ih =>
    rwa [(Store.onTick_checkpointStates_latestMessages step).1]
  | block _ step ih =>
    rwa [(Store.onBlock_checkpointStates_latestMessages step).1]
  | attestation _ step ih => exact Store.onAttestation_checkpointStates_of_found step ih
  | attesterSlashing _ step ih =>
    rwa [(Store.onAttesterSlashing_checkpointStates_latestMessages step).1]
  | payloadAttestation _ step ih =>
    obtain ⟨_, _, rfl⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes step
    exact ih
  | envelope _ step ih =>
    obtain ⟨_, _, _, _, _, record, rfl⟩ := Store.onExecutionPayloadEnvelope_ok step
    obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
    exact ih
  | inclusionList _ step ih =>
    obtain ⟨_, _, rfl⟩ := Store.onInclusionList_ok _ step
    exact ih

/-- Importing a block other than the anchor requires a positive slot duration. -/
private theorem justifiedState_duration {store : Store preset fork}
    (reached : Store.Reachable config anchorState anchorBlock store)
    {root : Root} {block : BeaconBlock preset fork}
    (held : store.blocks[root]? = some block) (other : block ≠ anchorBlock) :
    0 < config.SLOT_DURATION_MS := by
  induction reached with
  | anchor made =>
    obtain ⟨r, _, blocks, _⟩ := getForkchoiceStore_maps made
    rw [blocks, getElem?_insert_root] at held
    split at held
    · exact (other (Option.some.inj held).symm).elim
    · simp at held
  | tick _ step ih => exact ih ((Store.onTick_frame step).2.2.1 ▸ held)
  | @block before after checks sources signed _ step ih =>
    rcases Store.onBlock_same_or_insert step with same | ⟨r, hashed, absent, _⟩
    · exact ih (same ▸ held)
    · have fresh : ¬ before.blocks.contains r := by
        simp [Std.TreeMap.contains_eq_isSome_getElem?, absent]
      obtain ⟨⟨_, slotOk, _⟩, _⟩ := Store.onBlock_checks hashed fresh step
      exact Store.slotDuration_pos slotOk
  | attestation _ step ih => exact ih ((Store.onAttestation_frame step).2.1 ▸ held)
  | attesterSlashing _ step ih => exact ih ((Store.onAttesterSlashing_frame step).2.1 ▸ held)
  | payloadAttestation _ step ih =>
    exact ih ((Store.onPayloadAttestationMessage_onlyPtcVotes step).frame.2.1 ▸ held)
  | envelope _ step ih => exact ih ((Store.onExecutionPayloadEnvelope_frame step).2.1 ▸ held)
  | inclusionList _ step ih => exact ih ((Store.onInclusionList_frame step).2.1 ▸ held)

/-- An honest store caches the state of its justified checkpoint, and can count with it.

The anchor's checkpoint is cached when the store is built.

A later justified checkpoint has an epoch above the anchor's, so a vote of a held block targets it.

The store imported that block with its votes, and each vote cached the state of its target.

The state is that of the checkpoint block, or its slots up to a held child, so the store counts
with it.

The stake bound excludes justification by the balance floor alone. -/
theorem Execution.exists_justified_checkpointState {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (start : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (preGloas : fork < .glamsterdam)
    {limit : ℕ} {horizon : Epoch}
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).Counts config state →
      getCurrentEpoch state ≤ horizon →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit) :
    ∃ state, ((e.world k).state w).checkpointState
        ((e.world k).state w).justifiedCheckpoint = .ok state ∧
      ((e.world k).state w).Counts config state := by
  have reached := e.reachable
    (fun u hu => (start u hu).symm ▸ Store.Reachable.anchor anchored) k w honest
  obtain ⟨anchorRoot, hashed, _, _, justified, _⟩ := getForkchoiceStore_anchor anchored
  rcases (justifiedRoot_fields_after_anchor anchored reached).1 with same | later
  · obtain ⟨root, rootOk, held⟩ := reached.anchor_known
    rw [hashed, Except.ok.injEq] at rootOk
    subst root
    obtain ⟨state, found, atAnchor, _⟩ := reached.blockStatesFromParents held
    rw [atAnchor rfl] at found
    exact ⟨anchorState, Store.checkpointState_ok_iff.mpr
      (same ▸ justifiedState_anchor_cache anchored reached),
      ⟨anchorRoot, anchorState, found, .inl rfl⟩⟩
  have recent : getCurrentEpoch anchorState <
      ((e.world k).state w).justifiedCheckpoint.epoch := by
    simpa only [justified] using later
  have epochSize : 0 < preset.SLOTS_PER_EPOCH.toNat := by
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
  have duration : 0 < config.SLOT_DURATION_MS := by
    by_contra absent
    have allAnchor {r : Root} {s : BeaconState preset fork}
        (held : ((e.world k).state w).blockStates[r]? = some s) : s = anchorState := by
      obtain ⟨b, known⟩ := reached.known_of_blockState held
      have same : b = anchorBlock := by
        by_contra other
        exact absent (justifiedState_duration reached known other)
      obtain ⟨post, found, atAnchor, _⟩ := reached.blockStatesFromParents known
      rw [held, Option.some.injEq] at found
      subst post
      exact atAnchor same
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
  have forward := e.forwardReachable
    (fun u hu => (start u hu).symm ▸ Store.ForwardReachable.anchor anchored) k w honest
  obtain ⟨current, slotOk, blocksLe, statesLe⟩ :=
    forward.slots_le_current duration (UInt64.le_of_eq anchorSlot)
  have epochOk : ((e.world k).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset current) := by
    simp [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure]
  have upper := inHorizon w honest k _ bounded epochOk
  have result : ((e.world k).state w).justifiedCheckpoint.epoch ≤ getCurrentEpoch anchorState ∨
      ∃ cached, ((e.world k).state w).checkpointStates[
        ((e.world k).state w).justifiedCheckpoint]? = some cached ∧
        ((e.world k).state w).Counts config cached := by
    apply justified_target_property (checks := checks) (sources := sources)
      reached sound epochSize window preGloas
      (P := fun checkpoint => checkpoint.epoch ≤ getCurrentEpoch anchorState ∨
        ∃ cached, ((e.world k).state w).checkpointStates[checkpoint]? = some cached ∧
          ((e.world k).state w).Counts config cached)
      (fun _ old => .inl old)
      (fun r b s held stored other => e.exists_transition_of_nonanchor_block anchored
        honest (start w honest) (root := r) (block := b) (state := s) held stored other)
      ?_ (.inl rfl)
    intro root base state found advanced counts late currentEpoch indices total balance threshold
      weight counted totalOk balanceOk thresholdOk weightOk passed checkpoint _ _ epoch read
    by_cases old : checkpoint.epoch ≤ getCurrentEpoch anchorState
    · exact .inl old
    have later := UInt64.not_le.mp old
    have stateSlot : state.slot ≤ current := by
      rcases advanced with rfl | ⟨slot, childRoot, child, held, _, before, processed⟩
      · exact statesLe _ _ found
      · rw [(processSlots_slot processed).2]
        exact UInt64.le_trans before (blocksLe _ _ held)
    have inside : getCurrentEpoch state ≤ horizon := by
      apply UInt64.le_trans (b := computeEpochAtSlot preset current) ?_ upper
      apply UInt64.le_iff_toNat_le.mpr
      simp only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div]
      exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp stateSlot)
    obtain ⟨v, member⟩ := justifiedState_nonempty totalOk balanceOk thresholdOk weightOk passed
      (large w honest k state bounded counts inside)
    obtain ⟨cached, cachedOk⟩ := justifiedState_cached_of_counted anchored sound epochSize window
      start honest found advanced late currentEpoch counted member later epoch read
    have rootRead := read
    unfold getBlockRoot at rootRead
    simp only [bind_ok_iff] at rootRead
    obtain ⟨query, queryOk, rootRead⟩ := rootRead
    have queryOk := mapError_ok_iff.mp queryOk
    have anchorBefore : anchorState.slot ≤ query := by
      have boundary := (computeStartSlotAtEpoch_ok_iff.mp queryOk).2
      have lt := UInt64.lt_iff_toNat_lt.mp later
      rw [getCurrentEpoch_toNat] at lt
      apply UInt64.le_iff_toNat_le.mpr
      have floor := Nat.lt_mul_of_div_lt lt
      omega
    exact .inr ⟨cached, cachedOk, justifiedState_cached_counts anchored start honest
      (nonzero w honest k bounded) found advanced cachedOk queryOk rootRead anchorBefore⟩
  rcases result with old | ⟨cached, found, counts⟩
  · exact (UInt64.not_le.mpr recent old).elim
  · exact ⟨cached, Store.checkpointState_ok_iff.mpr found, counts⟩

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
  sorry

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
  sorry

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
  sorry

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
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (supply : ∀ w ∈ J, ∀ k (checkpoint : Checkpoint) (state : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).checkpointState checkpoint = .ok state →
      ActiveStakeAtMost stakeCapGwei state)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit) :
    ∃ head, ((e.world k).state w).getHead config = .ok head := by
  sorry

end EthLib.Consensus.Models.Network
