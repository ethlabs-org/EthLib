module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSafety
public import EthLib.Consensus.Transition.Genesis
-- The committee certificates reduce the derived equality decision procedure for Except.
import all Batteries.Data.Except
-- A zero-round shuffle reads the body of Array.range to enumerate the registry positions.
import all Init.Data.Array.Basic

/-!
# Compatibility of the fast-confirmation premises at the anchor

These results test the premises of the safety statement for Theorem 1 of [the paper][fcr].

The anchor store and the anchor state can name different justified checkpoints.

`OneJustifiedPerEpoch` identifies them when their positive epochs agree within its horizon.

If that identifies the anchor root with its parent, the `anchorParent` premise fails.

At genesis, the raw state's checkpoint need not be justified in the store.

[fcr]: https://arxiv.org/html/2405.00549v4#S4
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- Uniqueness compares a positive-epoch state checkpoint with the store's checkpoint. -/
theorem Execution.anchor_currentJustified_eq_of_oneJustifiedPerEpoch
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J)
    {horizon : Epoch} (unique : OneJustifiedPerEpoch e horizon)
    (sameEpoch : anchorState.currentJustifiedCheckpoint.epoch = getCurrentEpoch anchorState)
    (positive : 0 < anchorState.currentJustifiedCheckpoint.epoch)
    (within : getCurrentEpoch anchorState ≤ horizon) :
    anchorState.currentJustifiedCheckpoint = anchor.justifiedCheckpoint := by
  obtain ⟨root, _, _, stored, justified, _⟩ := getForkchoiceStore_anchor anchored
  have atStart : (e.world 0).state u = anchor := start u caller
  -- Both alternatives of Justified are present in the initial world.
  have stateJustified : anchor.Justified anchorState.currentJustifiedCheckpoint :=
    .inr (.inr ⟨positive, .inl ⟨root, anchorState, stored, rfl⟩⟩)
  have storeJustified : anchor.Justified anchor.justifiedCheckpoint := .inl rfl
  exact unique u caller u caller 0 0 _ _ (atStart ▸ stateJustified)
    (atStart ▸ storeJustified) (by simpa [justified] using sameEpoch)
    (sameEpoch ▸ within)

/-- A same-epoch anchor checkpoint cannot name the anchor's excluded parent. -/
theorem Execution.false_of_anchor_checkpoint_parent
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J)
    {horizon : Epoch} (unique : OneJustifiedPerEpoch e horizon)
    (sameEpoch : anchorState.currentJustifiedCheckpoint.epoch = getCurrentEpoch anchorState)
    (positive : 0 < anchorState.currentJustifiedCheckpoint.epoch)
    (within : getCurrentEpoch anchorState ≤ horizon)
    (parent : anchorState.currentJustifiedCheckpoint.root = anchorBlock.parentRoot)
    {limit : ℕ} (started : e.startTime ≤ limit)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none) : False := by
  obtain ⟨root, _, held, _, justified, _⟩ := getForkchoiceStore_anchor anchored
  have same := e.anchor_currentJustified_eq_of_oneJustifiedPerEpoch anchored start caller
    unique sameEpoch positive within
  have rootEq : anchorBlock.parentRoot = root := by
    simpa [parent, justified] using congrArg Checkpoint.root same
  -- The excluded parent is the anchor itself, which the initial store holds.
  have missing := anchorParent u caller 0 started
  change (e.start u).blocks[anchorBlock.parentRoot]? = none at missing
  rw [start u caller, rootEq, held] at missing
  contradiction

/-- A raw genesis checkpoint naming the excluded parent is not justified in the store.

This covers an anchor whose parent and state's current justified root are both zero.

No assertion about the value or injectivity of a hash is needed. -/
theorem Execution.not_justified_of_genesis_anchor_checkpoint_parent
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J)
    {horizon : Epoch} (unique : OneJustifiedPerEpoch e horizon)
    (sound : Invariant anchorState) (epochZero : getCurrentEpoch anchorState = 0)
    (parent : anchorState.currentJustifiedCheckpoint.root = anchorBlock.parentRoot)
    {limit : ℕ} (started : e.startTime ≤ limit)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none) :
    ¬ anchor.Justified anchorState.currentJustifiedCheckpoint := by
  intro rawJustified
  have settled := sound.settled
  have sameEpoch : anchorState.currentJustifiedCheckpoint.epoch = getCurrentEpoch anchorState := by
    apply UInt64.toNat_inj.mp
    simpa [JustifiedSettled, getPreviousEpoch, epochZero, Uint64.saturatingSub,
      UInt64.le_iff_toNat_le] using settled
  obtain ⟨root, _, held, _, justified, _⟩ := getForkchoiceStore_anchor anchored
  have atStart : (e.world 0).state u = anchor := start u caller
  have storeJustified : anchor.Justified anchor.justifiedCheckpoint := .inl rfl
  have same := unique u caller u caller 0 0
    anchorState.currentJustifiedCheckpoint anchor.justifiedCheckpoint (atStart ▸ rawJustified)
    (atStart ▸ storeJustified)
    (by simpa [justified] using sameEpoch) (by simp [sameEpoch, epochZero])
  have rootEq : anchorBlock.parentRoot = root := by
    simpa [parent, justified] using congrArg Checkpoint.root same
  -- The excluded parent would be the anchor itself.
  have missing := anchorParent u caller 0 started
  change (e.start u).blocks[anchorBlock.parentRoot]? = none at missing
  rw [start u caller, rootEq, held] at missing
  contradiction

/-- A store built from an anchor cannot read a shuffling dependency before that anchor.

The block handler reads this dependency even when the proposer boost is zero. -/
theorem _root_.EthLib.Consensus.Store.Reachable.getShufflingDependentRoot_ne_ok_of_lt_anchor
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {epoch : Epoch} {slot : Slot}
    (dependent : computeShufflingDependentSlot preset epoch = .ok slot)
    (before : slot < anchorBlock.slot) (root result : Root) :
    store.getShufflingDependentRoot root epoch ≠ .ok result := by
  intro read
  simp only [Store.getShufflingDependentRoot, Base.bind_ok_iff, Base.mapError_ok_iff,
    pure, Except.pure, Except.ok.injEq] at read
  obtain ⟨dependentSlot, slotOk, ancestor, walk, _⟩ := read
  rw [dependent, Except.ok.injEq] at slotOk
  subst dependentSlot
  obtain ⟨block, known, below⟩ := Store.getAncestor_le walk
  have above := reachable.anchorSlot_le_block known
  rw [UInt64.le_iff_toNat_le] at above below
  rw [UInt64.lt_iff_toNat_lt] at before
  omega

/-- The common-state premise bounds a vote's target by the epoch of the head state.

An old head cannot supply this premise for an arbitrarily recent cached vote target. -/
theorem CommitteesFollow.targetEpoch_le_headEpoch_add_lookahead
    (committees : CommitteesFollow e) {w : ValidatorIndex} (honest : w ∈ J)
    {k : ℕ} {head : ForkChoiceNode} {headState : BeaconState preset fork}
    {current : Epoch} {v : ValidatorIndex} {attestation : Attestation preset fork}
    {targetState : BeaconState preset fork}
    (headOk : ((e.world k).state w).getHead config = .ok head)
    (headStateOk : ((e.world k).state w).blockState head.root = .ok headState)
    (currentOk : ((e.world k).state w).getCurrentStoreEpoch config = .ok current)
    (targetPast : attestation.data.target.epoch.toNat ≤ current.toNat)
    (recent : current.toNat ≤ attestation.data.target.epoch.toNat + 1)
    (origin : ((e.world k).state w).VoteOrigin config v attestation)
    (targetOk : ((e.world k).state w).checkpointStates[attestation.data.target]? =
      some targetState) :
    attestation.data.target.epoch.toNat ≤
      (getCurrentEpoch headState).toNat + preset.MIN_SEED_LOOKAHEAD.toNat := by
  obtain ⟨common, headRun, _, targetBound, _⟩ :=
    committees.common w honest k head headState current v attestation targetState
      headOk headStateOk currentOk targetPast recent origin targetOk
  -- A common state is no later than the head state that follows it.
  have headLater := UInt64.le_iff_toNat_le.mp headRun.later
  omega

/-- Every reachable store retains each checkpoint state cached at initialization.

The handlers extend this cache without replacing an existing entry. -/
theorem _root_.EthLib.Consensus.Store.Reachable.checkpointStates_of_anchor
    {anchor store : Store preset fork} {checkpoint : Checkpoint}
    {state : BeaconState preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (initial : anchor.checkpointStates[checkpoint]? = some state) :
    store.checkpointStates[checkpoint]? = some state := by
  induction reachable with
  | anchor made =>
    rw [anchored, Except.ok.injEq] at made
    subst made
    exact initial
  | tick _ ticked ih =>
    rw [(Store.onTick_checkpointStates_latestMessages ticked).1]
    exact ih
  | block _ added ih =>
    rw [(Store.onBlock_checkpointStates_latestMessages added).1]
    exact ih
  | attestation _ attested ih =>
    exact Store.onAttestation_checkpointStates_of_found attested ih
  | attesterSlashing _ slashed ih =>
    rw [(Store.onAttesterSlashing_checkpointStates_latestMessages slashed).1]
    exact ih
  | payloadAttestation _ voted ih =>
    obtain ⟨_, _, rfl⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes voted
    exact ih
  | envelope _ accepted ih =>
    obtain ⟨_, _, _, _, _, record, rfl⟩ := Store.onExecutionPayloadEnvelope_ok accepted
    obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
    exact ih
  | inclusionList _ accepted ih =>
    obtain ⟨_, _, rfl⟩ := Store.onInclusionList_ok ‹_› accepted
    exact ih

/-- An initially cached target fixes the signers in every reachable reading of a vote.

The no-forgery condition can use this one indexed reading without assuming hash injectivity. -/
theorem mem_indexedStatements_of_cached_target
    {anchor : Store preset fork} {state : BeaconState preset fork}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (initial : anchor.checkpointStates[attestation.data.target]? = some state)
    (read : getIndexedAttestation state attestation = .ok indexed)
    {x : ValidatorIndex × AttestationData}
    (member : x ∈ attestationStatements (config := config) (checks := checks)
      anchorState anchorBlock attestation) : x ∈ indexedStatements indexed := by
  obtain ⟨store, other, reachable, ⟨withTarget, targetState, stored, found, indexedOk, _⟩,
    statement⟩ := member
  have cached := reachable.checkpointStates_of_anchor anchored initial
  have contains : store.checkpointStates.contains attestation.data.target := by
    rw [Std.TreeMap.contains_eq_isSome_getElem?, cached]
    rfl
  -- Reading an already cached target does not recompute it from another block state.
  simp only [Store.storeTargetCheckpointState, contains, ↓reduceIte,
    pure, Except.pure, Except.ok.injEq] at stored
  subst withTarget
  have found' : store.checkpointState attestation.data.target = .ok state := by
    simp [Store.checkpointState, cached, pure, Except.pure]
  rw [found', Except.ok.injEq] at found
  subst targetState
  rw [read, Except.ok.injEq] at indexedOk
  subst other
  exact statement

namespace FinitePrefix

variable {ν μ σ κ : Type*} [DecidableEq ν]

/-- A finite event list followed by waits that advance the clock without bound.

The infinite tail supplies the unbounded time required by the network model of the paper's §2. -/
def events (steps : List (Event ν μ σ)) (lastTime : ℕ) (n : ℕ) : Event ν μ σ :=
  if h : n < steps.length then steps[n] else .wait (lastTime + (n - steps.length) + 1)

/-- Before the tail, the world is the fold of the events that have happened. -/
theorem world_prefix (steps : List (Event ν μ σ)) (lastTime : ℕ) (init : World ν μ σ)
    (n : ℕ) (within : n ≤ steps.length) :
    worldAt init (events steps lastTime) n = (steps.take n).foldl World.apply init := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have inside : n < steps.length := by omega
    -- Taking one more event appends exactly the event that the network applies.
    rw [worldAt, ih (by omega), events, dite_eq_left inside,
      List.take_succ_eq_append_getElem inside, List.foldl_append]
    rfl

/-- After the finite list, only the clock changes. -/
theorem world_tail (steps : List (Event ν μ σ)) (lastTime : ℕ) (init : World ν μ σ)
    (clock : (steps.foldl World.apply init).time = lastTime) (n : ℕ) :
    worldAt init (events steps lastTime) (steps.length + n) =
      { steps.foldl World.apply init with time := lastTime + n } := by
  induction n with
  | zero =>
    rw [Nat.add_zero, world_prefix _ _ _ _ (Nat.le_refl _), List.take_length]
    simp [← clock]
  | succ n ih =>
    -- Every tail event is a wait, so it preserves states, sent messages and views.
    rw [Nat.add_succ, worldAt, ih, events, dite_eq_right (by omega)]
    simp [World.apply]
    omega

/-- Allowed events in a finite list extend to an execution by waiting after its last time. -/
def execution (P : Protocol ν μ σ κ) (J : Set ν) (startTime : ℕ) (start : ν → σ)
    (steps : List (Event ν μ σ)) (lastTime : ℕ)
    (clock : (steps.foldl World.apply (World.initial startTime start)).time = lastTime)
    (valid : ∀ n (h : n < steps.length),
      Allowed P J ((steps.take n).foldl World.apply (World.initial startTime start)) steps[n]) :
    Execution P J where
  startTime
  start
  events := events steps lastTime
  allowed n := by
    by_cases inside : n < steps.length
    · rw [world_prefix _ _ _ _ (Nat.le_of_lt inside), events, dite_eq_left inside]
      exact valid n inside
    · have index : n = steps.length + (n - steps.length) := by omega
      -- Waiting one more millisecond is allowed at every point in the tail.
      rw [index, world_tail steps lastTime _ clock, events, dite_eq_right (by omega)]
      simp [Allowed]

/-- Finite timely delivery and complete final delivery suffice for infinite synchrony.

The finite list delivers every sent message to every honest validator before it ends.

The tail sends no new messages, so its delivery obligations are already discharged. -/
theorem synchronous_execution (P : Protocol ν μ σ κ) (J : Set ν)
    (startTime : ℕ) (start : ν → σ) (steps : List (Event ν μ σ)) (lastTime : ℕ)
    (clock : (steps.foldl World.apply (World.initial startTime start)).time = lastTime)
    (valid : ∀ n (h : n < steps.length),
      Allowed P J ((steps.take n).foldl World.apply (World.initial startTime start)) steps[n])
    (Δ : ℕ) (positive : 0 < Δ)
    (delivered : ∀ u ∈ J,
      (steps.foldl World.apply (World.initial startTime start)).sent ⊆
        (steps.foldl World.apply (World.initial startTime start)).view u)
    (timely : ∀ n k, n ≤ k → k ≤ steps.length → ∀ v ∈ J, ∀ u ∈ J,
      ∀ m ∈ ((steps.take n).foldl World.apply (World.initial startTime start)).view v,
      ((steps.take n).foldl World.apply (World.initial startTime start)).time + Δ ≤
        ((steps.take k).foldl World.apply (World.initial startTime start)).time →
      m ∈ ((steps.take k).foldl World.apply (World.initial startTime start)).view u) :
    (execution P J startTime start steps lastTime clock valid).Synchronous Δ := by
  let run := execution P J startTime start steps lastTime clock valid
  have before (n : ℕ) (within : n ≤ steps.length) :
      run.world n = (steps.take n).foldl World.apply (World.initial startTime start) :=
    world_prefix _ _ _ _ within
  have after (n : ℕ) (beyond : steps.length ≤ n) :
      run.world n = {steps.foldl World.apply (World.initial startTime start) with
        time := lastTime + (n - steps.length)} := by
    have index : n = steps.length + (n - steps.length) := by omega
    change worldAt _ _ _ = _
    conv_lhs => rw [index]
    exact world_tail _ _ _ clock _
  refine ⟨positive, ?_, ?_⟩
  · intro T
    refine ⟨steps.length + T, ?_⟩
    change T ≤ (run.world (steps.length + T)).time
    rw [after _ (by omega)]
    simp
  · intro n k later v honest u receiver m member arrived
    change m ∈ (run.world k).view u
    change m ∈ (run.world n).view v at member
    change max (run.world n).time 0 + Δ ≤ (run.world k).time at arrived
    rw [Nat.max_zero] at arrived
    by_cases early : k ≤ steps.length
    · rw [before k early]
      rw [before n (by omega)] at member
      rw [before n (by omega), before k early] at arrived
      exact timely n k later early v honest u receiver m member arrived
    · rw [after k (by omega)]
      apply delivered u receiver
      -- Every received message was sent; the tail's views contain every such message.
      have sent := run.view_subset_sent n v member
      by_cases first : n ≤ steps.length
      · have kept := run.monotone_sent first sent
        change m ∈ (run.world steps.length).sent at kept
        rw [before _ (Nat.le_refl _), List.take_length] at kept
        exact kept
      · rw [after n (by omega)] at sent
        exact sent

end FinitePrefix

end EthLib.Consensus.Models.Network

namespace EthLib.Consensus.Models.Network.FiveValidatorWitness

open Base Models

/-- A four-slot preset with small state vectors and whole balance increments. -/
def preset : Preset := { Preset.minimal with
  SHUFFLE_ROUND_COUNT := 0
  SLOTS_PER_EPOCH := 4
  SLOTS_PER_HISTORICAL_ROOT := 8
  EPOCHS_PER_HISTORICAL_VECTOR := 8
  EPOCHS_PER_SLASHINGS_VECTOR := 8
  VALIDATOR_REGISTRY_LIMIT := 8
  EFFECTIVE_BALANCE_INCREMENT := 100
  MAX_EFFECTIVE_BALANCE := 200
  MAX_EFFECTIVE_BALANCE_ELECTRA := 200
  BASE_REWARD_FACTOR := 0 }

/-- One-second slots and no proposer boost isolate the weight of the votes. -/
def config : Config := { Config.minimal with
  SLOT_DURATION_MS := 1000
  EJECTION_BALANCE := 0
  PROPOSER_SCORE_BOOST := 0
  CONFIRMATION_BYZANTINE_THRESHOLD := 34 }

/-- An active, unslashed validator with no scheduled exit. -/
def validator (weight : UInt64) : Validator :=
  ⟨default, default, weight, false, 0, 0, FAR_FUTURE_EPOCH, FAR_FUTURE_EPOCH⟩

/-- Genesis at time zero with four honest validators and one silent Byzantine validator.

The balances are 200, 200, 200, 100 and 200 Gwei; validator 3 is Byzantine.

The body root is a parameter so these state facts do not need to evaluate a hash.

These initialization facts alone do not certify an execution of Theorem 1. -/
def state (bodyRoot : Root) : BeaconState preset .phase0 :=
  { emptyGenesisState config (by decide) 0 default 0 bodyRoot with
    validators := .ofData #[validator 200, validator 200, validator 200,
      validator 100, validator 200] (by decide)
    balances := ⟨#[200, 200, 200, 100, 200], by decide⟩ }

/-- Validator 3 is the only active validator outside the honest set. -/
def honest : Set ValidatorIndex := {0, 1, 2, 4}

instance instDecidableHonest : DecidablePred (· ∈ honest) := fun v =>
  inferInstanceAs (Decidable (v ∈ ({0, 1, 2, 4} : Set ValidatorIndex)))

/-- The initialization satisfies the state-transition invariant for every body root. -/
theorem invariant (root : Root) : Invariant (state root) where
  balancesMatch := by rfl
  exitsOrdered := by
    intro v member
    change v ∈ #[validator 200, validator 200, validator 200, validator 100, validator 200]
      at member
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
  ordered := by
    change (0 : UInt64) ≤ 0 ∧ (0 : UInt64) ≤ 0
    decide
  settled := by
    -- The header root has no effect on the epoch of a state.
    change JustifiedSettled (state default)
    unfold JustifiedSettled
    decide
  aligned _ := by
    intro v member
    change v ∈ #[validator 200, validator 200, validator 200, validator 100, validator 200]
      at member
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide

/-- All five positions of the registry are active. -/
theorem active_voters (root : Root) : activeVoters (state root) = {0, 1, 2, 3, 4} := by
  -- Activity depends on the registry and epoch, not the header root.
  change activeVoters (state default) = _
  decide

/-- The initial stake is 900 Gwei, of which 100 Gwei is Byzantine. -/
theorem stakes (root : Root) :
    stake (fun v => balanceAt (state root) v.toNat) (activeVoters (state root)) = 900 ∧
    stake (fun v => balanceAt (state root) v.toNat)
      {v ∈ quorumVoters (state root) | v ∉ honest} = 100 := by
  -- None of the counted fields reads the header root.
  change stake (fun v => balanceAt (state default) v.toNat) (activeVoters (state default)) = 900 ∧
    stake (fun v => balanceAt (state default) v.toNat)
      {v ∈ quorumVoters (state default) | v ∉ honest} = 100
  decide

/-- The global Byzantine stake fits a 12-percent bound, strictly below one third. -/
theorem byzantine_stake (root : Root) :
    100 * stake (fun v => balanceAt (state root) v.toNat)
      {v ∈ quorumVoters (state root) | v ∉ honest} ≤ 12 * 900 := by
  rw [(stakes root).2]
  decide

/-- The mixed pair meets the separate 34-percent committee bound.

This is not the global Byzantine bound: 34 percent is greater than one third. -/
theorem mixed_committee_byzantine_stake (root : Root) :
    ByzantineStakeAtMost (fun v => balanceAt (state root) v.toNat) {3, 4} honest 34 100 := by
  change 0 < 100 ∧ 100 * 100 ≤ 34 * 300
  decide

/-- The last committee pairs the Byzantine validator with an honest validator of twice its stake. -/
theorem committees (root : Root) :
    getBeaconCommittee (state root) 0 0 = .ok #[0] ∧
    getBeaconCommittee (state root) 1 0 = .ok #[1] ∧
    getBeaconCommittee (state root) 2 0 = .ok #[2] ∧
    getBeaconCommittee (state root) 3 0 = .ok #[3, 4] := by
  -- Zero shuffle rounds leave registry order unchanged, independently of the seed.
  change getBeaconCommittee (state default) 0 0 = .ok #[0] ∧
    getBeaconCommittee (state default) 1 0 = .ok #[1] ∧
    getBeaconCommittee (state default) 2 0 = .ok #[2] ∧
    getBeaconCommittee (state default) 3 0 = .ok #[3, 4]
  decide +kernel

/-- The preset meets the lookahead bundle and its balance alignment requirements. -/
theorem parameters :
    MaxEffectiveBalancesAligned preset ∧
    1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat ∧ 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat ∧
    preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat ∧
    3 * 12 < 100 := by
  unfold MaxEffectiveBalancesAligned
  decide

end EthLib.Consensus.Models.Network.FiveValidatorWitness
