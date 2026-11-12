module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSafety
public import EthLib.Consensus.Transition.Genesis
public import EthLib.Serialization.Proofs.Ssz.Typed.Root
-- The committee certificates reduce the derived equality decision procedure for Except.
import all Batteries.Data.Except
-- A zero-round shuffle reads the body of Array.range to enumerate the registry positions.
import all Init.Data.Array.Basic
-- Hash certificates unfold SSZ's mutual definitions and check each SHA-256 call in the kernel.
import all EthLib.Serialization.Ssz.Merkle.Merkleize
import all EthLib.Serialization.Ssz.Codec.Root
import all EthLib.Serialization.Ssz.Codec.Serialize
import Lean
public meta import Lean
meta import EthLib.Serialization.Ssz.Codec.Root

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
    {horizon : Epoch} {limit : ℕ} (unique : OneJustifiedPerEpoch e horizon limit)
    (started : e.startTime ≤ limit)
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
  exact unique u caller u caller 0 0 started started _ _ (atStart ▸ stateJustified)
    (atStart ▸ storeJustified) (by simpa [justified] using sameEpoch)
    (sameEpoch ▸ within)

/-- A same-epoch anchor checkpoint cannot name the anchor's excluded parent. -/
theorem Execution.false_of_anchor_checkpoint_parent
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) {u : ValidatorIndex} (caller : u ∈ J)
    {horizon : Epoch} {limit : ℕ} (unique : OneJustifiedPerEpoch e horizon limit)
    (sameEpoch : anchorState.currentJustifiedCheckpoint.epoch = getCurrentEpoch anchorState)
    (positive : 0 < anchorState.currentJustifiedCheckpoint.epoch)
    (within : getCurrentEpoch anchorState ≤ horizon)
    (parent : anchorState.currentJustifiedCheckpoint.root = anchorBlock.parentRoot)
    (started : e.startTime ≤ limit)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none) : False := by
  obtain ⟨root, _, held, _, justified, _⟩ := getForkchoiceStore_anchor anchored
  have same := e.anchor_currentJustified_eq_of_oneJustifiedPerEpoch anchored start caller
    unique started sameEpoch positive within
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
    {horizon : Epoch} {limit : ℕ} (unique : OneJustifiedPerEpoch e horizon limit)
    (sound : Invariant anchorState) (epochZero : getCurrentEpoch anchorState = 0)
    (parent : anchorState.currentJustifiedCheckpoint.root = anchorBlock.parentRoot)
    (started : e.startTime ≤ limit)
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
  have same := unique u caller u caller 0 0 started started
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
    {limit : ℕ} (committees : CommitteesFollow e limit)
    {w : ValidatorIndex} (honest : w ∈ J)
    {k : ℕ} {head : ForkChoiceNode} {headState : BeaconState preset fork}
    {current : Epoch} {v : ValidatorIndex} {attestation : Attestation preset fork}
    {targetState : BeaconState preset fork}
    (bounded : (e.world k).time ≤ limit)
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
    committees.common w honest k bounded head headState current v attestation targetState
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

/-- Common initial stores and one possible sent block give agreement at every held root.

A block from the initial store remains at its root in every honest store.

Any other held block came from a message, and all such messages carry the same block.

No hash inequality is needed, even if the sent block collides with an initial root.

This does not prove agreement when different colliding blocks can be sent. -/
theorem Execution.oneBlockPerRoot_of_single_sent_block {anchor : Store preset fork}
    {block : BeaconBlock preset fork} {limit : ℕ}
    (start : ∀ w ∈ J, e.start w = anchor)
    (sent : ∀ n, (e.world n).time ≤ limit → ∀ signed,
      .block signed ∈ (e.world n).sent → signed.message = block) :
    OneBlockPerRoot e limit := by
  intro v hv u hu n k boundedN boundedK root left right foundLeft foundRight
  rcases e.exists_signed_of_blocks hv foundLeft with old | ⟨sb, pre, post, seen, same, _⟩
  · -- Every honest validator starts with this entry and retains it.
    have initial : ((e.world 0).state u).blocks[root]? = some left := by
      change (e.start u).blocks[root]? = some left
      rw [start u hu, ← start v hv]
      exact old.1
    have retained := e.blocks_of_le (Nat.zero_le k) initial
    exact Option.some.inj (retained.symm.trans foundRight)
  · have leftIs : left = block := same ▸ sent n boundedN sb (e.view_subset_sent n v seen)
    rcases e.exists_signed_of_blocks hu foundRight with old | ⟨sb', pre', post', seen', same', _⟩
    · -- An initial entry in the other store also wins over any colliding message.
      have initial : ((e.world 0).state v).blocks[root]? = some right := by
        change (e.start v).blocks[root]? = some right
        rw [start v hv, ← start u hu]
        exact old.1
      have retained := e.blocks_of_le (Nat.zero_le n) initial
      exact Option.some.inj (foundLeft.symm.trans retained)
    · have rightIs : right = block :=
        same' ▸ sent k boundedK sb' (e.view_subset_sent k u seen')
      exact leftIs.trans rightIs.symm

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

/-- Every world at or before the final prefix time belongs to that finite prefix.

The tail advances time strictly, so a bounded premise needs no tail-state case. -/
theorem index_le_length_of_time_le (steps : List (Event ν μ σ)) (lastTime : ℕ)
    (init : World ν μ σ) (clock : (steps.foldl World.apply init).time = lastTime)
    (n : ℕ) (bounded : (worldAt init (events steps lastTime) n).time ≤ lastTime) :
    n ≤ steps.length := by
  by_contra beyond
  have index : n = steps.length + (n - steps.length) := by omega
  rw [index, world_tail steps lastTime init clock] at bounded
  change lastTime + (n - steps.length) ≤ lastTime at bounded
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

The fork is phase0, with a small custom preset rather than mainnet parameters.

The modified minimal preset has zero shuffle rounds.

The modified minimal config has zero proposer boost and a committee threshold of 34 percent.

The committee certificates use kernel `decide`, which adds no compiler-trusting axiom.

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

/-- Any registered committee range pairing validator 3 with validator 4 meets the bound.

Additional honest members can only increase the total stake. -/
theorem committee_byzantine_of_paired (root : Root) (members : Finset ValidatorIndex)
    (registered : members ⊆ {0, 1, 2, 3, 4}) (paired : 3 ∈ members → 4 ∈ members) :
    ByzantineStakeAtMost (fun v => balanceAt (state root) v.toNat) members honest 34 100 := by
  -- Only validator 3 can contribute Byzantine stake among these registered positions.
  have subset : {v ∈ members | v ∉ honest} ⊆ ({3} : Finset ValidatorIndex) := by
    intro v member
    obtain ⟨inside, dishonest⟩ := Finset.mem_filter.mp member
    have known := registered inside
    simp only [Finset.mem_insert, Finset.mem_singleton] at known
    rcases known with rfl | rfl | rfl | rfl | rfl <;> simp_all [honest]
  refine ⟨by decide, ?_⟩
  by_cases present : 3 ∈ members
  · have minimum : ({3, 4} : Finset ValidatorIndex) ⊆ members := by
      intro v member
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl
      · exact present
      · exact paired present
    -- The pair contributes 300 Gwei, against at most 100 Gwei of Byzantine stake.
    have lower := stake_mono (w := fun v => balanceAt (state root) v.toNat) minimum
    have upper := stake_mono (w := fun v => balanceAt (state root) v.toNat) subset
    change 300 ≤ stake (fun v => balanceAt (state root) v.toNat) members at lower
    change stake (fun v : ValidatorIndex => balanceAt (state root) v.toNat) _ ≤ 100 at upper
    omega
  · have empty : {v ∈ members | v ∉ honest} = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v member
      have same := Finset.mem_singleton.mp (subset member)
      subst v
      exact present (Finset.mem_filter.mp member).1
    rw [empty, stake_empty]
    omega

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

open Serialization.Ssz

/-- An empty phase0 body supplies the header of the initial state. -/
def body : BeaconBlockBody preset .phase0 := emptyBody (by decide)

/-- The genesis block stores the root of the initial state. -/
def anchorBlock (stateRoot : Root) : BeaconBlock preset .phase0 :=
  ⟨0, 0, default, stateRoot, body⟩

set_option maxRecDepth 10000 in
/-- The five-validator state has a matching anchor and an initialized store.

SSZ totality supplies the roots without evaluating their bytes.

This proves neither that these roots are nonzero nor that different blocks have different roots. -/
theorem exists_initialization :
    ∃ (bodyRoot stateRoot anchorRoot : Root) (anchor : Store preset .phase0),
      SszType.hashTreeRoot body = .ok bodyRoot ∧
      SszType.hashTreeRoot (state bodyRoot) = .ok stateRoot ∧
      SszType.hashTreeRoot (anchorBlock stateRoot) = .ok anchorRoot ∧
      getForkchoiceStore config (state bodyRoot) (anchorBlock stateRoot) = .ok anchor := by
  -- The lawful state and block instances require positive lengths for their fixed vectors.
  let : NeZero preset.BYTES_PER_LOGS_BLOOM.toNat := ⟨by decide⟩
  let : NeZero preset.SYNC_COMMITTEE_SIZE.toNat := ⟨by decide⟩
  let : NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat := ⟨by decide⟩
  let : NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat := ⟨by decide⟩
  let : NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat := ⟨by decide⟩
  let : NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat := ⟨by decide⟩
  let : NeZero ((preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat) :=
    ⟨by decide⟩
  let : NeZero preset.PTC_SIZE.toNat := ⟨by decide⟩
  let : NeZero (2 * preset.SLOTS_PER_EPOCH.toNat) := ⟨by decide⟩
  let : NeZero ((preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat) :=
    ⟨by decide⟩
  let : NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat := ⟨by decide⟩
  obtain ⟨bodyRoot, bodyHashed⟩ := SszType.hashTreeRoot_total body
  obtain ⟨stateRoot, stateHashed⟩ := SszType.hashTreeRoot_total (state bodyRoot)
  obtain ⟨anchorRoot, anchorHashed⟩ := SszType.hashTreeRoot_total (anchorBlock stateRoot)
  refine ⟨bodyRoot, stateRoot, anchorRoot, ?_⟩
  suffices existsStore : ∃ anchor,
      getForkchoiceStore config (state bodyRoot) (anchorBlock stateRoot) = .ok anchor by
    obtain ⟨anchor, anchored⟩ := existsStore
    exact ⟨anchor, bodyHashed, stateHashed, anchorHashed, anchored⟩
  -- Initialization checks equality with the state root that totality supplied.
  have clock : computeTimeAtSlotMs config
      (secondsToMilliseconds (state bodyRoot).genesisTime) (state bodyRoot).slot = .ok 0 := by
    rfl
  simp only [getForkchoiceStore, stateHashed, anchorHashed, clock, Except.mapError,
    bind, Except.bind]
  have sameRoot : (anchorBlock stateRoot).stateRoot = stateRoot := rfl
  simp only [sameRoot, ne_eq, not_true_eq_false, ↓reduceIte]
  exact ⟨_, rfl⟩

/-! These certificates compute candidate bytes outside the kernel, then prove them inside it.

The candidate computation is not trusted: each result needs a kernel-checked equality proof.

Repeated SSZ subroots reuse those proofs instead of rebuilding their reduction traces. -/

set_option Elab.async false

open Lean Meta Sym Tactic.Cbv Cryptography.Hash in
local cbv_simproc cbv_eval sha256Certificate (Sha256.hash _) := fun e => do
  let_expr Sha256.hash bytes := e | return .rfl
  let_expr ByteArray.mk data := bytes | return .rfl
  let_expr Array.mk _ items := data | return .rfl
  let some elems := getListLitElems items | return .rfl
  let some values := elems.mapM (m := Option) (fun x => (Sym.getUInt8Value? x).run) |
    return .rfl
  let hashed := Sha256.hash ⟨values⟩
  let array := mkApp2 (mkConst ``Array.mk [0]) (mkConst ``UInt8) (toExpr hashed.data.toList)
  let result ← share <| mkApp (mkConst ``ByteArray.mk) array
  let expected ← liftM <| Meta.mkEq e result
  -- Reflexivity checks the actual SHA-256 reduction, not the candidate generator.
  let name ← liftM <| Meta.withFreshCache do
    let proof ← Meta.mkEqRefl result
    withOptions (Elab.async.set · false) <| mkAuxLemma [] expected proof
  return .step result (mkConst name)

private theorem zero_step (n : Nat) (previous next : Array UInt8)
    (ih : zeroSubtreeM (m := Id) Cryptography.Hash.Sha256.hash n = previous)
    (hashed : Cryptography.Hash.Sha256.hash ⟨previous ++ previous⟩ = ⟨next⟩) :
    zeroSubtreeM (m := Id) Cryptography.Hash.Sha256.hash (n + 1) = next := by
  change (Cryptography.Hash.Sha256.hash
    ⟨(zeroSubtreeM (m := Id) Cryptography.Hash.Sha256.hash n).run ++
      (zeroSubtreeM (m := Id) Cryptography.Hash.Sha256.hash n).run⟩).data = next
  rw [ih]
  exact congrArg ByteArray.data hashed

open Lean Meta Sym Tactic.Cbv Cryptography.Hash in
local cbv_simproc cbv_eval zeroCertificate (zeroSubtreeM Sha256.hash _) := fun e => do
  let_expr zeroSubtreeM _ _ _ count := e | return .rfl
  let some depth := Sym.getNatValue? count | return .rfl
  let literal (xs : Array UInt8) :=
    mkApp2 (mkConst ``Array.mk [0]) (mkConst ``UInt8) (toExpr xs.toList)
  let mut bytes : Array UInt8 := Array.replicate 32 0
  let mut value := literal bytes
  let mut proof ← liftM <| Meta.mkEqRefl value
  -- Each level uses the previous certificate, so padding costs one hash per level.
  for i in [:depth] do
    let next := (Sha256.hash ⟨bytes ++ bytes⟩).data
    let nextValue := literal next
    let input ← liftM <| mkAppM ``HAppend.hAppend #[value, value]
    let hash := mkApp (mkConst ``Sha256.hash) (mkApp (mkConst ``ByteArray.mk) input)
    let expected ← liftM <| Meta.mkEq hash (mkApp (mkConst ``ByteArray.mk) nextValue)
    let hashRefl ← liftM <| Meta.mkEqRefl (mkApp (mkConst ``ByteArray.mk) nextValue)
    let hashName ← liftM <|
      withOptions (Elab.async.set · false) <| mkAuxLemma [] expected hashRefl
    let step := mkApp5 (mkConst ``zero_step) (mkNatLit i) value nextValue proof (mkConst hashName)
    let type ← liftM <| Meta.inferType step
    let name ← liftM <| withOptions (Elab.async.set · false) <| mkAuxLemma [] type step
    value := nextValue
    proof := mkConst name
    bytes := next
  return .step (← share value) proof

private theorem depthFor_power_two (n : Nat) : depthFor (2 ^ n) = n := by
  apply Nat.le_antisymm (depthFor_le_of_le_two_pow (Nat.le_refl _))
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (le_two_pow_depthFor _)

open Lean Meta Sym Tactic.Cbv in
local cbv_simproc cbv_eval depthCertificate (depthFor _) := fun e => do
  let_expr depthFor count := e | return .rfl
  let some value := Sym.getNatValue? count | return .rfl
  let exponent := value.log2
  if value != 2 ^ exponent then return .rfl
  let result ← share (mkNatLit exponent)
  return .step result (mkApp (mkConst ``depthFor_power_two) result)

open Lean Meta Sym Tactic.Cbv in
private meta def literalDesc : Nat → Expr → Option Desc
  | 0, _ => none
  | fuel + 1, e => do
    let args := e.getAppArgs
    match e.getAppFn.constName! with
    | ``Desc.bool => return .bool
    | ``Desc.uint => return .uint (← (Sym.getNatValue? args[0]!).run)
    | ``Desc.byteVector => return .byteVector (← (Sym.getNatValue? args[0]!).run)
    | ``Desc.byteList => return .byteList (← (Sym.getNatValue? args[0]!).run)
    | ``Desc.bitVector => return .bitVector (← (Sym.getNatValue? args[0]!).run)
    | ``Desc.bitList => return .bitList (← (Sym.getNatValue? args[0]!).run)
    | ``Desc.vector =>
      return .vector (← literalDesc fuel args[0]!) (← (Sym.getNatValue? args[1]!).run)
    | ``Desc.list =>
      return .list (← literalDesc fuel args[0]!) (← (Sym.getNatValue? args[1]!).run)
    | ``Desc.container =>
      return .container
        ((← (← getListLitElems args[0]!).mapM Sym.getStringValue?).toList)
        ((← (← getListLitElems args[1]!).mapM (literalDesc fuel)).toList)
    | _ => none

open Lean Meta Sym Tactic.Cbv in
private meta def literalValue : Nat → Expr → Option Value
  | 0, _ => none
  | fuel + 1, e => do
    let a := e.appArg!
    match e.getAppFn.constName! with
    | ``Value.bool => return .bool (← (Sym.getBoolValue? a).run)
    | ``Value.uint => return .uint (← (Sym.getNatValue? a).run)
    | ``Value.bytes => do
      let_expr Array.mk _ items := a | none
      return .bytes (← (← getListLitElems items).mapM (fun x => (Sym.getUInt8Value? x).run))
    | ``Value.bits => do
      let_expr Array.mk _ items := a | none
      return .bits (← (← getListLitElems items).mapM (fun x => (Sym.getBoolValue? x).run))
    | ``Value.seq => return .seq ((← (← getListLitElems a).mapM (literalValue fuel)).toList)
    | _ => none

open Lean Meta Sym Tactic.Cbv Cryptography.Hash in
local cbv_simproc cbv_eval rootCertificate (hashTreeRootAtM _ _ _ _) := fun e => do
  let_expr hashTreeRootAtM _ _ _ budget shape input := e | return .rfl
  let some depth := Sym.getNatValue? budget | return .rfl
  -- The recursive evaluation handles this node itself and certifies only smaller children.
  if depth >= (← getOptions).get `witness.rootBudget 1000 then return .rfl
  let some desc := literalDesc 32 shape | return .rfl
  let some data := literalValue 32 input | return .rfl
  let output := (hashTreeRootAtM (m := Id) (Hasher.ofHash Sha256.hash) depth desc data).run
  let .ok bytes := output | return .rfl
  let array := mkApp2 (mkConst ``Array.mk [0]) (mkConst ``UInt8) (toExpr bytes.toList)
  let value := mkApp3 (mkConst ``Except.ok [0, 0]) (mkConst ``Err)
    (mkApp (mkConst ``Array [0]) (mkConst ``UInt8)) array
  let expected ← liftM <| Meta.mkEq e value
  -- Only an already checked equality may bypass proof construction.
  let env ← getEnv
  if let some (name, _) := (auxLemmasExt.getState env).lemmas.find?
      { type := expected, isPrivate := !env.isExporting, defeq := false } then
    return .step (← share value) (mkConst name)
  let reduced ← liftM <| Meta.withFreshCache <|
    withOptions (·.set `witness.rootBudget depth) <| cbvEntry e
  let .step _ proof .. := reduced | return .rfl
  let name ← liftM <| Meta.withFreshCache <|
    withOptions (Elab.async.set · false) <| mkAuxLemma [] expected proof
  return .step (← share value) (mkConst name)

attribute [local cbv_eval] hashTreeRootAtM.eq_def depthFor.eq_def SszType.hashTreeRoot_eq
  zeroSubtree_eq layoutChunksAtM.eq_def serialize.eq_def serializeSequence.eq_def
  serializeStruct.eq_def serializeEach.eq_def serializeEachFrom.eq_def serializeFields.eq_def
  serializeFieldsFrom.eq_def

@[local cbv_eval] private theorem hasher_certificate :
    sha256Hasher = Hasher.ofHash Cryptography.Hash.Sha256.hash := ofHash_sha256.symm

/-- The root certified below for the witness's empty phase0 body. -/
def bodyRoot : Root := ⟨#[204, 182, 36, 96, 105, 43, 224, 236, 129, 59, 86, 190,
  151, 246, 138, 130, 207, 87, 171, 193, 2, 226, 123, 244, 158, 191, 65, 144, 255, 34, 238, 221],
  by decide⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
set_option cbv.maxSteps 10000000 in
/-- The displayed body root agrees with the SSZ definition, checked by the kernel. -/
theorem body_root : SszType.hashTreeRoot body = .ok bodyRoot := by
  let : NeZero preset.BYTES_PER_LOGS_BLOOM.toNat := ⟨by decide⟩
  let : NeZero preset.SYNC_COMMITTEE_SIZE.toNat := ⟨by decide⟩
  let : NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat := ⟨by decide⟩
  let : NeZero preset.PTC_SIZE.toNat := ⟨by decide⟩
  let : NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat := ⟨by decide⟩
  rw [SszType.hashTreeRoot_eq]
  cbv

/-- The root certified below for the five-validator state with the certified body root. -/
def stateRoot : Root := ⟨#[0, 37, 86, 15, 195, 37, 68, 199, 169, 148, 187, 41, 148, 247, 69, 176,
  140, 110, 165, 78, 4, 31, 167, 109, 249, 126, 200, 58, 172, 5, 30, 84], by decide⟩

-- These normal forms avoid carrying the state constructor through every reduction step.

-- The two reflexivity proofs below check them against the existing typed SSZ definitions.
private def stateValue (root : Root) : Value :=
  let zero := Value.bytes (Array.replicate 32 0)
  let checkpoint := Value.seq [.uint 0, zero]
  let validatorValue (balance : Nat) := Value.seq
    [.bytes (Array.replicate 48 0), zero, .uint balance, .bool false, .uint 0, .uint 0,
      .uint 18446744073709551615, .uint 18446744073709551615]
  .seq [.uint 0, zero, .uint 0,
    .seq [.bytes #[0, 0, 0, 1], .bytes #[0, 0, 0, 1], .uint 0],
    .seq [.uint 0, .uint 0, zero, zero, .bytes root.toArray],
    .seq (List.replicate 8 zero), .seq (List.replicate 8 zero), .seq [],
    .seq [zero, .uint 0, zero], .seq [], .uint 0,
    .seq ([200, 200, 200, 100, 200].map validatorValue),
    .seq ([200, 200, 200, 100, 200].map Value.uint),
    .seq (List.replicate 8 zero), .seq (List.replicate 8 (.uint 0)), .seq [], .seq [],
    .bits #[false, false, false, false], checkpoint, checkpoint, checkpoint]

private def stateDesc : Desc :=
  let uint := Desc.uint 8
  let root := Desc.byteVector 32
  let checkpoint := Desc.container ["epoch", "root"] [uint, root]
  let eth1 := Desc.container ["deposit_root", "deposit_count", "block_hash"] [root, uint, root]
  let pending := Desc.container ["aggregation_bits", "data", "inclusion_delay", "proposer_index"]
    [.bitList 2048,
      .container ["slot", "index", "beacon_block_root", "source", "target"]
        [uint, uint, root, checkpoint, checkpoint], uint, uint]
  .container
    ["genesis_time", "genesis_validators_root", "slot", "fork", "latest_block_header",
      "block_roots", "state_roots", "historical_roots", "eth1_data", "eth1_data_votes",
      "eth1_deposit_index", "validators", "balances", "randao_mixes", "slashings",
      "previous_epoch_attestations", "current_epoch_attestations", "justification_bits",
      "previous_justified_checkpoint", "current_justified_checkpoint", "finalized_checkpoint"]
    [uint, root, uint,
      .container ["previous_version", "current_version", "epoch"]
        [.byteVector 4, .byteVector 4, uint],
      .container ["slot", "proposer_index", "parent_root", "state_root", "body_root"]
        [uint, uint, root, root, root],
      .vector root 8, .vector root 8, .list root 16777216, eth1, .list eth1 16, uint,
      .list (.container ["pubkey", "withdrawal_credentials", "effective_balance", "slashed",
        "activation_eligibility_epoch", "activation_epoch", "exit_epoch", "withdrawable_epoch"]
        [.byteVector 48, root, uint, .bool, uint, uint, uint, uint]) 8,
      .list uint 8, .vector root 8, .vector uint 8, .list pending 512, .list pending 512,
      .bitVector 4, checkpoint, checkpoint, checkpoint]

set_option maxRecDepth 10000 in
private theorem state_value (root : Root) : SszType.toValue (state root) = stateValue root := by
  rfl

set_option maxRecDepth 10000 in
private theorem state_desc : SszType.desc (BeaconState preset .phase0) = stateDesc := by rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
set_option cbv.maxSteps 10000000 in
/-- The actual initial state has the displayed root, with no hash assumption. -/
theorem state_root : SszType.hashTreeRoot (state bodyRoot) = .ok stateRoot := by
  let : NeZero preset.BYTES_PER_LOGS_BLOOM.toNat := ⟨by decide⟩
  let : NeZero preset.SYNC_COMMITTEE_SIZE.toNat := ⟨by decide⟩
  let : NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat := ⟨by decide⟩
  let : NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat := ⟨by decide⟩
  let : NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat := ⟨by decide⟩
  let : NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat := ⟨by decide⟩
  let : NeZero ((preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat) :=
    ⟨by decide⟩
  let : NeZero preset.PTC_SIZE.toNat := ⟨by decide⟩
  let : NeZero (2 * preset.SLOTS_PER_EPOCH.toNat) := ⟨by decide⟩
  let : NeZero ((preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat) :=
    ⟨by decide⟩
  let : NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat := ⟨by decide⟩
  rw [SszType.hashTreeRoot_eq, state_value, state_desc]
  cbv

/-- The anchor's state root is nonzero because its second byte is 37. -/
theorem stateRoot_ne_zero : stateRoot ≠ Vector.replicate 32 0 := by decide

/-- The root of the genesis block, with the certified state root. -/
def anchorRoot : Root := ⟨#[55, 33, 215, 25, 110, 21, 184, 68, 214, 44, 44, 231, 191, 73,
  184, 207, 124, 7, 161, 74, 206, 139, 115, 214, 204, 138, 1, 138, 62, 9, 235, 207], by decide⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
set_option cbv.maxSteps 1000000 in
/-- Replacing the body by its certified root leaves only the header to hash. -/
theorem anchor_root : SszType.hashTreeRoot (anchorBlock stateRoot) = .ok anchorRoot := by
  rw [← BeaconBlock.hashTreeRoot_header (block := anchorBlock stateRoot) body_root,
    SszType.hashTreeRoot_eq]
  cbv

/-- The anchor root differs from its zero parent root. -/
theorem anchorRoot_ne_zero : anchorRoot ≠ Vector.replicate 32 0 := by decide

/-- The initialized store, written out so later state certificates need not recompute its hashes. -/
def anchor : Store preset .phase0 where
  timeMs := 0
  genesisTimeMs := 0
  justifiedCheckpoint := ⟨0, anchorRoot⟩
  finalizedCheckpoint := ⟨0, anchorRoot⟩
  unrealizedJustifiedCheckpoint := ⟨0, anchorRoot⟩
  unrealizedFinalizedCheckpoint := ⟨0, anchorRoot⟩
  proposerBoostRoot := Vector.replicate 32 0
  equivocatingIndices := []
  blocks := Std.TreeMap.empty.insert anchorRoot (anchorBlock stateRoot)
  blockStates := Std.TreeMap.empty.insert anchorRoot (state bodyRoot)
  blockTimeliness := ∅
  ptcTimeliness := fun _ => Std.TreeMap.empty.insert anchorRoot true
  checkpointStates := Std.TreeMap.empty.insert ⟨0, anchorRoot⟩ (state bodyRoot)
  latestMessages := ∅
  unrealizedJustifications := Std.TreeMap.empty.insert anchorRoot ⟨0, anchorRoot⟩
  payloads := fun _ => ∅
  payloadTimelinessVote := fun _ =>
    Std.TreeMap.empty.insert anchorRoot (Vector.replicate _ none)
  payloadDataAvailabilityVote := fun _ =>
    Std.TreeMap.empty.insert anchorRoot (Vector.replicate _ none)
  inclusionLists := fun _ => .empty
  payloadInclusionListSatisfaction := fun _ => ∅

/-- Initialization accepts the actual body, state and block roots without a hash hypothesis. -/
theorem initialized :
    getForkchoiceStore config (state bodyRoot) (anchorBlock stateRoot) = .ok anchor := by
  simp only [getForkchoiceStore, state_root, anchor_root, Except.mapError, bind, Except.bind]
  have sameRoot : (anchorBlock stateRoot).stateRoot = stateRoot := rfl
  simp only [sameRoot, ne_eq, not_true_eq_false, ↓reduceIte]
  rfl

end EthLib.Consensus.Models.Network.FiveValidatorWitness
