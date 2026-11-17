module

public import EthLib.Consensus.Proofs.ForkChoice.BlockAgreement
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalStatements
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Indicators
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumReserve
public import EthLib.Consensus.Proofs.Transition.BalanceDrift
public import EthLib.Consensus.Proofs.Transition.BuilderPayments
public import EthLib.Consensus.Proofs.Transition.Trace
public import EthLib.Consensus.Proofs.Transition.Upgrade
public import EthLib.Consensus.Proofs.Transition.ValidatorCaps

/-!
# The quorum of a fast-confirmation call drifts by at most its reserve

A call of the fast confirmation rule reads the pulled-up head state of an honest store.

Its current target is the checkpoint of the store's epoch on the chain of the head.

A later state that counts the target is on the chain of a block of another honest store.

The quorum of the call drifts from the pulled-up head state to that later state.

The drift bound takes runs that start from one state at the start of the target's epoch.

This file builds those runs from the stores, and so bounds the drift of every call.

```text
  genesis ──▶ boundary ──edge──▶ middle ──tail──▶ pulled-up head state
                 │                  │
           start of epoch           └──────────────▶ later state of the receiver
```

- The boundary is right after the epoch transition, so the bands of hysteresis hold there.
- At most the target block, at the start of the epoch, lies between the boundary and the middle.
- The middle holds the queue of pending partial withdrawals of the target block.
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

/-- The drift of an honest voter set's stake between a call and a later state is within the reserve.

The call reads the pulled-up head state and the current target of an honest store.

The reserve reads the pulled-up head state and the state of the target block.

The later state is on the chain of a block that another honest store holds.

The checkpoint block of that chain for the target's epoch is the target.

The later state is the state of that block, or that state with more slots processed.

It is in the target's epoch or the next one, and within the horizon.

The voters are active at the call's state and not slashed at the later state.

With the count's `margin + quorumReserve`, the reserve cancels against this drift. -/
def QuorumDriftWithin (horizon : Epoch) (last : ℕ) : Prop :=
  ∀ u ∈ J, ∀ n (head : Root) (pulled anc : BeaconState preset fork) (target : Checkpoint),
    (e.world n).time ≤ last →
    ((e.world n).state u).getPulledUpHeadState config head = .ok pulled →
    ((e.world n).state u).getCurrentTarget config head = .ok target →
    ((e.world n).state u).blockStates[target.root]? = some anc →
    ∀ w ∈ J, ∀ k (root : Root) (rootState state : BeaconState preset fork),
    (e.world k).time ≤ last → ((e.world k).state w).blockStates[root]? = some rootState →
    ((e.world k).state w).getCheckpointBlock root target.epoch = .ok target.root →
    (state = rootState ∨ ∃ slot, processSlots config checks rootState slot = .ok state) →
    target.epoch ≤ getCurrentEpoch state →
    (getCurrentEpoch state).toNat ≤ target.epoch.toNat + 1 → getCurrentEpoch state ≤ horizon →
    ∀ (voters : Finset ValidatorIndex) (total pulledTotal : Gwei),
    (∀ v ∈ voters, v ∈ activeVoters pulled ∧ (slashedFlagAt state v.toNat).getD false = false) →
    getTotalActiveBalance state = .ok total → getTotalActiveBalance pulled = .ok pulledTotal →
    2 * total.toNat + 3 * stake (fun v => balanceAt pulled v.toNat) voters ≤
      2 * pulledTotal.toNat + 3 * stake (fun v => balanceAt state v.toNat) voters +
        quorumReserve config pulled anc

/-! ## Slots keep the queue of pending partial withdrawals

From Electra, only two steps of a block write the queue of pending partial withdrawals.

A withdrawal request appends an entry, and the withdrawals of the payload remove the paid ones.

No step of a slot or of an epoch writes it ([EIP-7251]).

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/

section Partials

variable {state after : BeaconState preset fork}

/-- Two states hold the same queue of pending partial withdrawals, from Electra. -/
private def PartialsSame (state after : BeaconState preset fork) : Prop :=
  ∀ electra : .pectra ≤ fork,
    after.pendingPartialWithdrawals electra = state.pendingPartialWithdrawals electra

private theorem PartialsSame.refl (state : BeaconState preset fork) : PartialsSame state state :=
  fun _ => rfl

private theorem PartialsSame.trans {first second third : BeaconState preset fork}
    (one : PartialsSame first second) (two : PartialsSame second third) :
    PartialsSame first third :=
  fun electra => (two electra).trans (one electra)

private theorem partialsSame_setValidatorAt {position : Nat} {validator : Validator}
    (set : state.setValidatorAt position validator = .ok after) : PartialsSame state after := by
  obtain ⟨_, rfl⟩ := setValidatorAt_ok set
  exact fun _ => rfl

private theorem partialsSame_setValidator {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) : PartialsSame state after :=
  partialsSame_setValidatorAt (by rwa [← setValidator_eq_setValidatorAt])

private theorem partialsSame_setBalance {index : ValidatorIndex} {balance : Gwei}
    (set : state.setBalance index balance = .ok after) : PartialsSame state after := by
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact fun _ => rfl

private theorem partialsSame_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : PartialsSame state after :=
  let ⟨_, set⟩ := increaseBalance_ok computed
  partialsSame_setBalance set

private theorem partialsSame_decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : PartialsSame state after :=
  let ⟨_, set⟩ := decreaseBalance_ok computed
  partialsSame_setBalance set

private theorem partialsSame_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    PartialsSame state after := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok computed
  · exact PartialsSame.refl _
  refine PartialsSame.trans ?_ (partialsSame_setValidator set)
  unfold exitQueue at queue
  split at queue
  · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at queue
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := queue
    exact fun _ => rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at queue
    obtain ⟨_, _, rfl, _⟩ := queue
    exact PartialsSame.refl _

private theorem partialsSame_addValidatorToRegistry {pubkey withdrawalCredentials amount}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    PartialsSame state after := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
    exact fun _ => rfl
  split at computed
  · cases computed
    exact fun _ => rfl
  · cases computed

/-- Keeping the queue satisfies the laws of the epoch steps. -/
private theorem partialsEpochFrameLaws : EpochFrameLaws (@PartialsSame preset fork) where
  refl := PartialsSame.refl
  trans := PartialsSame.trans
  setValidatorAt := fun set _ _ _ _ _ => partialsSame_setValidatorAt set
  increaseBalance := partialsSame_increaseBalance
  decreaseBalance := partialsSame_decreaseBalance
  initiateValidatorExit := partialsSame_initiateValidatorExit
  addValidatorToRegistry := fun computed _ => partialsSame_addValidatorToRegistry computed
  eth1DataVotes _ _ := fun _ => rfl
  inactivityScores _ _ := fun _ => rfl
  slashings _ _ := fun _ => rfl
  randaoMixes _ _ := fun _ => rfl
  historicalRoots _ _ := fun _ => rfl
  historicalSummaries _ _ := fun _ => rfl
  participationRecords _ := fun _ => rfl
  pendingDeposits _ _ _ := fun _ => rfl
  pendingConsolidations _ _ := fun _ => rfl
  syncCommittees _ _ _ := fun _ => rfl
  proposerLookahead _ _ := fun _ => rfl
  ptcWindow _ _ := fun _ => rfl

private theorem partialsSame_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) :
    PartialsSame state after := by
  obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · exact PartialsSame.refl _
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    exact fun _ => by rw [← rest]

/-- From Altair, the epoch transition keeps the queue. -/
private theorem partialsSame_processEpoch (altair : .altair ≤ fork)
    (computed : processEpoch config checks state = .ok after) : PartialsSame state after := by
  unfold processEpoch at computed
  simp only [altair, ↓reduceDIte] at computed
  obtain ⟨justified, rooted, justifiedOk, head, tail⟩ :=
    partialsEpochFrameLaws.processEpochAltair_rotationSplit
      (fun _ ok => by rw [processBuilderPendingPayments_eq ok]; exact fun _ => rfl) computed
  exact (partialsSame_processJustificationAndFinalization justifiedOk).trans <| head.trans <|
    (show PartialsSame rooted (processParticipationFlagUpdates rooted altair) from
      fun _ => rfl).trans tail

/-- One slot keeps the queue: it caches roots, and at the end of an epoch runs the transition. -/
private theorem partialsSame_advanceSlot (altair : .altair ≤ fork)
    (computed : advanceSlot config checks state = .ok after) : PartialsSame state after := by
  intro electra
  obtain ⟨next, cached, epoched, -, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  unfold epochIfLast at epochedOk
  split at epochedOk
  · exact partialsSame_processEpoch altair epochedOk electra
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    rfl

/-- From Altair, advancing to a later slot keeps the queue of pending partial withdrawals. -/
private theorem processSlots_pendingPartialWithdrawals (altair : .altair ≤ fork) {slot : Slot}
    (computed : processSlots config checks state slot = .ok after) : PartialsSame state after := by
  simp only [Consensus.processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨-, -, advanced⟩ := computed
  generalize slot.toNat - state.slot.toNat = count at advanced
  induction count generalizing state with
  | zero =>
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at advanced
    subst advanced
    exact PartialsSame.refl _
  | succ count step =>
    simp only [advanceSlots, bind_ok_iff] at advanced
    obtain ⟨next, nextOk, rest⟩ := advanced
    exact (partialsSame_advanceSlot altair nextOk).trans (step rest)

end Partials

/-! ## The bands of hysteresis at the start of an epoch -/

section Epochs

variable {state after : BeaconState preset fork}

/-- Right after the epoch transition, each effective balance lies within the bands of its balance.

The update of the effective balances puts them there.

The later stages of the epoch keep the validators and the balances.

The increment must be positive and at most the upward band. -/
private theorem hysteresis_of_epochTransition (bands : preset.IncrementWithinUpwardBand)
    (computed : processEpoch config checks state = .ok after) : Hysteresis after := by
  have trace := processEpoch_trace computed
  change EpochTrace _ ((EpochStage.prefixStages ++ [.payments]) ++
    [.effectiveBalances, .slashingsReset, .randaoReset, .history, .participation,
      .syncCommittees, .proposerLookahead, .ptcWindow]) _ _ at trace
  obtain ⟨_, -, tail⟩ := EpochTrace.append_iff.mp trace
  cases tail
  rename_i updated tail
  have last := balanceDrift_late tail
  exact (processEffectiveBalanceUpdates_hysteresis bands
    (EpochStage.action_cases.mp updated)).of_data (congrArg (·.data) last.1)
    (congrArg (·.data) last.2) fun _ => rfl

/-- A slot step that reaches the first slot of an epoch ends within the bands of hysteresis.

That step ran the epoch transition, and moving the slot on keeps the validators and balances. -/
private theorem hysteresis_of_advanceSlot (bands : preset.IncrementWithinUpwardBand)
    (computed : advanceSlot config checks state = .ok after)
    (boundary : after.slot % preset.SLOTS_PER_EPOCH = 0) : Hysteresis after := by
  obtain ⟨next, cached, epoched, -, -, epochOk, rfl⟩ := advanceSlot_ok computed
  simp only [epochIfLast, show next % preset.SLOTS_PER_EPOCH = 0 from boundary, ↓reduceIte]
    at epochOk
  exact (hysteresis_of_epochTransition bands epochOk).of_data rfl rfl fun _ => rfl

/-- The state at the first slot of an epoch, reached by slot steps, is within the bands.

The last slot step ran the epoch transition. -/
private theorem hysteresis_of_processSlots (bands : preset.IncrementWithinUpwardBand)
    {slot : Slot} (computed : processSlots config checks state slot = .ok after)
    (boundary : slot % preset.SLOTS_PER_EPOCH = 0) : Hysteresis after := by
  obtain ⟨later, reached⟩ := processSlots_slot computed
  simp only [Consensus.processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨-, -, advanced⟩ := computed
  have gap := UInt64.lt_iff_toNat_lt.mp later
  obtain ⟨count, counted⟩ : ∃ count, slot.toNat - state.slot.toNat = count + 1 :=
    ⟨slot.toNat - state.slot.toNat - 1, by omega⟩
  rw [counted] at advanced
  -- The last of the slot steps reaches the slot.
  clear counted gap later
  induction count generalizing state with
  | zero =>
    obtain ⟨_, first, rest⟩ := bind_ok_iff.mp advanced
    cases rest
    exact hysteresis_of_advanceSlot bands first (by rw [reached]; exact boundary)
  | succ count ih =>
    obtain ⟨_, first, rest⟩ := bind_ok_iff.mp advanced
    exact ih rest

end Epochs

/-- A run from genesis to a state at the first slot of an epoch passes the boundary state.

The boundary state is at the same slot, after the epoch transition and the upgrades of the slot.

Only blocks at that slot lead from the boundary state to the last state.

The bands of hysteresis hold at the boundary state.

Genesis is before Altair and the last state is at Fulu or later, so the run has a slot step.

The epoch transition of that step sets the bands.

An upgrade keeps them, since every effective balance is at most its cap. -/
private theorem run_boundaryState {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (bands : preset.IncrementWithinUpwardBand)
    (electraFloor : preset.MAX_EFFECTIVE_BALANCE = preset.MIN_ACTIVATION_BALANCE)
    (electraCap : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA) :
    ∀ {x : ForkedBeaconState preset}, Run config checks g x → x.fork < .glamsterdam →
      .fusaka ≤ x.fork → x.state.slot % preset.SLOTS_PER_EPOCH = 0 →
      ∃ boundary : BeaconState preset x.fork, boundary.slot = x.state.slot ∧
        Hysteresis boundary ∧ Nonempty (Run config checks g ⟨x.fork, boundary⟩) ∧
        Nonempty (Run config checks ⟨x.fork, boundary⟩ x) := by
  intro x run
  induction run with
  | nil =>
    intro _ fulu _
    obtain ⟨_, _, _, initialized⟩ := genesis
    obtain ⟨phase0, -⟩ := initializeBeaconStateFromEth1_ok initialized
    exact absurd (Nat.lt_of_le_of_lt fulu phase0) (by decide)
  | @snoc middle last pre step ih =>
    intro early fulu atStart
    cases step with
    | slot ok =>
      obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
      have middleEarly : middle.fork < .glamsterdam :=
        Nat.lt_of_le_of_lt (processUpgrades_fork_le (forked := ⟨middle.fork, advanced⟩) upgraded)
          early
      have kept : last.state.slot = advanced.slot := processUpgrades_slot upgraded
      have banded := hysteresis_of_advanceSlot bands advancedOk (kept ▸ atStart)
      -- The step before the upgrades keeps each effective balance at most its cap.
      have capped := advanceSlot_capped advancedOk
        (pre.effectiveBalance_capped genesis (UInt64.le_of_eq electraFloor) electraCap
          middleEarly)
      exact ⟨last.state, rfl,
        Hysteresis.upgrade (forked := ⟨middle.fork, advanced⟩) banded electraFloor electraCap
          capped upgraded,
        ⟨pre.snoc (.slot ok)⟩, ⟨.nil⟩⟩
    | block engine signed due ok =>
      have kept := processBlock_slot (applySignedBlock_ok ok).2.1
      obtain ⟨boundary, atSlot, banded, first, ⟨rest⟩⟩ := ih early fulu (kept ▸ atStart)
      exact ⟨boundary, atSlot.trans kept.symm, banded, first,
        ⟨rest.snoc (.block engine signed due ok)⟩⟩

/-! ## Runs along the chains of a store -/

/-- The slot is before the activation of each later fork. -/
private abbrev BeforeFork (config : Config) (fork : Fork) (slot : Slot) : Prop :=
  ∀ next ∈ config.nextFork fork, slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat

/-- The second state is at the same slot or later, and a run reaches it before the next fork. -/
private def RunsTo (config : Config) (checks : SignatureChecks)
    (first second : BeaconState preset fork) : Prop :=
  first.slot ≤ second.slot ∧
    (BeforeFork (preset := preset) config fork second.slot →
      Nonempty (Run config checks ⟨fork, first⟩ ⟨fork, second⟩))

private theorem RunsTo.refl (state : BeaconState preset fork) : RunsTo config checks state state :=
  ⟨UInt64.le_refl _, fun _ => ⟨.nil⟩⟩

private theorem RunsTo.trans {first second third : BeaconState preset fork}
    (one : RunsTo config checks first second) (two : RunsTo config checks second third) :
    RunsTo config checks first third := by
  refine ⟨UInt64.le_trans one.1 two.1, fun before => ?_⟩
  have middle : BeforeFork (preset := preset) config fork second.slot := fun next member =>
    Nat.lt_of_le_of_lt (UInt64.le_iff_toNat_le.mp two.1) (before next member)
  obtain ⟨left⟩ := one.2 middle
  obtain ⟨right⟩ := two.2 before
  exact ⟨left.append right⟩

/-- A block transition is a run. -/
private theorem RunsTo.ofTransition {first second : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    (transitioned : Consensus.stateTransition config checks engine first signed true = .ok second) :
    RunsTo config checks first second := by
  obtain ⟨lower, atBlock⟩ := stateTransition_slot transitioned
  refine ⟨atBlock ▸ UInt64.le_of_lt lower, fun before => ?_⟩
  obtain ⟨_, slots, due, applied, -⟩ := run_of_stateTransition transitioned (atBlock ▸ before)
  exact ⟨slots.snoc (.block engine signed due applied)⟩

/-- Slots processed up to a slot at or before a block, then the rest of its transition, run. -/
private theorem RunsTo.ofPrefix {first middle second : BeaconState preset fork} {slot : Slot}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    (prefixOk : processSlots config checks first slot = .ok middle)
    (atMost : slot ≤ signed.message.slot)
    (transitioned : Consensus.stateTransition config checks engine first signed true = .ok second) :
    RunsTo config checks middle second := by
  have middleSlot := (processSlots_slot prefixOk).2
  have secondSlot := (stateTransition_slot transitioned).2
  refine ⟨by rw [middleSlot, secondSlot]; exact atMost, fun before => ?_⟩
  rw [secondSlot] at before
  simp only [Consensus.stateTransition, bind_ok_iff] at transitioned
  obtain ⟨advanced, slotsOk, applied⟩ := transitioned
  have advancedSlot := (processSlots_slot slotsOk).2
  have due : upgradeDue config ⟨fork, advanced⟩ = false :=
    upgradeDue_of_before fun next scheduled => advancedSlot ▸ before next scheduled
  -- The slots after the prefix, if any, lead to the state the block applies to.
  obtain ⟨slots⟩ : Nonempty (Run config checks ⟨fork, middle⟩ ⟨fork, advanced⟩) := by
    rcases UInt64.lt_or_eq_of_le atMost with lower | same
    · obtain ⟨middle', middleOk, restOk⟩ :=
        processSlots_split (processSlots_slot prefixOk).1 lower slotsOk
      rw [Except.ok.inj (middleOk.symm.trans prefixOk)] at restOk
      exact run_of_processSlots restOk before
    · rw [← same] at slotsOk
      rw [Except.ok.inj (slotsOk.symm.trans prefixOk)]
      exact ⟨.nil⟩
  exact ⟨slots.snoc (.block engine signed due applied)⟩

variable {store : Store preset fork}

/-- A held state is at the slot of its block. -/
private theorem blockState_slot_eq (anchorSlot : anchorBlock.slot = anchorState.slot)
    (reachable : Store.Reachable config anchorState anchorBlock store) {root : Root}
    {block : BeaconBlock preset fork} {state : BeaconState preset fork}
    (found : store.blocks[root]? = some block)
    (stored : store.blockStates[root]? = some state) : state.slot = block.slot := by
  obtain ⟨kept, keptFound, isAnchor, notAnchor⟩ := reachable.blockStatesFromParents found
  rw [stored, Option.some.injEq] at keptFound
  subst keptFound
  by_cases same : block = anchorBlock
  · rw [isAnchor same, same, anchorSlot]
  · obtain ⟨_, _, _, _, -, message, -, transition⟩ := notAnchor same
    rw [(stateTransition_slot transition).2, message]

/-- In a store built with one setting of the checks, a run reaches each held state from the anchor.

Each held state must be before the next fork. -/
private theorem run_of_held (forward : Store.ForwardReachableWith config checks anchorState
      anchorBlock store)
    (before : ∀ (root : Root) (state : BeaconState preset fork),
      store.blockStates[root]? = some state → BeforeFork (preset := preset) config fork state.slot)
    {root : Root} {state : BeaconState preset fork}
    (stored : store.blockStates[root]? = some state) :
    Nonempty (Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩) := by
  refine forward.reachable.blockState_induction forward.blockStatesFromParents
    (fun _ state => Nonempty (Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩))
    (fun _ _ => ⟨.nil⟩) (fun root _ _ _ _ _ _ _ held _ ok _ _ transitioned previous => ?_) stored
  subst ok
  obtain ⟨pre⟩ := previous
  obtain ⟨last⟩ := (RunsTo.ofTransition transitioned).2 (before root _ held)
  exact ⟨pre.append last⟩

/-- A slot of an epoch within the horizon is before the next fork. -/
private theorem beforeFork_of_epoch {horizon : Epoch}
    (window : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) {slot : Slot}
    (inside : slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ horizon.toNat) :
    BeforeFork (preset := preset) config fork slot := fun next member =>
  (Nat.div_lt_iff_lt_mul positive).mp (Nat.lt_of_le_of_lt inside (window next member))

/-- The current epoch of a state, in natural numbers. -/
private theorem toNat_getCurrentEpoch (state : BeaconState preset fork) :
    (getCurrentEpoch state).toNat = state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
  simp only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div]

/-- A store whose epoch is within the horizon holds states before the next fork.

Its current slot is at or after each held state, and in an epoch within the horizon. -/
private theorem held_beforeFork {horizon : Epoch}
    (window : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) (slots : 0 < config.SLOT_DURATION_MS)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (bounded : ∀ epoch, store.getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon) :
    (∀ epoch, store.getCurrentStoreEpoch config = .ok epoch →
      ∀ slot : Slot, slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ epoch.toNat →
        BeforeFork (preset := preset) config fork slot) ∧
    ∀ (root : Root) (state : BeaconState preset fork),
      store.blockStates[root]? = some state →
        BeforeFork (preset := preset) config fork state.slot := by
  obtain ⟨current, currentOk, -, statesLe⟩ :=
    forward.slots_le_current slots (UInt64.le_of_eq anchorSlot)
  have epochOk : store.getCurrentStoreEpoch config = .ok (computeEpochAtSlot preset current) := by
    simp [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
  have within := UInt64.le_iff_toNat_le.mp (bounded _ epochOk)
  have currentNat : (computeEpochAtSlot preset current).toNat =
      current.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
  refine ⟨fun epoch ok slot inside => ?_, fun root state stored => ?_⟩
  · have := UInt64.le_iff_toNat_le.mp (bounded epoch ok)
    exact beforeFork_of_epoch window positive (by omega)
  · have low := UInt64.le_iff_toNat_le.mp (statesLe root state stored)
    exact beforeFork_of_epoch window positive
      (Nat.le_trans (Nat.div_le_div_right low) (currentNat ▸ within))

/-- A slot step run is a run, when the last slot is before the next fork. -/
private theorem RunsTo.ofProcessSlots {first second : BeaconState preset fork} {slot : Slot}
    (processed : processSlots config checks first slot = .ok second) :
    RunsTo config checks first second := by
  obtain ⟨lower, reached⟩ := processSlots_slot processed
  exact ⟨reached ▸ UInt64.le_of_lt lower, fun before =>
    run_of_processSlots processed (reached ▸ before)⟩

/-- A checkpoint read whose block is at or before the start of the epoch names that block. -/
private theorem eq_of_getCheckpointBlock {root checkpoint : Root} {epoch : Epoch} {start : Slot}
    {block : BeaconBlock preset fork}
    (read : store.getCheckpointBlock root epoch = .ok checkpoint)
    (startOk : computeStartSlotAtEpoch preset epoch = .ok start)
    (found : store.blocks[root]? = some block) (atMost : block.slot ≤ start) :
    root = checkpoint := by
  simp only [Store.getCheckpointBlock, bind_ok_iff, mapError_ok_iff, pure, Except.pure,
    Except.ok.injEq] at read
  obtain ⟨start', startOk', node, walk, rooted⟩ := read
  rw [startOk, Except.ok.injEq] at startOk'
  subst startOk'
  rw [Store.getAncestor_of_le (node := ⟨root, .pending⟩) found atMost, Except.ok.injEq] at walk
  rw [← rooted, ← walk]

/-- The runs of a call, from one state at the start of its target's epoch.

The call is the pulled-up head state and the current target of an honest store.

The receiver state is on the chain of a block of another honest store.

The checkpoint block of that chain for the target's epoch is the target.

The boundary state is at the start of the target's epoch, and genesis reaches it.

The bands of hysteresis hold at the boundary state.

A middle state at the same slot holds the queue of partial withdrawals of the target block.

The target block itself, when it is at the start of the epoch, is the only block on the way to it.

From the middle state, runs reach the pulled-up head state and the receiver state.

The blocks from the boundary state to the pulled-up head state number at most one per slot.

The spec pulls the head state up with BLS checks, so the stores check signatures with BLS. -/
private theorem runs_of_call
    {e : Execution (honestForkChoice config .bls sources anchorState anchorBlock assignment
      genesisTimeMs) J}
    {limit : ℕ} {anchor : Store preset fork} {horizon : Epoch}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    {g : ForkedBeaconState preset} (genesis : Genesis config .bls g)
    (history : Run config .bls g ⟨fork, anchorState⟩) (early : fork < .glamsterdam)
    (fulu : .fusaka ≤ fork) (window : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat)
    (bounded : HonestStoreEpochsBounded (e := e) horizon limit)
    (agree : HonestBlocksAgree (e := e) limit) (bands : preset.IncrementWithinUpwardBand)
    (electraFloor : preset.MAX_EFFECTIVE_BALANCE = preset.MIN_ACTIVATION_BALANCE)
    (electraCap : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} (callTime : (e.world n).time ≤ limit)
    {head : Root} {pulled anc : BeaconState preset fork} {target : Checkpoint}
    (pulledOk : ((e.world n).state u).getPulledUpHeadState config head = .ok pulled)
    (targetOk : ((e.world n).state u).getCurrentTarget config head = .ok target)
    (held : ((e.world n).state u).blockStates[target.root]? = some anc)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (receiveTime : (e.world k).time ≤ limit)
    {root : Root} {rootState state : BeaconState preset fork}
    (stored : ((e.world k).state w).blockStates[root]? = some rootState)
    (read : ((e.world k).state w).getCheckpointBlock root target.epoch = .ok target.root)
    (reach : state = rootState ∨ ∃ slot, processSlots config .bls rootState slot = .ok state)
    (later : target.epoch ≤ getCurrentEpoch state) (inside : getCurrentEpoch state ≤ horizon) :
    getCurrentEpoch pulled = target.epoch ∧
      ∃ boundary middle : BeaconState preset fork,
        getCurrentEpoch boundary = target.epoch ∧ getCurrentEpoch middle = target.epoch ∧
        Hysteresis boundary ∧ Nonempty (Run config .bls g ⟨fork, boundary⟩) ∧
        (∀ electra : .pectra ≤ fork,
          middle.pendingPartialWithdrawals electra = anc.pendingPartialWithdrawals electra) ∧
        ∃ (edge : Run config .bls ⟨fork, boundary⟩ ⟨fork, middle⟩)
          (tail : Run config .bls ⟨fork, middle⟩ ⟨fork, pulled⟩),
          edge.blockCount ≤ 1 ∧
          edge.blockCount + tail.blockCount ≤
            pulled.slot.toNat - target.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + 1 ∧
          Nonempty (Run config .bls ⟨fork, middle⟩ ⟨fork, state⟩) := by
  have forward (v : ValidatorIndex) (honest : v ∈ J) (i : ℕ) :=
    e.forwardReachableWith (anchorState := anchorState) (anchorBlock := anchorBlock)
      (fun a member => (start a member) ▸ Store.ForwardReachableWith.anchor anchored) i v honest
  obtain ⟨epochBefore, heldBefore⟩ := held_beforeFork window positive slots anchorSlot
    (forward u caller n).forwardReachable (fun epoch ok => bounded u caller n epoch callTime ok)
  obtain ⟨-, heldBeforeW⟩ := held_beforeFork window positive slots anchorSlot
    (forward w receiver k).forwardReachable
    (fun epoch ok => bounded w receiver k epoch receiveTime ok)
  obtain ⟨epoch, checkpoint, epochOk, checkpointOk, rfl⟩ :=
    Store.getCurrentTarget_eq_ok_iff.mp targetOk
  dsimp only at held read later ⊢
  obtain ⟨boundary, aBlock, boundaryOk, aFound, aLe, -⟩ :=
    Store.isAncestor_of_getCheckpointBlock early checkpointOk
  have boundaryNat := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
  have atStart : boundary % preset.SLOTS_PER_EPOCH = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mod, boundaryNat, Nat.mul_mod_left, UInt64.toNat_zero]
  have epochAt {s : BeaconState preset fork} (atSlot : s.slot = boundary) :
      getCurrentEpoch s = epoch := by
    simp only [getCurrentEpoch, atSlot]
    exact computeEpochAtSlot_computeStartSlotAtEpoch (UInt64.lt_iff_toNat_lt.mpr positive)
      boundaryOk
  have ancSlot : anc.slot = aBlock.slot :=
    blockState_slot_eq anchorSlot (forward u caller n).reachable aFound held
  have ancLe : anc.slot ≤ boundary := ancSlot ▸ aLe
  -- The epoch of the store's clock bounds every slot the call reads.
  obtain ⟨now, nowOk, -, statesLe⟩ := (forward u caller n).forwardReachable.slots_le_current
    slots (UInt64.le_of_eq anchorSlot)
  have epochNow : epoch.toNat = now.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    have same : epoch = computeEpochAtSlot preset now := by
      refine Except.ok.inj (epochOk.symm.trans ?_)
      simp only [Store.getCurrentStoreEpoch, nowOk, bind, Except.bind, pure, Except.pure]
    rw [same]
    simp only [computeEpochAtSlot, UInt64.toNat_div]
  -- The call's middle state is the target state at the start of the epoch, which runs on to it.
  simp only [Store.getPulledUpHeadState, bind_ok_iff] at pulledOk
  obtain ⟨headState, headOk, current, currentOk, pulledOk⟩ := pulledOk
  have headStored := Store.blockState_ok_iff.mp headOk
  obtain rfl : current = epoch := Except.ok.inj (currentOk.symm.trans epochOk)
  obtain ⟨headBlock, headFound⟩ := (forward u caller n).reachable.known_of_blockState headStored
  have headSlot : headState.slot = headBlock.slot :=
    blockState_slot_eq anchorSlot (forward u caller n).reachable headFound headStored
  obtain ⟨middle, lookOk, toPulled, pulledEpoch⟩ : ∃ middle,
      lookaheadState config .bls anc boundary = .ok middle ∧
      RunsTo config .bls middle pulled ∧ getCurrentEpoch pulled = current := by
    split at pulledOk
    · rename_i older
      simp only [bind_ok_iff] at pulledOk
      obtain ⟨boundary', boundaryOk', processed⟩ := pulledOk
      obtain rfl : boundary' = boundary :=
        Except.ok.inj ((mapError_ok_iff.mp boundaryOk').symm.trans boundaryOk)
      have processed := mapError_ok_iff.mp processed
      have below := (processSlots_slot processed).1
      -- A head before the epoch is its own checkpoint block, so the call pulls up the target.
      obtain rfl : head = checkpoint := eq_of_getCheckpointBlock checkpointOk boundaryOk
        headFound (headSlot ▸ UInt64.le_of_lt below)
      obtain rfl : headState = anc := Option.some.inj (headStored.symm.trans held)
      refine ⟨pulled, ?_, RunsTo.refl _, epochAt (processSlots_slot processed).2⟩
      simp [lookaheadState, below, processed, Except.mapError]
    · rename_i notOlder
      simp only [pure, Except.pure, Except.ok.injEq] at pulledOk
      subst pulledOk
      have notOlderNat := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp notOlder)
      rw [toNat_getCurrentEpoch] at notOlderNat
      have atOrAfter : boundary ≤ headBlock.slot := by
        rw [← headSlot, UInt64.le_iff_toNat_le, boundaryNat]
        exact (Nat.le_div_iff_mul_le positive).mp notOlderNat
      obtain ⟨middle, lookOk, toHead⟩ :=
        (forward u caller n).relation_of_checkpointPrefix_with (RunsTo config .bls) RunsTo.refl
          RunsTo.trans RunsTo.ofTransition RunsTo.ofPrefix (UInt64.le_of_eq anchorSlot)
          (checkpoint := ⟨current, checkpoint⟩) checkpointOk headFound boundaryOk atOrAfter held
          headStored
      refine ⟨middle, lookOk, toHead, ?_⟩
      have upper := UInt64.le_iff_toNat_le.mp (statesLe head _ headStored)
      apply UInt64.toNat_inj.mp
      rw [toNat_getCurrentEpoch]
      exact Nat.le_antisymm (epochNow ▸ Nat.div_le_div_right upper) notOlderNat
  have middleBoundary : middle.slot = boundary := by
    unfold lookaheadState at lookOk
    split at lookOk
    · exact (processSlots_slot (mapError_ok_iff.mp lookOk)).2
    · rename_i notBelow
      simp only [pure, Except.pure, Except.ok.injEq] at lookOk
      subst lookOk
      exact UInt64.le_antisymm ancLe (UInt64.not_lt.mp notBelow)
  have epochBoundaryOk : ∀ slot : Slot, slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
      current.toNat → BeforeFork (preset := preset) config fork slot :=
    epochBefore current epochOk
  have pulledBefore : BeforeFork (preset := preset) config fork pulled.slot :=
    epochBoundaryOk pulled.slot (by rw [← toNat_getCurrentEpoch, pulledEpoch])
  obtain ⟨tail⟩ := toPulled.2 pulledBefore
  -- The receiver holds the same target state, and its state runs on from the middle state.
  obtain ⟨-, aBlockW, -, aFoundW, -, -⟩ := Store.isAncestor_of_getCheckpointBlock early read
  obtain ⟨ancW, heldW, -⟩ := (forward w receiver k).reachable.blockStatesFromParents aFoundW
  obtain rfl : anc = ancW := e.blockStates_eq anchored caller receiver (start u caller)
    (start w receiver) (agree u caller w receiver n k callTime receiveTime) held heldW
  have stateLater : boundary ≤ state.slot := by
    have := UInt64.le_iff_toNat_le.mp later
    rw [toNat_getCurrentEpoch] at this
    rw [UInt64.le_iff_toNat_le, boundaryNat]
    exact (Nat.le_div_iff_mul_le positive).mp this
  have stateBefore : BeforeFork (preset := preset) config fork state.slot :=
    beforeFork_of_epoch window positive
      (by rw [← toNat_getCurrentEpoch]; exact UInt64.le_iff_toNat_le.mp inside)
  have toState : RunsTo config .bls middle state := by
    obtain ⟨rootBlock, rootFound⟩ := (forward w receiver k).reachable.known_of_blockState stored
    have fromRoot : RunsTo config .bls rootState state := by
      rcases reach with rfl | ⟨_, processed⟩
      · exact RunsTo.refl _
      · exact RunsTo.ofProcessSlots processed
    by_cases far : boundary ≤ rootBlock.slot
    · obtain ⟨middle', lookOk', toRoot⟩ :=
        (forward w receiver k).relation_of_checkpointPrefix_with (RunsTo config .bls)
          RunsTo.refl RunsTo.trans RunsTo.ofTransition RunsTo.ofPrefix
          (UInt64.le_of_eq anchorSlot) (checkpoint := ⟨current, checkpoint⟩) read rootFound
          boundaryOk far heldW stored
      obtain rfl : middle' = middle := Except.ok.inj (lookOk'.symm.trans lookOk)
      exact toRoot.trans fromRoot
    · -- A root before the epoch is the target block, and its state is processed past the start.
      have before := UInt64.not_le.mp far
      obtain rfl : root = checkpoint :=
        eq_of_getCheckpointBlock read boundaryOk rootFound (UInt64.le_of_lt before)
      obtain rfl : anc = rootState := Option.some.inj (heldW.symm.trans stored)
      have ancBelow : anc.slot < boundary :=
        (blockState_slot_eq anchorSlot (forward w receiver k).reachable rootFound stored) ▸ before
      have looked : processSlots config .bls anc boundary = .ok middle := by
        simp only [lookaheadState, ancBelow, ↓reduceIte] at lookOk
        exact mapError_ok_iff.mp lookOk
      rcases reach with rfl | ⟨slot, processed⟩
      · exact absurd (UInt64.lt_of_lt_of_le ancBelow stateLater) (UInt64.lt_irrefl _)
      · have reached := (processSlots_slot processed).2
        rcases UInt64.lt_or_eq_of_le (reached ▸ stateLater) with lower | same
        · obtain ⟨middle', firstOk, restOk⟩ := processSlots_split ancBelow lower processed
          obtain rfl : middle' = middle := Except.ok.inj (firstOk.symm.trans looked)
          exact RunsTo.ofProcessSlots restOk
        · subst same
          obtain rfl : state = middle := Except.ok.inj (processed.symm.trans looked)
          exact RunsTo.refl _
  obtain ⟨toStateRun⟩ := toState.2 stateBefore
  -- The boundary state, before the target block when the block is at the start of the epoch.
  obtain ⟨ancRun⟩ := run_of_held (forward u caller n) heldBefore held
  have boundaryBefore :=
    epochBoundaryOk boundary (by rw [boundaryNat, Nat.mul_div_cancel _ positive])
  obtain ⟨start, startSlot, banded, first, edge, single, queue⟩ : ∃ start : BeaconState preset fork,
      start.slot = boundary ∧ Hysteresis start ∧ Nonempty (Run config .bls g ⟨fork, start⟩) ∧
      ∃ edge : Run config .bls ⟨fork, start⟩ ⟨fork, middle⟩, edge.blockCount ≤ 1 ∧
        ∀ electra : .pectra ≤ fork,
          middle.pendingPartialWithdrawals electra = anc.pendingPartialWithdrawals electra := by
    rcases UInt64.lt_or_eq_of_le ancLe with below | same
    · have processed : processSlots config .bls anc boundary = .ok middle := by
        simp only [lookaheadState, below, ↓reduceIte] at lookOk
        exact mapError_ok_iff.mp lookOk
      obtain ⟨slotRun⟩ := run_of_processSlots processed boundaryBefore
      exact ⟨middle, middleBoundary, hysteresis_of_processSlots bands processed atStart,
        ⟨(history.append ancRun).append slotRun⟩, .nil, Nat.zero_le _,
        processSlots_pendingPartialWithdrawals
          (Nat.le_trans (show Fork.altair ≤ Fork.fusaka by decide) fulu) processed⟩
    · obtain rfl : anc = middle := by
        simpa [lookaheadState, same, UInt64.lt_irrefl, pure, Except.pure] using lookOk
      obtain ⟨start, atSlot, banded, first, ⟨edge⟩⟩ :=
        run_boundaryState genesis bands electraFloor electraCap (history.append ancRun) early fulu
          (show anc.slot % preset.SLOTS_PER_EPOCH = 0 from same ▸ atStart)
      have counted := edge.blocks_le_slots (a := boundary.toNat) (b := boundary.toNat)
        (by rw [atSlot, same]) (by rw [same])
      exact ⟨start, atSlot.trans same, banded, first, edge, by omega, fun _ => rfl⟩
  have counted := (edge.append tail).blocks_le_slots (a := boundary.toNat)
    (b := pulled.slot.toNat) (by rw [startSlot]) (Nat.le_refl _)
  rw [Run.blockCount_append, boundaryNat] at counted
  exact ⟨pulledEpoch, start, middle, epochAt startSlot, epochAt middleBoundary, banded, first,
    queue, edge, tail, single, counted, ⟨toStateRun⟩⟩

/-- The quorum of each call of an honest store drifts by at most its reserve, at every receiver.

This holds for executions whose honest stores check signatures with BLS, at Fulu or later.

Fast confirmation was implemented at Fulu.

The spec pulls the head state of a call up with BLS checks, and the epoch transition reads them.

So only with BLS do the call and a receiver share the runs that the drift bound takes.

The drift bound `bound` is taken as a hypothesis, in the form of the reserve inequality.

It bounds the drift over runs from one middle state at the start of the target's epoch.

This theorem builds those runs from the stores of the call and of the receiver.

The parameters must keep the bands of hysteresis, the withdrawal delay and the Electra caps.

The stores stay before the next fork through the horizon, and agree on the blocks they hold. -/
theorem Execution.quorumDriftWithin_of_bound
    {e : Execution (honestForkChoice config .bls sources anchorState anchorBlock assignment
      genesisTimeMs) J}
    (bound : ∀ {g : ForkedBeaconState preset}
      {boundary middle pulled anc state : BeaconState preset fork},
      Genesis config .bls g → Run config .bls g ⟨fork, boundary⟩ →
      ∀ (edge : Run config .bls ⟨fork, boundary⟩ ⟨fork, middle⟩)
        (tailP : Run config .bls ⟨fork, middle⟩ ⟨fork, pulled⟩),
      Run config .bls ⟨fork, middle⟩ ⟨fork, state⟩ →
      fork < .glamsterdam → .fusaka ≤ fork → preset.IncrementWithinUpwardBand →
      1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat → CapOrder preset →
      Hysteresis boundary → edge.blockCount ≤ 1 →
      edge.blockCount + tailP.blockCount ≤
        pulled.slot.toNat - (getCurrentEpoch pulled).toNat * preset.SLOTS_PER_EPOCH.toNat + 1 →
      (∀ electra : .pectra ≤ fork,
        middle.pendingPartialWithdrawals electra = anc.pendingPartialWithdrawals electra) →
      getCurrentEpoch middle = getCurrentEpoch boundary →
      getCurrentEpoch pulled = getCurrentEpoch boundary →
      getCurrentEpoch pulled ≤ getCurrentEpoch state →
      (getCurrentEpoch state).toNat ≤ (getCurrentEpoch pulled).toNat + 1 →
      ∀ {voters : Finset ValidatorIndex} {total pulledTotal : Gwei},
      (∀ v ∈ voters,
        v ∈ activeVoters pulled ∧ (slashedFlagAt state v.toNat).getD false = false) →
      getTotalActiveBalance state = .ok total → getTotalActiveBalance pulled = .ok pulledTotal →
      2 * total.toNat + 3 * stake (fun v => balanceAt pulled v.toNat) voters ≤
        2 * pulledTotal.toNat + 3 * stake (fun v => balanceAt state v.toNat) voters +
          quorumReserve config pulled anc)
    {anchor : Store preset fork} {g : ForkedBeaconState preset} {horizon : Epoch} {limit : ℕ}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (slots : 0 < config.SLOT_DURATION_MS) (parameters : DirectSafety.Parameters preset)
    (genesis : Genesis config .bls g) (history : Run config .bls g ⟨fork, anchorState⟩)
    (early : fork < .glamsterdam) (fulu : .fusaka ≤ fork)
    (window : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat)
    (bounded : HonestStoreEpochsBounded (e := e) horizon limit)
    (agree : HonestBlocksAgree (e := e) limit) (bands : preset.IncrementWithinUpwardBand)
    (withdrawDelay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (electraFloor : preset.MAX_EFFECTIVE_BALANCE = preset.MIN_ACTIVATION_BALANCE)
    (electraCap : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA) :
    QuorumDriftWithin (e := e) horizon limit := by
  intro u caller n head pulled anc target callTime pulledOk targetOk held w receiver k root
    rootState state receiveTime stored read reach later near inside voters total pulledTotal
    voting totalOk pulledTotalOk
  obtain ⟨pulledEpoch, boundary, middle, boundaryEpoch, middleEpoch, banded, ⟨toBoundary⟩,
    queue, edge, tail, single, counted, ⟨toState⟩⟩ :=
    runs_of_call anchored start anchorSlot slots parameters.slots genesis history early fulu window
      bounded agree bands electraFloor electraCap caller callTime pulledOk targetOk held receiver
      receiveTime stored read reach later inside
  rw [← pulledEpoch] at counted later near
  exact bound genesis toBoundary edge tail toState early fulu bands withdrawDelay
    ⟨UInt64.le_of_eq electraFloor, electraCap⟩ banded single counted queue
    (middleEpoch.trans boundaryEpoch.symm) (pulledEpoch.trans boundaryEpoch.symm) later near
    voting totalOk pulledTotalOk

end EthLib.Consensus.Models.Network
