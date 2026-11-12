module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Rule

/-! Joint satisfiability of the premises of fast-confirmation Theorem 1.

The theorem is the safety part of arXiv 2405.00549v4, Section 4, as stated by EthLib.

The witness uses eight validators, four slots per epoch and zero shuffle rounds.

It has zero proposer boost and a churn limit of one.

The proof certifies the premises and the advancing call without using the safety theorem's proof. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.EightValidatorWitness.Trace
open Base Base.Uint64

/-- A held parent is the slot-zero anchor of the sole slot-one child. -/
theorem local_parents (code : Local) : code.store.ParentsBelow := by
  intro root block parent held parentHeld
  rcases local_block held with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · rcases local_block parentHeld with ⟨bad, _⟩ | ⟨bad, _⟩
    · exact False.elim (anchorRoot_ne_zero bad.symm)
    · exact False.elim (blockRoot_ne_zero bad.symm)
  · rcases local_block parentHeld with ⟨_, rfl⟩ | ⟨bad, _⟩
    · decide
    · exact False.elim (blockRoot_ne_anchorRoot bad.symm)

/-- Every premise of `Execution.safeAt_confirmedRoot`, specialized to the witness parameters.

The delay is one millisecond, the horizon epoch is one, and the last time is 4000 milliseconds.

Validator zero calls at event 112, in slot three, with zero drift margin and weight shift.

The global Byzantine percentage is twelve; the separate committee percentage is thirty-four.

Keeping the fields in statement order makes the correspondence with the theorem explicit. -/
structure TheoremOnePremises (e : Execution protocol honest) : Prop where
  sync : e.Synchronous 1
  half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100
  boost : config.PROPOSER_SCORE_BOOST.toNat ≤ 100
  slots : 0 < config.SLOT_DURATION_MS
  long : 1 < preset.SLOTS_PER_EPOCH
  window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat
  lookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat ∧ 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat ∧
    preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat
  votes : Votes e.startTime 4000 e
  fits : DelayFits .phase0 config 0 1
  prompt : Prompt e 4000
  committees : CommitteesFollow e 4000
  follows : HeadFollowsSupport e 4000
  preGloas : Fork.phase0 < .glamsterdam
  oneBlock : OneBlockPerRoot e 4000
  admitted : BlocksAdmitted e 0 1 4000
  included : TargetIncluded e 4000
  anchored : getForkchoiceStore config (state bodyRoot) (anchorBlock stateRoot) = .ok anchor
  sound : Invariant (state bodyRoot)
  anchorSlot : (anchorBlock stateRoot).slot = (state bodyRoot).slot
  anchorAtBoundary : isStartSlotAtEpoch preset (anchorBlock stateRoot).slot = .ok true
  start : ∀ w ∈ honest, e.start w = anchor
  noVotes : anchor.latestMessages.isEmpty
  syncStart : (getCurrentEpoch (state bodyRoot)).toNat = 0 ∨
    anchor.genesisTimeMs.toNat + ((getCurrentEpoch (state bodyRoot)).toNat +
      preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat *
        config.SLOT_DURATION_MS.toNat ≤ e.startTime
  maxAligned : MaxEffectiveBalancesAligned preset
  increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0
  chain : FinalizedPrefix e 1 4000
  unique : OneJustifiedPerEpoch e 1 4000
  byzantine : ∀ w ∈ honest, ∀ k (s : BeaconState preset .phase0) total,
    (e.world k).time ≤ 4000 → ((e.world k).state w).Counts config s →
    (getCurrentEpoch s).toNat ≤ (1 : Epoch).toNat + 1 →
    getTotalActiveBalance s = .ok total →
    100 * stake (fun v => balanceAt s v.toNat) {v ∈ quorumVoters s | v ∉ honest} ≤ 12 * total.toNat
  unslashed : ∀ w ∈ honest, ∀ k (s : BeaconState preset .phase0), (e.world k).time ≤ 4000 →
    ((e.world k).state w).Counts config s → ∀ v ∈ honest, NotSlashed s v
  supply : ∀ w ∈ honest, ∀ k checkpoint s, (e.world k).time ≤ 4000 →
    ((e.world k).state w).checkpointState checkpoint = .ok s → ActiveStakeAtMost stakeCapGwei s
  exits : ∀ u ∈ honest, ∀ n (c : Checkpoint) (source : BeaconState preset .phase0),
    (e.world n).time ≤ 4000 → ((e.world n).state u).checkpointState c = .ok source →
    ∀ w ∈ honest, ∀ k (head : Root) (hs : BeaconState preset .phase0),
    (e.world k).time ≤ 4000 → ((e.world k).state w).blockStates[head]? = some hs →
    ((e.world k).state w).getCheckpointBlock head c.epoch = .ok c.root →
    ∀ epoch : Epoch, c.epoch ≤ epoch → epoch.toNat ≤ c.epoch.toNat + 2 → epoch ≤ 1 →
    epoch.toNat ≤ (getCurrentEpoch hs).toNat + 1 →
    stake (fun v => balanceAt source v.toNat)
        {v ∈ activeVoters source | isActiveAt hs epoch v.toNat = false} ≤
      exitReserve config source
  positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT
  enough : 3 * 12 < 200
  large : ∀ w ∈ honest, ∀ k (s : BeaconState preset .phase0),
    (e.world k).time ≤ 4000 → ((e.world k).state w).Counts config s →
    (getCurrentEpoch s).toNat ≤ (1 : Epoch).toNat + 1 →
    3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun v => balanceAt s v.toNat) (activeVoters s)
  nonzero : ∀ w ∈ honest, ∀ k, (e.world k).time ≤ 4000 →
    ∀ (root : Root) (block : BeaconBlock preset .phase0),
    ((e.world k).state w).blocks[root]? = some block → block.stateRoot ≠ Vector.replicate 32 0
  headDrifts : ∀ w ∈ honest, ∀ n head headState epoch, (e.world n).time ≤ 4000 →
    ((e.world n).state w).getPulledUpHeadState config head = .ok headState →
    ((e.world n).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ 1 →
    ∀ v ∈ honest, ∀ k (s : BeaconState preset .phase0), (e.world k).time ≤ 4000 →
      ((e.world k).state v).Counts config s → epoch.toNat ≤ (getCurrentEpoch s).toNat →
      (getCurrentEpoch s).toNat ≤ epoch.toNat + 1 → DriftAtMost headState s 0
  caller : (0 : ValidatorIndex) ∈ honest
  upToDate : ∀ n ∈ ([112] : List Nat), UpToDate config .acceptAll sources (e.world n).time
    ((e.world n).view 0) ((e.world n).state 0)
  lower : ∀ n ∈ ([112] : List Nat), ((e.world n).state 0).ParentsBelow
  atSlots : ∀ i n, ([112] : List Nat)[i]? = some n → ∃ slot begin,
    ((e.world n).state 0).getCurrentSlot config = .ok slot ∧
    slot.toNat = (3 : Slot).toNat + i ∧ computeTimeAtSlotMs config 0 slot = .ok begin ∧
    (e.world n).time = begin.toNat
  ran : (([112] : List Nat).map fun n => (e.world n).state 0).foldlM
    (fun fcr store => store.onFastConfirmation config fcr) (getFastConfirmationStore anchor) =
      .ok confirmed
  bounds : RuleBounds e 0 [112] (getFastConfirmationStore anchor) 0 0 4000
  inHorizon : ∀ w ∈ honest, ∀ k epoch, (e.world k).time ≤ 4000 →
    ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ 1
  anchorParent : ∀ w ∈ honest, ∀ k, (e.world k).time ≤ 4000 →
    ((e.world k).state w).blocks[(anchorBlock stateRoot).parentRoot]? = none
  lastCall : ([112] : List Nat).getLast? = some 112
  slotOk : ((e.world 112).state 0).getCurrentSlot config = .ok 3
  nextOk : addChecked (3 : Slot) 1 = .ok 4
  followingOk : computeTimeAtSlotMs config 0 4 = .ok 4000
  nonempty : (4000 : UInt64).toNat ≤ 4000

/-- The same allowed execution satisfies every specialized premise simultaneously. -/
theorem all_premises : TheoremOnePremises execution where
  sync := synchronous
  half := by decide
  boost := by decide
  slots := by decide
  long := by decide
  window := by decide
  lookahead := ⟨parameters.2.1, parameters.2.2.1, parameters.2.2.2.1⟩
  votes := votes
  fits := delay_fits
  prompt := prompt
  committees := committees_follow
  follows := head_follows
  preGloas := by decide
  oneBlock := one_block
  admitted := blocks_admitted
  included := included
  anchored := initialized
  sound := invariant bodyRoot
  anchorSlot := rfl
  anchorAtBoundary := rfl
  start := fun _ _ => rfl
  noVotes := rfl
  syncStart := .inl rfl
  maxAligned := parameters.1
  increment := by decide
  chain := finalized_prefix
  unique := unique
  byzantine := byzantine
  unslashed := unslashed
  supply := supply
  exits := exits
  positive := by decide
  enough := by decide
  large := large
  nonzero := nonzero
  headDrifts := head_drifts
  caller := by decide
  upToDate := by
    intro n member
    simp only [List.mem_singleton] at member
    subst n
    exact call_ready
  lower := by
    intro n member
    simp only [List.mem_singleton] at member
    subst n
    rw [call_store]
    exact local_parents (.running 3000 4)
  atSlots := by
    intro i n index
    cases i with
    | succ i => simp at index
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at index
      subst n
      refine ⟨3, 3000, ?_, rfl, rfl, confirms_by_walk.1⟩
      rw [call_store]
      exact call_slot
  ran := by
    simp only [List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil, bind_pure]
    rw [call_store]
    exact running_call
  bounds := rule_bounds
  inHorizon := in_horizon
  anchorParent := anchor_parent
  lastCall := rfl
  slotOk := by rw [call_store]; exact call_slot
  nextOk := rfl
  followingOk := rfl
  nonempty := by decide

/-- The full call selects the anchor as its start and checks the distinct child's walk. -/
theorem call_checked : ((execution.world 112).state 0).Checked config confirmed
    blockRoot anchorRoot blockRoot := by
  rw [call_store]
  obtain ⟨head, slot, start, headOk, _, _, _, _, _, _, _, selected, result⟩ :=
    Store.onFastConfirmation_checked (local_parents (.running 3000 4)) running_call
  change (running 3000 4).getHead config = .ok head at headOk
  rw [call_head, Except.ok.injEq] at headOk
  subst head
  have startEq : start = anchorRoot := by
    obtain ⟨base, baseCase, startCase⟩ := selected
    have baseEq : base = anchorRoot := baseCase.elim (fun h => h.1) (fun h => h.1)
    exact startCase.elim (fun h => h.1.trans baseEq) (fun h => h.1)
  subst start
  rcases result with same | ⟨_, checked, _⟩
  · exact False.elim (blockRoot_ne_anchorRoot same)
  · exact checked

/-- An allowed execution satisfies every premise and genuinely advances through the walk.

The eight-validator phase0 witness uses the custom preset and configuration described above.

It uses acceptance-only signature checks, fixed balances totalling 1600 Gwei, and one child block.

Four honest votes supply 800 Gwei against the child's 672-Gwei confirmation threshold.

Every validator is honest and holds the maximum balance of 200 Gwei, two per slot.

The churn limit is one, so the exit reserve of the anchor is 200 Gwei.

Every ordered range of committees then weighs at least 400 Gwei.

So `100 B + 50 reserve = 10000` is at most `34 w` on each of them.

Some quantified obligations hold only vacuously on this short horizon:

* `TargetIncluded` requires `target.epoch + 2 ≤ current`, but every receiver is before epoch two.
* The late-margin field of `RuleBounds` requires a complete epoch between time 3000 and time 4000.
  No such epoch exists.
* Epoch-one instances of the head-drift bound have no counted epoch-one state.
* The dishonest-equivocator field of `WeightBounds` is vacuous: no store has an equivocator.
* The slot-zero vote deadline precedes the execution's start, so `Votes` does not require it.
* `FinalizedPrefix` and `OneJustifiedPerEpoch` compare only the epoch-zero anchor checkpoint.
* `exits` holds with zero exited stake, since no validator has an exit epoch.
  Every registered validator is active at each epoch up to the horizon in each held head state.

No later-epoch target, duty or checkpoint instance is exercised beyond these time bounds.

The witness proves satisfiability, not that these restricted circumstances represent mainnet. -/
theorem exists_nonvacuity : ∃ e : Execution protocol honest,
    TheoremOnePremises e ∧
    ((e.world 112).state 0).Checked config confirmed blockRoot anchorRoot blockRoot ∧
    (e.world 112).time = 3000 ∧
    ((e.world 112).state 0).onFastConfirmation config (getFastConfirmationStore anchor) =
      .ok confirmed ∧
    ((e.world 112).state 0).findLatestConfirmedDescendant config
      (getFastConfirmationStore anchor) blockRoot anchorRoot = .ok blockRoot ∧
    confirmed.confirmedRoot ≠ anchorRoot :=
  ⟨execution, all_premises, call_checked, confirms_by_walk⟩

end EthLib.Consensus.Models.Network.EightValidatorWitness.Trace
