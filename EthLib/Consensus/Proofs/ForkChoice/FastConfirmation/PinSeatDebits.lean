module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinEventsKept
public import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Penalties
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Assembly
import EthLib.Consensus.Proofs.DirectSafety.BalanceSources
import EthLib.Consensus.Proofs.Transition.Totality.Supply

/-!
# The sync debits of a run fit one envelope per seat per slot

A block pays the members of the sync committee that did not sign one participant reward each.

The sum of the debits of any set of keys over a block is therefore at most the committee size times that reward.

The reward reads the total active balance of the block.

If that total is within three halves of a given total, the reward is at most the envelope of the given total.

A run has at most one block for each slot it covers, and a slot step records no sync event.

So the sync debits of the run fit one envelope per seat per slot of the epochs that the run touches.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network.PinSplit5

open Base Uint64 Models DirectSafety

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The sync debit of one key in one event. -/
def keySyncDebit (v : ℕ) (event : BalanceEvent preset) : ℕ :=
  if event.source = .sync then actualBalanceAt event.before v - actualBalanceAt event.after v else 0

/-- The participant reward of the sync committee, at the most that a total within three halves of the given total allows.

The reward is the base rewards of the total, times the sync weight, per slot and per member.

The base rewards of a total are at most the base reward factor times its root plus 2. -/
def syncEnvelope (preset : Preset) (total : ℕ) : ℕ :=
  preset.BASE_REWARD_FACTOR.toNat * (Nat.sqrt (3 * total / 2) + 2) *
    SYNC_REWARD_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat / preset.SLOTS_PER_EPOCH.toNat /
      preset.SYNC_COMMITTEE_SIZE.toNat

/-- The participant reward at a state whose total is within three halves of a total is at most the envelope. -/
private theorem syncReward_le_envelope {fork : Fork} {s : BeaconState preset fork}
    {reward T : Gwei} (rewardOk : syncParticipantReward s = .ok reward)
    (totalOk : getTotalActiveBalance s = .ok T) (total : ℕ) (band : 2 * T.toNat ≤ 3 * total) :
    reward.toNat ≤ syncEnvelope preset total := by
  simp only [syncParticipantReward, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff] at rewardOk
  obtain ⟨read, readOk, perIncrement, perOk, rewardOk⟩ := rewardOk
  obtain rfl : T = read := Except.ok.inj (totalOk.symm.trans readOk)
  obtain ⟨increments, incrementsOk, base, baseOk, weighted, weightedOk, perWeight, perWeightOk,
    perSlot, perSlotOk, rewardOk⟩ := rewardOk
  rw [divChecked_ok_iff] at incrementsOk perWeightOk perSlotOk rewardOk
  rw [mulChecked_ok_iff] at baseOk weightedOk
  have weightValue : SYNC_REWARD_WEIGHT.toNat = 2 := rfl
  have denominator : WEIGHT_DENOMINATOR.toNat = 64 := rfl
  rw [weightValue] at weightedOk
  rw [denominator] at perWeightOk
  have rootLe : Nat.sqrt T.toNat ≤ Nat.sqrt (3 * total / 2) :=
    Nat.sqrt_le_sqrt (by omega)
  have baseLe : base.toNat ≤ preset.BASE_REWARD_FACTOR.toNat * (Nat.sqrt (3 * total / 2) + 2) := by
    rw [baseOk.2, incrementsOk.2, toNat_getBaseRewardPerIncrement perOk, Nat.mul_comm]
    rcases Nat.eq_zero_or_pos T.toNat with zero | positive
    · simp [zero]
    · exact (div_mul_div_sqrt_le positive _).trans (Nat.mul_le_mul_left _ (by omega))
  unfold syncEnvelope
  rw [weightValue, denominator, rewardOk.2, perSlotOk.2, perWeightOk.2, weightedOk.2]
  exact Nat.div_le_div_right (Nat.div_le_div_right (Nat.div_le_div_right
    (Nat.mul_le_mul_right 2 baseLe)))

/-- A sync aggregate debits, over any keys, at most one participant reward for each member.

This restates the debit half of `sync_bounds` (IntervalFunding), which is private there. -/
private theorem syncAggregate_debits {fork : Fork} {s t : BeaconState preset fork}
    (altair : .altair ≤ fork) (aggregate : SyncAggregate preset)
    (ok : processSyncAggregate config checks s altair aggregate = .ok t) (keys : Finset ℕ) :
    ∃ reward, syncParticipantReward s = .ok reward ∧
      ∑ i ∈ keys, (actualBalanceAt ⟨fork, s⟩ i - actualBalanceAt ⟨fork, t⟩ i) ≤
        preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat := by
  simp only [processSyncAggregate, bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, reward, rewardOk, proposer, proposerOk,
    members, membersOk, folded⟩ := ok
  refine ⟨reward, rewardOk, ?_⟩
  have fold (xs : List (ValidatorIndex × Bool)) (s t : BeaconState preset fork)
      (proposerIndex : Except AccessorError ValidatorIndex)
      (ok : xs.foldlM (applySyncReward reward proposer proposerIndex) s = .ok t) :
      t.balances.data.size = s.balances.data.size ∧
      balanceDebits s t ≤ xs.length * reward.toNat := by
    induction xs generalizing s with
    | nil => cases ok; simp [balanceDebits]
    | cons x xs ih =>
      obtain ⟨u, one, rest⟩ := bind_ok_iff.mp ok
      have bounds := sync_reward_bounds s u reward proposer proposerIndex x one
      have sizes : u.balances.data.size = s.balances.data.size := by
        unfold applySyncReward at one
        split at one
        · simp only [bind_ok_iff, liftAccessor_ok] at one
          obtain ⟨v, first, _, _, last⟩ := one
          exact (sameSizes_increaseBalance last).2.trans (sameSizes_increaseBalance first).2
        · exact (sameSizes_decreaseBalance (liftAccessor_ok.mp one)).2
      have tail := ih u rest
      have triangle := debits_triangle s u t sizes.symm
      refine ⟨tail.1.trans sizes, ?_⟩
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      split_ifs at bounds <;> omega
  have bounds := fold _ s t _ (by simpa only [← Array.foldlM_toList] using folded)
  have length : (members.zip aggregate.syncCommitteeBits.bits.toArray).toList.length ≤
      preset.SYNC_COMMITTEE_SIZE.toNat := by
    simp only [Array.length_toList, Array.size_zip]
    exact (Nat.min_le_right _ _).trans (by simp)
  have registry : ∑ i ∈ keys, (actualBalanceAt ⟨fork, s⟩ i - actualBalanceAt ⟨fork, t⟩ i) ≤
      balanceDebits s t := by
    unfold balanceDebits
    refine Finset.sum_le_sum_of_ne_zero fun j _ positive => Finset.mem_range.mpr ?_
    by_contra outside
    apply positive
    simp [actualBalanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt outside)]
  exact registry.trans (bounds.2.trans (Nat.mul_le_mul_right _ length))

/-- Move a fork-conditional replay before its common continuation. -/
private theorem except_dite_bind {α β : Type} (p : Prop) [Decidable p]
    (yes : p → Except TransitionError α) (no : ¬p → Except TransitionError α)
    (next : α → Except TransitionError β) :
    (if h : p then yes h >>= next else no h >>= next) =
      ((if h : p then yes h else no h) >>= next) := by
  split <;> rfl

/-- The events of a replay record no sync pass. -/
private def NoSync {fork : Fork} (pre : BalanceReplay preset fork) : Prop :=
  ∀ e ∈ pre.2, e.source ≠ .sync

private theorem NoSync.carry {fork : Fork}
    {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
    {p q : BalanceReplay preset fork} (held : NoSync p) (ok : carryBalance action p = .ok q) :
    NoSync q := by
  intro e member
  rw [(PinSplit4.carryBalance_cases ok).2] at member
  exact held e member

private theorem NoSync.record {fork : Fork} {source : BalanceSource}
    {limits : BeaconState preset fork → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
    {p q : BalanceReplay preset fork} (held : NoSync p)
    (ok : recordBalance source limits action p = .ok q) (notSync : source ≠ .sync) :
    NoSync q := by
  intro e member
  rcases (PinSplit4.recordBalance_cases ok).2 e member with old | new
  · exact held e old
  · rw [new]
    exact notSync

/-- The sync debits of a block over any keys fit the participant reward of the block's total.

The sync pass is the last pass of the replay, and no other pass records a sync event.

It reads the total of the state after the block, since a sync aggregate changes only balances. -/
private theorem block_syncDebits_le {fork : Fork} {a t : BeaconState preset fork}
    (early : fork < .glamsterdam) (altair : .altair ≤ fork) {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork} {events : List (BalanceEvent preset)}
    (replay : blockBalanceReplay (config := config) (checks := checks) early engine a block =
      .ok (t, events))
    (total : ℕ) (band : ∀ T : Gwei, getTotalActiveBalance t = .ok T → 2 * T.toNat ≤ 3 * total)
    (keys : Finset ℕ) :
    ∑ i ∈ keys, (events.map (keySyncDebit i)).sum ≤
      preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope preset total := by
  have normalized := replay
  unfold blockBalanceReplay at normalized
  simp only [altair, ↓reduceDIte] at normalized
  simp only [← bind_assoc, except_dite_bind] at normalized
  simp only [bind_assoc] at normalized
  simp only [bind_ok_iff, ensure_ok_iff] at normalized
  obtain ⟨headed, headedOk, executed, executedOk, revealed, revealedOk, voted, votedOk, _, _, _,
    _, proposed, proposedOk, slashed, slashedOk, attested, attestedOk, deposited, depositedOk,
    exited, exitedOk, changed, changedOk, consolidated, requestsOk, syncOk⟩ := normalized
  have start : NoSync ((a, []) : BalanceReplay preset fork) := fun _ member => by cases member
  have one := start.carry headedOk
  have two : NoSync executed := by
    split at executedOk
    · exact one.record executedOk (by decide)
    · cases executedOk
      exact one
  have three := two.carry revealedOk
  have four := three.carry votedOk
  have five := foldlM_ok_invariant NoSync
    (fun _ _ _ prior computed => prior.record computed (by decide)) four proposedOk
  have six := foldlM_ok_invariant NoSync
    (fun _ _ _ prior computed => prior.record computed (by decide)) five slashedOk
  have seven := foldlM_ok_invariant NoSync
    (fun _ _ _ prior computed => prior.record computed (by decide)) six attestedOk
  have eight := foldlM_ok_invariant NoSync
    (fun _ _ _ prior computed => prior.record computed (by decide)) seven depositedOk
  have nine := eight.carry (by simpa only [← Array.foldlM_toList] using exitedOk)
  have ten := nine.carry changedOk
  have eleven : NoSync consolidated := by
    split at requestsOk
    · simp only [bind_ok_iff] at requestsOk
      obtain ⟨requested, requestedOk, withdrawn, withdrawnOk, consolidatedOk⟩ := requestsOk
      have first := ten.carry requestedOk
      have second := first.carry withdrawnOk
      exact foldlM_ok_invariant NoSync
        (fun _ _ _ prior computed => prior.record computed (by decide)) second consolidatedOk
    · cases requestsOk
      exact ten
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq] at syncOk
  obtain ⟨⟨credit, debit⟩, limitsOk, u, synced, rfl, rfl⟩ := syncOk
  obtain ⟨reward, rewardOk, bound⟩ := syncAggregate_debits altair _ synced keys
  obtain ⟨balances, rfl⟩ := processSyncAggregate_eq synced
  obtain ⟨reward', rewardOk', -⟩ := limitsOk
  have same : reward' = reward := Except.ok.inj (rewardOk'.symm.trans rewardOk)
  have reads := rewardOk
  simp only [syncParticipantReward, bind_ok_iff, liftAccessor_ok] at reads
  obtain ⟨T, totalEnd, -⟩ := reads
  have envelope := syncReward_le_envelope rewardOk totalEnd total (band T totalEnd)
  have silent : ∀ i, (consolidated.2.map (keySyncDebit i)).sum = 0 := fun i =>
    List.sum_eq_zero fun x member => by
      obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
      simp [keySyncDebit, eleven e inside]
  simp only [List.map_append, List.sum_append, silent, keySyncDebit, ↓reduceIte, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Nat.zero_add, Nat.add_zero]
  exact bound.trans (Nat.mul_le_mul_left _ envelope)

private theorem replayDeltas_noSync {fork : Fork} {source : BalanceSource}
    {deltas : Array Gwei × Array Gwei} {p q : BalanceReplay preset fork}
    (notSync : source ≠ .sync) (held : NoSync p) (ok : replayDeltas source deltas p = .ok q) :
    NoSync q := by
  unfold replayDeltas at ok
  refine foldlM_ok_invariant NoSync (fun r i r' previous step => ?_) held ok
  simp only [bind_ok_iff] at step
  obtain ⟨index, _, raised, raisedOk, loweredOk⟩ := step
  exact ((previous.record raisedOk (by decide)).record loweredOk notSync)

private theorem replayRewards_noSync {fork : Fork} {p q : BalanceReplay preset fork}
    (held : NoSync p) (ok : replayRewards (config := config) p = .ok q) : NoSync q := by
  unfold replayRewards at ok
  split at ok
  · simp only [pure, Except.pure, Except.ok.injEq] at ok
    subst ok
    exact held
  · simp only [bind_ok_iff] at ok
    obtain ⟨ordinary, _, inactivity, _, ok⟩ := ok
    split at ok
    · obtain ⟨middle, middleOk, lastOk⟩ := bind_ok_iff.mp ok
      have first : NoSync middle := foldlM_ok_invariant NoSync
        (fun _ _ _ previous step => replayDeltas_noSync (by decide) previous step) held middleOk
      exact replayDeltas_noSync (by decide) first lastOk
    · obtain ⟨_, _, ok⟩ := bind_ok_iff.mp ok
      obtain ⟨one, oneOk, ok⟩ := bind_ok_iff.mp ok
      obtain ⟨two, twoOk, lastOk⟩ := bind_ok_iff.mp ok
      have first := replayDeltas_noSync (by decide) held oneOk
      have middle : NoSync two := foldlM_ok_invariant NoSync
        (fun _ _ _ previous step => replayDeltas_noSync (by decide) previous step) first twoOk
      exact replayDeltas_noSync (by decide) middle lastOk

/-- No stage of an epoch before the payments records a sync pass. -/
private theorem replay_stage_noSync {fork : Fork} {k : EpochStage}
    (member : k ∈ EpochStage.prefixStages) {p q : BalanceReplay preset fork}
    (ok : epochReplayAction (config := config) (checks := checks) k p = .ok q) :
    NoSync p → NoSync q := by
  intro held
  simp only [EpochStage.prefixStages, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [epochReplayAction] at ok
    exact held.carry ok
  · simp only [epochReplayAction] at ok
    split at ok
    · exact held.carry ok
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      exact held
  · simp only [epochReplayAction] at ok
    exact replayRewards_noSync held ok
  · simp only [epochReplayAction] at ok
    exact held.carry ok
  · simp only [epochReplayAction] at ok
    exact held.record ok (by decide)
  · simp only [epochReplayAction] at ok
    split at ok
    · exact held.carry ok
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      exact held
  · simp only [epochReplayAction] at ok
    split at ok
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨deposited, _, rfl⟩ := ok
      intro e member
      rcases List.mem_append.mp member with old | added
      · exact held e old
      · rw [List.mem_singleton.mp added]
        exact nofun
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      exact held
  · simp only [epochReplayAction] at ok
    split at ok
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨consolidated, _, rfl⟩ := ok
      intro e member
      rcases List.mem_append.mp member with old | added
      · exact held e old
      · rw [List.mem_singleton.mp added]
        exact nofun
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      exact held

/-- From Electra, a slot step records no sync pass. -/
private theorem slot_noSync {x y : ForkedBeaconState preset} (electra : .pectra ≤ x.fork)
    (ok : advanceSlotAcross config checks x = .ok y) (early : y.fork < .glamsterdam)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.slot ok : Step config checks x y).balanceEvents = .ok events) :
    ∀ e ∈ events, e.source ≠ .sync := by
  obtain ⟨advanced, cached, crossings, advanceOk, upgrades, cachedOk, crossingOk, branch⟩ :=
    Step.balanceEvents_slot ok early replayed
  have noCrossings : crossings = [] :=
    DirectSafety.Apriori.Internal.upgradeBalanceReplay_electra_nil
      (u := ⟨x.fork, advanced⟩) electra crossingOk
  rcases branch with ⟨_, eventsEq⟩ | ⟨middle, updated, recorded, recordOk, _, _, _, eventsEq, _⟩
  · rw [eventsEq, noCrossings]
    intro e member
    cases member
  · rw [eventsEq, noCrossings, List.append_nil]
    have trace := epochBalanceReplay_trace recordOk
    have quiet := trace.transport (fun p q => NoSync p → NoSync q) (fun _ held => held)
      (fun one two held => two (one held))
      (fun _ member _ _ computed => replay_stage_noSync member computed)
    exact quiet (fun _ member => by cases member)

/-- The sync debits of a run fit the committee size times the envelope for each block of the run. -/
private theorem run_syncDebits_le {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (fulu : .fusaka ≤ x.fork) (early : y.fork < .glamsterdam) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (total : ℕ)
    (band : ∀ z ∈ tail.balancePath, ∀ t : Gwei, getTotalActiveBalance z.state = .ok t →
      2 * t.toNat ≤ 3 * total)
    (keys : Finset ℕ) :
    ∑ i ∈ keys, (events.map (keySyncDebit i)).sum ≤
      tail.blockCount * (preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope preset total) := by
  induction tail generalizing events with
  | nil =>
    simp only [Run.balanceEvents, pure, Except.pure, Except.ok.injEq] at replayed
    subst replayed
    simp [Run.blockCount]
  | @snoc middle last pre step ih =>
    have earlyMiddle : middle.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have fuluMiddle : .fusaka ≤ middle.fork :=
      Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    have priorBound := ih earlyMiddle priorOk (fun z member => band z (by
      simp only [Run.balancePath, List.mem_append]
      exact .inl member))
    split at rest
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
      obtain ⟨added, addedOk, rfl⟩ := rest
      simp only [List.map_append, List.sum_append, Finset.sum_add_distrib]
      cases step with
      | slot ok =>
        have quiet := slot_noSync (Nat.le_trans (by decide) fuluMiddle) ok early addedOk
        have zero : ∀ i, (added.map (keySyncDebit i)).sum = 0 := fun i =>
          List.sum_eq_zero fun v member => by
            obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
            simp [keySyncDebit, quiet e inside]
        simpa [zero, Run.blockCount] using priorBound
      | @block fork before after engine signed due ok =>
        have altair : Fork.altair ≤ fork :=
          Nat.le_trans (show Fork.altair ≤ Fork.fusaka by decide) fuluMiddle
        have replay := Step.balanceEvents_block early addedOk
        have bound := block_syncDebits_le early altair replay total
          (fun T hT => band ⟨fork, after⟩ (by simp [Run.balancePath, Step.balancePath]) T hT) keys
        simp only [Run.blockCount, Nat.add_mul, Nat.one_mul]
        omega
    · simp only [pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      cases step with
      | slot ok => simpa [Run.blockCount] using priorBound
      | block => exact priorBound.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))

/-- The sync debits of any set of keys over a run from Fulu are at most one envelope per seat per slot of the epochs the run touches.

Every total along the run is within three halves of `total`.

The run has at most one block for each slot that it covers, and each block debits the keys at most one participant reward per seat. -/
theorem Run.syncDebits_le {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (fulu : .fusaka ≤ x.fork) (early : y.fork < .glamsterdam) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (total : ℕ) (_positive : 0 < total)
    (band : ∀ z ∈ tail.balancePath, ∀ t : Gwei, getTotalActiveBalance z.state = .ok t →
      2 * t.toNat ≤ 3 * total)
    (keys : Finset ℕ) :
    ∑ i ∈ keys, (events.map (keySyncDebit i)).sum ≤
      ((getCurrentEpoch y.state).toNat + 1 - (getCurrentEpoch x.state).toNat) *
        preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
          syncEnvelope preset total := by
  refine (run_syncDebits_le tail fulu early high replayed total band keys).trans ?_
  by_cases empty : preset.SLOTS_PER_EPOCH.toNat = 0
  · have zero : syncEnvelope preset total = 0 := by
      unfold syncEnvelope
      rw [empty]
      simp
    simp [zero]
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := Nat.pos_of_ne_zero empty
  have epochLe := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat] at epochLe ⊢
  have low : x.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat ≤
      x.state.slot.toNat := Nat.div_mul_le_self _ _
  have high' := Nat.lt_mul_div_succ y.state.slot.toNat positive
  have blocks := tail.blocks_le_slots low (b := preset.SLOTS_PER_EPOCH.toNat *
      (y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1) - 1) (by omega)
  have difference : (y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 -
      x.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat) * preset.SLOTS_PER_EPOCH.toNat =
      preset.SLOTS_PER_EPOCH.toNat * (y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1) -
        x.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat := by
    rw [Nat.sub_mul, Nat.mul_comm (preset.SLOTS_PER_EPOCH.toNat)]
  have grows : x.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat <
      preset.SLOTS_PER_EPOCH.toNat * (y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1) := by
    calc x.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat
        ≤ y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat :=
          Nat.mul_le_mul_right _ epochLe
      _ < preset.SLOTS_PER_EPOCH.toNat * (y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1) := by
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]
          omega
  have counted : tail.blockCount ≤ (y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 -
      x.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat) * preset.SLOTS_PER_EPOCH.toNat := by
    rw [difference]
    generalize x.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat *
      preset.SLOTS_PER_EPOCH.toNat = lowest at *
    generalize preset.SLOTS_PER_EPOCH.toNat *
      (y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1) = highest at *
    omega
  calc tail.blockCount * (preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope preset total)
      ≤ ((y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 -
        x.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat) * preset.SLOTS_PER_EPOCH.toNat) *
          (preset.SYNC_COMMITTEE_SIZE.toNat * syncEnvelope preset total) :=
        Nat.mul_le_mul_right _ counted
    _ = _ := by ring

end EthLib.Consensus.Models.Network.PinSplit5
