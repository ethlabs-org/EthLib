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

/-- An honest store holds the block of its justified checkpoint, up to a last time.

The checkpoint is the anchor's, or the root that a held state records for its epoch.

That root is the root of a held block, the latest of that chain at or before the first slot.

A nonzero state root fills the header of each held block only once. -/
theorem Execution.justifiedRoot_known {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (start : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (preGloas : fork < .glamsterdam) {limit : ℕ}
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit) :
    ∃ block, ((e.world k).state w).blocks[((e.world k).state w).justifiedCheckpoint.root]? =
      some block := by
  sorry

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

/-- The unslashed active balances sum to at most the cap when the registry indices fit. -/
private theorem p7_unslashed_sum_le {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) (stakeLe : ActiveStakeAtMost stakeCapGwei state) :
    ((unslashedActiveBalances state).map fun entry => entry.2.toNat).sum ≤ stakeCapGwei := by
  classical
  let entries := unslashedActiveBalances state
  have balance : ∀ entry ∈ entries, balanceAt state entry.1.toNat = entry.2.toNat := by
    rintro ⟨index, gwei⟩ member
    simp only [entries, unslashedActiveBalances, List.mem_filterMap,
      Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, Prod.exists] at member
    obtain ⟨validator, i, inZip, -, rfl, rfl⟩ := member
    have found := List.mem_zipIdx_iff_getElem?.mp inZip
    have lt : i < state.validators.data.size := by
      simpa using (List.getElem?_eq_some_iff.mp found).1
    rw [toNat_toUInt64_of_lt within lt]
    simp [balanceAt, by simpa using found]
  have distinct : (entries.map (·.1)).Nodup := by
    have sorted := validatorPositions_sorted within
      fun validator => isActiveValidator validator (getCurrentEpoch state) && !validator.slashed
    have same : entries.map (·.1) = state.validators.data.toList.zipIdx.filterMap
        fun (validator, index) =>
          if isActiveValidator validator (getCurrentEpoch state) && !validator.slashed then
            some index.toUInt64
          else none := by
      simp only [entries, unslashedActiveBalances, List.map_filterMap]
      congr 1
      funext entry
      split <;> rfl
    rw [same]
    exact sorted.imp UInt64.ne_of_lt
  have subset : (entries.map (·.1)).toFinset ⊆
      (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset := by
    intro v member
    simp only [List.mem_toFinset, List.mem_map] at member
    obtain ⟨⟨index, gwei⟩, inside, rfl⟩ := member
    simp only [entries, unslashedActiveBalances, List.mem_filterMap,
      Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, Prod.exists] at inside
    obtain ⟨validator, i, inZip, active, rfl, -⟩ := inside
    simp only [List.mem_toFinset, getActiveValidatorIndices, List.mem_filterMap,
      Option.ite_none_right_eq_some, Option.some.injEq, Prod.exists]
    exact ⟨validator, i, inZip, (Bool.and_eq_true_iff.mp active).1, rfl⟩
  have eq : stake (fun v => balanceAt state v.toNat) (entries.map (·.1)).toFinset =
      (entries.map fun entry => entry.2.toNat).sum := by
    rw [stake, List.sum_toFinset _ distinct, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun entry member => balance entry member)
  exact eq ▸ (stake_mono subset).trans stakeLe

/-- Successful vote checks make the fold succeed, adding at most the given balances. -/
private theorem p7_fold_exists (store : Store preset fork) (node : ForkChoiceNode)
    (votes : List (ValidatorIndex × Gwei))
    (checks : ∀ entry ∈ votes, ∀ message, store.latestMessages[entry.1]? = some message →
      ∃ result, (store.getSupportedNode message >>= (store.isAncestor · node)) = .ok result)
    (initial : Nat) :
    ∃ total,
      votes.foldlM (init := initial) (fun (total : Nat) (index, balance) =>
        match store.latestMessages[index]? with
        | none => pure total
        | some message => do
          if store.equivocatingIndices.contains index then return total
          if ← store.isAncestor (← store.getSupportedNode message) node then
            return total + balance.toNat
          return total) = (Except.ok total : Except ForkChoiceError Nat) ∧
      total ≤ initial + (votes.map fun entry => entry.2.toNat).sum := by
  induction votes generalizing initial with
  | nil => exact ⟨initial, rfl, by simp⟩
  | cons entry rest ih =>
    obtain ⟨index, balance⟩ := entry
    have tail := ih (fun entry member => checks entry (List.mem_cons_of_mem _ member))
    rw [List.foldlM_cons]
    cases latest : store.latestMessages[index]? with
    | none =>
      obtain ⟨total, fold, le⟩ := tail initial
      exact ⟨total, by simpa only [latest, bind, Except.bind, pure, Except.pure] using fold,
        by simp only [List.map_cons, List.sum_cons]; omega⟩
    | some message =>
      obtain ⟨result, resultOk⟩ := checks _ List.mem_cons_self message latest
      cases supported : store.getSupportedNode message with
      | error error => simp [supported, bind, Except.bind] at resultOk
      | ok supported =>
        simp only [supported, bind, Except.bind] at resultOk
        by_cases equivocating : store.equivocatingIndices.contains index
        · obtain ⟨total, fold, le⟩ := tail initial
          exact ⟨total,
            by simpa only [latest, equivocating, ↓reduceIte,
              bind, Except.bind, pure, Except.pure] using fold,
            by simp only [List.map_cons, List.sum_cons]; omega⟩
        · cases result
          · obtain ⟨total, fold, le⟩ := tail initial
            exact ⟨total, by simpa only [latest, equivocating, supported, resultOk,
              Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure] using fold,
              by simp only [List.map_cons, List.sum_cons]; omega⟩
          · obtain ⟨total, fold, le⟩ := tail (initial + balance.toNat)
            exact ⟨total, by simpa only [latest, equivocating, supported, resultOk,
              Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure] using fold,
              by simpa [Nat.add_assoc] using le⟩

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
  have votes : ∀ entry ∈ unslashedActiveBalances state, ∀ message,
      ((e.world k).state w).latestMessages[entry.1]? = some message →
      ∃ result, (((e.world k).state w).getSupportedNode message >>=
        (((e.world k).state w).isAncestor · ⟨root, .pending⟩)) = .ok result := by
    intro entry _ message latest
    obtain ⟨attestation, _, _, same, _, origin⟩ :=
      e.exists_signed_origin_of_latestMessages anchored start honest latest
    obtain ⟨votedBlock, votedKnown, _⟩ := origin.voted
    obtain ⟨result, read⟩ := e.exists_isAncestor_of_held anchored start anchorSlot
      preGloas anchorParent honest bounded votedKnown known
    refine ⟨result, ?_⟩
    simpa only [Store.getSupportedNode_of_lt preGloas, same, LatestMessage.ofAttestation,
      bind, Except.bind] using read
  obtain ⟨total, fold, le⟩ := p7_fold_exists ((e.world k).state w)
    ⟨root, .pending⟩ (unslashedActiveBalances state) votes 0
  have totalLe : total ≤ stakeCapGwei := by
    simp only [Nat.zero_add] at le
    exact le.trans (p7_unslashed_sum_le (state.validators.bound preGloas) stakeLe)
  have fits := totalLe.trans_lt stakeCapGwei_lt
  refine ⟨total.toUInt64, ?_, ?_⟩
  · change ((e.world k).state w).getAttestationScore ⟨root, .pending⟩ state = _
    rw [Store.getAttestationScore_eq_fold, bind_ok_iff]
    refine ⟨total, fold, ?_⟩
    simp only [ite_eq_right (Nat.not_le.mpr fits), pure, Except.pure]
  · simpa only [UInt64.toNat_ofNat_of_lt' fits] using totalLe

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
