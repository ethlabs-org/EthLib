module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationDuties
public import EthLib.Consensus.Proofs.ForkChoice.PendingCommittees
public import EthLib.Consensus.Proofs.ForkChoice.TargetJustification

/-!
# Late coverage of a block of the call's own epoch

A call of the rule in epoch `E` that confirms a block of epoch `E` makes it safe until later.

A store that is two or more epochs after the block holds it in its filtered tree.

Otherwise its justified block is above the block.

The counted honest voters sign the target before the next epoch, and Assumption 3 includes them.

Their votes reach a leaf above the block, which then has a voting source of epoch `E`.

`Execution.coveredOrViableAt_of_checked` takes this as its hypothesis `currentLate`. -/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Fork}

/-- An active index names a position of the registry. -/
private theorem late_active_inside {state : BeaconState preset fork} {epoch : Epoch}
    {v : ValidatorIndex} (active : v ∈ getActiveValidatorIndices state epoch) :
    v.toNat < state.validators.data.size := by
  unfold getActiveValidatorIndices at active
  obtain ⟨⟨validator, index⟩, member, picked⟩ := List.mem_filterMap.mp active
  have bound := (List.mem_zipIdx member).2.1
  by_cases act : isActiveValidator validator epoch = true
  · simp only [act, ↓reduceIte, Option.some.injEq] at picked
    subst picked
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
    simp only [Array.length_toList, Nat.zero_add] at bound
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) bound
  · simp [act] at picked

/-- A weighing past the first two epochs reads the total active balance. -/
private theorem late_total_of_justified {state after : BeaconState preset fork}
    (computed : processJustificationAndFinalization state = .ok after)
    (counted : GENESIS_EPOCH + 1 < getCurrentEpoch state) :
    ∃ total, getTotalActiveBalance state = .ok total := by
  have late : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1 := UInt64.not_le.mpr counted
  unfold processJustificationAndFinalization at computed
  split at computed
  · simp only [processJustificationAndFinalizationAltair, late, ↓reduceIte, bind_ok_iff,
      liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, total, totalOk, _⟩ := computed
    exact ⟨total, totalOk⟩
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, total, totalOk, _⟩ := computed
    exact ⟨total, totalOk⟩

/-- The last slot of an epoch past the first two reads the total active balance. -/
private theorem late_total_of_advance {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork}
    (advanced : advanceSlot config checks state = .ok after)
    (lastSlot : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    (counted : GENESIS_EPOCH + 1 < getCurrentEpoch state) :
    ∃ total, getTotalActiveBalance state = .ok total := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, -⟩ := advanceSlot_ok advanced
  have boundary : next % preset.SLOTS_PER_EPOCH = 0 := by
    apply UInt64.toNat_inj.mp
    simpa [UInt64.toNat_mod, sum] using lastSlot
  simp only [epochIfLast, boundary, ↓reduceIte] at epochedOk
  obtain ⟨justified, justifiedOk, -⟩ := processEpoch_frame epochedOk
  obtain ⟨current, -, totalEq, -⟩ := processSlot_countingBalances cachedOk
  obtain ⟨total, totalOk⟩ := late_total_of_justified justifiedOk (current.symm ▸ counted)
  exact ⟨total, totalEq ▸ totalOk⟩

/-- The list of an epoch of a seed or the next one reads that epoch. -/
private theorem late_list_epoch {state : BeaconState preset fork} {epoch : Epoch}
    (lower : epoch ≤ getCurrentEpoch state)
    (upper : (getCurrentEpoch state).toNat < epoch.toNat + 2) :
    (if decide (getCurrentEpoch state = epoch) then getCurrentEpoch state
      else getPreviousEpoch state) = epoch := by
  by_cases same : getCurrentEpoch state = epoch
  · simp [same]
  · simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte]
    have lowerNat := UInt64.le_iff_toNat_le.mp lower
    have ne : (getCurrentEpoch state).toNat ≠ epoch.toNat := fun eq => same (UInt64.toNat_inj.mp eq)
    apply UInt64.toNat_inj.mp
    rw [getPreviousEpoch_toNat]
    omega

/-- Slots inside an epoch keep its recent root, target flags and pending attestations. -/
private theorem late_slots_keep {config : Config} {checks : SignatureChecks}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {epoch : Epoch} {root : Root} :
    ∀ {count : ℕ} {state after : BeaconState preset fork},
      advanceSlots config checks count state = .ok after →
      state.slot.toNat + count <
        ((getCurrentEpoch state).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat →
      RunKept state after ∧ getCurrentEpoch after = getCurrentEpoch state ∧
      ((getCurrentEpoch state).toNat ≤ epoch.toNat + 1 → getBlockRoot state epoch = .ok root →
        getBlockRoot after epoch = .ok root) ∧
      (∀ (altair : .altair ≤ fork) (current : Bool) (position : ℕ),
        position < state.validators.data.size →
        TargetFlagAt (recentParticipation state altair current) position →
        TargetFlagAt (recentParticipation after altair current) position) ∧
      (∀ (before : fork < .altair) (current : Bool), ∀ pending ∈ recentPending state before current,
        pending ∈ recentPending after before current)
  | 0, state, after, computed, _ => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨RunKept.refl _, rfl, fun _ read => read, fun _ _ _ _ flagged => flagged,
      fun _ _ _ member => member⟩
  | count + 1, state, after, computed, inside => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    have nextSlot := advanceSlot_slot nextOk
    have stateEpoch : (getCurrentEpoch state).toNat =
        state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      simp only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div]
    have nextEpochNat : (getCurrentEpoch next).toNat =
        next.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      simp only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div]
    have low := Nat.div_mul_le_self state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    rw [← stateEpoch] at low
    have same : getCurrentEpoch next = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      rw [nextEpochNat, nextSlot]
      apply Nat.div_eq_of_lt_le
      · omega
      · rw [Nat.add_mul, Nat.one_mul]
        rw [Nat.add_mul, Nat.one_mul] at inside
        omega
    have nextInside : next.slot.toNat + count <
        ((getCurrentEpoch next).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
      rw [same, nextSlot]
      omega
    obtain ⟨run, epochEq, roots, flags, pendings⟩ :=
      late_slots_keep positive window (epoch := epoch) (root := root) rest nextInside
    have step := runKept_advanceSlot nextOk
    refine ⟨step.trans run, epochEq.trans same, fun near read => ?_, ?_, ?_⟩
    · apply roots (same ▸ near)
      apply getBlockRoot_advanceSlot nextOk read
      rw [Nat.add_mul, Nat.one_mul] at inside
      have := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat near
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    · intro altair current position within flagged
      exact flags altair current position (Nat.lt_of_lt_of_le within step.grows)
        ((advanceSlot_keepsTargetFlag nextOk altair within current flagged).1 same)
    · intro before current pending member
      exact pendings before current pending
        ((advanceSlot_keepsPending before nextOk current member).1 same)

/-- A block keeps the run, the epoch, each root, each target flag and each pending attestation. -/
private theorem late_block_keep {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    {state after : BeaconState preset fork}
    (computed : processBlock config checks engine state block = .ok after)
    {epoch : Epoch} {root : Root} :
    RunKept state after ∧ getCurrentEpoch after = getCurrentEpoch state ∧
      ((getCurrentEpoch state).toNat ≤ epoch.toNat + 1 → getBlockRoot state epoch = .ok root →
        getBlockRoot after epoch = .ok root) ∧
      (∀ (altair : .altair ≤ fork) (current : Bool) (position : ℕ),
        position < state.validators.data.size →
        TargetFlagAt (recentParticipation state altair current) position →
        TargetFlagAt (recentParticipation after altair current) position) ∧
      (∀ (before : fork < .altair) (current : Bool), ∀ pending ∈ recentPending state before current,
        pending ∈ recentPending after before current) := by
  have slotEq := processBlock_slot computed
  refine ⟨runKept_processBlock computed, by simp only [getCurrentEpoch, slotEq], ?_,
    fun altair current _ inside flagged =>
      processBlock_keepsTargetFlag computed altair current inside flagged,
    fun before current _ member => processBlock_keepsPending before computed current member⟩
  intro _ read
  unfold getBlockRoot at read ⊢
  simpa only [getBlockRootAtSlot_congr slotEq (processBlock_blockRoots computed)] using read

/-- A state that keeps the seed's votes passes them on through a step that keeps them. -/
private theorem late_kept_trans {seed state after : BeaconState preset fork}
    {epoch : Epoch} {root : Root} {recent : Bool}
    (near : (getCurrentEpoch seed).toNat ≤ epoch.toNat + 1)
    (kept : RunKept seed state ∧ getCurrentEpoch state = getCurrentEpoch seed ∧
      getBlockRoot state epoch = .ok root ∧
      (∀ (altair : .altair ≤ fork) (position : ℕ), position < seed.validators.data.size →
        TargetFlagAt (recentParticipation seed altair recent) position →
        TargetFlagAt (recentParticipation state altair recent) position) ∧
      (∀ (before : fork < .altair), ∀ pending ∈ recentPending seed before recent,
        pending ∈ recentPending state before recent))
    (step : RunKept state after ∧ getCurrentEpoch after = getCurrentEpoch state ∧
      ((getCurrentEpoch state).toNat ≤ epoch.toNat + 1 → getBlockRoot state epoch = .ok root →
        getBlockRoot after epoch = .ok root) ∧
      (∀ (altair : .altair ≤ fork) (current : Bool) (position : ℕ),
        position < state.validators.data.size →
        TargetFlagAt (recentParticipation state altair current) position →
        TargetFlagAt (recentParticipation after altair current) position) ∧
      (∀ (before : fork < .altair) (current : Bool), ∀ pending ∈ recentPending state before current,
        pending ∈ recentPending after before current)) :
    RunKept seed after ∧ getCurrentEpoch after = getCurrentEpoch seed ∧
      getBlockRoot after epoch = .ok root ∧
      (∀ (altair : .altair ≤ fork) (position : ℕ), position < seed.validators.data.size →
        TargetFlagAt (recentParticipation seed altair recent) position →
        TargetFlagAt (recentParticipation after altair recent) position) ∧
      (∀ (before : fork < .altair), ∀ pending ∈ recentPending seed before recent,
        pending ∈ recentPending after before recent) := by
  obtain ⟨run, epochEq, read, flags, pendings⟩ := kept
  obtain ⟨run', epochEq', roots, flags', pendings'⟩ := step
  exact ⟨run.trans run', epochEq'.trans epochEq, roots (epochEq ▸ near) read,
    fun altair position inside flagged => flags' altair recent position
      (Nat.lt_of_lt_of_le inside run.grows) (flags altair position inside flagged),
    fun before pending member => pendings' before recent pending (pendings before pending member)⟩

namespace Models.Network

/-- Above a seed, each block state keeps its votes within that epoch, or has justified it.

The weighing at the last slot of the seed's epoch is the hypothesis `weigh`. -/
private theorem late_carry {config : Config} {checks : SignatureChecks}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (preGloas : fork < .glamsterdam)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {engine : ExecutionEngine preset fork}
    (transitions : ∀ (root : Root) (block : BeaconBlock preset fork)
      (state : BeaconState preset fork), store.blocks[root]? = some block →
      store.blockStates[root]? = some state → block ≠ anchorBlock →
      ∃ parent signed, signed.message = block ∧
        store.blockStates[block.parentRoot]? = some parent ∧
        stateTransition config checks engine parent signed true = .ok state)
    {seed : ForkChoiceNode} {seedSlot : Slot} {seedState : BeaconState preset fork}
    (anchorBelow : anchorBlock.slot ≤ seedSlot)
    (seedStored : store.blockStates[seed.root]? = some seedState)
    {epoch : Epoch} {root : Root} {recent : Bool}
    (near : (getCurrentEpoch seedState).toNat ≤ epoch.toNat + 1)
    (seedRead : getBlockRoot seedState epoch = .ok root)
    (weigh : ∀ (parent : Root) (parentState state after : BeaconState preset fork)
        (child : Root) (childBlock : BeaconBlock preset fork),
      store.blockStates[parent]? = some parentState →
      store.getAncestor ⟨parent, .pending⟩ seedSlot = .ok seed →
      store.blocks[child]? = some childBlock → childBlock.parentRoot = parent →
      (state = parentState ∨ ∃ slot, slot ≤ childBlock.slot ∧
        processSlots config checks parentState slot = .ok state) →
      (RunKept seedState state ∧ getCurrentEpoch state = getCurrentEpoch seedState ∧
        getBlockRoot state epoch = .ok root ∧
        (∀ (altair : .altair ≤ fork) (position : ℕ), position < seedState.validators.data.size →
          TargetFlagAt (recentParticipation seedState altair recent) position →
          TargetFlagAt (recentParticipation state altair recent) position) ∧
        (∀ (before : fork < .altair), ∀ pending ∈ recentPending seedState before recent,
          pending ∈ recentPending state before recent)) →
      advanceSlot config checks state = .ok after →
      (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
      epoch ≤ after.currentJustifiedCheckpoint.epoch)
    {node : ForkChoiceNode} {state : BeaconState preset fork}
    (held : store.blockStates[node.root]? = some state)
    (walk : store.getAncestor node seedSlot = .ok seed) :
    (RunKept seedState state ∧ getCurrentEpoch state = getCurrentEpoch seedState ∧
      getBlockRoot state epoch = .ok root ∧
      (∀ (altair : .altair ≤ fork) (position : ℕ), position < seedState.validators.data.size →
        TargetFlagAt (recentParticipation seedState altair recent) position →
        TargetFlagAt (recentParticipation state altair recent) position) ∧
      (∀ (before : fork < .altair), ∀ pending ∈ recentPending seedState before recent,
        pending ∈ recentPending state before recent)) ∨
      epoch ≤ state.currentJustifiedCheckpoint.epoch := by
  obtain ⟨block, found⟩ := reachable.known_of_blockState held
  by_cases low : block.slot ≤ seedSlot
  · rw [Store.getAncestor_of_le found low] at walk
    cases walk
    rw [held, Option.some.injEq] at seedStored
    subst seedStored
    exact .inl ⟨RunKept.refl _, rfl, seedRead, fun _ _ _ flagged => flagged,
      fun _ _ member => member⟩
  have other : block ≠ anchorBlock := fun same => low (same ▸ anchorBelow)
  obtain ⟨parentState, signed, message, parentHeld, transition⟩ :=
    transitions node.root block state found held other
  rw [Store.getAncestor] at walk
  split at walk
  · simp_all
  rename_i b same
  rw [found, Option.some.injEq] at same
  subst b
  simp only [low, ↓reduceIte] at walk
  split at walk
  · simp [throw, throwThe, MonadExceptOf.throw] at walk
  rename_i parent parentFound
  split at walk
  swap
  · simp [throw, throwThe, MonadExceptOf.throw] at walk
  have parentInv := (reachable.ordered sound).2 parentHeld
  obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok transition
  have slotBounds := stateTransition_slot transition
  rw [message] at slotsOk blockOk slotBounds
  have cjEq : state.currentJustifiedCheckpoint = advanced.currentJustifiedCheckpoint :=
    (frame_processBlock blockOk).currentJustified
  rcases late_carry reachable sound preGloas positive window transitions anchorBelow seedStored near
      seedRead weigh parentHeld walk with kept | justified
  swap
  · exact .inr (UInt64.le_trans justified
      (stateTransition_currentJustified_mono parentInv transition))
  have parentEpochNat : (getCurrentEpoch parentState).toNat =
      parentState.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    simp only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div]
  have parentHigh : parentState.slot.toNat <
      ((getCurrentEpoch parentState).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
    rw [parentEpochNat, Nat.add_mul, Nat.one_mul]
    have := Nat.lt_div_mul_add (a := parentState.slot.toNat) positive
    omega
  have blockAfter := UInt64.lt_iff_toNat_lt.mp slotBounds.1
  have blockFits := block.slot.toNat_lt
  by_cases inEpoch : block.slot.toNat <
      ((getCurrentEpoch parentState).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat
  · simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
    obtain ⟨_, _, advancedOk⟩ := slotsOk
    have slotsKeep := late_slots_keep positive window (epoch := epoch) (root := root) advancedOk
      (by omega)
    exact .inl (late_kept_trans near (late_kept_trans near kept slotsKeep)
      (late_block_keep blockOk))
  obtain ⟨middle, middleShape, middleSlot, middleKept, middleRest⟩ : ∃ middle,
      (middle = parentState ∨ ∃ slot, slot ≤ block.slot ∧
        processSlots config checks parentState slot = .ok middle) ∧
      middle.slot.toNat + 1 =
        ((getCurrentEpoch parentState).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat ∧
      (RunKept seedState middle ∧ getCurrentEpoch middle = getCurrentEpoch seedState ∧
        getBlockRoot middle epoch = .ok root ∧
        (∀ (altair : .altair ≤ fork) (position : ℕ), position < seedState.validators.data.size →
          TargetFlagAt (recentParticipation seedState altair recent) position →
          TargetFlagAt (recentParticipation middle altair recent) position) ∧
        (∀ (before : fork < .altair), ∀ pending ∈ recentPending seedState before recent,
          pending ∈ recentPending middle before recent)) ∧
      processSlots config checks middle block.slot = .ok advanced := by
    by_cases atEnd : parentState.slot.toNat + 1 =
        ((getCurrentEpoch parentState).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat
    · exact ⟨parentState, .inl rfl, atEnd, kept, slotsOk⟩
    have lastNat : (UInt64.ofNat (((getCurrentEpoch parentState).toNat + 1) *
        preset.SLOTS_PER_EPOCH.toNat - 1)).toNat =
        ((getCurrentEpoch parentState).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat - 1 := by
      rw [UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨middle, firstOk, restOk⟩ := processSlots_split
      (UInt64.lt_iff_toNat_lt.mpr (by rw [lastNat]; omega))
      (UInt64.lt_iff_toNat_lt.mpr (by rw [lastNat]; omega)) slotsOk
    have middleSlot := (processSlots_slot firstOk).2
    have firstCopy := firstOk
    simp only [processSlots, bind_ok_iff, ensure_ok_iff] at firstCopy
    obtain ⟨_, _, advancing⟩ := firstCopy
    have keep := late_slots_keep positive window (epoch := epoch) (root := root) advancing
      (by rw [lastNat]; omega)
    refine ⟨middle, .inr ⟨_, UInt64.le_iff_toNat_le.mpr (by rw [lastNat]; omega), firstOk⟩,
      by rw [middleSlot, lastNat]; omega, late_kept_trans near kept keep, restOk⟩
  have middleInv : Invariant middle := by
    rcases middleShape with same | ⟨_, _, ok⟩
    · exact same ▸ parentInv
    · exact (processSlots_invariant parentInv ok).1
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at middleRest
  obtain ⟨_, _, restAdvance⟩ := middleRest
  have countPos : block.slot.toNat - middle.slot.toNat =
      (block.slot.toNat - middle.slot.toNat - 1) + 1 := by omega
  rw [countPos] at restAdvance
  simp only [advanceSlots, bind_ok_iff] at restAdvance
  obtain ⟨next, nextOk, tail⟩ := restAdvance
  have justified := weigh _ parentState middle next node.root block parentHeld
    (by rwa [Store.parentPayloadStatus_of_lt preGloas] at walk) found rfl
    middleShape middleKept nextOk (by rw [middleSlot]; exact Nat.mul_mod_left _ _)
  have nextInv := (advanceSlot_invariant middleInv nextOk).1
  rw [cjEq]
  exact .inr (UInt64.le_trans justified (advanceSlots_currentJustified_mono nextInv tail))
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transition
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

end Models.Network

namespace Models.Network

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J} [DecidablePred (· ∈ J)]

omit [DecidablePred (· ∈ J)] in
/-- A root of the call's own epoch has a target check of that epoch at or before the call.

Its start is of the epoch before, and the call itself checked the target.

Or its start is of the same epoch, and the record of the start serves for the root above it. -/
private theorem late_root_checked {anchorRoot : Root} {margin : ℕ}
    (preGloas : fork < .glamsterdam) {u : ValidatorIndex} {n : ℕ}
    (upToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    {fcr : FastConfirmationStore} {head : ForkChoiceNode} {start root : Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (checked : ((e.world n).state u).Checked config fcr head.root start root)
    (onChain : ((e.world n).state u).isAncestor ⟨head.root, .pending⟩ ⟨root, .pending⟩ =
      .ok true)
    {slot : Slot} {begin : UInt64} {epoch : Epoch}
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok slot)
    (beginOk : computeTimeAtSlotMs config genesisTimeMs slot = .ok begin)
    (atSlot : (e.world n).time = begin.toNat)
    (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    (rootEpochOk : ((e.world n).state u).getBlockEpoch root = .ok epoch)
    (targetVotes : ∀ state target anc,
      ((e.world n).state u).getPulledUpHeadState config head.root = .ok state →
      ((e.world n).state u).getCurrentTarget config head.root = .ok target →
      ((e.world n).state u).blockStates[target.root]? = some anc →
      HonestTargetVotes e (margin + quorumReserve config state anc) u n head.root)
    (lineage : ((e.world n).state u).getBlockEpoch start = .ok epoch →
      TargetChecked e margin anchorRoot u n epoch start)
    (rootAboveStart : ((e.world n).state u).isAncestor ⟨root, .pending⟩ ⟨start, .pending⟩ =
      .ok true)
    (rootSafe : SafeAt e (e.world n).time root) :
    TargetChecked e margin anchorRoot u n epoch root := by
  obtain ⟨readEpoch, readSlot, rootEpoch, startEpoch, readEpochOk, _, readRootOk, startEpochOk,
    _, branches⟩ := checked
  cases Except.ok.inj (readEpochOk.symm.trans epochOk)
  cases Except.ok.inj (readRootOk.symm.trans rootEpochOk)
  by_cases sameStart : startEpoch = epoch
  · subst sameStart
    obtain ⟨k, kLe, origin, _, originEpoch, startAbove, record, originSafe⟩ :=
      lineage startEpochOk
    have startRead := rootAboveStart
    unfold Store.isAncestor at startRead
    obtain ⟨startBlockRead, startBlockOk, _⟩ := bind_ok_iff.mp startRead
    have originRead := startAbove
    unfold Store.isAncestor at originRead
    obtain ⟨originBlockRead, originBlockOk, _⟩ := bind_ok_iff.mp originRead
    exact ⟨k, kLe, origin, rootEpochOk, originEpoch,
      Store.isAncestor_trans_of_lt preGloas (Store.block_ok_iff.mp startBlockOk)
        (Store.block_ok_iff.mp originBlockOk) rootAboveStart startAbove, record, originSafe⟩
  rcases branches with old | current
  · exact absurd rfl old.2.1
  have check := current.2.1 rfl sameStart
  have rootRead := onChain
  unfold Store.isAncestor at rootRead
  obtain ⟨rootBlockRead, rootBlockOk, _⟩ := bind_ok_iff.mp rootRead
  refine ⟨n, le_rfl, root, rootEpochOk, rootEpochOk,
    Store.isAncestor_self (node := ⟨root, .pending⟩) (Store.block_ok_iff.mp rootBlockOk),
    .inr ⟨head, upToDate, epochOk, headOk, check, onChain, targetVotes, slot, begin, slotOk,
      beginOk, atSlot⟩, fun time lower upper => ?_⟩
  have same : time = (e.world n).time := Nat.le_antisymm upper lower
  exact same ▸ rootSafe

omit [DecidablePred (· ∈ J)] in
/-- A target check with the count of the rule names an honest quorum with its surplus.

The check reads two thirds of the active balance in the honest support of the target.

The count adds the margin and the quorum reserve of the target state on top of that support. -/
private theorem late_quorum_of_record {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor) (preGloas : fork < .glamsterdam)
    {u : ValidatorIndex} (caller : u ∈ J) {q margin : ℕ} {head : Root}
    (check : ((e.world q).state u).willCurrentTargetBeJustified config head = .ok true)
    (count : ∀ state target anc,
      ((e.world q).state u).getPulledUpHeadState config head = .ok state →
      ((e.world q).state u).getCurrentTarget config head = .ok target →
      ((e.world q).state u).blockStates[target.root]? = some anc →
      HonestTargetVotes e (margin + quorumReserve config state anc) u q head) :
    ∃ (state anc : BeaconState preset fork) (total : Gwei) (target : Checkpoint)
      (slot first last : Slot) (participants : Std.TreeSet ValidatorIndex)
      (voters : Finset ValidatorIndex),
      ((e.world q).state u).getPulledUpHeadState config head = .ok state ∧
      getTotalActiveBalance state = .ok total ∧
      ((e.world q).state u).getCurrentTarget config head = .ok target ∧
      ((e.world q).state u).blockStates[target.root]? = some anc ∧
      ((e.world q).state u).getCurrentSlot config = .ok slot ∧
      ((e.world q).state u).getCurrentStoreEpoch config = .ok target.epoch ∧
      computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot) = .ok first ∧
      subChecked slot 1 = .ok last ∧
      ((e.world q).state u).getCommitteesBetweenSlots head first last = .ok participants ∧
      ((e.world q).state u).getCheckpointBlock head target.epoch = .ok target.root ∧
      (∀ v ∈ voters, v ∈ J ∧ v ∈ activeVoters state ∧
        (SignsTarget e v target (e.world q).time ∨ v ∉ participants)) ∧
      2 * total.toNat + (margin + quorumReserve config state anc) ≤
        3 * stake (fun v => balanceAt state v.toNat) voters := by
  obtain ⟨state, total, support, -, -, stateOk, totalOk, supportOk, -, -, -⟩ :=
    Store.willCurrentTargetBeJustified_eq_ok_true_iff.mp check
  have enough := Store.two_mul_le_three_mul_of_willCurrentTargetBeJustified
    stateOk totalOk supportOk check
  have reachable := e.reachable
    (fun a ha => (anchored a ha) ▸ Store.Reachable.anchor anchorStore) q u caller
  obtain ⟨target, targetOk⟩ : ∃ target,
      ((e.world q).state u).getCurrentTarget config head = .ok target := by
    have score := supportOk
    unfold Store.computeHonestFfgSupportForCurrentTarget at score
    simp only [bind_ok_iff, mapError_ok_iff] at score
    obtain ⟨_, _, _, _, _, _, scoreValue, scoreOk, _⟩ := score
    unfold Store.getCurrentTargetScore at scoreOk
    obtain ⟨target, targetOk, _⟩ := bind_ok_iff.mp scoreOk
    exact ⟨target, targetOk⟩
  obtain ⟨epoch, checkpoint, _, read, rfl⟩ := Store.getCurrentTarget_eq_ok_iff.mp targetOk
  obtain ⟨_, block, _, held, _, _⟩ := Store.isAncestor_of_getCheckpointBlock preGloas read
  obtain ⟨anc, stored, _⟩ := reachable.blockStatesFromParents held
  obtain ⟨readTarget, slot, first, last, participants, voters, readTargetOk, slotOk, epochOk,
    firstOk, lastOk, participantsOk, targetRead, members, counted⟩ :=
    coverage_quorum_of_count (count state ⟨epoch, checkpoint⟩ anc stateOk targetOk stored)
      stateOk supportOk
  have same := Except.ok.inj (readTargetOk.symm.trans targetOk)
  subst same
  exact ⟨state, anc, total, ⟨epoch, checkpoint⟩, slot, first, last, participants, voters,
    stateOk, totalOk, targetOk, stored, slotOk, epochOk, firstOk, lastOk, participantsOk,
    targetRead, members, by omega⟩

omit [DecidablePred (· ∈ J)] in
/-- An ancestry that one honest store reads holds in another store that holds the descendant. -/
private theorem late_copy_ancestor {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor) (preGloas : fork < .glamsterdam)
    {limit : ℕ} (oneBlock : OneBlockPerRoot e limit)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : ℕ}
    (nBound : (e.world n).time ≤ limit) (kBound : (e.world k).time ≤ limit)
    {a b : Root} {aBlock bBlock : BeaconBlock preset fork}
    (bKnown : ((e.world n).state u).blocks[b]? = some bBlock)
    (above : ((e.world n).state u).isAncestor ⟨a, .pending⟩ ⟨b, .pending⟩ = .ok true)
    (aReceived : ((e.world k).state w).blocks[a]? = some aBlock) :
    ((e.world k).state w).isAncestor ⟨a, .pending⟩ ⟨b, .pending⟩ = .ok true := by
  have reached := e.reachable
    (fun x hx => (anchored x hx) ▸ Store.Reachable.anchor anchorStore) n u caller
  have received := e.reachable
    (fun x hx => (anchored x hx) ▸ Store.Reachable.anchor anchorStore) k w receiver
  have walk := Store.getAncestor_of_isAncestor_of_lt preGloas bKnown above
  have copied := Store.getAncestor_of_same_blocks received
    (oneBlock u caller w receiver n k nBound kBound) (reached.anchorSlot_le_block bKnown)
    ⟨aBlock, aReceived⟩ walk
  obtain ⟨other, otherHeld, _⟩ := Store.getAncestor_le copied
  have same := oneBlock w receiver u caller k n kBound nBound b other bBlock otherHeld bKnown
  subst same
  simp [Store.isAncestor, Store.block_ok_iff.mpr otherHeld, copied, bind, Except.bind, pure,
    Except.pure]

omit [DecidablePred (· ∈ J)] in
/-- Safety of a block protects each ancestor that an honest store reads below it. -/
private theorem late_safe_ancestor {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor) (preGloas : fork < .glamsterdam)
    {limit : ℕ} (oneBlock : OneBlockPerRoot e limit)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} (nBound : (e.world n).time ≤ limit)
    {root origin : Root} {originBlock : BeaconBlock preset fork}
    (originKnown : ((e.world n).state u).blocks[origin]? = some originBlock)
    (descends : ((e.world n).state u).isAncestor ⟨root, .pending⟩ ⟨origin, .pending⟩ =
      .ok true)
    {time : ℕ} (bounded : time ≤ limit) (safe : SafeAt e time root) :
    SafeAt e time origin := by
  intro w receiver k head atTime ready headOk
  have kBound : (e.world k).time ≤ limit := atTime ▸ bounded
  have supports := safe w receiver k head atTime ready headOk
  have rootRead := supports
  unfold Store.isAncestor at rootRead
  obtain ⟨rootBlock, rootBlockOk, _⟩ := bind_ok_iff.mp rootRead
  have rootHeld := Store.block_ok_iff.mp rootBlockOk
  have ancestry := late_copy_ancestor anchorStore anchored preGloas oneBlock caller receiver
    nBound kBound originKnown descends rootHeld
  have originRead := ancestry
  unfold Store.isAncestor at originRead
  obtain ⟨heldBlock, heldBlockOk, _⟩ := bind_ok_iff.mp originRead
  exact Store.isAncestor_trans_of_lt preGloas rootHeld (Store.block_ok_iff.mp heldBlockOk)
    supports ancestry

/-- The boundary of the epoch after an epoch reads at a later slot two epochs on. -/
private theorem late_next_boundary {epoch : Epoch} {current : Slot} {currentBegin : UInt64}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (late : epoch.toNat + 1 < (computeEpochAtSlot preset current).toNat)
    (currentBeginOk : computeTimeAtSlotMs config genesisTimeMs current = .ok currentBegin) :
    ∃ (next : Epoch) (boundary : Slot) (begin : UInt64),
      addChecked epoch 1 = .ok next ∧ computeStartSlotAtEpoch preset next = .ok boundary ∧
      computeTimeAtSlotMs config genesisTimeMs boundary = .ok begin ∧ boundary < current ∧
      begin ≤ currentBegin := by
  have curNat : (computeEpochAtSlot preset current).toNat =
      current.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
  rw [curNat] at late
  have twoBelow : (epoch.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat ≤ current.toNat :=
    (Nat.le_div_iff_mul_le positive).mp (by omega)
  have split : (epoch.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat =
      (epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat := by
    ring
  have fits : (epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat < current.toNat := by omega
  have currentFits := current.toNat_lt
  have nextFits : epoch.toNat + 1 < 2 ^ 64 := by
    have := Nat.le_mul_of_pos_right (epoch.toNat + 1) positive
    omega
  have nextNat : (epoch + 1).toNat = epoch.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one]
    exact Nat.mod_eq_of_lt nextFits
  have nextOk : addChecked epoch 1 = .ok (epoch + 1) :=
    addChecked_ok_iff.mpr ⟨by rw [UInt64.toNat_one]; exact nextFits,
      by rw [nextNat, UInt64.toNat_one]⟩
  have boundaryNat : (UInt64.ofNat ((epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat)).toNat =
      (epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have boundaryOk : computeStartSlotAtEpoch preset (epoch + 1) =
      .ok (UInt64.ofNat ((epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat)) :=
    computeStartSlotAtEpoch_ok_iff.mpr ⟨by rw [nextNat]; omega, by rw [boundaryNat, nextNat]⟩
  have boundaryLt : UInt64.ofNat ((epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat) < current :=
    UInt64.lt_iff_toNat_lt.mpr (by rw [boundaryNat]; exact fits)
  obtain ⟨begin, beginOk, _, beginLe⟩ :=
    exists_timeAtSlotMs_of_le (UInt64.le_of_lt boundaryLt) currentBeginOk
  exact ⟨epoch + 1, _, begin, nextOk, boundaryOk, beginOk, boundaryLt, beginLe⟩

/-- A block of the call's own epoch stays covered or viable for each later receiver.

The receiver is two or more epochs after the block, and its justified block is below it.

The hypotheses are those of `Execution.coveredOrViableAt_of_checked`. -/
theorem Execution.coveredOrViableAt_late_current {Δ : ℕ} (sync : e.Synchronous Δ)
    (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (incrementPositive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (retained : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (preGloas : fork < .glamsterdam)
    {time : ℕ} (admitted : BlocksAdmitted e 0 Δ time)
    (oneBlock : OneBlockPerRoot e time)
    (votes : Votes e.startTime time e) (fits : DelayFits fork config genesisTimeMs Δ)
    (prompt : Prompt e time) (committees : CommitteesFollow e time)
    (follows : HeadFollowsSupport e time)
    {horizon anchorEpoch : Epoch} {margin : ℕ}
    (chain : FinalizedPrefix e horizon time)
    (unique : OneJustifiedPerEpoch e horizon time)
    (pins : HonestThirdPins e anchorEpoch horizon margin time)
    (voted : JustifiedByHonestVote e anchorEpoch horizon time) (included : TargetIncluded e time)
    {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (anchorAtBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (upToDate : UpToDate config checks sources (e.world n).time ((e.world n).view u)
      ((e.world n).state u))
    (atSlot : ∃ slot begin,
      ((e.world n).state u).getCurrentSlot config = .ok slot ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧
      (e.world n).time = begin.toNat)
    (callEpochs : ∀ epoch, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
      GENESIS_EPOCH + 1 < epoch ∧ getCurrentEpoch anchorState < epoch)
    {fcr : FastConfirmationStore} {head : ForkChoiceNode} {start root : Root}
    (headOk : ((e.world n).state u).getHead config = .ok head)
    (checked : ((e.world n).state u).Checked config fcr head.root start root)
    (onChain : ((e.world n).state u).isAncestor ⟨head.root, .pending⟩ ⟨root, .pending⟩ =
      .ok true)
    (atStart : ∀ slot rootEpoch epoch,
      ((e.world n).state u).getCurrentSlot config = .ok slot →
      isStartSlotAtEpoch preset slot = .ok true →
      ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
      ((e.world n).state u).getBlockEpoch root = .ok rootEpoch →
      rootEpoch = epoch → root = ((e.world n).state u).finalizedCheckpoint.root)
    (previousHead : fcr.previousSlotHead = anchor.finalizedCheckpoint.root ∨
      ∃ k < n, ∃ previous previousSlot currentSlot,
        UpToDate config checks sources (e.world k).time ((e.world k).view u)
          ((e.world k).state u) ∧
        ((e.world k).state u).getHead config = .ok previous ∧
        previous.root = fcr.previousSlotHead ∧
        ((e.world k).state u).getCurrentSlot config = .ok previousSlot ∧
        ((e.world n).state u).getCurrentSlot config = .ok currentSlot ∧
        addChecked previousSlot 1 = .ok currentSlot)
    (targetVotes : ∀ slot, ((e.world n).state u).getCurrentSlot config = .ok slot →
      isStartSlotAtEpoch preset slot = .ok false → ∀ state target anc,
      ((e.world n).state u).getPulledUpHeadState config head.root = .ok state →
      ((e.world n).state u).getCurrentTarget config head.root = .ok target →
      ((e.world n).state u).blockStates[target.root]? = some anc →
      HonestTargetVotes e (margin + quorumReserve config state anc) u n head.root)
    (lineage : ∀ epoch, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
      ((e.world n).state u).getBlockEpoch start = .ok epoch →
      TargetChecked e margin anchor.finalizedCheckpoint.root u n epoch start)
    (previousLineage : ∀ epoch previous slot,
      ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
      ((e.world n).state u).getCurrentSlot config = .ok slot →
      isStartSlotAtEpoch preset slot = .ok true → addChecked previous 1 = .ok epoch →
      ((e.world n).state u).getBlockEpoch start = .ok previous →
      TargetChecked e margin anchor.finalizedCheckpoint.root u n previous start ∨
        (((e.world n).state u).unrealizedJustification head.root =
          .ok fcr.currentEpochObservedJustifiedCheckpoint ∧
          start = fcr.currentEpochObservedJustifiedCheckpoint.root))
    (later : (e.world n).time ≤ time)
    (nonzero : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ∀ (r : Root) (b : BeaconBlock preset fork),
        ((e.world k).state w).blocks[r]? = some b → b.stateRoot ≠ Vector.replicate 32 0)
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ time →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (supply : ∀ w ∈ J, ∀ k (checkpoint : Checkpoint) (state : BeaconState preset fork),
      (e.world k).time ≤ time → ((e.world k).state w).checkpointState checkpoint = .ok state →
      ActiveStakeAtMost stakeCapGwei state)
    (quorumDrifts : ∀ u ∈ J, ∀ n (head : Root) (pulled anc : BeaconState preset fork)
        (target : Checkpoint),
      (e.world n).time ≤ time →
      ((e.world n).state u).getPulledUpHeadState config head = .ok pulled →
      ((e.world n).state u).getCurrentTarget config head = .ok target →
      ((e.world n).state u).blockStates[target.root]? = some anc →
      ∀ w ∈ J, ∀ k (root : Root) (rootState state : BeaconState preset fork),
      (e.world k).time ≤ time → ((e.world k).state w).blockStates[root]? = some rootState →
      ((e.world k).state w).getCheckpointBlock root target.epoch = .ok target.root →
      (state = rootState ∨ ∃ slot, processSlots config checks rootState slot = .ok state) →
      target.epoch ≤ getCurrentEpoch state →
      (getCurrentEpoch state).toNat ≤ target.epoch.toNat + 1 → getCurrentEpoch state ≤ horizon →
      ∀ (voters : Finset ValidatorIndex) (total pulledTotal : Gwei),
      (∀ v ∈ voters, v ∈ activeVoters pulled ∧ NotSlashed state v) →
      getTotalActiveBalance state = .ok total → getTotalActiveBalance pulled = .ok pulledTotal →
      2 * total.toNat + 3 * stake (fun v => balanceAt pulled v.toNat) voters ≤
        2 * pulledTotal.toNat + 3 * stake (fun v => balanceAt state v.toNat) voters +
          quorumReserve config pulled anc)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    (large : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      (e.world k).time ≤ time → ((e.world k).state w).Counts config state →
      getCurrentEpoch state ≤ horizon →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun v => balanceAt state v.toNat) (activeVoters state))
    (unslashed : ∀ w ∈ J, ∀ k (state : BeaconState preset fork), (e.world k).time ≤ time →
      ((e.world k).state w).Counts config state → ∀ v ∈ J, NotSlashed state v)
    (long : 1 < preset.SLOTS_PER_EPOCH) (boost : config.PROPOSER_SCORE_BOOST.toNat ≤ 100)
    (startSafe : ∀ earlier, (e.world n).time ≤ earlier → earlier ≤ time → SafeAt e earlier start)
    (safe : ∀ earlier, (e.world n).time ≤ earlier → earlier < time → SafeAt e earlier root)
    (known : ∀ w ∈ J, ∀ k, (e.world k).time = time →
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w) →
      ∃ block, ((e.world k).state w).blocks[root]? = some block)
    (realized : ((e.world n).state u).RealizedRecent [root])
    (rootRecent : ∀ epoch block, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
      ((e.world n).state u).blocks[root]? = some block →
      epoch.toNat ≤ (computeEpochAtSlot preset block.slot).toNat + 1)
    (realizedHead : ∀ epoch block, ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
      ((e.world n).state u).blocks[root]? = some block →
      computeEpochAtSlot preset block.slot < epoch →
      ∃ headState, ((e.world n).state u).blockStates[head.root]? = some headState ∧
        ((e.world n).state u).isAncestor head ⟨root, .pending⟩ = .ok true ∧
        computeEpochAtSlot preset block.slot ≤ headState.currentJustifiedCheckpoint.epoch)
    (sourceLe : ∀ w ∈ J, ∀ k (tip : Root) (source : Checkpoint), (e.world k).time = time →
      getCurrentEpoch anchorState ≤ ((e.world k).state w).justifiedCheckpoint.epoch →
      ((e.world k).state w).getVotingSource config tip = .ok source →
      source.epoch ≤ ((e.world k).state w).justifiedCheckpoint.epoch)
    (genesis : ∀ w ∈ J, ∀ i, ((e.world i).state w).genesisTimeMs = genesisTimeMs)
    (rootAfterStart : ∀ rootBlock startBlock,
      ((e.world n).state u).blocks[root]? = some rootBlock →
      ((e.world n).state u).blocks[start]? = some startBlock → startBlock.slot < rootBlock.slot) :
    ∀ w ∈ J, ∀ k nodes (rootBlock : BeaconBlock preset fork) (slot current : Slot),
      (e.world k).time = time →
      UpToDate config checks sources (e.world k).time ((e.world k).view w)
        ((e.world k).state w) →
      ((e.world k).state w).getFilteredNodeTree config = .ok nodes →
      ((e.world n).state u).blocks[root]? = some rootBlock →
      ((e.world n).state u).getCurrentSlot config = .ok slot →
      computeEpochAtSlot preset rootBlock.slot = computeEpochAtSlot preset slot →
      ((e.world k).state w).getCurrentSlot config = .ok current →
      (computeEpochAtSlot preset rootBlock.slot).toNat + 1 <
        (computeEpochAtSlot preset current).toNat →
      ((e.world k).state w).isAncestor ⟨root, .pending⟩
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ = .ok true →
      ((e.world k).state w).isAncestor
          ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
        (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes := by
  intro w receiver k nodes rootBlock slot current atTime ready tree rootKnown slotOk sameEpoch
    currentOk lateEpoch descends
  have pending : head = (⟨head.root, .pending⟩ : ForkChoiceNode) := by
    have p := Store.getHead_pending preGloas headOk
    cases head
    simp_all
  -- The root is above the start of the walk.
  have startHead := startSafe _ le_rfl later u caller n head rfl upToDate headOk
  have startRead := startHead
  unfold Store.isAncestor at startRead
  obtain ⟨startBlock, startBlockOk, _⟩ := bind_ok_iff.mp startRead
  have startKnown := Store.block_ok_iff.mp startBlockOk
  have rootHead : ((e.world n).state u).isAncestor head ⟨root, .pending⟩ = .ok true := by
    rw [pending]
    exact onChain
  have rootAboveStart : ((e.world n).state u).isAncestor ⟨root, .pending⟩ ⟨start, .pending⟩ =
      .ok true := by
    rcases coverage_ancestors_comparable preGloas rootKnown startKnown rootHead startHead with
      above | below
    · exact above
    · obtain ⟨startNodeBlock, startNodeKnown, le⟩ := Store.slot_le_of_isAncestor rootKnown below
      have same := Option.some.inj (startNodeKnown.symm.trans startKnown)
      subst same
      exact absurd (rootAfterStart rootBlock startNodeBlock rootKnown startKnown)
        (UInt64.not_lt.mpr le)
  -- The receiver is at a later time than the call, so the root is safe at the call.
  have callerSlot := mapError_ok_iff.mp slotOk
  have receiverSlot := mapError_ok_iff.mp currentOk
  change computeSlotAtTimeMs config ((e.world n).state u).genesisTimeMs
    ((e.world n).state u).timeMs = .ok slot at callerSlot
  change computeSlotAtTimeMs config ((e.world k).state w).genesisTimeMs
    ((e.world k).state w).timeMs = .ok current at receiverSlot
  rw [genesis u caller n] at callerSlot
  rw [genesis w receiver k] at receiverSlot
  have afterCall : (e.world n).time < time := by
    rcases Nat.lt_or_eq_of_le later with lt | eq
    · exact lt
    exfalso
    have sameMs : ((e.world n).state u).timeMs = ((e.world k).state w).timeMs :=
      UInt64.toNat_inj.mp (by rw [upToDate.1, ready.1, atTime, eq])
    rw [sameMs, receiverSlot, Except.ok.injEq] at callerSlot
    subst callerSlot
    rw [sameEpoch] at lateEpoch
    omega
  have rootSafe := safe _ le_rfl afterCall
  obtain ⟨callSlot, callBegin, callSlotOk, callBeginOk, atCall⟩ := atSlot
  have slotEq := Except.ok.inj (callSlotOk.symm.trans slotOk)
  subst slotEq
  have epochOk : ((e.world n).state u).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset callSlot) := by
    simp [Store.getCurrentStoreEpoch, callSlotOk, bind, Except.bind, pure, Except.pure]
  have rootEpochOk : ((e.world n).state u).getBlockEpoch root =
      .ok (computeEpochAtSlot preset callSlot) := by
    simp [Store.getBlockEpoch, Store.block_ok_iff.mpr rootKnown, sameEpoch, bind, Except.bind,
      pure, Except.pure]
  by_cases atBoundary : isStartSlotAtEpoch preset callSlot = .ok false
  swap
  -- A root of the call's own epoch at an epoch start is the finalized root.
  · have startTrue : isStartSlotAtEpoch preset callSlot = .ok true := by
      have first := computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) callSlot
      unfold isStartSlotAtEpoch computeSlotsSinceEpochStart at atBoundary ⊢
      rw [first] at atBoundary ⊢
      simp only [Except.mapError, bind, Except.bind, pure, Except.pure, Except.ok.injEq]
        at atBoundary ⊢
      simpa using atBoundary
    have finalRoot := atStart callSlot _ _ callSlotOk startTrue epochOk rootEpochOk rfl
    obtain ⟨jb, jk⟩ := Store.filterNodeTree_known tree
    rcases e.finalizedCheckpoint_eq_or_add_two_le anchorStore sound (anchored u caller)
        epochOk with same | age
    -- The anchor's root is below every block that an honest store holds.
    · rw [finalRoot, same]
      exact .inl (e.isAncestor_anchor_of_known anchorStore anchored receiver jk)
    -- A later finalized root is at or before the first slot of an epoch two before the call.
    have forwardCaller := e.forwardReachable
      (fun v hv => (anchored v hv) ▸ Store.ForwardReachable.anchor anchorStore) n u caller
    have justifiedHorizon := UInt64.le_trans ((forwardCaller.justified_epoch_le_current sound
      slots (UInt64.le_of_eq anchorSlot) epochOk).1) (inHorizon u caller n _ later epochOk)
    have read := chain u caller u caller n n later later _ (.inl rfl)
      (forwardCaller.reachable.finalized_le_justified sound) justifiedHorizon
    obtain ⟨boundary, finalBlock, boundaryOk, finalKnown, finalBefore, _⟩ :=
      Store.isAncestor_of_getCheckpointBlock preGloas read
    rw [← finalRoot, rootKnown, Option.some.injEq] at finalKnown
    subst finalBlock
    have boundaryNat := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
    have slotLe := UInt64.le_iff_toNat_le.mp finalBefore
    have rootEpochNat : (computeEpochAtSlot preset callSlot).toNat =
        rootBlock.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      rw [← sameEpoch]
      simp only [computeEpochAtSlot, UInt64.toNat_div]
    have bound := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
      (show rootBlock.slot.toNat ≤
        ((e.world n).state u).finalizedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat
        by omega)
    rw [Nat.mul_div_cancel _ positive] at bound
    omega
  -- The quorum record of the root's epoch.
  have record := late_root_checked preGloas upToDate headOk checked onChain callSlotOk
    callBeginOk atCall epochOk rootEpochOk
    (targetVotes callSlot callSlotOk atBoundary)
    (lineage _ epochOk) rootAboveStart rootSafe
  obtain ⟨q, qLe, origin, _, originEpoch, rootAboveOrigin, arm, originSafe⟩ := record
  rcases arm with anchorOrigin | ⟨headQ, readyQ, epochQ, headQOk, checkQ, originBelowHeadQ,
    countQ, slotQ, beginQ, slotQOk, beginQOk, atQ⟩
  -- An origin at the anchor would put the call in the anchor's epoch.
  · obtain ⟨anchorKey, anchorHash, anchorKnown⟩ :=
      (e.reachable (fun v hv => (anchored v hv) ▸ Store.Reachable.anchor anchorStore) n u
        caller).anchor_known
    obtain ⟨anchorRoot, rootHash, _, _, _, anchorFinal, _⟩ := getForkchoiceStore_anchor anchorStore
    have sameKey := Except.ok.inj (anchorHash.symm.trans rootHash)
    subst sameKey
    subst anchorOrigin
    simp only [anchorFinal] at originEpoch
    simp only [Store.getBlockEpoch, Store.block_ok_iff.mpr anchorKnown, bind, Except.bind, pure,
      Except.pure, Except.ok.injEq] at originEpoch
    have after := (callEpochs _ epochOk).2
    rw [← originEpoch, anchorSlot] at after
    exact absurd after (UInt64.lt_irrefl _)
  obtain ⟨stateQ, ancQ, totalQ, target, slotQ', firstQ, lastQ, participantsQ, voters, stateQOk,
    totalQOk, targetQOk, ancQStored, slotQOk', targetEpochQ, firstQOk, lastQOk, participantsQOk,
    targetReadQ, members, quorum⟩ :=
    late_quorum_of_record anchorStore anchored preGloas caller checkQ countQ
  -- The target of the record is of the call's epoch, and so is the origin.
  have slotQEq := Except.ok.inj (slotQOk'.symm.trans slotQOk)
  rw [slotQEq] at firstQOk lastQOk
  have targetEpoch : target.epoch = computeEpochAtSlot preset callSlot :=
    Except.ok.inj (targetEpochQ.symm.trans epochQ)
  have firstOk : computeStartSlotAtEpoch preset target.epoch = .ok firstQ := by
    have slotEpoch : computeEpochAtSlot preset slotQ = target.epoch := by
      simpa [Store.getCurrentStoreEpoch, slotQOk, bind, Except.bind, pure, Except.pure]
        using targetEpochQ
    rw [← slotEpoch]
    exact firstQOk
  have originRead := originBelowHeadQ
  unfold Store.isAncestor at originRead
  obtain ⟨originBlock, originBlockOk, _⟩ := bind_ok_iff.mp originRead
  have originHeldQ := Store.block_ok_iff.mp originBlockOk
  have originHeldN := e.blocks_of_le qLe originHeldQ
  have originEpochEq : computeEpochAtSlot preset originBlock.slot = target.epoch := by
    rw [targetEpoch]
    simpa [Store.getBlockEpoch, Store.block_ok_iff.mpr originHeldN, bind, Except.bind, pure,
      Except.pure] using originEpoch
  -- The boundary of the next epoch is before the receiver.
  obtain ⟨currentBegin, currentBeginOk, currentBeginLe⟩ :=
    exists_slot_start_of_current_slot receiverSlot
  have currentBeginBound : currentBegin.toNat ≤ time := by
    rw [← atTime, ← ready.1]
    exact UInt64.le_iff_toNat_le.mp currentBeginLe
  have lateNat : (computeEpochAtSlot preset callSlot).toNat + 1 <
      (computeEpochAtSlot preset current).toNat := by
    simpa only [sameEpoch] using lateEpoch
  obtain ⟨nextEpoch, boundary, begin, nextOk, boundaryOk, beginOk, boundaryLt, _⟩ :=
    late_next_boundary positive lateNat currentBeginOk
  rw [← targetEpoch] at nextOk
  have beginBefore : begin.toNat < time := by
    have := coverage_delay_before_later_slot fits boundaryLt beginOk currentBeginOk
    omega
  have qBound : (e.world q).time ≤ time := (e.monotone_time qLe).trans later
  -- The origin stays safe through the boundary: recorded before the call, then below the root.
  have originSafe' : ∀ t, (e.world q).time ≤ t → t ≤ begin.toNat → SafeAt e t origin := by
    intro t low high
    by_cases early : t ≤ (e.world n).time
    · exact originSafe t low early
    · exact late_safe_ancestor anchorStore anchored preGloas oneBlock caller later originHeldN
        rootAboveOrigin (by omega) (safe t (Nat.le_of_lt (Nat.lt_of_not_ge early)) (by omega))
  -- Each counted honest voter signs the target before the next epoch.
  have signed := e.signsTarget_by_boundary anchorStore sound anchored anchorSlot anchorAtBoundary
    slots positive long window preGloas boost oneBlock prompt committees follows retained votes
    fits nonzero anchorParent inHorizon large supply caller readyQ headQOk stateQOk targetQOk
    targetEpochQ slotQOk beginQOk atQ firstOk lastQOk participantsQOk originHeldQ originEpochEq
    originBelowHeadQ nextOk boundaryOk beginOk (Nat.le_of_lt beginBefore) originSafe' members
  -- The receiver reads the target as the checkpoint of the root.
  obtain ⟨receivedRoot, receivedRootHeld⟩ := known w receiver k atTime ready
  have rootAboveOriginReceiver := late_copy_ancestor anchorStore anchored preGloas oneBlock
    caller receiver later atTime.le originHeldN rootAboveOrigin receivedRootHeld
  have rootRead := coverage_target_read anchorStore anchored preGloas oneBlock caller receiver
    qBound atTime.le targetReadQ originHeldQ originBelowHeadQ originEpochEq
    rootAboveOriginReceiver
  have sameRoot := oneBlock u caller w receiver n k later atTime.le root rootBlock receivedRoot
    rootKnown receivedRootHeld
  subst sameRoot
  have rootEpochReceiver : ((e.world k).state w).getBlockEpoch root = .ok target.epoch := by
    simp [Store.getBlockEpoch, Store.block_ok_iff.mpr receivedRootHeld, sameEpoch, targetEpoch,
      bind, Except.bind, pure, Except.pure]
  have receiverEpochOk : ((e.world k).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset current) := by
    simp [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
  -- Assumption 3: a seed above the root carries the voters' target votes.
  obtain ⟨seed, seedBlock, seedState, seedHeld, seedStored, seedAbove, seedLower, seedUpper,
      seedRead, seedVotes⟩ :=
    included u caller q n qLe later headQ stateQ totalQ target voters headQOk stateQOk targetQOk
      totalQOk targetEpochQ (by rw [targetEpoch]; exact epochOk) (by omega) nextEpoch boundary
      begin nextOk boundaryOk beginOk (fun v member => ⟨(members v member).1, signed v member⟩)
      w receiver k (computeEpochAtSlot preset current) atTime.le (by rw [atTime]; exact later)
      ready receiverEpochOk (by rw [targetEpoch]; omega) root target.epoch rootEpochReceiver
      (UInt64.le_refl _) rootRead (fun t low high => safe t low (by rw [← atTime]; exact high))
  have targetLate : GENESIS_EPOCH + 1 < target.epoch := targetEpoch ▸ (callEpochs _ epochOk).1
  have anchorBefore : getCurrentEpoch anchorState < target.epoch :=
    targetEpoch ▸ (callEpochs _ epochOk).2
  have forward := e.forwardReachable
    (fun v hv => (anchored v hv) ▸ Store.ForwardReachable.anchor anchorStore)
  have reached := (forward k w receiver).reachable
  have lower := reached.parentsBelow (UInt64.le_of_eq anchorSlot)
    (anchorParent w receiver k atTime.le)
  obtain ⟨jb, jk⟩ := Store.filterNodeTree_known tree
  have anchorEpochEq : anchorEpoch = getCurrentEpoch anchorState := by
    obtain ⟨_, _, _, _, anchorJustified, _⟩ := getForkchoiceStore_anchor anchorStore
    rw [← anchorOk, anchorJustified]
  have slotEpochNat (slot : Slot) :
      (computeEpochAtSlot preset slot).toNat = slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
  have rootEpochNat : target.epoch.toNat =
      rootBlock.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    rw [targetEpoch, ← sameEpoch, slotEpochNat]
  have rootSlotHigh : rootBlock.slot.toNat <
      (target.epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
    rw [rootEpochNat, Nat.add_mul, Nat.one_mul]
    have := Nat.lt_div_mul_add (a := rootBlock.slot.toNat) positive
    omega
  have anchorBelowRoot : getCurrentEpoch anchorState ≤ target.epoch := by
    have le := UInt64.le_iff_toNat_le.mp (reached.anchorSlot_le_block receivedRootHeld)
    rw [anchorSlot] at le
    apply UInt64.le_iff_toNat_le.mpr
    rw [rootEpochNat, getCurrentEpoch, slotEpochNat]
    exact Nat.div_le_div_right le
  have currentNat := slotEpochNat current
  have justifiedCurrent := ((forward k w receiver).justified_epoch_le_current sound slots
    (UInt64.le_of_eq anchorSlot) receiverEpochOk).1
  have receiverHorizon := inHorizon w receiver k _ atTime.le receiverEpochOk
  have targetNat := congrArg UInt64.toNat targetEpoch
  by_cases justifiedLate : target.epoch < ((e.world k).state w).justifiedCheckpoint.epoch
  -- A receiver justification after the root's epoch is above the root.
  · have jLe := UInt64.le_iff_toNat_le.mp justifiedCurrent
    rw [currentNat] at jLe
    have jFits : ((e.world k).state w).justifiedCheckpoint.epoch.toNat *
        preset.SLOTS_PER_EPOCH.toNat ≤ current.toNat :=
      (Nat.mul_le_mul_right _ jLe).trans (Nat.div_mul_le_self _ _)
    have currentFits := current.toNat_lt
    have boundaryNat : (UInt64.ofNat (((e.world k).state w).justifiedCheckpoint.epoch.toNat *
        preset.SLOTS_PER_EPOCH.toNat)).toNat =
        ((e.world k).state w).justifiedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := by
      rw [UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by omega)
    have boundaryOk : computeStartSlotAtEpoch preset
        ((e.world k).state w).justifiedCheckpoint.epoch =
          .ok (UInt64.ofNat (((e.world k).state w).justifiedCheckpoint.epoch.toNat *
            preset.SLOTS_PER_EPOCH.toNat)) :=
      computeStartSlotAtEpoch_ok_iff.mpr ⟨by omega, boundaryNat⟩
    have startEpochOk : ((e.world n).state u).getBlockEpoch start =
        .ok (computeEpochAtSlot preset startBlock.slot) := by
      simp [Store.getBlockEpoch, Store.block_ok_iff.mpr startKnown, bind, Except.bind, pure,
        Except.pure]
    have startEpochLe : computeEpochAtSlot preset startBlock.slot ≤ target.epoch := by
      apply UInt64.le_iff_toNat_le.mpr
      rw [rootEpochNat, slotEpochNat]
      exact Nat.div_le_div_right (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp
        (rootAfterStart rootBlock startBlock rootKnown startKnown)))
    rcases coverage_current_justified anchorStore anchorSlot anchored preGloas positive slots
        incrementPositive fits oneBlock unique pins voted committees (by omega) anchorOk nonzero
        inHorizon caller receiver later atTime.le ready headOk checked rootHead
        ⟨callSlot, callBegin, callSlotOk, callBeginOk, atCall⟩
        (fun slot slotOk inside => coverage_targetVotes_of_reserve anchorStore anchored preGloas
          caller (targetVotes slot slotOk inside))
        epochOk rootEpochOk startEpochOk
        (fun _ => UInt64.lt_of_le_of_lt startEpochLe justifiedLate) currentOk
        (by rw [← targetEpoch]; exact UInt64.le_of_lt justifiedLate)
        (by rw [anchorEpochEq]; exact UInt64.lt_of_le_of_lt anchorBelowRoot justifiedLate)
        (UInt64.le_trans justifiedCurrent receiverHorizon) boundaryOk receivedRootHeld jk
        (fun t low high => safe t low (by rw [← atTime]; exact high)) with covered | ⟨_, early⟩
    · exact .inl covered
    · have before := UInt64.lt_iff_toNat_lt.mp (early _ boundaryOk)
      rw [boundaryNat] at before
      have step := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat
        (show target.epoch.toNat + 1 ≤ ((e.world k).state w).justifiedCheckpoint.epoch.toNat from
          UInt64.lt_iff_toNat_lt.mp justifiedLate)
      omega
  have justifiedLe : ((e.world k).state w).justifiedCheckpoint.epoch ≤ target.epoch :=
    UInt64.not_lt.mp justifiedLate
  -- A leaf above the seed, and its voting source.
  have seedAboveJ := Store.isAncestor_trans_of_lt preGloas receivedRootHeld jk seedAbove descends
  have path := (Store.isAncestor_iff (lower := lower) preGloas jk rfl seedAboveJ).mp rfl
  obtain ⟨leaf, leafBlock, leafKnown, leafPath, terminal, ⟨verdict, read⟩, _⟩ :=
    Store.exists_leaf_above_of_filterNodeTree (lower := lower) preGloas seedHeld path tree
  have leafAboveSeed : ((e.world k).state w).isAncestor ⟨leaf, .pending⟩ ⟨seed, .pending⟩ =
      .ok true := by
    obtain ⟨result, resultOk⟩ := e.exists_isAncestor_of_held anchorStore anchored anchorSlot
      preGloas anchorParent receiver atTime.le leafKnown seedHeld
    have eq := (Store.isAncestor_iff (lower := lower) (node := ⟨seed, .pending⟩) preGloas
      seedHeld rfl resultOk).mpr leafPath
    exact eq ▸ resultOk
  have leafAboveRoot := Store.isAncestor_trans_of_lt (middle := ⟨seed, .pending⟩) preGloas
    seedHeld receivedRootHeld leafAboveSeed seedAbove
  obtain ⟨leafState, leafStored, _⟩ := reached.blockStatesFromParents leafKnown
  unfold Store.isViableLeaf at read
  rw [bind_ok_iff] at read
  obtain ⟨ep, epOk, read⟩ := read
  have epEq := Except.ok.inj (epOk.symm.trans receiverEpochOk)
  subst ep
  rw [bind_ok_iff] at read
  obtain ⟨source, sourceOk, _⟩ := read
  -- A stored state is at the slot of its block.
  have stateSlot : ∀ (r : Root) (b : BeaconBlock preset fork) (st : BeaconState preset fork),
      ((e.world k).state w).blocks[r]? = some b →
      ((e.world k).state w).blockStates[r]? = some st → st.slot = b.slot := by
    intro r b st found stored
    by_cases same : b = anchorBlock
    · obtain ⟨post, postOk, atAnchor, -⟩ := reached.blockStatesFromParents found
      rw [stored, Option.some.injEq] at postOk
      rw [postOk, atAnchor same, same, anchorSlot]
    · exact (reached.blockState_header found stored same).1
  have seedEpochEq : getCurrentEpoch seedState = computeEpochAtSlot preset seedBlock.slot := by
    simp only [getCurrentEpoch, stateSlot seed seedBlock seedState seedHeld seedStored]
  have near : (getCurrentEpoch seedState).toNat ≤ target.epoch.toNat + 1 := by
    rw [seedEpochEq]
    omega
  have listEpoch : ∀ X : BeaconState preset fork,
      getCurrentEpoch X = computeEpochAtSlot preset seedBlock.slot →
      (if decide (computeEpochAtSlot preset seedBlock.slot = target.epoch) then getCurrentEpoch X
        else getPreviousEpoch X) = target.epoch := by
    intro X epochEq
    have list := late_list_epoch (state := X) (by rw [epochEq]; exact seedLower)
      (by rw [epochEq]; exact seedUpper)
    rw [epochEq] at list ⊢
    exact list
  -- The voting source of the leaf is at least the root's epoch.
  have sourceLower : target.epoch ≤ source.epoch := by
    rcases seedVotes with realizedSeed | seedVotes
    · exact UInt64.le_trans realizedSeed
        (walk_realized_le_source reached sound preGloas seedHeld seedStored leafAboveSeed sourceOk)
    have originReceiver := rootAboveOriginReceiver
    unfold Store.isAncestor at originReceiver
    obtain ⟨originReceived, originReceivedOk, _⟩ := bind_ok_iff.mp originReceiver
    have originHeldReceiver := Store.block_ok_iff.mp originReceivedOk
    have seedAboveOrigin := Store.isAncestor_trans_of_lt preGloas receivedRootHeld
      originHeldReceiver seedAbove rootAboveOriginReceiver
    have pulledEpoch := coverage_pulled_epoch_of_current_epoch (forward q u caller) positive
      targetEpochQ stateQOk
    -- The counted voters are active at the target epoch in each state above the origin.
    have activeAt : ∀ (P : Root) (Ps : BeaconState preset fork),
        ((e.world k).state w).blockStates[P]? = some Ps →
        ((e.world k).state w).isAncestor ⟨P, .pending⟩ ⟨origin, .pending⟩ = .ok true →
        ∀ v ∈ voters, v ∈ getActiveValidatorIndices Ps target.epoch := by
      intro P Ps stored descendsOrigin v member
      have same := coverage_activity_eq_of_common_ancestor anchorStore anchored anchorSlot
        preGloas oneBlock caller receiver qBound atTime.le originHeldQ originHeldReceiver stateQOk
        (Store.blockState_ok_iff.mpr stored) originBelowHeadQ descendsOrigin
      rw [originEpochEq] at same
      rw [← same, ← pulledEpoch]
      simpa only [activeVoters, List.mem_toFinset] using (members v member).2.1
    have transitions : ∀ (r : Root) (b : BeaconBlock preset fork) (st : BeaconState preset fork),
        ((e.world k).state w).blocks[r]? = some b →
        ((e.world k).state w).blockStates[r]? = some st → b ≠ anchorBlock →
        ∃ parent signed, signed.message = b ∧
          ((e.world k).state w).blockStates[b.parentRoot]? = some parent ∧
          stateTransition config checks sources.engine parent signed true = .ok st :=
      fun _ _ _ found stored other => e.exists_transition_of_nonanchor_block anchorStore
        receiver (anchored w receiver) found stored other
    have rootFirst : firstQ ≤ rootBlock.slot := UInt64.le_iff_toNat_le.mpr (by
      rw [(computeStartSlotAtEpoch_ok_iff.mp firstOk).2, rootEpochNat]
      exact Nat.div_mul_le_self _ _)
    -- A state that keeps the seed's votes and that the store counts can weigh them.
    have weighAt : ∀ (P : Root) (Ps W : BeaconState preset fork) (total : Gwei),
        ((e.world k).state w).blockStates[P]? = some Ps →
        ((e.world k).state w).getAncestor ⟨P, .pending⟩ seedBlock.slot = .ok ⟨seed, .pending⟩ →
        ((e.world k).state w).Counts config W →
        (W = Ps ∨ ∃ slot, processSlots config checks Ps slot = .ok W) →
        (RunKept seedState W ∧ getCurrentEpoch W = getCurrentEpoch seedState ∧
          getBlockRoot W target.epoch = .ok target.root ∧
          (∀ (altair : .altair ≤ fork) (position : ℕ),
            position < seedState.validators.data.size →
            TargetFlagAt (recentParticipation seedState altair
              (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch))) position →
            TargetFlagAt (recentParticipation W altair
              (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch))) position) ∧
          (∀ (before : fork < .altair), ∀ pending ∈ recentPending seedState before
              (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)),
            pending ∈ recentPending W before
              (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)))) →
        getTotalActiveBalance W = .ok total →
        getBlockRoot W (if decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)
          then getCurrentEpoch W else getPreviousEpoch W) = .ok target.root ∧
        2 * total.toNat ≤ 3 * stake (fun v => balanceAt W v.toNat) voters ∧
        ∀ v ∈ voters,
          v ∈ getActiveValidatorIndices W
            (if decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)
              then getCurrentEpoch W else getPreviousEpoch W) ∧
          NotSlashed W v ∧
          ((∃ altair : .altair ≤ fork, TargetFlagAt (recentParticipation W altair
              (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch))) v.toNat) ∨
            ∃ before : fork < .altair, ∃ pending ∈ recentPending W before
                (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)),
              pending.data.target.root = target.root ∧
              ∃ indices, getPendingAttestingIndices W pending = .ok indices ∧ v ∈ indices) := by
      intro P Ps W total stored walk counts shape kept totalOk
      obtain ⟨run, epochW, readW, flagsW, pendingW⟩ := kept
      have epochSeed := epochW.trans seedEpochEq
      have list := listEpoch W epochSeed
      have aboveSeed := Store.isAncestor_of_getAncestor walk
      have aboveOrigin := Store.isAncestor_trans_of_lt preGloas seedHeld originHeldReceiver
        aboveSeed seedAboveOrigin
      have seedRun := coverage_runKept_of_ancestor reached transitions
        (reached.anchorSlot_le_block seedHeld) seedStored stored walk
      have activeP := activeAt P Ps stored aboveOrigin
      have activeW : ∀ v ∈ voters, v ∈ getActiveValidatorIndices W target.epoch := by
        intro v member
        rcases shape with same | ⟨_, ok⟩
        · exact same ▸ activeP v member
        · rw [(runKept_processSlots ok).active.getActiveValidatorIndices_eq
            (UInt64.le_trans (UInt64.le_trans (by rw [seedEpochEq]; exact seedLower)
              seedRun.later) (getCurrentEpoch_le_activityFixedEpoch Ps))]
          exact activeP v member
      have clean : ∀ v ∈ voters, NotSlashed W v := fun v member =>
        unslashed w receiver k W atTime.le counts v (members v member).1
      have checkRead := Store.getCheckpointBlock_of_isAncestor preGloas receivedRootHeld
        (Store.isAncestor_trans_of_lt preGloas seedHeld receivedRootHeld aboveSeed seedAbove)
        firstOk rootFirst rootRead
      have epochWNat : (getCurrentEpoch W).toNat ≤ target.epoch.toNat + 1 := by
        rw [epochSeed]
        omega
      have drift := quorumDrifts u caller q headQ.root stateQ ancQ target qBound stateQOk
        targetQOk ancQStored w receiver k P Ps W atTime.le stored checkRead shape
        (by rw [epochSeed]; exact seedLower) epochWNat
        (UInt64.le_trans (UInt64.le_iff_toNat_le.mpr (by omega)) receiverHorizon) voters total
        totalQ (fun v member => ⟨(members v member).2.1, clean v member⟩) totalOk totalQOk
      refine ⟨by rw [list]; exact readW, by omega,
        fun v member => ⟨by rw [list]; exact activeW v member, clean v member, ?_⟩⟩
      rcases seedVotes with ⟨altair, flags⟩ | ⟨before, pendings⟩
      · exact .inl ⟨altair, flagsW altair v.toNat
          (late_active_inside (activeAt seed seedState seedStored seedAboveOrigin v member))
          (flags v member)⟩
      · obtain ⟨pending, pendingMember, pendingTarget, indices, indicesOk, mem⟩ :=
          pendings v member
        obtain ⟨_, slotEpoch, -⟩ := countedPending_held anchorStore sound receiver
          (anchored w receiver) seedStored before
          (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch))
          (by rw [listEpoch seedState seedEpochEq]; exact anchorBefore) pending pendingMember
        refine .inr ⟨before, pending, pendingW before pending pendingMember,
          by rw [pendingTarget], indices, ?_, mem⟩
        rw [run.pendingAttestingIndices_eq_through_next_epoch retained
          (by rw [slotEpoch, pendingTarget, seedEpochEq]; exact seedLower)
          (by rw [slotEpoch, pendingTarget]; exact epochWNat)]
        exact indicesOk
    -- The last slot of the seed's epoch justifies the target.
    have weigh : ∀ (parent : Root) (parentState state after : BeaconState preset fork)
        (child : Root) (childBlock : BeaconBlock preset fork),
        ((e.world k).state w).blockStates[parent]? = some parentState →
        ((e.world k).state w).getAncestor ⟨parent, .pending⟩ seedBlock.slot =
          .ok ⟨seed, .pending⟩ →
        ((e.world k).state w).blocks[child]? = some childBlock → childBlock.parentRoot = parent →
        (state = parentState ∨ ∃ slot, slot ≤ childBlock.slot ∧
          processSlots config checks parentState slot = .ok state) →
        (RunKept seedState state ∧ getCurrentEpoch state = getCurrentEpoch seedState ∧
          getBlockRoot state target.epoch = .ok target.root ∧
          (∀ (altair : .altair ≤ fork) (position : ℕ),
            position < seedState.validators.data.size →
            TargetFlagAt (recentParticipation seedState altair
              (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch))) position →
            TargetFlagAt (recentParticipation state altair
              (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch))) position) ∧
          (∀ (before : fork < .altair), ∀ pending ∈ recentPending seedState before
              (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)),
            pending ∈ recentPending state before
              (decide (computeEpochAtSlot preset seedBlock.slot = target.epoch)))) →
        advanceSlot config checks state = .ok after →
        (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
        target.epoch ≤ after.currentJustifiedCheckpoint.epoch := by
      intro parent parentState state after child childBlock stored walk childHeld childParent
        shape kept advanced lastSlot
      have epochSeed := kept.2.1.trans seedEpochEq
      have counted : GENESIS_EPOCH + 1 < getCurrentEpoch state :=
        UInt64.lt_of_lt_of_le targetLate (by rw [epochSeed]; exact seedLower)
      obtain ⟨total, totalOk⟩ := late_total_of_advance advanced lastSlot counted
      obtain ⟨rootOk, enough, votedW⟩ := weighAt parent parentState state total stored walk
        ⟨parent, parentState, stored, shape.imp_right fun ⟨slot, le, ok⟩ =>
          ⟨checks, slot, child, childBlock, childHeld, childParent, le, ok⟩⟩
        (shape.imp_right fun ⟨slot, _, ok⟩ => ⟨slot, ok⟩) kept totalOk
      have result := advanceSlot_justifies positive window advanced lastSlot counted _ rootOk
        totalOk enough votedW
      rwa [listEpoch state epochSeed] at result
    have leafWalk := Store.getAncestor_of_isAncestor_of_lt preGloas seedHeld leafAboveSeed
    rcases late_carry reached sound preGloas positive window transitions
        (reached.anchorSlot_le_block seedHeld) seedStored near seedRead weigh leafStored
        leafWalk with kept | justified
    swap
    · exact UInt64.le_trans justified (walk_realized_le_source reached sound preGloas leafKnown
        leafStored (Store.isAncestor_self (node := ⟨leaf, .pending⟩) leafKnown) sourceOk)
    -- The leaf is of the seed's epoch, so its source is its pull-up, which weighs the votes.
    have leafEpoch := kept.2.1.trans seedEpochEq
    have leafSlot := stateSlot leaf leafBlock leafState leafKnown leafStored
    have leafEarly : computeEpochAtSlot preset leafBlock.slot <
        computeEpochAtSlot preset current := by
      have eq : computeEpochAtSlot preset leafBlock.slot = getCurrentEpoch leafState := by
        simp only [getCurrentEpoch, leafSlot]
      rw [eq, leafEpoch]
      apply UInt64.lt_iff_toNat_lt.mpr
      omega
    have voting := sourceOk
    unfold Store.getVotingSource at voting
    simp only [bind_ok_iff] at voting
    obtain ⟨tipBlock, tipRead, tipEpoch, tipEpochOk, voting⟩ := voting
    have tipSame : tipBlock = leafBlock :=
      Option.some.inj ((Store.block_ok_iff.mp tipRead).symm.trans leafKnown)
    subst tipBlock
    have epochSame := Except.ok.inj (tipEpochOk.symm.trans receiverEpochOk)
    subst tipEpoch
    simp only [leafEarly, ↓reduceIte] at voting
    cases entry : ((e.world k).state w).unrealizedJustifications[leaf]? with
    | none => simp [entry, throw, throwThe, MonadExceptOf.throw] at voting
    | some checkpoint =>
      simp only [entry, pure, Except.pure, Except.ok.injEq] at voting
      subst source
      rcases walk_cache_origin_state reached preGloas entry with ⟨cachedEpoch, held⟩ |
        ⟨st, pulled, held, run, same⟩
      · rw [leafStored, Option.some.injEq] at held
        rw [cachedEpoch, ← held, leafEpoch]
        exact seedLower
      · rw [leafStored, Option.some.injEq] at held
        subst st
        have counted : GENESIS_EPOCH + 1 < getCurrentEpoch leafState :=
          UInt64.lt_of_lt_of_le targetLate (by rw [leafEpoch]; exact seedLower)
        obtain ⟨total, totalOk⟩ := late_total_of_justified run counted
        obtain ⟨rootOk, enough, votedW⟩ := weighAt leaf leafState leafState total leafStored
          leafWalk ⟨leaf, leafState, leafStored, .inl rfl⟩ (.inl rfl) kept totalOk
        have result := processJustificationAndFinalization_justifies run counted _ rootOk
          totalOk enough votedW
        rw [listEpoch leafState leafEpoch] at result
        rw [← same]
        exact result
  -- The source is the receiver's justification, so the leaf is viable.
  have anchorLowerJ : getCurrentEpoch anchorState ≤
      ((e.world k).state w).justifiedCheckpoint.epoch := by
    have lowerJ := (e.epochsLe_of_le w (Nat.zero_le k)).1.epoch_le
    simp only [Execution.world_zero, World.initial, anchored w receiver, anchorOk] at lowerJ
    rw [← anchorEpochEq]
    exact lowerJ
  have sourceUpper := sourceLe w receiver k leaf source atTime anchorLowerJ sourceOk
  have sourceSame : source.epoch = ((e.world k).state w).justifiedCheckpoint.epoch :=
    UInt64.le_antisymm sourceUpper (UInt64.le_trans justifiedLe sourceLower)
  have anchorHorizon : getCurrentEpoch anchorState ≤ horizon := UInt64.le_trans anchorBelowRoot
    (by rw [targetEpoch]; exact inHorizon u caller n _ later epochOk)
  have finalized : ((e.world k).state w).getCheckpointBlock leaf
      ((e.world k).state w).finalizedCheckpoint.epoch =
        .ok ((e.world k).state w).finalizedCheckpoint.root := by
    have ordered : ((e.world k).state w).finalizedCheckpoint.epoch ≤ source.epoch := by
      rw [sourceSame]
      exact reached.finalized_le_justified sound
    by_cases old : source.epoch ≤ getCurrentEpoch anchorState
    · have same := walk_finalized_eq_anchor anchorStore anchored anchorSlot anchorAtBoundary
        preGloas chain receiver atTime.le (UInt64.le_trans ordered old) anchorHorizon
      rw [same]
      exact walk_anchor_read anchorStore anchored anchorSlot anchorAtBoundary preGloas receiver
        leafKnown
    -- A leaf at the anchor has a source no later than the anchor's epoch.
    have notAnchor : leafBlock ≠ anchorBlock := by
      intro same
      apply old
      obtain ⟨post, postOk, atAnchor, -⟩ := reached.blockStatesFromParents leafKnown
      have anchorStored : ((e.world k).state w).blockStates[leaf]? = some anchorState :=
        atAnchor same ▸ postOk
      have voting := sourceOk
      unfold Store.getVotingSource at voting
      simp only [bind_ok_iff] at voting
      obtain ⟨_, _, _, _, voting⟩ := voting
      split at voting
      · cases entry : ((e.world k).state w).unrealizedJustifications[leaf]? with
        | none => simp [entry, throw, throwThe, MonadExceptOf.throw] at voting
        | some checkpoint =>
          simp only [entry, pure, Except.pure, Except.ok.injEq] at voting
          subst source
          rcases walk_cache_origin reached preGloas entry with eq |
            ⟨st, pulled, stHeld, run, sameCheckpoint⟩
          · exact UInt64.le_of_eq eq
          · rw [anchorStored, Option.some.injEq] at stHeld
            subst st
            rw [← sameCheckpoint]
            exact (processJustificationAndFinalization_invariant sound.ordered sound.settled
              run).2.2.1
      · simp only [anchorStored, pure, Except.pure, Except.ok.injEq] at voting
        subst source
        exact UInt64.le_trans sound.settled (getPreviousEpoch_le _)
    have notLe : ¬source.epoch.toNat ≤ (getCurrentEpoch anchorState).toNat :=
      fun le => old (UInt64.le_iff_toNat_le.mpr le)
    have afterGenesis : GENESIS_EPOCH < source.epoch := by
      apply UInt64.lt_iff_toNat_lt.mpr
      simp only [GENESIS_EPOCH, UInt64.toNat_zero]
      omega
    rcases walk_source_ancestor reached sound preGloas positive window
        (UInt64.le_of_eq anchorSlot) (nonzero w receiver k atTime.le)
        ⟨leaf, leafBlock, leafKnown, notAnchor⟩ (.inl sourceOk) with early |
        ⟨_, _, _, _, boundaryOk, _, sourceRead⟩
    · exact absurd early old
    · exact walk_finalized_read_of_source chain preGloas receiver receiver atTime.le atTime.le
        (.inl sourceOk) boundaryOk sourceRead ordered
        (UInt64.le_trans sourceUpper (UInt64.le_trans justifiedCurrent receiverHorizon))
        afterGenesis
  have viable : ((e.world k).state w).isViableLeaf config ⟨leaf, .pending⟩ = .ok true := by
    unfold Store.isViableLeaf
    simp [receiverEpochOk, sourceOk, sourceSame, finalized, bind, Except.bind, pure, Except.pure]
  exact .inr (coverage_mem_of_viable_leaf lower preGloas receivedRootHeld descends leafAboveRoot
    terminal viable tree)

end Models.Network

end EthLib.Consensus
