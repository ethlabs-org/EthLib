module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.CheckpointConsistency
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalReads
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalSigners
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDeep

/-!
# A pinned set signs each justified checkpoint of its epoch

A call's pinned set holds more than a third of the call's pulled-up total, with the pin reserve.

The count that set a later justified checkpoint needed two thirds of its own total.

So the stake outside the pinned set was below that, and a voter of the set voted for it.

The pin reserve pays for the drift between the call's state and the counting state.

That drift is bounded within the withdrawal delay of the finalized block's state.

Deeper calls are covered because the reserve then holds three times the call's whole active set.

The counting state's chain must read the finalized checkpoint of the call's target block.

Finality across honest stores puts it there, or gives direct-safety evidence.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- The pinned quorum and the drift bound leave the rest of the counting quorum below two thirds.

The quorum voters split into those of the set and the others.

The drift bound charges the counting state's quorum against the set's stake in both states.

Subtracting the pinned quorum leaves the others below two thirds of the counting total. -/
private theorem few_of_pin {counted pulled : BeaconState preset fork}
    {voters : Finset ValidatorIndex} {total pulledTotal reserve margin : ℕ}
    (pinned : pulledTotal + (margin + reserve) <
      3 * stake (fun v => balanceAt pulled v.toNat) voters)
    (drift : 3 * stake (fun v => balanceAt counted v.toNat) (quorumVoters counted) +
        3 * stake (fun v => balanceAt pulled v.toNat) voters ≤
      2 * total + pulledTotal + reserve +
        3 * stake (fun v => balanceAt counted v.toNat) {v ∈ quorumVoters counted | v ∈ voters}) :
    3 * stake (fun v => balanceAt counted v.toNat) {v ∈ quorumVoters counted | v ∉ voters} <
      2 * total := by
  -- The quorum's stake is that of its voters in the set plus that of the others.
  have split : stake (fun v => balanceAt counted v.toNat) (quorumVoters counted) =
      stake (fun v => balanceAt counted v.toNat) {v ∈ quorumVoters counted | v ∈ voters} +
        stake (fun v => balanceAt counted v.toNat) {v ∈ quorumVoters counted | v ∉ voters} :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  omega

/-- A held root on the way to a counting state reads the finalized checkpoint of a call's target.

The call's head is its store's head, and its target block's finalized epoch is after the anchor's.

That checkpoint is on the head's chain, at or below the call store's finalized checkpoint.

Finality across honest stores puts that checkpoint on the counting store's justified chain.

The held root reads that justified checkpoint, so it reads the target's finalized one too.

Both stores hold the blocks between, and agree on them. -/
private theorem finalized_read_of_counted {anchor : Store preset fork}
    {g : ForkedBeaconState preset} {last : Nat}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorHeader : anchorState.latestBlockHeader.slot = anchorBlock.slot ∧
      anchorState.latestBlockHeader.proposerIndex = anchorBlock.proposerIndex ∧
      anchorState.latestBlockHeader.parentRoot = anchorBlock.parentRoot ∧
      SszType.hashTreeRoot anchorBlock.body = .ok anchorState.latestBlockHeader.bodyRoot)
    (anchorZero : anchorState.latestBlockHeader.stateRoot = Vector.replicate 32 0)
    (slots : 0 < config.SLOT_DURATION_MS) (parameters : DirectSafety.Parameters preset)
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (roots : HeldBlockStateRootsNonzero (e := e) last)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last → (e.world j).time ≤ last →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    (preGloas : fork < .glamsterdam)
    (family : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last → (e.world j).time ≤ last →
      ((e.world i).state a).finalizedCheckpoint.epoch ≤
        ((e.world j).state b).justifiedCheckpoint.epoch →
      ((e.world j).state b).getCheckpointBlock ((e.world j).state b).justifiedCheckpoint.root
        ((e.world i).state a).finalizedCheckpoint.epoch =
          .ok ((e.world i).state a).finalizedCheckpoint.root)
    {u : ValidatorIndex} (hu : u ∈ J) {n : ℕ} (timeN : (e.world n).time ≤ last)
    {head : Root} (headNode : ∃ node, ((e.world n).state u).getHead config = .ok node ∧
      node.root = head)
    {epoch : Epoch} (epochOk : ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch)
    {target : Checkpoint}
    (targetOk : ((e.world n).state u).getCurrentTarget config head = .ok target)
    {anc : BeaconState preset fork}
    (ancOk : ((e.world n).state u).blockStates[target.root]? = some anc)
    (guard : getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch)
    {w : ValidatorIndex} (hw : w ∈ J) {k : ℕ} (high : (e.world k).time ≤ last)
    (justEpoch : ((e.world k).state w).justifiedCheckpoint.epoch = epoch)
    {root : Root} {base counted : BeaconState preset fork}
    (held : ((e.world k).state w).blockStates[root]? = some base)
    (advanced : counted = base ∨ ∃ slot, processSlots config checks base slot = .ok counted)
    (rootRead : getBlockRoot counted ((e.world k).state w).justifiedCheckpoint.epoch =
      .ok ((e.world k).state w).justifiedCheckpoint.root) :
    ((e.world k).state w).getCheckpointBlock root anc.finalizedCheckpoint.epoch =
      .ok anc.finalizedCheckpoint.root := by
  have reachedU := e.forwardReachableWith
    (fun a ha => (start a ha) ▸ Store.ForwardReachableWith.anchor anchored) n u hu
  have reachedW := e.forwardReachableWith
    (fun a ha => (start a ha) ▸ Store.ForwardReachableWith.anchor anchored) k w hw
  have sound : Invariant anchorState := (DirectSafety.run_justified_separated pre genesis).1
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by have := parameters.slots; omega
  have window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    have := parameters.roots; omega
  -- The finalized epochs are ordered: the target block's, the store's, then its justified one.
  have ancLe := (reachedU.reachable.ordered_finalized sound).2 ancOk
  have finalJust := reachedU.reachable.finalized_le_justified sound
  have justNow := (reachedU.forwardReachable.justified_epoch_le_current sound slots
    (UInt64.le_of_eq anchorSlot) epochOk).1
  have finalNow := UInt64.le_trans finalJust justNow
  have ancNow := UInt64.le_trans ancLe finalNow
  -- The head reads the target at the epoch, and the target's state reads its finalized checkpoint.
  obtain ⟨epoch', block, epochOk', headTarget, rfl⟩ :=
    Store.getCurrentTarget_eq_ok_iff.mp targetOk
  rw [epochOk, Except.ok.injEq] at epochOk'
  subst epoch'
  have ancRead : ((e.world n).state u).getCheckpointBlock block anc.finalizedCheckpoint.epoch =
      .ok anc.finalizedCheckpoint.root := by
    rcases reachedU.reachable.getCheckpointBlock_of_blockState sound (UInt64.le_of_eq anchorSlot)
        positive window ancOk (.inl (by simp)) guard with ⟨read, -⟩ | zero
    · exact read
    · -- The anchor state hashes to the anchor block's state root, which is not zero.
      obtain ⟨anchorRoot, -, anchorFound⟩ := reachedU.reachable.anchor_known
      have rooted := reachedU.reachable.anchorState_root
      rw [zero, Except.ok.injEq] at rooted
      exact absurd rooted.symm (roots u hu n timeN anchorRoot anchorBlock anchorFound)
  have headAnc : ((e.world n).state u).getCheckpointBlock head anc.finalizedCheckpoint.epoch =
      .ok anc.finalizedCheckpoint.root := by
    rw [Store.getCheckpointBlock_trans preGloas headTarget ancNow]
    exact ancRead
  -- The head also reads the store's finalized checkpoint, so that checkpoint reads the target's.
  obtain ⟨node, headOk, rfl⟩ := headNode
  have headFinal : ((e.world n).state u).getCheckpointBlock node.root
      ((e.world n).state u).finalizedCheckpoint.epoch =
        .ok ((e.world n).state u).finalizedCheckpoint.root := by
    rcases Store.getHead_viable headOk with viable | ⟨-, rfl⟩
    · rcases Store.isViableLeaf_finalized viable with genesisEpoch | read
      · -- At the genesis epoch the target's finalized epoch would not be after the anchor's.
        have := UInt64.le_iff_toNat_le.mp ancLe
        have := UInt64.lt_iff_toNat_lt.mp guard
        rw [genesisEpoch] at *
        simp [GENESIS_EPOCH] at *
        omega
      · exact read
    · exact family u hu u hu n n timeN timeN finalJust
  have finalAnc : ((e.world n).state u).getCheckpointBlock
      ((e.world n).state u).finalizedCheckpoint.root anc.finalizedCheckpoint.epoch =
        .ok anc.finalizedCheckpoint.root := by
    rw [← Store.getCheckpointBlock_trans preGloas headFinal ancLe]
    exact headAnc
  -- Finality across stores puts the store's finalized checkpoint on the counting store's chain.
  have justRead := family u hu w hw n k timeN high (by rw [justEpoch]; exact finalNow)
  -- The counting store holds that block and agrees with the call's store, so it reads the same.
  have finalAncW : ((e.world k).state w).getCheckpointBlock
      ((e.world n).state u).finalizedCheckpoint.root anc.finalizedCheckpoint.epoch =
        .ok anc.finalizedCheckpoint.root := by
    obtain ⟨-, finalBlock, -, finalHeld, -, -⟩ :=
      Store.isAncestor_of_getCheckpointBlock preGloas justRead
    obtain ⟨boundary, boundaryOk, walk⟩ := Store.getCheckpointBlock_walk preGloas finalAnc
    have above : anchorBlock.slot ≤ boundary := by
      have boundaryNat := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
      have guardNat := UInt64.lt_iff_toNat_lt.mp guard
      rw [getCurrentEpoch_toNat] at guardNat
      have := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat (Nat.succ_le_of_lt guardNat)
      rw [Nat.succ_mul] at this
      have := Nat.lt_div_mul_add (a := anchorState.slot.toNat) positive
      rw [UInt64.le_iff_toNat_le, boundaryNat, anchorSlot]
      omega
    have moved := Store.getAncestor_of_same_blocks reachedW.reachable
      (fun r b c hb hc => agree u hu w hw n k timeN high r b c hb hc) above
      ⟨finalBlock, finalHeld⟩ walk
    simp [Store.getCheckpointBlock, boundaryOk, moved, Except.mapError, bind, Except.bind, pure,
      Except.pure]
  -- The held root reads the counting store's justified checkpoint at its epoch.
  have ancJust :
      anc.finalizedCheckpoint.epoch ≤ ((e.world k).state w).justifiedCheckpoint.epoch := by
    rw [justEpoch]
    exact ancNow
  obtain ⟨-, rootJust⟩ := reachedW.reachable.getCheckpointBlock_of_processed anchorSlot
    anchorHeader anchorZero (roots w hw k high) held
    (advanced.imp_right fun ⟨slot, slotsOk⟩ => ⟨checks, slot, slotsOk⟩) rootRead
    fun startSlot startOk => by
      have startNat := (computeStartSlotAtEpoch_ok_iff.mp startOk).2
      have guardNat := UInt64.lt_iff_toNat_lt.mp (UInt64.lt_of_lt_of_le guard ancJust)
      rw [getCurrentEpoch_toNat] at guardNat
      have := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat (Nat.succ_le_of_lt guardNat)
      rw [Nat.succ_mul] at this
      have := Nat.lt_div_mul_add (a := anchorState.slot.toNat) positive
      rw [UInt64.le_iff_toNat_le, startNat]
      omega
  rw [Store.getCheckpointBlock_trans preGloas rootJust ancJust,
    Store.getCheckpointBlock_trans preGloas justRead ancLe]
  exact finalAncW

/-- A pinned honest set of a call signs each justified checkpoint of the call's epoch.

The set holds more than a third of the call's pulled-up total, plus `margin` and the pin reserve.

The checkpoint was set by one count, which needed two thirds of the counting state's total.

Within the withdrawal delay of the finalized block's state, `PinDriftWithin` bounds the drift.

So the quorum voters outside the set had less than two thirds there.

Deeper, the reserve holds three times the call's active set, so no such set exists.

After the anchor's epoch, the counting chain reads the target block's finalized checkpoint.

Finality across honest stores puts it there.

Otherwise two honest stores collide on a block, or there is direct-safety evidence. -/
theorem Execution.justifiedPinned {anchor : Store preset fork} {g : ForkedBeaconState preset}
    {anchorEpoch horizon : Epoch} {margin first last : Nat}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (boundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (anchorHeader : anchorState.latestBlockHeader.slot = anchorBlock.slot ∧
      anchorState.latestBlockHeader.proposerIndex = anchorBlock.proposerIndex ∧
      anchorState.latestBlockHeader.parentRoot = anchorBlock.parentRoot ∧
      SszType.hashTreeRoot anchorBlock.body = .ok anchorState.latestBlockHeader.bodyRoot)
    (anchorZero : anchorState.latestBlockHeader.stateRoot = Vector.replicate 32 0)
    (slots : 0 < config.SLOT_DURATION_MS) (parameters : DirectSafety.Parameters preset)
    (delay : preset.InclusionDelayPositive)
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (roots : HeldBlockStateRootsNonzero (e := e) last) (absent : AnchorParentAbsent (e := e) last)
    (heldEarly : HeldStatesBeforeUpgrade (e := e) last)
    (bounded : HonestStoreEpochsBounded (e := e) horizon last)
    (enough : HeldRunStakeFloor (e := e) pre horizon last)
    (terminal : HeldTerminalStakeFloor (e := e) horizon last)
    (afterAnchor : getCurrentEpoch anchorState ≤ anchorEpoch)
    (fusaka : .fusaka ≤ fork) (preGloas : fork < .glamsterdam)
    (drift : PinDriftWithin (e := e) horizon last) :
    JustifiedPinned (e := e) anchorEpoch margin first last ∨
      CrossStoreDirectSafetyEvidence (e := e) pre last := by
  rcases e.crossStoreFinality_or_evidence anchored start anchorSlot boundary slots bounded roots
      absent parameters genesis pre heldEarly enough terminal with family | evidence
  swap
  · exact .inr evidence
  refine .inl ?_
  intro u hu n head state total epoch voters timeN headNode pulledOk totalOk epochOk target anc
    fin targetOk ancOk finRead finAnchor votersOk pinned w hw k slot low high upToDate slotOk
    justEpoch after
  classical
  rcases e.blocksAgree_or_collision last with agree | collision
  swap
  · exact .inr collision
  refine .inl ?_
  -- Deeper than the withdrawal delay, the reserve covers the whole active set, so no pin exists.
  by_cases shallow : (getCurrentEpoch state).toNat + 2 - (getCurrentEpoch fin).toNat ≤
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  swap
  · have covers := deep_reserve_covers_active (anc := anc) totalOk (Nat.lt_of_not_le shallow)
    have inside : voters ⊆ activeVoters state := fun v member => (votersOk v member).2
    have mono := stake_mono (w := fun v : ValidatorIndex => balanceAt state v.toNat) inside
    omega
  have targetEpoch := Store.epoch_eq_of_getCurrentTarget epochOk targetOk
  have storeEpochOk : ((e.world k).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset slot) := by
    simp [Store.getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure]
  have horizonBound := bounded w hw k _ high storeEpochOk
  -- The count that set the checkpoint had a voter of the pinned set.
  obtain ⟨v, member, rest⟩ := e.exists_signer_of_counted (↑voters : Set ValidatorIndex)
    anchored start anchorSlot anchorHeader anchorZero slots parameters delay genesis pre roots
    absent heldEarly bounded enough terminal afterAnchor hw high slotOk
    (by rw [justEpoch]; exact after)
    fun root base counted countedTotal held path counts atLeast atMost now rootRead
        countedTotalOk => by
      rw [justEpoch] at atLeast atMost
      rcases drift fusaka u hu n head state anc fin target timeN headNode pulledOk targetOk ancOk
          finRead finAnchor shallow w hw k root base counted high held path counts
          (by rw [targetEpoch]; exact atLeast) (by rw [targetEpoch]; exact atMost)
          (UInt64.le_trans now horizonBound)
          (fun guard => finalized_read_of_counted anchored start anchorSlot anchorHeader
            anchorZero slots parameters genesis pre roots agree preGloas family hu timeN headNode
            epochOk targetOk ancOk guard hw high justEpoch held path rootRead)
          voters countedTotal total votersOk countedTotalOk totalOk with bound | collision
      · exact few_of_pin (margin := margin) pinned bound
      · exact absurd collision (e.not_honestCollision_of_agree agree)
  exact ⟨v, member, rest⟩

end EthLib.Consensus.Models.Network
