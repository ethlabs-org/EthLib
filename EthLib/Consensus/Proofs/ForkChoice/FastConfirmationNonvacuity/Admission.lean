module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.FirstBlockRoot

/-! Admission of the witness's first block into the initialized fork-choice store. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.FiveValidatorWitness

open Base Serialization.Ssz

attribute [local cbv_eval] Array.compareLex_eq_compareLex_toList

/-- The accepting engine is used by the transition; phase0 reads none of the other sources. -/
def sources : BlockSources preset .phase0 :=
  { engine := .constant true, powBlock := fun _ => none, blobsAndProofs := fun _ => none
    columns := fun _ => none
    setup := ⟨Vector.replicate _ default, Vector.replicate _ default, Vector.replicate _ default⟩
    inclusionListSatisfied := fun _ _ => true }

/-- The anchor store at the beginning of slot one. -/
def ticked : Store preset .phase0 := { anchor with timeMs := 1000 }

set_option maxRecDepth 10000 in
/-- Moving the anchor's clock to slot one changes no checkpoint. -/
theorem first_tick : anchor.onTick config 1000 = .ok ticked := by
  have caught : Store.catchUp config anchor 1 = .ok ticked := by
    rw [Store.catchUp]
    change Store.catchUp config ticked 1 = .ok ticked
    rw [Store.catchUp]
    rfl
  change (do let current ← Store.catchUp config anchor 1
             current.onTickPerSlot config 1000) = .ok ticked
  rw [caught]
  rfl

set_option maxRecDepth 10000 in
/-- The checkpoint at genesis is the anchor itself. -/
theorem ticked_checkpoint : ticked.getCheckpointBlock anchorRoot 0 = .ok anchorRoot := by
  have ancestor : ticked.getAncestor ⟨anchorRoot, .pending⟩ 0 =
      .ok ⟨anchorRoot, .pending⟩ :=
    Store.getAncestor_of_le (block := anchorBlock stateRoot)
      (by simp [ticked, anchor]) (by decide)
  change (do let node ← ticked.getAncestor ⟨anchorRoot, .pending⟩ 0
             pure node.root) = .ok anchorRoot
  rw [ancestor]
  rfl

set_option maxRecDepth 10000 in
/-- Before the first child is admitted, the anchor is the head. -/
theorem ticked_head : ticked.getHead config = .ok ⟨anchorRoot, .pending⟩ := by
  have children : ticked.getNodeChildren ⟨anchorRoot, .pending⟩ = .ok [] := by cbv
  have viable : ticked.isViableLeaf config ⟨anchorRoot, .pending⟩ = .ok true := by
    simp only [Store.isViableLeaf, show ticked.finalizedCheckpoint.epoch = 0 from rfl,
      ticked_checkpoint]
    cbv
  have filtered : ticked.getFilteredNodeTree config = .ok [⟨anchorRoot, .pending⟩] := by
    unfold Store.getFilteredNodeTree
    rw [Store.filterNodeTree]
    simp only [show ticked.justifiedCheckpoint.root = anchorRoot from rfl, children,
      viable, bind, Except.bind]
    rfl
  simp only [Store.getHead, filtered, bind, Except.bind]
  change ticked.getHeadFrom config ticked.justifiedTally [⟨anchorRoot, .pending⟩]
    ⟨anchorRoot, .pending⟩ = .ok ⟨anchorRoot, .pending⟩
  rw [Store.getHeadFrom]
  simp only [Store.heaviestChild, children, bind, Except.bind]
  rfl

set_option maxRecDepth 10000 in
/-- The first block passes the handler's clock, parent, finalized-checkpoint and state checks. -/
theorem first_validated : ticked.validateOnBlock config .acceptAll sources signedBlock blockRoot =
    .ok postState := by
  have pre : ticked.blockState signedBlock.message.parentRoot = .ok (state bodyRoot) := by
    simp [Store.blockState, ticked, anchor, signedBlock, firstBlock, pure, Except.pure]
  have checkpoint : ticked.getCheckpointBlock signedBlock.message.parentRoot
      ticked.finalizedCheckpoint.epoch = .ok anchorRoot := ticked_checkpoint
  have parentOk : ticked.validateParentPayload signedBlock.message = .ok () := rfl
  have slotOk : ticked.getCurrentSlot config = .ok 1 := rfl
  have finalizedSlot : computeStartSlotAtEpoch preset ticked.finalizedCheckpoint.epoch =
      .ok 0 := rfl
  have dataOk : validateDataAvailability config sources signedBlock.message blockRoot =
      .ok () := rfl
  simp only [Store.validateOnBlock, pre, parentOk, slotOk, finalizedSlot, checkpoint, dataOk,
    show ticked.finalizedCheckpoint.root = anchorRoot from rfl,
    show signedBlock.message.slot = 1 from rfl, ne_eq, not_true_eq_false,
    show ¬ (1 : Slot) < 1 by decide, show ¬ (1 : Slot) ≤ 0 by decide,
    show Fork.phase0 ≠ Fork.bellatrix by decide, ↓reduceIte, ↓reduceDIte,
    Except.mapError, bind, Except.bind]
  rw [show sources.engine = .constant true from rfl, first_transition]
  rfl

/-- The store after the first block, before any votes have arrived. -/
def admitted : Store preset .phase0 :=
  { ticked with
    blocks := ticked.blocks.insert blockRoot signedBlock.message
    blockStates := ticked.blockStates.insert blockRoot postState
    blockTimeliness := ticked.blockTimeliness.insert blockRoot true
    proposerBoostRoot := blockRoot
    unrealizedJustifications := ticked.unrealizedJustifications.insert blockRoot
      postState.currentJustifiedCheckpoint }

set_option maxRecDepth 10000 in
/-- The handler admits the child with its certified post-state, without votes or slashings. -/
theorem first_admitted :
    ticked.onBlockWithVotes config .acceptAll sources signedBlock = .ok admitted := by
  let inserted : Store preset .phase0 := { ticked with
    blocks := ticked.blocks.insert blockRoot signedBlock.message
    blockStates := ticked.blockStates.insert blockRoot postState }
  let timely : Store preset .phase0 := { inserted with
    blockTimeliness := inserted.blockTimeliness.insert blockRoot true }
  let boosted : Store preset .phase0 := { timely with proposerBoostRoot := blockRoot }
  have blockOk : inserted.block blockRoot = .ok signedBlock.message := by
    simp [Store.block, inserted, pure, Except.pure]
  have timeliness : inserted.recordBlockTimeliness config blockRoot = .ok timely := by
    simp only [Store.recordBlockTimeliness, blockOk, bind, Except.bind]
    dsimp only [timely, inserted]
    rfl
  have anchorFound : timely.blocks[anchorRoot]? = some (anchorBlock stateRoot) := by
    simp only [timely, inserted, ticked, anchor, Std.TreeMap.getElem?_insert]
    simp [blockRoot_ne_anchorRoot]
  have childFound : timely.blocks[blockRoot]? = some signedBlock.message := by
    simp [timely, inserted]
  have parentFound : timely.blocks[signedBlock.message.parentRoot]? =
      some (anchorBlock stateRoot) := anchorFound
  have ancestor : timely.getAncestor ⟨anchorRoot, .pending⟩ 0 =
      .ok ⟨anchorRoot, .pending⟩ := Store.getAncestor_of_le anchorFound (by decide)
  have childAncestor : timely.getAncestor ⟨blockRoot, .pending⟩ 0 =
      .ok ⟨anchorRoot, .pending⟩ :=
    Store.getAncestor_parent_of_slot_lt childFound parentFound (by decide)
  have headDependent : timely.getShufflingDependentRoot anchorRoot 0 = .ok anchorRoot := by
    change (do let node ← timely.getAncestor ⟨anchorRoot, .pending⟩ 0
               pure node.root) = .ok anchorRoot
    rw [ancestor]
    rfl
  have blockDependent : timely.getShufflingDependentRoot blockRoot 0 = .ok anchorRoot := by
    change (do let node ← timely.getAncestor ⟨blockRoot, .pending⟩ 0
               pure node.root) = .ok anchorRoot
    rw [childAncestor]
    rfl
  have boost : timely.updateProposerBoostRoot config anchorRoot blockRoot = .ok boosted := by
    have epochOk : timely.getCurrentStoreEpoch config = .ok 0 := by
      dsimp only [timely, inserted]
      rfl
    have found : timely.blockTimeliness[blockRoot]? = some true := by simp [timely]
    simp only [Store.updateProposerBoostRoot, found, epochOk, headDependent, blockDependent,
      bind, Except.bind, pure, Except.pure]
    rfl
  have pulled : boosted.computePulledUpTip config blockRoot = .ok admitted := by
    have stateOk : boosted.blockState blockRoot = .ok postState := by
      simp [Store.blockState, boosted, timely, inserted, pure, Except.pure]
    have stateSame : processJustificationAndFinalization postState = .ok postState := rfl
    have blockOk : admitted.block blockRoot = .ok signedBlock.message := by
      simp [Store.block, admitted, pure, Except.pure]
    have epochOk : admitted.getCurrentStoreEpoch config = .ok 0 := rfl
    simp only [Store.computePulledUpTip, stateOk, stateSame, Except.mapError, bind, Except.bind]
    dsimp only [boosted, timely, inserted]
    change (do
      let block ← admitted.block blockRoot
      let epoch ← admitted.getCurrentStoreEpoch config
      if computeEpochAtSlot preset block.slot < epoch then
        pure (admitted.updateCheckpoints postState.currentJustifiedCheckpoint
          postState.finalizedCheckpoint)
      else pure admitted) = .ok admitted
    rw [blockOk]
    dsimp only [bind, Except.bind]
    rw [epochOk]
    rfl
  have absent : ticked.blocks.contains blockRoot = false := by
    simp [ticked, anchor, Ne.symm blockRoot_ne_anchorRoot]
  have accepted : ticked.onBlock config .acceptAll sources signedBlock = .ok admitted := by
    simp only [Store.onBlock, first_block_root, absent,
      Except.mapError, bind, Except.bind, Bool.false_eq_true, ↓reduceIte,
      Store.addBlock, first_validated, ticked_head]
    have ptc : inserted.recordBlockPtcVotes config .acceptAll signedBlock blockRoot postState =
        .ok inserted := rfl
    rw [ptc]
    dsimp only [bind, Except.bind]
    rw [timeliness]
    dsimp only [bind, Except.bind]
    rw [boost]
    change boosted.computePulledUpTip config blockRoot = .ok admitted
    exact pulled
  simp only [Store.onBlockWithVotes, accepted, bind, Except.bind]
  rfl

end EthLib.Consensus.Models.Network.FiveValidatorWitness
