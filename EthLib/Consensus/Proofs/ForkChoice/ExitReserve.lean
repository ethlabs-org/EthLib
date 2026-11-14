module

public import EthLib.Consensus.Proofs.Transition.ExitReserve
public import EthLib.Consensus.Proofs.ForkChoice.BlockAgreement
public import EthLib.Consensus.Proofs.ForkChoice.HonestCheckpoints
public import EthLib.Consensus.Proofs.ForkChoice.HonestHeads
public import EthLib.Consensus.Proofs.DirectSafety.Execution
import EthLib.Consensus.Proofs.ForkChoice.BlockRuns
import Mathlib.Tactic.Linarith

/-! # Exit reserves for a checkpoint state and a head state -/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models DirectSafety Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

private theorem reachable_of_start {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    {w : ValidatorIndex} (start : e.start w = anchor) (k : ℕ) :
    Store.Reachable config anchorState anchorBlock ((e.world k).state w) := by
  induction k with
  | zero =>
    change Store.Reachable config anchorState anchorBlock (e.start w)
    rw [start]
    exact .anchor anchored
  | succ k ih =>
    rcases e.state_succ k w with same | ⟨_, moved⟩
    · exact same ▸ ih
    · exact moved.reachable ih

private theorem run_of_blockState {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    (before : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      ∀ next ∈ config.nextFork fork,
        block.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    {root : Root} {state : BeaconState preset fork}
    (stored : ((e.world k).state w).blockStates[root]? = some state) :
    Nonempty (Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩) := by
  have reachable := reachable_of_start anchored start k
  obtain ⟨block, found⟩ := reachable.known_of_blockState stored
  by_cases same : block = anchorBlock
  · obtain ⟨post, postOk, initial, -⟩ := reachable.blockStatesFromParents found
    have equal : post = state := Option.some.inj (postOk.symm.trans stored)
    rw [← equal, initial same]
    exact ⟨.nil⟩
  · obtain ⟨parent, signed, message, parentFound, transitioned⟩ :=
      e.exists_transition_of_nonanchor_block anchored honest start found stored same
    obtain ⟨pre⟩ := run_of_blockState anchored anchorSlot honest start before parentFound
    have across : stateTransitionAcross config checks sources.engine ⟨fork, parent⟩ signed true =
        .ok state := by
      rw [stateTransitionAcross_of_before (by simpa only [message] using before root block found)]
      exact transitioned
    obtain ⟨advanced, slotRun, due, applied, -, -, -⟩ :=
      Run.exists_of_stateTransitionAcross sources.engine signed across
    exact ⟨pre.append (slotRun.snoc (.block sources.engine signed due applied))⟩
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

/-- A run from a state at a boundary slot along a chain of blocks above it to a later block state.

The start is the state of an ancestor block, kept as it is or processed to the boundary.

No block of the chain lies from the ancestor to the boundary except the ancestor itself. -/
private theorem run_along_chain {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (early : fork < .glamsterdam) (anchorSlot : anchorBlock.slot = anchorState.slot)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    (before : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      ∀ next ∈ config.nextFork fork,
        block.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    {a : Root} {aBlock : BeaconBlock preset fork} {sa s0 : BeaconState preset fork}
    {boundary : Slot}
    (aFound : ((e.world k).state w).blocks[a]? = some aBlock)
    (storedA : ((e.world k).state w).blockStates[a]? = some sa)
    (bridge : (sa.slot = boundary ∧ s0 = sa) ∨
      (sa.slot < boundary ∧ processSlots config checks sa boundary = .ok s0)) :
    ∀ (n : ℕ) (b : Root) (block : BeaconBlock preset fork) (sb : BeaconState preset fork),
      block.slot.toNat = n →
      ((e.world k).state w).blocks[b]? = some block →
      ((e.world k).state w).blockStates[b]? = some sb →
      ((e.world k).state w).isAncestor ⟨b, .pending⟩ ⟨a, .pending⟩ = .ok true →
      (∀ (q : Root) (qBlock : BeaconBlock preset fork),
        ((e.world k).state w).blocks[q]? = some qBlock →
        ((e.world k).state w).isAncestor ⟨b, .pending⟩ ⟨q, .pending⟩ = .ok true →
        aBlock.slot ≤ qBlock.slot → qBlock.slot ≤ boundary → q = a) →
      boundary < block.slot →
      Nonempty (Run config checks ⟨fork, s0⟩ ⟨fork, sb⟩) := by
  have reachable := reachable_of_start anchored start k
  have aLe : aBlock.slot ≤ boundary := by
    have h2 := reachable.slot_le_of_blockState (UInt64.le_of_eq anchorSlot) aFound storedA
    rcases bridge with ⟨h, _⟩ | ⟨h, _⟩
    · exact UInt64.le_trans h2 (UInt64.le_of_eq h)
    · exact UInt64.le_trans h2 (UInt64.le_of_lt h)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b block sb hn found stored descends clear far
    have aLt : aBlock.slot < block.slot := UInt64.lt_of_le_of_lt aLe far
    have other : block ≠ anchorBlock := by
      intro same
      have h1 := reachable.anchorSlot_le (anchorSlot ▸ UInt64.le_refl _) aFound
      rw [same] at aLt
      exact UInt64.lt_irrefl _ (UInt64.lt_of_le_of_lt h1 aLt)
    obtain ⟨parent, signed, message, parentFound, transitioned⟩ :=
      e.exists_transition_of_nonanchor_block anchored honest start found stored other
    obtain ⟨pBlock, pFound⟩ := reachable.known_of_blockState parentFound
    have parentLe := reachable.slot_le_of_blockState (UInt64.le_of_eq anchorSlot) pFound parentFound
    have parentLt : parent.slot < block.slot := by
      simpa only [message] using (stateTransition_slot transitioned).1
    have pLt : pBlock.slot < block.slot := UInt64.lt_of_le_of_lt parentLe parentLt
    have viaBefore : ∀ next ∈ config.nextFork fork,
        signed.message.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat := by
      simpa only [message] using before b block found
    have transitioned' := transitioned
    simp only [stateTransition, bind_ok_iff] at transitioned
    obtain ⟨adv, slotsOk, applied⟩ := transitioned
    by_cases isA : block.parentRoot = a
    · rw [isA, storedA, Option.some.injEq] at parentFound
      subst parentFound
      have viaS0 : processSlots config checks s0 signed.message.slot = .ok adv := by
        rcases bridge with ⟨_, rfl⟩ | ⟨lt, ran⟩
        · exact slotsOk
        · obtain ⟨middle, middleOk, rest⟩ := processSlots_split lt
            (by simpa only [message] using far) slotsOk
          rw [ran, Except.ok.injEq] at middleOk
          subst middleOk
          exact rest
      have across : stateTransitionAcross config checks sources.engine ⟨fork, s0⟩ signed true =
          .ok sb := by
        rw [stateTransitionAcross_of_before viaBefore]
        simp only [stateTransition, bind_ok_iff]
        exact ⟨adv, viaS0, applied⟩
      obtain ⟨advanced, slotRun, due, applied', -, -, -⟩ :=
        Run.exists_of_stateTransitionAcross sources.engine signed across
      exact ⟨slotRun.snoc (.block sources.engine signed due applied')⟩
    · -- The walk from the block to the ancestor passes through the parent.
      have walk := Store.getAncestor_of_isAncestor_of_lt early aFound descends
      have step := Store.getAncestor_step (node := ⟨b, .pending⟩) (slot := aBlock.slot) found
        (UInt64.not_le.mpr aLt) pFound pLt
      rw [Store.parentPayloadStatus_of_lt early] at step
      rw [step] at walk
      have above : aBlock.slot ≤ pBlock.slot := by
        by_contra below
        have le : pBlock.slot ≤ aBlock.slot := UInt64.le_of_lt (UInt64.not_le.mp below)
        rw [Store.getAncestor_of_le (node := ⟨block.parentRoot, .pending⟩) pFound le] at walk
        exact isA (congrArg ForkChoiceNode.root (Except.ok.inj walk))
      have pDescends : ((e.world k).state w).isAncestor ⟨block.parentRoot, .pending⟩
          ⟨a, .pending⟩ = .ok true := by
        simp [Store.isAncestor, Store.block_ok_iff.mpr aFound, walk, bind, Except.bind,
          pure, Except.pure]
      have bToParent : ((e.world k).state w).isAncestor ⟨b, .pending⟩
          ⟨block.parentRoot, .pending⟩ = .ok true :=
        Store.isAncestor_of_parent early found pFound pLt (Store.isAncestor_self pFound)
      have pFar : boundary < pBlock.slot := by
        by_contra notFar
        exact isA (clear _ pBlock pFound bToParent above (UInt64.not_lt.mp notFar))
      have clear' : ∀ (q : Root) (qBlock : BeaconBlock preset fork),
          ((e.world k).state w).blocks[q]? = some qBlock →
          ((e.world k).state w).isAncestor ⟨block.parentRoot, .pending⟩ ⟨q, .pending⟩ =
            .ok true → aBlock.slot ≤ qBlock.slot → qBlock.slot ≤ boundary → q = a :=
        fun q qBlock qFound h => clear q qBlock qFound
          (Store.isAncestor_of_parent early found pFound pLt h)
      obtain ⟨run⟩ := ih pBlock.slot.toNat (hn ▸ UInt64.lt_iff_toNat_lt.mp pLt) block.parentRoot
        pBlock parent rfl pFound parentFound pDescends clear' pFar
      have across : stateTransitionAcross config checks sources.engine ⟨fork, parent⟩ signed
          true = .ok sb := by
        rw [stateTransitionAcross_of_before viaBefore]
        exact transitioned'
      obtain ⟨advanced, slotRun, due, applied', -, -, -⟩ :=
        Run.exists_of_stateTransitionAcross sources.engine signed across
      exact ⟨run.append (slotRun.snoc (.block sources.engine signed due applied'))⟩

/-- A checkpoint read leaves no block of the chain from the checkpoint block to the boundary. -/
private theorem clear_of_getCheckpointBlock {store : Store preset fork}
    (early : fork < .glamsterdam) {b a : Root} {aBlock : BeaconBlock preset fork}
    {epoch : Epoch} {boundary : Slot}
    (boundaryOk : computeStartSlotAtEpoch preset epoch = .ok boundary)
    (read : store.getCheckpointBlock b epoch = .ok a)
    (aFound : store.blocks[a]? = some aBlock) :
    ∀ (q : Root) (qBlock : BeaconBlock preset fork), store.blocks[q]? = some qBlock →
      store.isAncestor ⟨b, .pending⟩ ⟨q, .pending⟩ = .ok true →
      aBlock.slot ≤ qBlock.slot → qBlock.slot ≤ boundary → q = a := by
  intro q qBlock qFound hq above below
  unfold Store.getCheckpointBlock at read
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at read
  obtain ⟨boundary', boundaryOk', anc, walk, rootEq⟩ := read
  have same : boundary' = boundary := by
    have := mapError_ok_iff.mp boundaryOk'
    rw [boundaryOk] at this
    exact (Except.ok.inj this).symm
  subst same
  have pending := Store.getAncestor_pending_of_lt early rfl walk
  have ancEq : anc = ⟨a, .pending⟩ := by
    cases anc
    simp_all
  subst ancEq
  have toQ := Store.getAncestor_of_isAncestor_of_lt early qFound hq
  have through := Store.getAncestor_trans below walk
  rw [Store.getAncestor_of_le (node := ⟨a, .pending⟩) aFound above] at through
  rw [toQ, Except.ok.injEq] at through
  exact congrArg ForkChoiceNode.root through

/-- From a start state at a boundary, the same slots lead to a later state of the same ancestor. -/
private theorem run_from_bridge {sa s0 y : BeaconState preset fork} {boundary target : Slot}
    (bridge : (sa.slot = boundary ∧ s0 = sa) ∨
      (sa.slot < boundary ∧ processSlots config checks sa boundary = .ok s0))
    (later : boundary ≤ target)
    (reach : (sa.slot = target ∧ y = sa) ∨
      (sa.slot < target ∧ processSlots config checks sa target = .ok y))
    (before : ∀ next ∈ config.nextFork fork,
      target.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    Nonempty (Run config checks ⟨fork, s0⟩ ⟨fork, y⟩) := by
  rcases bridge with ⟨low, rfl⟩ | ⟨low, ran⟩
  · rcases reach with ⟨same, rfl⟩ | ⟨_, processed⟩
    · exact ⟨.nil⟩
    · exact run_of_processSlots processed before
  · rcases reach with ⟨same, rfl⟩ | ⟨_, processed⟩
    · exact absurd (UInt64.lt_of_lt_of_le low (same ▸ later)) (UInt64.lt_irrefl _)
    · by_cases equal : boundary = target
      · subst equal
        rw [ran, Except.ok.injEq] at processed
        subst processed
        exact ⟨.nil⟩
      · obtain ⟨middle, middleOk, rest⟩ := processSlots_split low
          (UInt64.lt_of_le_of_ne later equal) processed
        rw [ran, Except.ok.injEq] at middleOk
        subst middleOk
        exact run_of_processSlots rest before

/-- A block on the chain above an ancestor has a child of the ancestor on its chain.

That child is reached from the state of the ancestor by a successful run of slots. -/
private theorem exists_child_of_chain {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (early : fork < .glamsterdam) (anchorSlot : anchorBlock.slot = anchorState.slot)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    {a : Root} {aBlock : BeaconBlock preset fork} {sa : BeaconState preset fork}
    (aFound : ((e.world k).state w).blocks[a]? = some aBlock)
    (storedA : ((e.world k).state w).blockStates[a]? = some sa) :
    ∀ (n : ℕ) (b : Root) (block : BeaconBlock preset fork) (sb : BeaconState preset fork),
      block.slot.toNat = n →
      ((e.world k).state w).blocks[b]? = some block →
      ((e.world k).state w).blockStates[b]? = some sb →
      ((e.world k).state w).isAncestor ⟨b, .pending⟩ ⟨a, .pending⟩ = .ok true →
      b ≠ a →
      ∃ (x : Root) (xBlock : BeaconBlock preset fork),
        ((e.world k).state w).blocks[x]? = some xBlock ∧
        ((e.world k).state w).isAncestor ⟨b, .pending⟩ ⟨x, .pending⟩ = .ok true ∧
        xBlock.parentRoot = a ∧ aBlock.slot < xBlock.slot ∧
        ∃ advanced, processSlots config checks sa xBlock.slot = .ok advanced := by
  have reachable := reachable_of_start anchored start k
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b block sb hn found stored descends distinct
    have walk := Store.getAncestor_of_isAncestor_of_lt early aFound descends
    have aLt : aBlock.slot < block.slot := by
      by_contra notLt
      rw [Store.getAncestor_of_le (node := ⟨b, .pending⟩) found (UInt64.not_lt.mp notLt)] at walk
      exact distinct (congrArg ForkChoiceNode.root (Except.ok.inj walk))
    have other : block ≠ anchorBlock := by
      intro same
      have h1 := reachable.anchorSlot_le (anchorSlot ▸ UInt64.le_refl _) aFound
      rw [same] at aLt
      exact UInt64.lt_irrefl _ (UInt64.lt_of_le_of_lt h1 aLt)
    obtain ⟨parent, signed, message, parentFound, transitioned⟩ :=
      e.exists_transition_of_nonanchor_block anchored honest start found stored other
    obtain ⟨pBlock, pFound⟩ := reachable.known_of_blockState parentFound
    have parentLe := reachable.slot_le_of_blockState (UInt64.le_of_eq anchorSlot) pFound parentFound
    have parentLt : parent.slot < block.slot := by
      simpa only [message] using (stateTransition_slot transitioned).1
    have pLt : pBlock.slot < block.slot := UInt64.lt_of_le_of_lt parentLe parentLt
    by_cases isA : block.parentRoot = a
    · rw [isA, storedA, Option.some.injEq] at parentFound
      subst parentFound
      obtain ⟨adv, slotsOk, _⟩ := bind_ok_iff.mp
        (show (processSlots config checks sa signed.message.slot >>= fun s =>
          applySignedBlock config checks sources.engine s signed true) = .ok sb from transitioned)
      exact ⟨b, block, found, Store.isAncestor_self found, isA, aLt,
        adv, by simpa only [message] using slotsOk⟩
    · have step := Store.getAncestor_step (node := ⟨b, .pending⟩) (slot := aBlock.slot) found
        (UInt64.not_le.mpr aLt) pFound pLt
      rw [Store.parentPayloadStatus_of_lt early] at step
      rw [step] at walk
      have above : aBlock.slot ≤ pBlock.slot := by
        by_contra below
        have le : pBlock.slot ≤ aBlock.slot := UInt64.le_of_lt (UInt64.not_le.mp below)
        rw [Store.getAncestor_of_le (node := ⟨block.parentRoot, .pending⟩) pFound le] at walk
        exact isA (congrArg ForkChoiceNode.root (Except.ok.inj walk))
      have pDescends : ((e.world k).state w).isAncestor ⟨block.parentRoot, .pending⟩
          ⟨a, .pending⟩ = .ok true := by
        simp [Store.isAncestor, Store.block_ok_iff.mpr aFound, walk, bind, Except.bind,
          pure, Except.pure]
      obtain ⟨x, xBlock, xFound, xAbove, xParent, xLt, xSlots⟩ :=
        ih pBlock.slot.toNat (hn ▸ UInt64.lt_iff_toNat_lt.mp pLt) block.parentRoot pBlock parent
          rfl pFound parentFound pDescends isA
      exact ⟨x, xBlock, xFound, Store.isAncestor_of_parent early found pFound pLt xAbove,
        xParent, xLt, xSlots⟩

/-- From the state of an ancestor block, a run reaches a head-chain state no later than an epoch.

The head state is no later than the epoch.

The run stops at the head state, or at the state of the ancestor when the head is the ancestor.

Its registry at the epoch is the one of the head state. -/
private theorem run_to_epoch_early {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (early : fork < .glamsterdam) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (lookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    (before : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      ∀ next ∈ config.nextFork fork,
        block.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    {a : Root} {aBlock : BeaconBlock preset fork} {sa s0 : BeaconState preset fork}
    {boundary : Slot}
    (aFound : ((e.world k).state w).blocks[a]? = some aBlock)
    (storedA : ((e.world k).state w).blockStates[a]? = some sa)
    (bridge : (sa.slot = boundary ∧ s0 = sa) ∨
      (sa.slot < boundary ∧ processSlots config checks sa boundary = .ok s0))
    {head : Root} {headBlock : BeaconBlock preset fork} {hs : BeaconState preset fork}
    (headFound : ((e.world k).state w).blocks[head]? = some headBlock)
    (stored : ((e.world k).state w).blockStates[head]? = some hs)
    (descends : ((e.world k).state w).isAncestor ⟨head, .pending⟩ ⟨a, .pending⟩ = .ok true)
    (clearC : ∀ (q : Root) (qBlock : BeaconBlock preset fork),
      ((e.world k).state w).blocks[q]? = some qBlock →
      ((e.world k).state w).isAncestor ⟨head, .pending⟩ ⟨q, .pending⟩ = .ok true →
      aBlock.slot ≤ qBlock.slot → qBlock.slot ≤ boundary → q = a)
    {epoch : Epoch}
    (boundaryEpoch : computeEpochAtSlot preset boundary ≤ epoch)
    (boundaryBefore : ∀ next ∈ config.nextFork fork,
      boundary.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (bounded : epoch.toNat < 2 ^ 64 - 1)
    (recent : epoch.toNat ≤ (getCurrentEpoch hs).toNat + 1)
    (cur : getCurrentEpoch hs ≤ epoch) :
    ∃ y : BeaconState preset fork, Nonempty (Run config checks ⟨fork, s0⟩ ⟨fork, y⟩) ∧
      getCurrentEpoch y ≤ epoch ∧
      ∀ position, isActiveAt y epoch position = isActiveAt hs epoch position := by
  have s0Slot : s0.slot = boundary := by
    rcases bridge with ⟨h, rfl⟩ | ⟨_, ran⟩
    · exact h
    · exact (processSlots_slot ran).2
  have aSlot : sa.slot = aBlock.slot := by
    have reachable := reachable_of_start anchored start k
    exact blockState_slot_eq reachable anchorSlot aFound storedA
  by_cases isHeadA : head = a
  · subst isHeadA
    have same : hs = sa := Option.some.inj (stored.symm.trans storedA)
    subst same
    have runSa : Nonempty (Run config checks ⟨fork, hs⟩ ⟨fork, s0⟩) := by
      rcases bridge with ⟨_, rfl⟩ | ⟨_, ran⟩
      · exact ⟨.nil⟩
      · exact run_of_processSlots ran boundaryBefore
    obtain ⟨run⟩ := runSa
    refine ⟨s0, ⟨.nil⟩, ?_, ?_⟩
    · simpa only [getCurrentEpoch, s0Slot] using boundaryEpoch
    · intro position
      exact activeKept_of_chainSteps run.chainSteps epoch
        (ExitChurn.fixed_ge hs recent lookahead bounded) position
  · obtain ⟨hb, hbFound, aLeHead⟩ := Store.slot_le_of_isAncestor aFound descends
    have hbEq : hb = headBlock := Option.some.inj (hbFound.symm.trans headFound)
    subst hbEq
    have far : boundary < hb.slot := by
      by_contra notFar
      exact isHeadA (clearC head hb headFound (Store.isAncestor_self headFound) aLeHead
        (UInt64.not_lt.mp notFar))
    obtain ⟨run⟩ := run_along_chain anchored early anchorSlot honest start before aFound storedA
      bridge hb.slot.toNat head hb hs rfl headFound stored descends clearC far
    exact ⟨hs, ⟨run⟩, cur, fun _ => rfl⟩

/-- From the state of an ancestor block, a run reaches the start of an epoch on the head chain.

The head state is later than the epoch.

The registry of the reached state at the epoch is the one of the head state. -/
private theorem run_to_epoch_late {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (early : fork < .glamsterdam) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    (before : ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      ∀ next ∈ config.nextFork fork,
        block.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    {a : Root} {aBlock : BeaconBlock preset fork} {sa s0 : BeaconState preset fork}
    {boundary : Slot}
    (aFound : ((e.world k).state w).blocks[a]? = some aBlock)
    (storedA : ((e.world k).state w).blockStates[a]? = some sa)
    (bridge : (sa.slot = boundary ∧ s0 = sa) ∨
      (sa.slot < boundary ∧ processSlots config checks sa boundary = .ok s0))
    {head : Root} {headBlock : BeaconBlock preset fork} {hs : BeaconState preset fork}
    (headFound : ((e.world k).state w).blocks[head]? = some headBlock)
    (stored : ((e.world k).state w).blockStates[head]? = some hs)
    (descends : ((e.world k).state w).isAncestor ⟨head, .pending⟩ ⟨a, .pending⟩ = .ok true)
    (clearC : ∀ (q : Root) (qBlock : BeaconBlock preset fork),
      ((e.world k).state w).blocks[q]? = some qBlock →
      ((e.world k).state w).isAncestor ⟨head, .pending⟩ ⟨q, .pending⟩ = .ok true →
      aBlock.slot ≤ qBlock.slot → qBlock.slot ≤ boundary → q = a)
    {epoch : Epoch} {S : Slot} (SOk : computeStartSlotAtEpoch preset epoch = .ok S)
    (boundaryLe : boundary ≤ S)
    (beforeS : ∀ next ∈ config.nextFork fork,
      S.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (bounded : epoch.toNat < 2 ^ 64 - 1)
    {bE : Root} (readE : ((e.world k).state w).getCheckpointBlock head epoch = .ok bE)
    (later : epoch < getCurrentEpoch hs) :
    ∃ y : BeaconState preset fork, Nonempty (Run config checks ⟨fork, s0⟩ ⟨fork, y⟩) ∧
      getCurrentEpoch y ≤ epoch ∧
      ∀ position, isActiveAt y epoch position = isActiveAt hs epoch position := by
  have reachable := reachable_of_start anchored start k
  have positiveNat : 0 < preset.SLOTS_PER_EPOCH.toNat := UInt64.lt_iff_toNat_lt.mp positive
  have headSlot : hs.slot = headBlock.slot :=
    blockState_slot_eq reachable anchorSlot headFound stored
  have aSlot : sa.slot = aBlock.slot := blockState_slot_eq reachable anchorSlot aFound storedA
  have aLe : aBlock.slot ≤ boundary := by
    rw [← aSlot]
    rcases bridge with ⟨h, _⟩ | ⟨h, _⟩
    · exact UInt64.le_of_eq h
    · exact UInt64.le_of_lt h
  have s0Slot : s0.slot = boundary := by
    rcases bridge with ⟨h, rfl⟩ | ⟨_, ran⟩
    · exact h
    · exact (processSlots_slot ran).2
  have SEpoch : computeEpochAtSlot preset S = epoch :=
    computeEpochAtSlot_computeStartSlotAtEpoch positive SOk
  have SNat : S.toNat = epoch.toNat * preset.SLOTS_PER_EPOCH.toNat :=
    (computeStartSlotAtEpoch_ok_iff.mp SOk).2
  have boundaryBefore : ∀ next ∈ config.nextFork fork,
      boundary.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat := fun next member =>
    Nat.lt_of_le_of_lt (UInt64.le_iff_toNat_le.mp boundaryLe) (beforeS next member)
  have curHs : (getCurrentEpoch hs).toNat =
      headBlock.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    simp [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div, headSlot]
  have farS : S.toNat < headBlock.slot.toNat := by
    have := UInt64.lt_iff_toNat_lt.mp later
    rw [curHs] at this
    have step : epoch.toNat + 1 ≤ headBlock.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := this
    have := (Nat.le_div_iff_mul_le positiveNat).mp step
    rw [SNat]
    nlinarith
  obtain ⟨S', bEBlock, SOk', bEFound, bELe, bEDesc⟩ :=
    Store.isAncestor_of_getCheckpointBlock early readE
  have SEq : S' = S := Except.ok.inj (SOk'.symm.trans SOk)
  subst S'
  have clearE := clear_of_getCheckpointBlock early SOk readE bEFound
  obtain ⟨sE, storedE⟩ : ∃ sE, ((e.world k).state w).blockStates[bE]? = some sE := by
    obtain ⟨post, postOk, -⟩ := reachable.blockStatesFromParents bEFound
    exact ⟨post, postOk⟩
  have sESlot : sE.slot = bEBlock.slot := blockState_slot_eq reachable anchorSlot bEFound storedE
  have headNe : head ≠ bE := by
    intro same
    subst same
    have eq : bEBlock = headBlock := Option.some.inj (bEFound.symm.trans headFound)
    subst eq
    exact absurd (UInt64.le_iff_toNat_le.mp bELe) (by omega)
  have farHead : S < headBlock.slot := UInt64.lt_iff_toNat_lt.mpr farS
  -- The state of the checkpoint block at the start of the epoch.
  obtain ⟨y, reach⟩ : ∃ y : BeaconState preset fork,
      (sE.slot = S ∧ y = sE) ∨ (sE.slot < S ∧ processSlots config checks sE S = .ok y) := by
    by_cases atS : sE.slot = S
    · exact ⟨sE, .inl ⟨atS, rfl⟩⟩
    · have below : sE.slot < S := UInt64.lt_of_le_of_ne (sESlot ▸ bELe) atS
      obtain ⟨x, xBlock, xFound, xAbove, xParent, xLt, advanced, xSlots⟩ :=
        exists_child_of_chain anchored early anchorSlot honest start bEFound storedE
          headBlock.slot.toNat head headBlock hs rfl headFound stored bEDesc headNe
      have xFar : S < xBlock.slot := by
        by_contra notFar
        have same := clearE x xBlock xFound xAbove (UInt64.le_of_lt xLt)
          (UInt64.not_lt.mp notFar)
        subst same
        have eq : bEBlock = xBlock := Option.some.inj (bEFound.symm.trans xFound)
        subst eq
        exact UInt64.lt_irrefl _ xLt
      obtain ⟨middle, middleOk, -⟩ := processSlots_split below xFar xSlots
      exact ⟨middle, .inr ⟨below, middleOk⟩⟩
  have ySlot : y.slot = S := by
    rcases reach with ⟨h, rfl⟩ | ⟨_, ran⟩
    · exact h
    · exact (processSlots_slot ran).2
  have curY : getCurrentEpoch y = epoch := by
    simp only [getCurrentEpoch, ySlot]
    exact SEpoch
  have walkE : ((e.world k).state w).getAncestor ⟨head, .pending⟩ S = .ok ⟨bE, .pending⟩ := by
    have read := readE
    unfold Store.getCheckpointBlock at read
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at read
    obtain ⟨boundary', boundaryOk', anc, walk, rootEq⟩ := read
    have same : boundary' = S := by
      have := mapError_ok_iff.mp boundaryOk'
      rw [SOk] at this
      exact (Except.ok.inj this).symm
    subst same
    have pending := Store.getAncestor_pending_of_lt early rfl walk
    have ancEq : anc = ⟨bE, .pending⟩ := by
      cases anc
      simp_all
    rw [← ancEq]
    exact walk
  have runY : Nonempty (Run config checks ⟨fork, s0⟩ ⟨fork, y⟩) := by
    by_cases isEA : bE = a
    · subst isEA
      have same : sE = sa := Option.some.inj (storedE.symm.trans storedA)
      subst same
      exact run_from_bridge bridge boundaryLe reach beforeS
    · have walkA := Store.getAncestor_of_isAncestor_of_lt early aFound descends
      have aLeS : aBlock.slot ≤ S := UInt64.le_trans aLe boundaryLe
      have through := Store.getAncestor_trans aLeS walkE
      rw [walkA] at through
      have aLeE : aBlock.slot ≤ bEBlock.slot := by
        by_contra notLe
        have le : bEBlock.slot ≤ aBlock.slot := UInt64.le_of_lt (UInt64.not_le.mp notLe)
        rw [Store.getAncestor_of_le (node := ⟨bE, .pending⟩) bEFound le] at through
        exact isEA (congrArg ForkChoiceNode.root (Except.ok.inj through)).symm
      have aDescE : ((e.world k).state w).isAncestor ⟨bE, .pending⟩ ⟨a, .pending⟩ =
          .ok true := by
        simp [Store.isAncestor, Store.block_ok_iff.mpr aFound, through.symm, bind, Except.bind,
          pure, Except.pure]
      have clearA : ∀ (q : Root) (qBlock : BeaconBlock preset fork),
          ((e.world k).state w).blocks[q]? = some qBlock →
          ((e.world k).state w).isAncestor ⟨bE, .pending⟩ ⟨q, .pending⟩ = .ok true →
          aBlock.slot ≤ qBlock.slot → qBlock.slot ≤ boundary → q = a :=
        fun q qBlock qFound hq above below => clearC q qBlock qFound
          (Store.isAncestor_trans_of_lt early bEFound qFound bEDesc hq) above below
      have farE : boundary < bEBlock.slot := by
        by_contra notFar
        exact isEA (clearC bE bEBlock bEFound bEDesc aLeE (UInt64.not_lt.mp notFar))
      obtain ⟨r1⟩ := run_along_chain anchored early anchorSlot honest start before aFound storedA
        bridge bEBlock.slot.toNat bE bEBlock sE rfl bEFound storedE aDescE clearA farE
      obtain ⟨r2⟩ := run_from_bridge (sa := sE) (s0 := sE) (boundary := sE.slot)
        (.inl ⟨rfl, rfl⟩) (sESlot ▸ bELe) reach beforeS
      exact ⟨r1.append r2⟩
  obtain ⟨runYH⟩ := run_along_chain anchored early anchorSlot honest start before bEFound storedE
    reach headBlock.slot.toNat head headBlock hs rfl headFound stored bEDesc clearE farHead
  refine ⟨y, runY, UInt64.le_of_eq curY, ?_⟩
  intro position
  have kept := activeKept_of_chainSteps runYH.chainSteps epoch
    (ExitChurn.fixed_ge y (n := 0) (by rw [curY]; omega) (Nat.zero_le _) bounded) position
  exact kept.symm

/-- The blocks that an honest store holds are before the next fork. -/
private theorem blocks_before_fork {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (slots : 0 < config.SLOT_DURATION_MS) (parameters : DirectSafety.Parameters preset)
    {horizon : Epoch}
    (forkWindow : fork < .glamsterdam ∧ ∀ next ∈ config.nextFork fork,
      horizon.toNat < next.2.toNat) {limit : ℕ}
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ} (bounded : (e.world k).time ≤ limit) :
    ∀ (root : Root) (block : BeaconBlock preset fork),
      ((e.world k).state w).blocks[root]? = some block →
      ∀ next ∈ config.nextFork fork,
        block.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat := by
  have forward := e.forwardReachable (anchorState := anchorState) (anchorBlock := anchorBlock)
    (fun v member => by rw [start v member]; exact .anchor anchored) k w honest
  obtain ⟨current, currentOk, blocks, -⟩ := forward.slots_le_current slots
    (by rw [anchorSlot]; exact UInt64.le_refl _)
  have currentEpoch : ((e.world k).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset current) := by
    simp only [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
  have high := UInt64.le_iff_toNat_le.mp (inHorizon w honest k _ bounded currentEpoch)
  simp only [computeEpochAtSlot, UInt64.toNat_div] at high
  intro root block found next scheduled
  have blockLe := UInt64.le_iff_toNat_le.mp (blocks root block found)
  have nextLt := forkWindow.2 next scheduled
  have positive := parameters.slots
  have currentLt : current.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat :=
    (Nat.div_lt_iff_lt_mul (by omega)).mp (by omega)
  omega

/-- The stake that leaves the active set between a source checkpoint state and a head state.

The source is the state of a checkpoint of one honest store.

The head state is a block state of another, and the chain of the head holds the checkpoint block.

The registry of the head state is read at an epoch within two epochs of the source.

Its validators that are active in the source and inactive there fit the reserve of the source. -/
theorem Execution.exitsHead_of_oneBlock {limit : ℕ} {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (slots : 0 < config.SLOT_DURATION_MS) (parameters : DirectSafety.Parameters preset)
    {g : ForkedBeaconState preset} (genesis : Genesis (config := config) (checks := checks) g)
    (history : Run config checks g ⟨fork, anchorState⟩) {horizon : Epoch}
    (forkWindow : fork < .glamsterdam ∧ ∀ next ∈ config.nextFork fork,
      horizon.toNat < next.2.toNat)
    (inHorizon : ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ limit →
      ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon)
    (anchorParent : ∀ w ∈ J, ∀ k, (e.world k).time ≤ limit →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    (oneBlock : OneBlockPerRoot e limit)
    (lookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat) (long : 1 < preset.SLOTS_PER_EPOCH) :
    ∀ u ∈ J, ∀ n (c : Checkpoint) (source : BeaconState preset fork),
      (e.world n).time ≤ limit → ((e.world n).state u).checkpointState c = .ok source →
      ∀ w ∈ J, ∀ k (head : Root) (hs : BeaconState preset fork),
      (e.world k).time ≤ limit → ((e.world k).state w).blockStates[head]? = some hs →
      ((e.world k).state w).getCheckpointBlock head c.epoch = .ok c.root →
      ∀ epoch : Epoch, c.epoch ≤ epoch → epoch.toNat ≤ c.epoch.toNat + 2 → epoch ≤ horizon →
      epoch.toNat ≤ (getCurrentEpoch hs).toNat + 1 →
      stake (fun v => balanceAt source v.toNat)
          {v ∈ ExitChurn.activeSet source | isActiveAt hs epoch v.toNat = false} ≤
        ExitChurn.exitReserve config source := by
  intro u hu n c source bn sourceOk w hw k head hs bk stored read epoch cle near ehor recent
  have early := forkWindow.1
  have positive : 0 < preset.SLOTS_PER_EPOCH := UInt64.lt_trans (by decide) long
  have longNat : 2 ≤ preset.SLOTS_PER_EPOCH.toNat := UInt64.lt_iff_toNat_lt.mp long
  have reachU : Store.Reachable config anchorState anchorBlock ((e.world n).state u) :=
    e.reachable (fun v hv => (start v hv).symm ▸ Store.Reachable.anchor anchored) n u hu
  have reachW : Store.Reachable config anchorState anchorBlock ((e.world k).state w) :=
    e.reachable (fun v hv => (start v hv).symm ▸ Store.Reachable.anchor anchored) k w hw
  obtain ⟨headBlock, headFound⟩ := reachW.known_of_blockState stored
  obtain ⟨base, boundary, storedBaseU, boundaryOk, bridgeU⟩ :=
    e.checkpointState_fromBlock anchored start hu sourceOk
  obtain ⟨boundary', aBlock, boundaryOk', aFound, aLe, descends⟩ :=
    Store.isAncestor_of_getCheckpointBlock early read
  have sameBoundary : boundary' = boundary := Except.ok.inj (boundaryOk'.symm.trans boundaryOk)
  subst boundary'
  obtain ⟨sa, storedA⟩ : ∃ sa, ((e.world k).state w).blockStates[c.root]? = some sa := by
    obtain ⟨post, postOk, -⟩ := reachW.blockStatesFromParents aFound
    exact ⟨post, postOk⟩
  have baseEq : base = sa := e.blockStates_eq anchored hu hw (start u hu) (start w hw)
    (oneBlock u hu w hw n k bn bk) storedBaseU storedA
  subst baseEq
  have aSlot : base.slot = aBlock.slot := blockState_slot_eq reachW anchorSlot aFound storedA
  have bridge : (base.slot = boundary ∧ source = base) ∨
      (base.slot < boundary ∧ processSlots config checks base boundary = .ok source) := by
    rcases bridgeU with ⟨le, same⟩ | ran
    · exact .inl ⟨UInt64.le_antisymm (aSlot ▸ aLe) le, same⟩
    · exact .inr ran
  have clearC := clear_of_getCheckpointBlock early boundaryOk read aFound
  have before := blocks_before_fork anchored start anchorSlot slots parameters forkWindow
    inHorizon hw bk
  have cEpoch : computeEpochAtSlot preset boundary = c.epoch :=
    computeEpochAtSlot_computeStartSlotAtEpoch positive boundaryOk
  have boundaryNat := computeStartSlotAtEpoch_ok_iff.mp boundaryOk
  have cle' : c.epoch.toNat ≤ epoch.toNat := UInt64.le_iff_toNat_le.mp cle
  have ehor' : epoch.toNat ≤ horizon.toNat := UInt64.le_iff_toNat_le.mp ehor
  have boundaryBefore : ∀ next ∈ config.nextFork fork,
      boundary.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat := by
    intro next member
    have below := forkWindow.2 next member
    rw [boundaryNat.2]
    exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  have bounded : epoch.toNat < 2 ^ 64 - 1 := by
    have fits := boundaryNat.1
    have double : c.epoch.toNat * 2 ≤ c.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat :=
      Nat.mul_le_mul_left _ longNat
    omega
  -- The run from genesis to the source.
  obtain ⟨sourceRun⟩ : Nonempty (Run config checks ⟨fork, base⟩ ⟨fork, source⟩) := by
    rcases bridge with ⟨_, rfl⟩ | ⟨_, ran⟩
    · exact ⟨.nil⟩
    · exact run_of_processSlots ran boundaryBefore
  obtain ⟨headRun⟩ := run_of_blockState anchored anchorSlot hw (start w hw) before storedA
  have sourceSlot : source.slot = boundary := by
    rcases bridge with ⟨h, rfl⟩ | ⟨_, ran⟩
    · exact h
    · exact (processSlots_slot ran).2
  have sourceEpoch : getCurrentEpoch source = c.epoch := by
    simp only [getCurrentEpoch, sourceSlot]
    exact cEpoch
  -- The run from the source to a state whose registry at the epoch is the one of the head state.
  obtain ⟨y, ⟨tail⟩, yLe, registry⟩ : ∃ y : BeaconState preset fork,
      Nonempty (Run config checks ⟨fork, source⟩ ⟨fork, y⟩) ∧ getCurrentEpoch y ≤ epoch ∧
      ∀ position, isActiveAt y epoch position = isActiveAt hs epoch position := by
    by_cases cur : getCurrentEpoch hs ≤ epoch
    · exact run_to_epoch_early anchored early anchorSlot lookahead hw (start w hw) before aFound
        storedA bridge headFound stored descends clearC (cEpoch ▸ cle) boundaryBefore bounded
        recent cur
    · have later : epoch < getCurrentEpoch hs := UInt64.not_le.mp cur
      have headSlot : hs.slot = headBlock.slot :=
        blockState_slot_eq reachW anchorSlot headFound stored
      have above : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := by
        have step : epoch.toNat + 1 ≤ hs.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
          have := UInt64.lt_iff_toNat_lt.mp later
          simp only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div] at this
          omega
        have := (Nat.le_div_iff_mul_le (by omega)).mp step
        have := hs.slot.toNat_lt
        nlinarith
      obtain ⟨S, SOk⟩ : ∃ S, computeStartSlotAtEpoch preset epoch = .ok S :=
        ⟨UInt64.ofNat (epoch.toNat * preset.SLOTS_PER_EPOCH.toNat),
          computeStartSlotAtEpoch_ok_iff.mpr ⟨above, by
            rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt above]⟩⟩
      have SNat := (computeStartSlotAtEpoch_ok_iff.mp SOk).2
      have boundaryLe : boundary ≤ S := by
        rw [UInt64.le_iff_toNat_le, boundaryNat.2, SNat]
        exact Nat.mul_le_mul_right _ cle'
      have beforeS : ∀ next ∈ config.nextFork fork,
          S.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat := by
        intro next member
        have below := forkWindow.2 next member
        rw [SNat]
        exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      have anchorLe : anchorBlock.slot ≤ S :=
        UInt64.le_trans (reachW.anchorSlot_le (anchorSlot ▸ UInt64.le_refl _) aFound)
          (UInt64.le_trans aLe boundaryLe)
      obtain ⟨bE, readE⟩ := e.exists_getCheckpointBlock_of_held anchored start anchorSlot early
        anchorParent hw bk headFound SOk anchorLe
      exact run_to_epoch_late anchored early anchorSlot positive hw (start w hw) before aFound
        storedA bridge headFound stored descends clearC SOk boundaryLe beforeS bounded readE later
  have bound := ExitChurn.departing_stake_le_epoch genesis
    ((history.append headRun).append sourceRun) tail lookahead early yLe
    (by rw [sourceEpoch]; exact near)
  simp only [registry] at bound
  exact bound

end EthLib.Consensus.Models.Network
