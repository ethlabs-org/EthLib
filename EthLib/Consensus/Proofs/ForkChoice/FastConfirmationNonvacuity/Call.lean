module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Walk

/-! A full fast-confirmation call advances from the anchor in the candidate slot-3 store. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.FiveValidatorWitness

open Base

/-- The call records the child as both its current head and its confirmed root. -/
def confirmed : FastConfirmationStore :=
  { getFastConfirmationStore anchor with currentSlotHead := blockRoot, confirmedRoot := blockRoot }

set_option maxRecDepth 10000 in
/-- The reset and checkpoint-selection branches preserve the anchor as the walk's start.

The store stays abstract here to avoid repeating its maps in the kernel's branch checks. -/
theorem latest_of_reads (store : Store preset .phase0) (fcr : FastConfirmationStore)
    (root : fcr.confirmedRoot = anchorRoot)
    (source : fcr.currentEpochObservedJustifiedCheckpoint = ⟨0, anchorRoot⟩)
    (slot : store.getCurrentSlot config = .ok 3)
    (epoch : store.getCurrentStoreEpoch config = .ok 0)
    (parent : store.block anchorRoot = .ok (anchorBlock stateRoot))
    (epochParent : store.getBlockEpoch anchorRoot = .ok 0)
    (ancestor : store.isAncestor ⟨blockRoot, .pending⟩ ⟨anchorRoot, .pending⟩ = .ok true)
    (unrealized : store.unrealizedJustification blockRoot =
      .ok postState.currentJustifiedCheckpoint)
    (walked : store.findLatestConfirmedDescendant config fcr blockRoot anchorRoot = .ok blockRoot) :
    store.getLatestConfirmed config fcr blockRoot = .ok blockRoot := by
  simp only [Store.getLatestConfirmed, epoch, slot, root, epochParent, bind, Except.bind]
  simp only [show Uint64.addChecked 0 1 = .ok 1 from rfl, Except.mapError,
    show ¬ (1 : Epoch) < 0 by decide, ↓reduceIte, ancestor,
    show isStartSlotAtEpoch preset 3 = .ok false from rfl, pure, Except.pure,
    Bool.false_eq_true]
  simp only [source, parent, unrealized]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, false_and,
    show computeEpochAtSlot preset (anchorBlock stateRoot).slot = 0 from rfl,
    show Uint64.addChecked 0 1 = .ok 1 from rfl,
    show (0 : Epoch) ≤ 1 by decide, walked]

set_option maxRecDepth 10000 in
/-- Starting from the anchor, the candidate store selects the child through the walk. -/
theorem running_latest (fcr : FastConfirmationStore)
    (root : fcr.confirmedRoot = anchorRoot)
    (source : fcr.currentEpochObservedJustifiedCheckpoint = ⟨0, anchorRoot⟩) :
    (running 3000 2).getLatestConfirmed config fcr blockRoot = .ok blockRoot := by
  have slot : (running 3000 2).getCurrentSlot config = .ok 3 := by
    change (computeSlotAtTimeMs config 0 3000).mapError ForkChoiceError.arith = .ok 3
    simp [computeSlotAtTimeMs, Uint64.subChecked, Uint64.divChecked, config,
      bind, Except.bind, Except.mapError]
  have epoch : (running 3000 2).getCurrentStoreEpoch config = .ok 0 := by
    rw [Store.getCurrentStoreEpoch, slot]
    rfl
  have parent : (running 3000 2).block anchorRoot = .ok (anchorBlock stateRoot) := by
    simp [Store.block, running_anchor, pure, Except.pure]
  have epochParent : (running 3000 2).getBlockEpoch anchorRoot = .ok 0 := by
    rw [Store.getBlockEpoch, parent]
    rfl
  have ancestor : (running 3000 2).isAncestor ⟨blockRoot, .pending⟩
      ⟨anchorRoot, .pending⟩ = .ok true := by
    have path' := Store.getAncestor_parent_of_slot_lt (node := ⟨blockRoot, .pending⟩)
      (running_child 3000 2) (running_anchor 3000 2)
      (show signedBlock.message.slot > 0 by decide)
    change (running 3000 2).getAncestor ⟨blockRoot, .pending⟩ 0 =
      .ok ⟨anchorRoot, .pending⟩ at path'
    simp [Store.isAncestor, parent, show (anchorBlock stateRoot).slot = 0 from rfl,
      path', bind, Except.bind, pure, Except.pure,
      show ¬ Fork.glamsterdam ≤ Fork.phase0 by decide]
  have unrealized : (running 3000 2).unrealizedJustification blockRoot =
      .ok postState.currentJustifiedCheckpoint := by
    simp [Store.unrealizedJustification, running, admitted, pure, Except.pure]
  exact latest_of_reads _ fcr root source slot epoch parent epochParent ancestor unrealized
    (running_walk fcr source)

set_option maxRecDepth 10000 in
/-- A full call on the candidate store confirms its child from the initial rule state.

This computes a store operation; it does not yet exhibit an allowed network execution. -/
theorem running_call :
    (running 3000 2).onFastConfirmation config (getFastConfirmationStore anchor) =
      .ok confirmed := by
  have slot : (running 3000 2).getCurrentSlot config = .ok 3 := by
    change (computeSlotAtTimeMs config 0 3000).mapError ForkChoiceError.arith = .ok 3
    simp [computeSlotAtTimeMs, Uint64.subChecked, Uint64.divChecked, config,
      bind, Except.bind, Except.mapError]
  have epoch : (running 3000 2).getCurrentStoreEpoch config = .ok 0 := by
    rw [Store.getCurrentStoreEpoch, slot]
    rfl
  have head := running_head 3000 2 (by decide) epoch (.inl rfl)
  let updated := { getFastConfirmationStore anchor with currentSlotHead := blockRoot }
  have update : (running 3000 2).updateFastConfirmationVariables config
      (getFastConfirmationStore anchor) blockRoot = .ok updated := by
    rw [Store.updateFastConfirmationVariables, slot]
    rfl
  simp only [Store.onFastConfirmation, head, bind, Except.bind, update,
    running_latest updated rfl rfl]
  rfl

/-- The successful call changes the confirmed root, rather than returning its selected start. -/
theorem running_call_nontrivial :
    ∃ after, (running 3000 2).onFastConfirmation config (getFastConfirmationStore anchor) =
      .ok after ∧ after.confirmedRoot ≠ anchorRoot :=
  ⟨confirmed, running_call, blockRoot_ne_anchorRoot⟩

end EthLib.Consensus.Models.Network.FiveValidatorWitness
