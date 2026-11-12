module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Anchor
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Certificates
-- The proposer certificate reduces arrays and the derived Except equality procedure.
import all Init.Data.Array.Basic
import all Batteries.Data.Except

/-! Advance the five-validator witness from genesis to the slot of its first block. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.FiveValidatorWitness

open Base Serialization.Ssz
open scoped NonvacuityCertificates

/-- The first slot records the anchor roots and fills the previous header's state root. -/
def advanced : BeaconState preset .phase0 :=
  { state bodyRoot with
    slot := 1
    stateRoots := (state bodyRoot).stateRoots.set 0 stateRoot (by decide)
    blockRoots := (state bodyRoot).blockRoots.set 0 anchorRoot (by decide)
    latestBlockHeader := { (state bodyRoot).latestBlockHeader with stateRoot } }

/-- Filling the initial header's state root gives the already certified anchor root. -/
theorem initial_header_root :
    SszType.hashTreeRoot { (state bodyRoot).latestBlockHeader with stateRoot } =
      .ok anchorRoot :=
  (BeaconBlock.hashTreeRoot_header (block := anchorBlock stateRoot) body_root).trans anchor_root

set_option maxRecDepth 10000 in
/-- Advancing to slot one changes no epoch fields and reuses the two anchor certificates. -/
theorem first_slot : processSlots config .acceptAll (state bodyRoot) 1 = .ok advanced := by
  have emptyHeader : (state bodyRoot).latestBlockHeader.stateRoot = Vector.replicate 32 0 := rfl
  change advanceSlots config .acceptAll 1 (state bodyRoot) = .ok advanced
  simp only [advanceSlots, advanceSlot, epochIfLast, processSlot,
    state_root, emptyHeader, ↓reduceIte, initial_header_root, liftSsz, liftAccessor,
    Except.mapError, bind, Except.bind, pure, Except.pure]
  rfl

-- The equation avoids reducing the implementation of well-founded recursion.
attribute [local cbv_eval] proposerSearch.eq_def

set_option Elab.async false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 500000 in
set_option cbv.maxSteps 1000000 in
/-- Validator zero is the selected proposer at slot one. -/
theorem first_proposer : getBeaconProposerIndex advanced = .ok 0 := by
  -- Header and historical roots do not enter proposer selection.
  change getBeaconProposerIndex { state default with slot := 1 } = .ok 0
  cbv

end EthLib.Consensus.Models.Network.FiveValidatorWitness
