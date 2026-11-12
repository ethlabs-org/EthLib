module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Joint

/-! Apply fast-confirmation Theorem 1 to the certified witness premises.

The theorem is the safety part of arXiv 2405.00549v4, Section 4, as stated by EthLib.

This module inherits the safety theorem's unfinished proof dependencies.

It stays outside the proof roots until those dependencies are proved. -/

public section

namespace EthLib.Consensus.Models.Network.FiveValidatorWitness.Trace

/-- The certified call's root is safe on the witness's next-slot interval. -/
theorem safe_confirmed_root :
    ∀ time : ℕ, 4000 ≤ time → time ≤ 4000 → SafeAt execution time confirmed.confirmedRoot := by
  have p := all_premises
  exact execution.safeAt_confirmedRoot p.sync p.half p.boost p.slots p.long p.window p.lookahead
    p.votes p.fits p.prompt p.committees p.follows p.preGloas p.oneBlock p.admitted p.included
    p.anchored p.sound p.anchorSlot p.anchorAtBoundary p.start p.noVotes p.syncStart p.maxAligned
    p.increment p.chain p.unique p.byzantine p.unslashed p.supply p.positive p.enough p.large
    p.nonzero p.headDrifts p.caller p.upToDate p.lower p.atSlots p.ran p.bounds p.inHorizon
    p.anchorParent p.lastCall p.slotOk p.nextOk p.followingOk p.nonempty

end EthLib.Consensus.Models.Network.FiveValidatorWitness.Trace
