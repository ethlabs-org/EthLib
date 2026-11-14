module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Joint

/-! The place for applying fast-confirmation Theorem 1 to a certified premise bundle.

The theorem is the safety part of arXiv 2405.00549v4, Section 4, as stated by EthLib.

It now takes executions that check signatures with BLS.

The acceptance-only fixture of `Joint` does not satisfy that, so nothing is applied here.

An application needs a BLS premise bundle for the same execution.

This module stays outside the proof roots. -/

public section

namespace EthLib.Consensus.Models.Network.EightValidatorWitness.Trace

end EthLib.Consensus.Models.Network.EightValidatorWitness.Trace
