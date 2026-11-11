module

public import EthLib.Consensus.Proofs.Models.Network.Model

/-!
# Statements: an honest validator is the first to send each of its signed statements

This file states a fact of the network model that the safety of the fast confirmation rule uses.

The proof is a placeholder, and the statement may still change.

No validator can carry a signed statement of an honest validator unless a sent message had it.

So the first message with such a statement comes from the honest validator itself.

The proofs in [verified-fast-confirmation][vfc] assume this as the premise `no_forgery`.

[vfc]: https://github.com/fradamt/verified-fast-confirmation
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

variable {ν μ σ κ : Type*} [DecidableEq ν] {P : Protocol ν μ σ κ} {J : Set ν}

/-- A statement of an honest validator in a sent message was first sent by that validator.

No message sent before that event carries the statement. -/
theorem Execution.exists_first_send_of_signed (e : Execution P J) {n : ℕ} {m : μ}
    (sent : m ∈ (e.world n).sent) {x : ν × κ} (signed : x ∈ P.signed m) (honest : x.1 ∈ J) :
    ∃ k < n, ∃ first, e.events k = .send x.1 first ∧ x ∈ P.signed first ∧
      ∀ earlier ∈ (e.world k).sent, x ∉ P.signed earlier := by
  sorry

end EthLib.Consensus.Models.Network
