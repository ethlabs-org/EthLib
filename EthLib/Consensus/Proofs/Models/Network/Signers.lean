module

public import EthLib.Consensus.Proofs.Models.Network.Model

/-!
# Proof: an honest validator is the first to send each of its signed statements

This module derives first-send provenance from the network model's restriction on forgery.

The signature assumption is in [arXiv 2405.00549v4, Section 2, Validators][fcr].

No validator can carry a signed statement of an honest validator unless a sent message had it.

So the first message with such a statement comes from the honest validator itself.

For comparison, [verified-fast-confirmation][vfc] assumes the premise `no_forgery`.

[fcr]: https://arxiv.org/abs/2405.00549v4
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
  classical
  induction n generalizing m with
  | zero => simp [Execution.world_zero, World.initial] at sent
  | succ n ih =>
    -- If a message already carried the statement, keep its first send.
    by_cases prior : ∃ earlier ∈ (e.world n).sent, x ∈ P.signed earlier
    · obtain ⟨earlier, member, signs⟩ := prior
      obtain ⟨k, before, first, sends, signsFirst, earliest⟩ := ih member signs
      exact ⟨k, Nat.lt_succ_of_lt before, first, sends, signsFirst, earliest⟩
    · have absent : ∀ earlier ∈ (e.world n).sent, x ∉ P.signed earlier := by
        intro earlier member signs
        exact prior ⟨earlier, member, signs⟩
      rw [Execution.world_succ] at sent
      cases event : e.events n with
      | send sender message =>
        rw [event] at sent
        rcases Set.mem_insert_iff.mp sent with same | earlier
        · subst m
          -- A different sender would need a prior message carrying the statement.
          have own : x.1 = sender := by
            by_contra other
            have allowed := e.allowed_world n
            rw [event] at allowed
            exact prior (allowed.1 x signed honest other)
          exact ⟨n, Nat.lt_succ_self n, message, own ▸ event, signed, absent⟩
        · exact (absent m earlier signed).elim
      | wait time =>
        rw [event] at sent
        exact (absent m sent signed).elim
      | deliver received =>
        rw [event] at sent
        exact (absent m sent signed).elim
      | move validator state =>
        rw [event] at sent
        exact (absent m sent signed).elim

end EthLib.Consensus.Models.Network
