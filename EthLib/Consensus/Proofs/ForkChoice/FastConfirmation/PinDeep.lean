module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumReserve
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalStatements

/-!
# The pin premise and its deep window

`PinDriftWithin` is the drift premise of the pin reserve for a counting state that may be on
another branch.
It covers calls within the withdrawal delay of the finalized block's state.

Deeper calls are covered by `deep_reserve_covers_active`: there the reserve holds three times the
stake of the call's active set.

This file is a temporary home.
Both declarations move unchanged to `FastConfirmation/PinDriftBound.lean`, their ruled home, when
the pin's producer lands after DR.
The CHANGELOG line naming `Execution.justifiedPinned` as the reader of
`deep_reserve_covers_active` goes with them.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}

/-- Deeper than the withdrawal delay from the finalized block's state, the pin reserve holds three
times the stake of the call's active set.

There `fall` charges every current key its whole effective balance, and the reserve adds three times
their sum.

The active voters of the call are its current keys, read at their effective balances.

A total that is computed has no active index past `2 ^ 64`, so the voters name distinct keys.

A deeper call therefore has no honest set with three times its stake above the reserve: the
consumer of the pin premise covers it by this lemma, and `PinDriftWithin` excludes it. -/
theorem deep_reserve_covers_active {pulled anc fin : BeaconState preset fork} {pulledTotal : Gwei}
    (pulledOk : getTotalActiveBalance pulled = .ok pulledTotal)
    (deep : config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat <
      (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) :
    3 * stake (fun v : ValidatorIndex => balanceAt pulled v.toNat) (activeVoters pulled) ≤
      pinReserve config pulled anc fin := by
  have active : stake (fun v : ValidatorIndex => balanceAt pulled v.toNat) (activeVoters pulled) ≤
      ∑ i ∈ (Finset.range pulled.validators.data.size).filter
        (fun i => isActiveAt pulled (getCurrentEpoch pulled) i = true), balanceAt pulled i := by
    obtain ⟨indices, checked, -⟩ := bind_ok_iff.mp pulledOk
    have same := getActiveValidatorIndicesChecked_ok checked
    unfold stake activeVoters
    rw [← same, ← Finset.sum_image (f := fun i => balanceAt pulled i) (g := UInt64.toNat)
      (fun a _ b _ h => UInt64.toNat_inj.mp h)]
    apply Finset.sum_le_sum_of_subset
    intro i member
    obtain ⟨v, inList, rfl⟩ := Finset.mem_image.mp member
    obtain ⟨validator, found, isActive⟩ :=
      (mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mp (List.mem_toFinset.mp inList)
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1, ?_⟩
    simp [isActiveAt, found, isActive]
  have shallowNot : ¬ ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat ≤
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) := by omega
  unfold pinReserve
  dsimp only
  simp only [shallowNot, ↓reduceIte]
  refine le_trans (Nat.mul_le_mul_left 3 active) ?_
  refine le_trans ?_ (Nat.le_add_left _ _)
  iterate 8 refine Nat.le_add_right_of_le ?_
  exact Nat.le_add_left _ _

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J}

/-- An honest voter set of a call keeps its stake in each counting state, up to the pin reserve.

The call reads the pulled-up state of its store's head and its current target.

The counting state belongs to an honest store, and may be on another branch since the finalized
checkpoint of the target block's state.

Once finality has passed the anchor, the counting state's chain reads that checkpoint.

The counting state is the state of that chain's block or a later slot of it, in the target's epoch
or the next.

Its slots need not stop at a child block of that chain; the epoch bounds limit them, and the
state is still a `CountedState`.

Then three times the stake of the counting state's quorum and of the voters at the call is at most
twice the counting total, plus the call's total and the pin reserve, plus three times the stake
of the voters in that quorum.

The reserve reads the call's blocks, so two honest stores may collide instead.

This is the shallow-window obligation: it asks that the call's epoch be within the withdrawal delay
of the finalized block's state, `depthFin ≤ partialDelay` in `pinReserve`.

Deeper calls are not covered here.

There `pinReserve` holds three times the stake of the call's active set
(`deep_reserve_covers_active`), and the consumer covers them by that lemma. -/
def PinDriftWithin (horizon : Epoch) (last : ℕ) : Prop :=
  .fusaka ≤ fork →
  ∀ u ∈ J, ∀ n (head : Root) (pulled anc fin : BeaconState preset fork)
    (target : Checkpoint),
    (e.world n).time ≤ last →
    (∃ node, ((e.world n).state u).getHead config = .ok node ∧ node.root = head) →
    ((e.world n).state u).getPulledUpHeadState config head = .ok pulled →
    ((e.world n).state u).getCurrentTarget config head = .ok target →
    ((e.world n).state u).blockStates[target.root]? = some anc →
    (getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch →
      ((e.world n).state u).blockStates[anc.finalizedCheckpoint.root]? = some fin) →
    (anc.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState → fin = anchorState) →
    (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat ≤
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat →
    ∀ w ∈ J, ∀ k (root : Root) (rootState counted : BeaconState preset fork),
    (e.world k).time ≤ last → ((e.world k).state w).blockStates[root]? = some rootState →
    (counted = rootState ∨ ∃ slot, processSlots config checks rootState slot = .ok counted) →
    CountedState ((e.world k).state w) config counted →
    target.epoch ≤ getCurrentEpoch counted →
    (getCurrentEpoch counted).toNat ≤ target.epoch.toNat + 1 → getCurrentEpoch counted ≤ horizon →
    (getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch →
      ((e.world k).state w).getCheckpointBlock root anc.finalizedCheckpoint.epoch =
        .ok anc.finalizedCheckpoint.root) →
    ∀ (voters : Finset ValidatorIndex) (total pulledTotal : Gwei),
    (∀ v ∈ voters, v ∈ J ∧ v ∈ activeVoters pulled) →
    getTotalActiveBalance counted = .ok total → getTotalActiveBalance pulled = .ok pulledTotal →
    3 * stake (fun v => balanceAt counted v.toNat) (quorumVoters counted) +
        3 * stake (fun v => balanceAt pulled v.toNat) voters ≤
      2 * total.toNat + pulledTotal.toNat + pinReserve config pulled anc fin +
        3 * stake (fun v => balanceAt counted v.toNat) {v ∈ quorumVoters counted | v ∈ voters} ∨
      HonestCollision (e := e) last

end EthLib.Consensus.Models.Network
