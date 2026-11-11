module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationSets
public import EthLib.Consensus.Proofs.ForkChoice.HonestDuties
public import EthLib.Consensus.Proofs.Transition.Invariants

/-!
# Statements: what the fast confirmation rule asks of the checkpoints of honest stores

This file names the facts of Casper FFG that the safety of the fast confirmation rule uses.

The rule is that of [arXiv 2405.00549v4][fcr].

The first two facts are definitions, and no theorem here proves them.

The theorems on the rule take them as hypotheses, and each definition may still change.

Each fact speaks of the stores of the honest validators along one execution.

A store counts a checkpoint as justified when it holds it, or a block of the store does.

The first two facts are the ones that accountable safety gives.

The finalized checkpoint of an honest store is on the chain of each later justified checkpoint.

Two justified checkpoints of one epoch are the same.

Neither names a quorum or a balance, and each holds up to a horizon, an epoch.

When one of them fails, two vote counts conflict.

A proof of accountable safety can then show that a third of the stake is slashable.

The third is less the change of balances up to the horizon.

So a theorem with the two facts as hypotheses gives one with that alternative in its conclusion.

The last two facts are not of that kind, since their failure makes no validator slashable.

Each justified checkpoint after the anchor is the target of the vote of an honest validator.

Take an honest third of the stake at one epoch.

Each justified checkpoint of that epoch is the target of the vote of one of them.

Both follow from one count, `Execution.exists_signsTarget_of_justified`.

The proof of that count is a placeholder.

A justified checkpoint has the votes of two thirds of an active balance.

The balance is that of the state that counts the votes.

So a set of validators signs it when the validators outside the set hold less than two thirds.

For the first fact the set is the honest validators, and the bound is Assumption 2 of the paper.

For the second it is the honest third, and the bound is the count that the rule makes.

H reads the Byzantine bound directly in the state that counts the votes.

N transports a particular honest subset from the pulled-up head state.

`DriftAtMost` bounds that subset's adverse weight shift by a number of Gwei.

Four lemmas of [verified-fast-confirmation][vfc] state these facts.

Two are `certified_finalized_prefix` and `certified_justified_unique`.

Two are `globalJustified_honestTarget` and `one_third_honest_intersects_two_thirds`.

There the set of validators is fixed, and the proofs count the stake of one registry.

[fcr]: https://arxiv.org/abs/2405.00549v4
[vfc]: https://github.com/fradamt/verified-fast-confirmation
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Fork}

/-- A checkpoint that a store counts as justified.

It is the justified checkpoint of the store, realized or not, or that of a block of the store.

A block has the justified checkpoint of its state and its unrealized justification. -/
def Store.Justified (store : Store preset fork) (checkpoint : Checkpoint) : Prop :=
  checkpoint = store.justifiedCheckpoint ∨ checkpoint = store.unrealizedJustifiedCheckpoint ∨
    (∃ (root : Root) (state : BeaconState preset fork), store.blockStates[root]? = some state ∧
      checkpoint = state.currentJustifiedCheckpoint) ∨
    ∃ root : Root, store.unrealizedJustifications[root]? = some checkpoint

/-- A state where a store can count votes: the state of one of its blocks, maybe at a later slot.

The state transition counts the votes for a target at the end of an epoch, after empty slots.

The rule and the fork choice count them in the state of a block, as it is or at a later slot. -/
def Store.Counts (store : Store preset fork) (config : Config)
    (state : BeaconState preset fork) : Prop :=
  ∃ (root : Root) (blockState : BeaconState preset fork),
    store.blockStates[root]? = some blockState ∧
      (state = blockState ∨
        ∃ (checks : SignatureChecks) (slot : Slot) (childRoot : Root)
          (child : BeaconBlock preset fork),
          store.blocks[childRoot]? = some child ∧ child.parentRoot = root ∧
          slot ≤ child.slot ∧
          processSlots config checks blockState slot = .ok state)

/-- The validators whose votes a state can count for a target.

Each is active in the epoch of the state or in the one before, and is not slashed. -/
def quorumVoters (state : BeaconState preset fork) : Finset ValidatorIndex :=
  {v ∈ (getActiveValidatorIndices state (getCurrentEpoch state) ++
      getActiveValidatorIndices state (getPreviousEpoch state)).toFinset |
    (state.validators.data[v.toNat]?.map (·.slashed)).getD true = false}

/-- A validator is not slashed in a state.

A validator that the state does not hold is not slashed in it. -/
def NotSlashed (state : BeaconState preset fork) (v : ValidatorIndex) : Prop :=
  (state.validators.data[v.toNat]?.map (·.slashed)).getD false = false

/-- The validators that are active in the epoch of a state. -/
def activeVoters (state : BeaconState preset fork) : Finset ValidatorIndex :=
  (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset

/-- The balances of a state have drifted from those of a reference by at most a number of Gwei.

The reference is the state where a bound on some validators is known.

The state is one that counts votes for a checkpoint.

Take any set of validators that holds no validator slashed in the state, and those outside it.

So the stake that a slashed validator loses is no drift.

In the state, those outside whose votes can count hold some share of the active balance.

Three times their stake less twice the active balance is the excess over two thirds.

That excess is at most the same excess in the reference plus the drift.

In the reference, the stake is that of the active validators.

The drift is the least number that moves a bound of two thirds from the reference to the state.

A count for each validator gives a bound on the drift, as a sum of three terms.

Each term counts only validators that are not slashed in the state.

The first is twice the active stake of the reference that is no longer active stake of the state.

The second is the stake that the active validators of the state have gained since the reference.

The third is three times such a gain of a voter that is active only in the epoch before.

With fixed balances the third is zero for each validator that is active in the reference.

No theorem here proves that bound. -/
def DriftAtMost (reference state : BeaconState preset fork) (drift : ℕ) : Prop :=
  ∀ (p : ValidatorIndex → Prop) [DecidablePred p] (total : Gwei),
    (∀ v, p v → NotSlashed state v) →
    getTotalActiveBalance state = .ok total →
    3 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | ¬p v} +
        2 * stake (fun v => balanceAt reference v.toNat) (activeVoters reference) ≤
      3 * stake (fun v => balanceAt reference v.toNat) {v ∈ activeVoters reference | ¬p v} +
        2 * total.toNat + drift

/-- The validators outside a set hold less than two thirds of a state, from a reference.

No validator of the set is slashed in the state.

In the reference they hold less than two thirds of the active stake, by more than the drift. -/
theorem DriftAtMost.lt_two_mul_total {reference state : BeaconState preset fork} {drift : ℕ}
    (bound : DriftAtMost reference state drift) (p : ValidatorIndex → Prop) [DecidablePred p]
    (clean : ∀ v, p v → NotSlashed state v)
    (margin : 3 * stake (fun v => balanceAt reference v.toNat)
        {v ∈ activeVoters reference | ¬p v} + drift <
      2 * stake (fun v => balanceAt reference v.toNat) (activeVoters reference))
    {total : Gwei} (totalOk : getTotalActiveBalance state = .ok total) :
    3 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | ¬p v} <
      2 * total.toNat := by
  have moved := bound p total clean totalOk
  omega

namespace Models.Network

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}

/-- The finalized checkpoint of an honest store is on the chain of each later justified one.

The justified checkpoint is one of an honest store, at the epoch of the finalized one or later.

Its epoch is at most the horizon, which bounds the epochs that the two chains can differ over.

That store finds the finalized block on the chain of the justified block, at the finalized epoch. -/
def FinalizedPrefix
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (horizon : Epoch) : Prop :=
  ∀ u ∈ J, ∀ w ∈ J, ∀ n k checkpoint, ((e.world k).state w).Justified checkpoint →
    ((e.world n).state u).finalizedCheckpoint.epoch ≤ checkpoint.epoch →
    checkpoint.epoch ≤ horizon →
    ((e.world k).state w).getCheckpointBlock checkpoint.root
      ((e.world n).state u).finalizedCheckpoint.epoch =
        .ok ((e.world n).state u).finalizedCheckpoint.root

/-- Two justified checkpoints of honest stores at one epoch, up to a horizon, are the same. -/
def OneJustifiedPerEpoch
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (horizon : Epoch) : Prop :=
  ∀ u ∈ J, ∀ w ∈ J, ∀ n k first second, ((e.world n).state u).Justified first →
    ((e.world k).state w).Justified second → first.epoch = second.epoch →
    first.epoch ≤ horizon → first = second

/-- A validator signs a vote with a target, in a message sent along the execution. -/
def SignsTarget
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (v : ValidatorIndex) (target : Checkpoint) : Prop :=
  ∃ k, ∃ m ∈ (e.world k).sent, ∃ data,
    (v, data) ∈ statements config checks anchorState anchorBlock m ∧ data.target = target

/-- A validator signs a vote with a target, of a slot before a given one. -/
def SignsTargetBefore
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (v : ValidatorIndex) (target : Checkpoint) (slot : Slot) : Prop :=
  ∃ k, ∃ m ∈ (e.world k).sent, ∃ data,
    (v, data) ∈ statements config checks anchorState anchorBlock m ∧ data.target = target ∧
      data.slot < slot

/-- A vote of a slot before a given one is a vote. -/
theorem SignsTargetBefore.signsTarget
    {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J} {v : ValidatorIndex} {target : Checkpoint} {slot : Slot}
    (signs : SignsTargetBefore e v target slot) : SignsTarget e v target :=
  let ⟨k, m, sent, data, member, same, _⟩ := signs
  ⟨k, m, sent, data, member, same⟩

/-- Each justified checkpoint of an honest store after the anchor has an honest vote.

The checkpoint is at a later epoch than the given one, the epoch of the anchor.

Its epoch is at most the horizon.

An honest validator signs a vote with the checkpoint as its target.

The vote is of a slot before the current slot of the store. -/
def JustifiedByHonestVote
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (anchorEpoch horizon : Epoch) : Prop :=
  ∀ u ∈ J, ∀ n checkpoint slot, ((e.world n).state u).Justified checkpoint →
    ((e.world n).state u).getCurrentSlot config = .ok slot →
    anchorEpoch < checkpoint.epoch → checkpoint.epoch ≤ horizon →
    ∃ v ∈ J, SignsTargetBefore e v checkpoint slot

/-- An honest third of the stake signs each justified checkpoint of the epoch of its count.

The stake is read in the pulled-up state of a block of an honest store, as the rule reads it.

The voters are honest and active in that state.

Three times their stake exceeds its active balance by more than the margin.

The margin covers the change of balances between that state and a state that counts votes.

The votes are for a checkpoint of the current epoch of the store.

Take such a checkpoint that an honest store counts as justified.

It is the target of a vote that one of the voters signs.

The vote is of a slot before the current slot of the store that counts the checkpoint.

The epoch is after the given one, the epoch of the anchor.

No voter has to sign a target here: the definition only counts stake. -/
def HonestThirdPins
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (anchorEpoch horizon : Epoch) (margin : ℕ) : Prop :=
  ∀ u ∈ J, ∀ n head state total epoch, ∀ voters : Finset ValidatorIndex,
    ((e.world n).state u).getPulledUpHeadState config head = .ok state →
    getTotalActiveBalance state = .ok total →
    ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
    epoch ≤ horizon →
    (∀ v ∈ voters, v ∈ J) → (∀ v ∈ voters, v ∈ activeVoters state) →
    total.toNat + margin < 3 * stake (fun v => balanceAt state v.toNat) voters →
    ∀ w ∈ J, ∀ k checkpoint slot, ((e.world k).state w).Justified checkpoint →
      ((e.world k).state w).getCurrentSlot config = .ok slot →
      checkpoint.epoch = epoch → anchorEpoch < epoch →
      ∃ v ∈ voters, SignsTargetBefore e v checkpoint slot

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
  genesisTimeMs) J}

/-- The count: a set of validators signs a justified checkpoint when the others cannot.

The checkpoint is one that an honest store counts as justified, after the epoch of its anchor.

The store starts as the store of the anchor.

No checkpoint of the state of the anchor is of a later epoch than that state.

A state of the store counts the votes for it, in its epoch or the one after.

It is the state of a block of the store, maybe at a later slot, as `Store.Counts` says.

In each such state, take the validators outside the set whose votes can count.

They hold less than two thirds of the active balance.

Then a validator of the set signs a vote with the checkpoint as its target.

The vote is of a slot before the current slot of the store.

A block holds only votes of earlier slots, and a store takes no block of a later slot.

The proof is new, and has three parts.

A justified checkpoint of a store comes from the count of a state of one of its blocks.

Each counted vote is in a block of the chain of that state.

The store has read each vote of each of its blocks.

It uses the agreement of the committees of the state of a block with those of the target state.

That agreement is a part of issue 1458.

In [verified-fast-confirmation][vfc], `IncludedSupermajorityLink` holds the signers of a count.

There `one_third_honest_intersects_two_thirds` and `two_quorums_intersect_honest` intersect them.

[vfc]: https://github.com/fradamt/verified-fast-confirmation -/
theorem Execution.exists_signsTarget_of_justified {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    {w : ValidatorIndex} (honest : w ∈ J) (start : e.start w = anchor) {k : ℕ}
    {checkpoint : Checkpoint} {slot : Slot}
    (justified : ((e.world k).state w).Justified checkpoint)
    (slotOk : ((e.world k).state w).getCurrentSlot config = .ok slot)
    (after : anchor.justifiedCheckpoint.epoch < checkpoint.epoch)
    (p : ValidatorIndex → Prop) [DecidablePred p]
    (few : ∀ (state : BeaconState preset fork) (total : Gwei),
      ((e.world k).state w).Counts config state →
      checkpoint.epoch.toNat ≤ (getCurrentEpoch state).toNat →
      (getCurrentEpoch state).toNat ≤ checkpoint.epoch.toNat + 1 →
      getTotalActiveBalance state = .ok total →
      3 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | ¬p v} <
        2 * total.toNat) :
    ∃ v, p v ∧ SignsTargetBefore e v checkpoint slot := by
  sorry

/-- Each justified checkpoint has an honest vote, from the bound in each counting state.

The bound counts Byzantine current-or-previous-epoch voters against the active denominator.

The threshold is in percent.

Take each state where an honest store can count votes, up to the epoch after the horizon.

The threshold is strictly below two thirds, and the denominator is positive.

No comparison with a reference state's balances is needed. -/
theorem Execution.justifiedByHonestVote [DecidablePred (· ∈ J)] {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (start : ∀ w ∈ J, e.start w = anchor) {horizon : Epoch}
    {threshold : ℕ}
    (byzantine : ∀ w ∈ J, ∀ k (state : BeaconState preset fork) total,
      ((e.world k).state w).Counts config state →
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      getTotalActiveBalance state = .ok total →
      100 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | v ∉ J} ≤
        threshold * total.toNat)
    (positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    (enough : 3 * threshold < 200) :
    JustifiedByHonestVote e anchor.justifiedCheckpoint.epoch horizon := by
  intro w honest k checkpoint slot justified slotOk after inHorizon
  refine e.exists_signsTarget_of_justified anchored sound honest (start w honest) justified slotOk
    after (· ∈ J) fun state total counts _ upper totalOk => ?_
  have inside := UInt64.le_iff_toNat_le.mp inHorizon
  have bound := byzantine w honest k state total counts (by omega) totalOk
  have lower := UInt64.le_iff_toNat_le.mp (le_getTotalBalance (getTotalActiveBalance_ok totalOk))
  have pos := UInt64.lt_iff_toNat_lt.mp positive
  have strict := Nat.mul_lt_mul_of_pos_right enough (show 0 < total.toNat by omega)
  nlinarith

/-- An honest third signs each justified checkpoint of its epoch, with the drift as the margin.

The reference is the pulled-up state of a block of an honest store, where the rule counts.

Take each state where an honest store can count votes.

Its epoch is the current epoch of the first store or the one after.

It has drifted from the reference by at most the given drift.

No honest validator is slashed in a state where an honest store can count votes.

That number is the margin, and it covers two epochs of drift at most. -/
theorem Execution.honestThirdPins {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState)
    (start : ∀ w ∈ J, e.start w = anchor) {horizon : Epoch} {drift : ℕ}
    (drifts : ∀ u ∈ J, ∀ n head reference epoch,
      ((e.world n).state u).getPulledUpHeadState config head = .ok reference →
      ((e.world n).state u).getCurrentStoreEpoch config = .ok epoch →
      epoch ≤ horizon →
      ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
        ((e.world k).state w).Counts config state →
        epoch.toNat ≤ (getCurrentEpoch state).toNat →
        (getCurrentEpoch state).toNat ≤ epoch.toNat + 1 →
        DriftAtMost reference state drift)
    (unslashed : ∀ w ∈ J, ∀ k (state : BeaconState preset fork),
      ((e.world k).state w).Counts config state → ∀ v ∈ J, NotSlashed state v) :
    HonestThirdPins e anchor.justifiedCheckpoint.epoch horizon drift := by
  intro u caller n head reference total epoch voters referenceOk totalOk epochOk inHorizon good active third w
    honest k checkpoint slot justified slotOk same after
  subst same
  obtain ⟨v, member, signs⟩ := e.exists_signsTarget_of_justified anchored sound honest
    (start w honest) justified slotOk after (· ∈ voters) fun state stateTotal counts lower upper
      stateTotalOk => by
    have split := Finset.sum_filter_add_sum_filter_not (activeVoters reference) (· ∈ voters)
      fun v => balanceAt reference v.toNat
    have same : ({v ∈ activeVoters reference | v ∈ voters} : Finset ValidatorIndex) = voters :=
      Finset.ext fun v => by
        simpa only [Finset.mem_filter, and_iff_right_iff_imp] using active v
    have covered := Store.stake_le_of_getTotalBalance (getTotalActiveBalance_ok totalOk)
      (W := activeVoters reference) fun v member => List.mem_toFinset.mp member
    rw [same] at split
    simp only [stake] at third covered ⊢
    exact (drifts u caller n head reference checkpoint.epoch referenceOk epochOk inHorizon w honest k
      state counts lower upper).lt_two_mul_total (· ∈ voters)
      (fun v member => unslashed w honest k state counts v (good v member))
      (by simp only [stake]; omega) stateTotalOk
  exact ⟨v, member, signs⟩

end Models.Network

end EthLib.Consensus
