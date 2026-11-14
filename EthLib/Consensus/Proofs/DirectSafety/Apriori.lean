module

public import EthLib.Consensus.Participation
public import EthLib.Consensus.Proofs.DirectSafety.BalanceSources
public import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
import EthLib.Consensus.Proofs.DirectSafety.Cohorts
import EthLib.Consensus.Proofs.DirectSafety.IntervalBounds
import EthLib.Consensus.Proofs.DirectSafety.DepartureQueue
import EthLib.Consensus.Proofs.DirectSafety.FundingEpoch
import EthLib.Consensus.Proofs.DirectSafety.Provenance
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Order.Monotone.Defs
import EthLib.Base.Proofs.MapM
import EthLib.Base.Proofs.Uint64
import EthLib.Consensus.Proofs.Participation
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.BlockRewards
import EthLib.Consensus.Proofs.Transition.EpochParticipation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# A priori bounds on the balance changes of one epoch

From Altair, the base reward of one increment of effective balance is a factor times the increment.

That product is divided by the integer square root of the total active balance, rounding down.

The total base rewards of an epoch are that reward for each whole increment of the total.

They bound what one epoch can issue, but they are not monotone in the total.

On mainnet, a total of 36,066,180 ETH gives 12,154,302,660 Gwei.

One more ETH gives 12,118,236,816 Gwei, since the square root steps up while the increments do not.

This module bounds them by `issuanceEnvelope`, which is monotone in the total.

It also bounds what the rewards pass of an epoch takes from the balances, inside a leak or not.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Uint64

variable {preset : Preset}

/-- The issuance envelope of one epoch, in Gwei, at a total active balance in Gwei.

It is the base reward factor times the integer square root of the total, plus two.

It bounds the total base rewards of an epoch, and it is monotone in the total. -/
private def issuanceEnvelope (preset : Preset) (total : Nat) : Nat :=
  preset.BASE_REWARD_FACTOR.toNat * (total.sqrt + 2)

/-- The issuance envelope does not decrease when the total active balance grows. -/
private theorem issuanceEnvelope_monotone : Monotone (issuanceEnvelope preset) := fun _ _ le =>
  Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.sqrt_le_sqrt le) 2)

/-- The whole increments of a total, times the scaled factor over its square root, rounding down.

The product is at most the factor times the square root plus two.

Both roundings only lower the product, so it is at most `total * factor / root`.

A total below `(root + 1)^2` is at most `root * (root + 2)`, which gives the bound. -/
private theorem div_mul_div_sqrt_le (total increment factor : Nat) :
    total / increment * (increment * factor / total.sqrt) ≤ factor * (total.sqrt + 2) := by
  have below : total ≤ total.sqrt * (total.sqrt + 2) := by
    have := Nat.lt_succ_sqrt total
    have square : total.sqrt * (total.sqrt + 2) + 1 = total.sqrt.succ * total.sqrt.succ := by
      rw [Nat.succ_eq_add_one]
      ring
    omega
  calc total / increment * (increment * factor / total.sqrt)
      ≤ total / increment * (increment * factor) / total.sqrt :=
        Nat.mul_div_le_mul_div_assoc _ _ _
    _ = total / increment * increment * factor / total.sqrt := by rw [Nat.mul_assoc]
    _ ≤ total * factor / total.sqrt :=
        Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _))
    _ ≤ factor * (total.sqrt + 2) := by
        apply Nat.div_le_of_le_mul
        calc total * factor ≤ total.sqrt * (total.sqrt + 2) * factor :=
              Nat.mul_le_mul_right _ below
          _ = total.sqrt * (factor * (total.sqrt + 2)) := by ring

/-- A successful base reward per increment is the scaled factor over the integer square root. -/
private theorem toNat_getBaseRewardPerIncrement {total perIncrement : Gwei}
    (computed : getBaseRewardPerIncrement preset total = .ok perIncrement) :
    perIncrement.toNat = preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      preset.BASE_REWARD_FACTOR.toNat / total.toNat.sqrt := by
  simp only [getBaseRewardPerIncrement, liftArith, mapError_ok_iff, bind_ok_iff] at computed
  obtain ⟨scaled, scaledOk, rootOk⟩ := computed
  rw [mulChecked_ok_iff] at scaledOk
  rw [divChecked_ok_iff] at rootOk
  rw [rootOk.2, scaledOk.2, toNat_integerSquareroot]

/-- The total base rewards of an epoch are at most the issuance envelope of its total.

They are the whole increments of the total active balance, times the base reward per increment.

The bound needs no premise beyond the success of the reward per increment. -/
private theorem totalBaseRewards_le_envelope {total perIncrement : Gwei}
    (computed : getBaseRewardPerIncrement preset total = .ok perIncrement) :
    total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * perIncrement.toNat ≤
      issuanceEnvelope preset total.toNat := by
  rw [toNat_getBaseRewardPerIncrement computed]
  exact div_mul_div_sqrt_le _ _ _

/-! ## The issuance of one epoch

From Electra, an epoch pays three kinds of credit that no deposit funds.

The rewards pass pays the flags of the previous epoch.

The blocks pay their proposers for newly set flags, and the sync committee for each slot.

They stay below twice the issuance envelope of the ceiling `T⁺`.

That needs `T⁺` to be at most three halves of the total active balance.

The bound is `3439 / 1792` of the envelope, where `3439 / 1792 < 2`.
-/

/-- Four times a stake `a` is at most `5 · √T · (√a + 2)`, in integer roots.

The total must be positive and at least two thirds of the stake.

It is the integer form of `√(3/2) < 5/4`. -/
private theorem four_le_five_sqrt {a T : Nat} (positive : 0 < T) (ratio : 2 * a ≤ 3 * T) :
    4 * a ≤ 5 * T.sqrt * (a.sqrt + 2) := by
  have below := Nat.lt_succ_sqrt T
  have belowStake := Nat.lt_succ_sqrt a
  have one : 0 < T.sqrt := Nat.sqrt_pos.mpr positive
  generalize T.sqrt = s at *
  generalize a.sqrt = S at *
  have total : T ≤ s * (s + 2) := by
    have square : s.succ * s.succ = s * (s + 2) + 1 := by rw [Nat.succ_eq_add_one]; ring
    omega
  have stake : a ≤ S * (S + 2) := by
    have square : S.succ * S.succ = S * (S + 2) + 1 := by rw [Nat.succ_eq_add_one]; ring
    omega
  by_cases wide : 6 * (s + 2) ≤ 5 * (S + 2)
  · calc 4 * a ≤ s * (6 * (s + 2)) := by
          rw [show s * (6 * (s + 2)) = 6 * (s * (s + 2)) by ring]
          omega
      _ ≤ s * (5 * (S + 2)) := Nat.mul_le_mul_left s wide
      _ = 5 * s * (S + 2) := by ring
  · have narrow : 4 * S ≤ 5 * s := by omega
    calc 4 * a ≤ 4 * S * (S + 2) := by rw [Nat.mul_assoc]; omega
      _ ≤ 5 * s * (S + 2) := Nat.mul_le_mul_right _ narrow

/-- The credits of one epoch are at most twice the issuance envelope of the ceiling `a`.

`F` bounds the flag rewards, `G` the proposer credits and `Y` the sync credits.

They are read at a total `T` of `n` whole increments `I`, with base reward per increment `perInc`.

`p` bounds the increments that set a flag, and `q` those that pay a proposer, over two epochs.

The total is at most `a` and at least two thirds of it. -/
private theorem issuance_certificate {I a T n perInc p q F G Y : Nat} (inc : 0 < I)
    (aligned : n * I = T) (positive : 0 < T) (ratio : 2 * a ≤ 3 * T) (bounded : T ≤ a)
    (rate : perInc * T.sqrt ≤ I * preset.BASE_REWARD_FACTOR.toNat)
    (part : p * I ≤ a) (attesters : q * I ≤ 2 * a)
    (flags : F * (n * 64) ≤ 54 * perInc * p ^ 2) (proposers : G * 448 ≤ 54 * perInc * q)
    (sync : Y * 28 ≤ issuanceEnvelope preset T) :
    F + G + Y ≤ 2 * issuanceEnvelope preset a := by
  have key := four_le_five_sqrt positive ratio
  have rootPos : 0 < T.sqrt := Nat.sqrt_pos.mpr positive
  have roots : T.sqrt ≤ a.sqrt := Nat.sqrt_le_sqrt bounded
  unfold issuanceEnvelope at sync ⊢
  generalize preset.BASE_REWARD_FACTOR.toNat = B at *
  generalize T.sqrt = s at *
  generalize a.sqrt = S at *
  -- The flag rewards: `F · 64 · T · s ≤ 54 · B · a²`, then `F · 256 ≤ 405 · B · (S + 2)`.
  have flagsScaled : F * 64 * T * s * I ≤ 54 * B * a ^ 2 * I := by
    calc F * 64 * T * s * I = F * (n * 64) * (s * I ^ 2) := by rw [← aligned]; ring
      _ ≤ 54 * perInc * p ^ 2 * (s * I ^ 2) := Nat.mul_le_mul_right _ flags
      _ = 54 * (perInc * s) * (p * I) ^ 2 := by ring
      _ ≤ 54 * (I * B) * a ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ rate) (Nat.pow_le_pow_left part 2)
      _ = 54 * B * a ^ 2 * I := by ring
  have flagsRatio : F * 64 * s * T ≤ 81 * B * a * T := by
    calc F * 64 * s * T = F * 64 * T * s := by ring
      _ ≤ 54 * B * a ^ 2 := Nat.le_of_mul_le_mul_right flagsScaled inc
      _ = 27 * B * a * (2 * a) := by ring
      _ ≤ 27 * B * a * (3 * T) := Nat.mul_le_mul_left _ ratio
      _ = 81 * B * a * T := by ring
  have flagsRoot : F * 256 * s ≤ 405 * B * (S + 2) * s := by
    calc F * 256 * s = F * 64 * s * 4 := by ring
      _ ≤ 81 * B * a * 4 := Nat.mul_le_mul_right _ (Nat.le_of_mul_le_mul_right flagsRatio positive)
      _ = 81 * B * (4 * a) := by ring
      _ ≤ 81 * B * (5 * s * (S + 2)) := Nat.mul_le_mul_left _ key
      _ = 405 * B * (S + 2) * s := by ring
  have flagsBound := Nat.le_of_mul_le_mul_right flagsRoot rootPos
  -- The proposer credits: `G · 448 · s ≤ 108 · B · a`, then `G · 1792 ≤ 540 · B · (S + 2)`.
  have proposersScaled : G * 448 * s * I ≤ 108 * B * a * I := by
    calc G * 448 * s * I = G * 448 * (s * I) := by ring
      _ ≤ 54 * perInc * q * (s * I) := Nat.mul_le_mul_right _ proposers
      _ = 54 * (perInc * s) * (q * I) := by ring
      _ ≤ 54 * (I * B) * (2 * a) := Nat.mul_le_mul (Nat.mul_le_mul_left _ rate) attesters
      _ = 108 * B * a * I := by ring
  have proposersRoot : G * 1792 * s ≤ 540 * B * (S + 2) * s := by
    calc G * 1792 * s = G * 448 * s * 4 := by ring
      _ ≤ 108 * B * a * 4 := Nat.mul_le_mul_right _ (Nat.le_of_mul_le_mul_right proposersScaled inc)
      _ = 108 * B * (4 * a) := by ring
      _ ≤ 108 * B * (5 * s * (S + 2)) := Nat.mul_le_mul_left _ key
      _ = 540 * B * (S + 2) * s := by ring
  have proposersBound := Nat.le_of_mul_le_mul_right proposersRoot rootPos
  -- The sync credits read the total itself, which is at most the ceiling.
  have syncBound : Y * 28 ≤ B * (S + 2) :=
    sync.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right roots 2))
  have flagsAtom : 405 * B * (S + 2) = 405 * (B * (S + 2)) := by ring
  have proposersAtom : 540 * B * (S + 2) = 540 * (B * (S + 2)) := by ring
  rw [flagsAtom] at flagsBound
  rw [proposersAtom] at proposersBound
  generalize B * (S + 2) = X at *
  omega

/-- The sync credits of one block are at most the issuance envelope over `28` per slot.

The participant reward is the base rewards of the total, times `2 / 64`, per slot and member.

The proposer share is at most a seventh of it.

The reward divides by the slots of an epoch, so a reward that exists makes them positive. -/
private theorem syncCredit_le {fork : Fork} {s : BeaconState preset fork}
    {reward proposer total : Gwei} (rewardOk : syncParticipantReward s = .ok reward)
    (share : proposer.toNat * 7 ≤ reward.toNat) (totalOk : getTotalActiveBalance s = .ok total) :
    preset.SYNC_COMMITTEE_SIZE.toNat * (reward.toNat + proposer.toNat) *
        (28 * preset.SLOTS_PER_EPOCH.toNat) ≤ issuanceEnvelope preset total.toNat ∧
      0 < preset.SLOTS_PER_EPOCH.toNat := by
  simp only [syncParticipantReward, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff] at rewardOk
  obtain ⟨read, readOk, perIncrement, perOk, rewardOk⟩ := rewardOk
  have same : read = total := Except.ok.inj (readOk.symm.trans totalOk)
  subst read
  obtain ⟨increments, incrementsOk, base, baseOk, weighted, weightedOk, perWeight, perWeightOk,
    perSlot, perSlotOk, rewardOk⟩ := rewardOk
  rw [divChecked_ok_iff] at incrementsOk perWeightOk perSlotOk rewardOk
  rw [mulChecked_ok_iff] at baseOk weightedOk
  have envelope := totalBaseRewards_le_envelope perOk
  have weightValue : SYNC_REWARD_WEIGHT.toNat = 2 := rfl
  have denominator : WEIGHT_DENOMINATOR.toNat = 64 := rfl
  rw [weightValue] at weightedOk
  rw [denominator] at perWeightOk
  -- Each step of the reward rounds down, so the members' rewards of a slot fit its share.
  have member : preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat ≤ perSlot.toNat := by
    rw [rewardOk.2, Nat.mul_comm]
    exact Nat.div_mul_le_self _ _
  have slot : perSlot.toNat * preset.SLOTS_PER_EPOCH.toNat ≤ perWeight.toNat := by
    rw [perSlotOk.2]
    exact Nat.div_mul_le_self _ _
  have weight : perWeight.toNat * 32 ≤ base.toNat := by
    rw [perWeightOk.2, weightedOk.2]
    have := Nat.div_mul_le_self (base.toNat * 2) 64
    omega
  have baseLe : base.toNat ≤ issuanceEnvelope preset total.toNat := by
    rw [baseOk.2, incrementsOk.2, Nat.mul_comm]
    exact envelope
  have proposerLe : preset.SYNC_COMMITTEE_SIZE.toNat * proposer.toNat * 7 ≤
      preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ share
  have members := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat member
  have chain : preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat * preset.SLOTS_PER_EPOCH.toNat *
      32 ≤ issuanceEnvelope preset total.toNat := by
    have := Nat.mul_le_mul_right 32 (members.trans slot)
    omega
  have scaled := Nat.mul_le_mul_right (4 * preset.SLOTS_PER_EPOCH.toNat) proposerLe
  refine ⟨?_, Nat.pos_of_ne_zero fun zero =>
    perSlotOk.1 (UInt64.toNat_inj.mp (by simpa using zero))⟩
  calc preset.SYNC_COMMITTEE_SIZE.toNat * (reward.toNat + proposer.toNat) *
        (28 * preset.SLOTS_PER_EPOCH.toNat) =
      preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat * preset.SLOTS_PER_EPOCH.toNat * 28 +
        preset.SYNC_COMMITTEE_SIZE.toNat * proposer.toNat * 7 *
          (4 * preset.SLOTS_PER_EPOCH.toNat) := by ring
    _ ≤ preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat * preset.SLOTS_PER_EPOCH.toNat * 28 +
        preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat * (4 * preset.SLOTS_PER_EPOCH.toNat) :=
        Nat.add_le_add_left scaled _
    _ = preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat * preset.SLOTS_PER_EPOCH.toNat * 32 := by
        ring
    _ ≤ issuanceEnvelope preset total.toNat := chain

/-! ## The penalties of one rewards pass

From Altair, the rewards pass charges an eligible validator three penalties at most.

It pays the weight of the source flag and of the target flag, each when that flag is missing.

The base reward times the weight is divided by the weight denominator, rounding down.

It also pays the inactivity penalty when the target flag is missing.

That penalty is the effective balance times the new score, over the score bias times the quotient.

A missing head flag costs nothing, and the rewards only raise the balance.

The sync committee penalties are not part of this pass.

`processSyncAggregate` applies them in each block.
-/

variable {config : Config} {fork : Fork} {state scored after : BeaconState preset fork}
  {total : Gwei}

/-- One pass of deltas records the reward of each validator as its credit, and keeps the registry.

Its penalties are recorded with no credit. -/
private theorem replayDeltas_credits {fork : Fork} (source : BalanceSource)
    (deltas : Array Gwei × Array Gwei) {pre post : BalanceReplay preset fork}
    (ok : replayDeltas source deltas pre = .ok post) :
    post.1.validators = pre.1.validators ∧
      (post.2.map (·.creditLimit)).sum = (pre.2.map (·.creditLimit)).sum +
        ((List.range pre.1.validators.data.size).map fun i => (deltas.1.getD i 0).toNat).sum := by
  unfold replayDeltas at ok
  generalize List.range pre.1.validators.data.size = indices at ok ⊢
  induction indices generalizing pre with
  | nil => cases ok; simp
  | cons i rest ih =>
    rw [List.foldlM_cons, bind_ok_iff] at ok
    obtain ⟨middle, stepOk, restOk⟩ := ok
    obtain ⟨registry, sum⟩ := ih restOk
    simp only [recordBalance, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq, exists_eq_left'] at stepOk
    obtain ⟨index, -, _, ⟨raised, raisedOk, rfl⟩, lowered, loweredOk, rfl⟩ := stepOk
    refine ⟨registry.trans ((decreaseBalance_validators loweredOk).trans
      (increaseBalance_validators raisedOk)), ?_⟩
    rw [sum]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    omega

/-- The credits of the rewards pass, from Altair, are its three flag rewards.

Each flag pays at most `w · perInc · p² / (n · 64)`.

There `w` is its weight, `p` its increments and `n` the active increments.

The weights sum to `54`, and `P` bounds the balance that sets each flag. -/
private theorem replayRewards_credits_le (altair : .altair ≤ fork)
    (within : state.RegistryWithinLimit) {events : List (BalanceEvent preset)}
    (replayed : replayRewards (config := config) (state, []) = .ok (after, events))
    (active : getTotalActiveBalance state = .ok total) {perIncrement : Gwei}
    (per : getBaseRewardPerIncrement preset total = .ok perIncrement) (P : Nat)
    (participating : ∀ flag participating (balance : Gwei),
      getUnslashedParticipatingIndices state altair flag (getPreviousEpoch state) =
        .ok participating →
      getTotalBalance state participating = .ok balance → balance.toNat ≤ P) :
    (events.map (·.creditLimit)).sum *
        (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * 64) ≤
      54 * perIncrement.toNat * (P / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ^ 2 := by
  unfold replayRewards at replayed
  split at replayed
  · cases replayed
    simp
  rename_i genesis
  simp only [bind_ok_iff] at replayed
  obtain ⟨ordinary, ordinaryOk, inactivity, inactivityOk, middle, folded, last⟩ := replayed
  simp only [rewardPasses, genesis, altair, ↓reduceIte, ↓reduceDIte] at ordinaryOk
  have finRange : List.finRange PARTICIPATION_FLAG_WEIGHTS.length =
      [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩] := rfl
  rw [finRange] at ordinaryOk
  simp only [List.mapM_cons, List.mapM_nil, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ordinaryOk
  obtain ⟨source, sourceOk, _, ⟨target, targetOk, _, ⟨head, headOk, _, rfl, rfl⟩, rfl⟩, rfl⟩ :=
    ordinaryOk
  rw [List.foldlM_cons, bind_ok_iff] at folded
  obtain ⟨first, firstOk, folded⟩ := folded
  rw [List.foldlM_cons, bind_ok_iff] at folded
  obtain ⟨second, secondOk, folded⟩ := folded
  rw [List.foldlM_cons, bind_ok_iff] at folded
  obtain ⟨third, thirdOk, folded⟩ := folded
  obtain rfl : third = middle := Except.ok.inj folded
  obtain ⟨firstSize, firstSum⟩ := replayDeltas_credits _ _ firstOk
  obtain ⟨secondSize, secondSum⟩ := replayDeltas_credits _ _ secondOk
  obtain ⟨-, thirdSum⟩ := replayDeltas_credits _ _ thirdOk
  obtain ⟨-, lastSum⟩ := replayDeltas_credits _ _ last
  -- The inactivity pass pays no reward.
  have noReward : ((List.range third.1.validators.data.size).map fun i =>
      (inactivity.1.getD i 0).toNat).sum = 0 := by
    simp [getInactivityPenaltyDeltas_rewards inactivityOk]
  -- Each flag pays at most its weight times the square of its increments.
  have flag {index : Fin PARTICIPATION_FLAG_WEIGHTS.length} {deltas : Array Gwei × Array Gwei}
      (computed : getFlagIndexDeltas state altair index = .ok deltas) :
      ((List.range state.validators.data.size).map fun i => (deltas.1.getD i 0).toNat).sum *
          (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * 64) ≤
        PARTICIPATION_FLAG_WEIGHTS[index].toNat * perIncrement.toNat *
          (P / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ^ 2 := by
    obtain ⟨rewards, penalties⟩ := deltas
    obtain ⟨flagged, balance, total', flaggedOk, weighed, totalOk, -⟩ :=
      getFlagIndexDeltas_getD within computed
    obtain rfl : total' = total := Except.ok.inj (totalOk.symm.trans active)
    have bound := getFlagIndexDeltas_rewards_le within computed flaggedOk weighed active per
    have balanceLe := participating _ _ _ flaggedOk weighed
    exact bound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (Nat.div_le_div_right balanceLe) 2))
  have one := flag sourceOk
  have two := flag targetOk
  have three := flag headOk
  have weights : PARTICIPATION_FLAG_WEIGHTS[(⟨0, by decide⟩ : Fin 3)].toNat +
      PARTICIPATION_FLAG_WEIGHTS[(⟨1, by decide⟩ : Fin 3)].toNat +
      PARTICIPATION_FLAG_WEIGHTS[(⟨2, by decide⟩ : Fin 3)].toNat = 54 := rfl
  rw [lastSum, noReward, thirdSum, secondSum, firstSum, secondSize, firstSize]
  simp only [List.map_nil, List.sum_nil, Nat.zero_add, Nat.add_zero]
  rw [← weights]
  simp only [Nat.add_mul] at one two three ⊢
  omega

/-- A sum of quotients is at most the quotient of the sum. -/
private theorem sum_div_le {ι : Type} (s : Finset ι) (f : ι → Nat) (d : Nat) :
    ∑ i ∈ s, f i / d ≤ (∑ i ∈ s, f i) / d := by
  rcases Nat.eq_zero_or_pos d with rfl | positive
  · simp
  · rw [Nat.le_div_iff_mul_le positive, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => Nat.div_mul_le_self _ _

/-- A balance loses at most the sum of the penalties of a list of deltas.

Each delta adds its reward without overflow, then subtracts its penalty, stopping at zero. -/
private theorem sub_foldl_le (j : Nat) :
    ∀ (deltas : List (Array Gwei × Array Gwei)) (balance : Gwei),
      deltas.foldlM (fun balance delta => (addChecked balance (delta.1.getD j 0)).map
          fun raised => saturatingSub raised (delta.2.getD j 0)) balance =
        .ok (deltas.foldl (fun balance delta =>
          saturatingSub (balance + delta.1.getD j 0) (delta.2.getD j 0)) balance) →
      balance.toNat - (deltas.foldl (fun balance delta =>
          saturatingSub (balance + delta.1.getD j 0) (delta.2.getD j 0)) balance).toNat ≤
        (deltas.map fun delta => (delta.2.getD j 0).toNat).sum
  | [], _, _ => by simp
  | delta :: rest, balance, folded => by
    rw [List.foldlM_cons, bind_ok_iff] at folded
    obtain ⟨next, stepped, restOk⟩ := folded
    cases added : addChecked balance (delta.1.getD j 0) with
    | error failure =>
      rw [added] at stepped
      cases stepped
    | ok raised =>
      rw [added] at stepped
      simp only [Except.map, Except.ok.injEq] at stepped
      obtain ⟨fits, value⟩ := addChecked_ok_iff.mp added
      have same : raised = balance + delta.1.getD j 0 :=
        UInt64.toNat_inj.mp (by rw [value, toNat_add_of_lt fits])
      subst same stepped
      have later := sub_foldl_le j rest _ restOk
      have step := toNat_saturatingSub (balance + delta.1.getD j 0) (delta.2.getD j 0)
      rw [toNat_add_of_lt fits] at step
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      omega

/-- The base reward of a validator, from Altair, is its whole increments times the scaled factor.

The factor times the increment is divided by the integer square root of the total. -/
private theorem toNat_getBaseReward_le (altair : .altair ≤ fork) {base : Gwei}
    {index : ValidatorIndex} (computed : getBaseReward state total index = .ok base)
    {validator : Validator} (found : state.validators.data[index.toNat]? = some validator) :
    base.toNat ≤ validator.effectiveBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat /
        total.toNat.sqrt) := by
  have copy := computed
  simp only [getBaseReward, altair, ↓reduceIte, bind_ok_iff] at copy
  obtain ⟨_, _, perIncrement, perOk, _⟩ := copy
  obtain ⟨validator', found', value⟩ := getBaseReward_eq_mul_of_altair altair perOk computed
  obtain rfl : validator' = validator := Option.some.inj (found'.symm.trans found)
  rw [value, toNat_getBaseRewardPerIncrement perOk]

/-- The loss of one balance in the rewards pass, from Altair, with the zero beyond the registry. -/
private theorem rewardsDebit_cases (altair : .altair ≤ fork) (within : state.RegistryWithinLimit)
    (updated : processInactivityUpdates config state altair = .ok scored)
    (computed : processRewardsAndPenalties config scored = .ok after)
    (active : getTotalActiveBalance state = .ok total) (j : Nat) :
    (state.validators.data.size ≤ j →
      actualBalanceAt ⟨fork, state⟩ j - actualBalanceAt ⟨fork, after⟩ j = 0) ∧
    ∀ inside : j < state.validators.data.size,
      actualBalanceAt ⟨fork, state⟩ j - actualBalanceAt ⟨fork, after⟩ j = 0 ∨
      ∃ base, isEligibleValidator (getPreviousEpoch state) state.validators.data[j] = .ok true ∧
        getBaseReward state total j.toUInt64 = .ok base ∧
        actualBalanceAt ⟨fork, state⟩ j - actualBalanceAt ⟨fork, after⟩ j ≤
          base.toNat * (TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat) /
              WEIGHT_DENOMINATOR.toNat +
            state.validators.data[j].effectiveBalance.toNat *
              (((after.inactivityScores altair).data[j]?.map UInt64.toNat).getD 0) /
              (config.INACTIVITY_SCORE_BIAS.toNat *
                (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
  have keptScores := congrFun (congrArg (fun s => s.inactivityScores)
    (processRewardsAndPenalties_frame computed)) altair
  -- The score update changes only the scores.
  obtain ⟨scores, rfl⟩ : ∃ scores, scored = { state with inactivityScores := scores } :=
    ⟨_, processInactivityUpdates_frame updated⟩
  have scoresAfter : after.inactivityScores altair = scores altair := keptScores
  by_cases genesis : getCurrentEpoch state = GENESIS_EPOCH
  · -- In the first epoch the pass changes nothing.
    obtain rfl : { state with inactivityScores := scores } = after := Except.ok.inj
      ((processRewardsAndPenalties_genesis config (by exact genesis)).symm.trans computed)
    have zero : actualBalanceAt ⟨fork, state⟩ j -
        actualBalanceAt ⟨fork, { state with inactivityScores := scores }⟩ j = 0 :=
      Nat.sub_self _
    exact ⟨fun _ => zero, fun _ => .inl zero⟩
  obtain ⟨flagDeltas, inactivityDeltas, flagged, penalized, balances⟩ :=
    processRewardsAndPenalties_balances_of_altair altair (by exact genesis) computed
  refine ⟨fun outside => ?_, fun inside => ?_⟩
  · have kept : after.balances.data[j]? = state.balances.data[j]? :=
      (balances j).2.2 outside
    simp only [actualBalanceAt, kept, Nat.sub_self]
  have finRange : List.finRange PARTICIPATION_FLAG_WEIGHTS.length =
      [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩] := rfl
  rw [finRange] at flagged
  simp only [List.mapM_cons, List.mapM_nil, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at flagged
  obtain ⟨⟨sourceRewards, sourcePenalties⟩, sourceOk, _, ⟨⟨targetRewards, targetPenalties⟩,
    targetOk, _, ⟨⟨headRewards, headPenalties⟩, headOk, _, rfl, rfl⟩, rfl⟩, rfl⟩ := flagged
  obtain ⟨inactivityRewards, inactivityPenalties⟩ := inactivityDeltas
  obtain ⟨source, _, total', -, -, totalOk, sourceFacts⟩ :=
    getFlagIndexDeltas_getD (by exact within) sourceOk
  obtain ⟨target, _, total'', -, -, totalOk', targetFacts⟩ :=
    getFlagIndexDeltas_getD (by exact within) targetOk
  obtain ⟨head, _, total''', -, -, totalOk'', headFacts⟩ :=
    getFlagIndexDeltas_getD (by exact within) headOk
  obtain rfl : total' = total := Except.ok.inj (totalOk.symm.trans active)
  obtain rfl : total'' = total' := Except.ok.inj (totalOk'.symm.trans active)
  obtain rfl : total''' = total'' := Except.ok.inj (totalOk''.symm.trans active)
  obtain ⟨matching, matchingOk, inactivityFacts⟩ :=
    getInactivityPenaltyDeltas_getD_of_altair altair (by exact within) penalized
  obtain ⟨eligible, eligibleOk, sourceNo, sourceYes⟩ := sourceFacts j inside
  obtain ⟨eligible₂, eligibleOk₂, targetNo, targetYes⟩ := targetFacts j inside
  obtain ⟨eligible₃, eligibleOk₃, headNo, headYes⟩ := headFacts j inside
  obtain ⟨eligible₄, eligibleOk₄, -, inactivityExempt, inactivityPaid⟩ :=
    inactivityFacts j inside
  obtain rfl : eligible = eligible₂ := Except.ok.inj (eligibleOk.symm.trans eligibleOk₂)
  obtain rfl : eligible = eligible₃ := Except.ok.inj (eligibleOk.symm.trans eligibleOk₃)
  obtain rfl : eligible = eligible₄ := Except.ok.inj (eligibleOk.symm.trans eligibleOk₄)
  -- The loss of the balance is at most the sum of the four penalties.
  have loss : actualBalanceAt ⟨fork, state⟩ j - actualBalanceAt ⟨fork, after⟩ j ≤
      (sourcePenalties.getD j 0).toNat + (targetPenalties.getD j 0).toNat +
        (headPenalties.getD j 0).toNat + (inactivityPenalties.getD j 0).toNat := by
    have after_j := (balances j).1 inside
    rcases found : state.balances.data[j]? with _ | balance
    · simp [actualBalanceAt, found]
    · have folded := sub_foldl_le j _ balance ((balances j).2.1 inside balance found)
      simp only [actualBalanceAt, after_j, found, Option.map_some, Option.getD_some]
      simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil] at folded ⊢
      omega
  cases eligible with
  | false =>
    -- A validator that is not eligible pays nothing.
    left
    have sourceZero := (sourceNo rfl).2
    have targetZero := (targetNo rfl).2
    have headZero := (headNo rfl).2
    have inactivityZero := inactivityExempt (.inl rfl)
    rw [sourceZero, targetZero, headZero, inactivityZero] at loss
    simpa using loss
  | true =>
    right
    obtain ⟨base, baseOk, sourceIn, sourceOut⟩ := sourceYes rfl
    obtain ⟨base₂, baseOk₂, targetIn, targetOut⟩ := targetYes rfl
    obtain ⟨base₃, baseOk₃, headIn, headOut⟩ := headYes rfl
    obtain rfl : base = base₂ := Except.ok.inj (baseOk.symm.trans baseOk₂)
    obtain rfl : base = base₃ := Except.ok.inj (baseOk.symm.trans baseOk₃)
    -- A missed source or target costs its weight, and a missed head costs nothing.
    have sourceLe : (sourcePenalties.getD j 0).toNat ≤
        base.toNat * TIMELY_SOURCE_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat := by
      by_cases mem : j.toUInt64 ∈ source
      · obtain ⟨_, _, _, penalty⟩ := sourceIn mem
        rw [penalty]
        exact Nat.zero_le _
      · exact Nat.le_of_eq (by rw [(sourceOut mem).2]; rfl)
    have targetLe : (targetPenalties.getD j 0).toNat ≤
        base.toNat * TIMELY_TARGET_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat := by
      by_cases mem : j.toUInt64 ∈ target
      · obtain ⟨_, _, _, penalty⟩ := targetIn mem
        rw [penalty]
        exact Nat.zero_le _
      · exact Nat.le_of_eq (by rw [(targetOut mem).2]; rfl)
    have headZero : (headPenalties.getD j 0).toNat = 0 := by
      by_cases mem : j.toUInt64 ∈ head
      · obtain ⟨_, _, _, penalty⟩ := headIn mem
        rw [penalty]
        rfl
      · rw [(headOut mem).2]
        rfl
    -- A missed target also costs the inactivity penalty of the new score.
    have inactivityLe : (inactivityPenalties.getD j 0).toNat ≤
        state.validators.data[j].effectiveBalance.toNat *
          (((after.inactivityScores altair).data[j]?.map UInt64.toNat).getD 0) /
          (config.INACTIVITY_SCORE_BIAS.toNat *
            (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
      by_cases mem : j.toUInt64 ∈ matching
      · rw [inactivityExempt (.inr mem)]
        exact Nat.zero_le _
      · obtain ⟨score, found, penalty⟩ := inactivityPaid rfl mem
        have scoreAfter : (after.inactivityScores altair).data[j]? = some score := by
          rw [scoresAfter]
          exact found
        rw [penalty, scoreAfter]
        exact Nat.le_refl _
    refine ⟨base, by exact eligibleOk, by exact baseOk, ?_⟩
    have split := Nat.div_add_div_le_add_div (x := base.toNat * TIMELY_SOURCE_WEIGHT.toNat)
      (y := base.toNat * TIMELY_TARGET_WEIGHT.toNat) (z := WEIGHT_DENOMINATOR.toNat)
    rw [← Nat.mul_add] at split
    omega

/-- The loss of one balance in the rewards pass, from Altair, inside or outside a leak.

The state is the one before the update of the inactivity scores, with its total active balance.

Either the balance does not fall, or the validator is eligible and has a base reward at that total.

Its loss is then at most the weights of the source and target flags in that base reward.

The inactivity penalty of its new score, or of a zero score when it has none, adds to that loss.

The two weights are applied together, which rounds down once and so can only raise the bound. -/
private theorem balance_sub_le_of_processRewardsAndPenalties (altair : .altair ≤ fork)
    (within : state.RegistryWithinLimit)
    (updated : processInactivityUpdates config state altair = .ok scored)
    (computed : processRewardsAndPenalties config scored = .ok after)
    (active : getTotalActiveBalance state = .ok total) {j : Nat}
    (inside : j < state.validators.data.size) :
    actualBalanceAt ⟨fork, state⟩ j - actualBalanceAt ⟨fork, after⟩ j = 0 ∨
      ∃ base, isEligibleValidator (getPreviousEpoch state) state.validators.data[j] = .ok true ∧
        getBaseReward state total j.toUInt64 = .ok base ∧
        actualBalanceAt ⟨fork, state⟩ j - actualBalanceAt ⟨fork, after⟩ j ≤
          base.toNat * (TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat) /
              WEIGHT_DENOMINATOR.toNat +
            state.validators.data[j].effectiveBalance.toNat *
              (((after.inactivityScores altair).data[j]?.map UInt64.toNat).getD 0) /
              (config.INACTIVITY_SCORE_BIAS.toNat *
                (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) :=
  (rewardsDebit_cases altair within updated computed active j).2 inside

/-- The total effective balance of the validators eligible for the rewards of the previous epoch.

A validator whose eligibility cannot be decided counts nothing. -/
private def eligibleBalance (state : BeaconState preset fork) : Nat :=
  ∑ j ∈ Finset.range state.validators.data.size,
    match state.validators.data[j]? with
    | some validator =>
      match isEligibleValidator (getPreviousEpoch state) validator with
      | .ok true => validator.effectiveBalance.toNat
      | _ => 0
    | none => 0

/-- The debits of one rewards pass, from Altair, inside or outside a leak.

The eligible balance `E` is that of the state before the update of the inactivity scores.

Each new score must be at most `maxScore`, and `T` is the total active balance of the state.

```text
debits <= (W_source + W_target) * BASE_REWARD_FACTOR * E / (WEIGHT_DENOMINATOR * isqrt T)
          + E * maxScore / (INACTIVITY_SCORE_BIAS * INACTIVITY_PENALTY_QUOTIENT)
```

Each key rounds down on its own, and the sum of those quotients is at most the quotient of the sum.
-/
private theorem balanceDebits_le_of_processRewardsAndPenalties (altair : .altair ≤ fork)
    (within : state.RegistryWithinLimit)
    (updated : processInactivityUpdates config state altair = .ok scored)
    (computed : processRewardsAndPenalties config scored = .ok after)
    (active : getTotalActiveBalance state = .ok total) {maxScore : Nat}
    (capped : ∀ (j : Nat) (score : UInt64),
      (after.inactivityScores altair).data[j]? = some score → score.toNat ≤ maxScore) :
    balanceDebits state after ≤
      (TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat) *
          preset.BASE_REWARD_FACTOR.toNat * eligibleBalance state /
          (WEIGHT_DENOMINATOR.toNat * total.toNat.sqrt) +
        eligibleBalance state * maxScore /
          (config.INACTIVITY_SCORE_BIAS.toNat *
            (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
  -- Short names for the constants of the bound.
  generalize hweights : TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat = weights
  generalize hdenominator : WEIGHT_DENOMINATOR.toNat = denominator
  generalize hquotient : config.INACTIVITY_SCORE_BIAS.toNat *
    (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat = quotient
  generalize hincrement : preset.EFFECTIVE_BALANCE_INCREMENT.toNat = increment
  generalize hfactor : preset.BASE_REWARD_FACTOR.toNat = factor
  generalize hroot : total.toNat.sqrt = root
  obtain ⟨weight, hbalance, heligible⟩ : ∃ weight : Nat → Nat,
      eligibleBalance state = ∑ j ∈ Finset.range state.validators.data.size, weight j ∧
      ∀ j (inside : j < state.validators.data.size),
        isEligibleValidator (getPreviousEpoch state) state.validators.data[j] = .ok true →
          weight j = state.validators.data[j].effectiveBalance.toNat :=
    ⟨_, rfl, fun j inside eligible => by
      simp only [Array.getElem?_eq_getElem inside, eligible]⟩
  rw [hbalance]
  let debit (j : Nat) := actualBalanceAt ⟨fork, state⟩ j - actualBalanceAt ⟨fork, after⟩ j
  -- Each loss is at most the bound of its own weight.
  have point : ∀ j ∈ Finset.range state.validators.data.size, debit j ≤
      weight j / increment * (increment * factor / root) * weights / denominator +
        weight j * maxScore / quotient := by
    intro j member
    have inside := Finset.mem_range.mp member
    rcases (rewardsDebit_cases altair within updated computed active j).2 inside with
      zero | ⟨base, eligible, baseOk, bound⟩
    · change actualBalanceAt ⟨fork, state⟩ j - actualBalanceAt ⟨fork, after⟩ j ≤ _
      rw [zero]
      exact Nat.zero_le _
    · have baseLe := toNat_getBaseReward_le altair baseOk
        (by rw [toNat_toUInt64_of_lt within inside]; exact Array.getElem?_eq_getElem inside)
      have scoreLe : ((after.inactivityScores altair).data[j]?.map UInt64.toNat).getD 0 ≤
          maxScore := by
        rcases found : (after.inactivityScores altair).data[j]? with _ | score
        · exact Nat.zero_le _
        · exact capped j score found
      rw [heligible j inside eligible]
      rw [hweights, hdenominator, hquotient] at bound
      rw [hincrement, hfactor, hroot] at baseLe
      refine Nat.le_trans bound (Nat.add_le_add ?_ ?_)
      · exact Nat.div_le_div_right (Nat.mul_le_mul_right _ baseLe)
      · exact Nat.div_le_div_right (Nat.mul_le_mul_left _ scoreLe)
  -- Positions past the registry lose nothing.
  have outside : ∀ j ∈ Finset.range state.balances.data.size, debit j ≠ 0 →
      j < state.validators.data.size := fun j _ nonzero => by
    by_contra past
    exact nonzero
      ((rewardsDebit_cases altair within updated computed active j).1 (Nat.le_of_not_lt past))
  -- The whole increments of the eligible balance bound those of each key.
  have increments : ∑ j ∈ Finset.range state.validators.data.size, weight j / increment ≤
      (∑ j ∈ Finset.range state.validators.data.size, weight j) / increment :=
    sum_div_le _ _ _
  generalize hsum : ∑ j ∈ Finset.range state.validators.data.size, weight j = eligible
    at increments
  have rewardsPart : ∑ j ∈ Finset.range state.validators.data.size,
      weight j / increment * (increment * factor / root) * weights / denominator ≤
        weights * factor * eligible / (denominator * root) := by
    -- Both roundings only lower the product.
    have scaled : eligible / increment * (increment * factor / root) ≤ eligible * factor / root :=
      calc eligible / increment * (increment * factor / root)
          ≤ eligible / increment * (increment * factor) / root :=
            Nat.mul_div_le_mul_div_assoc _ _ _
        _ = eligible / increment * increment * factor / root := by rw [Nat.mul_assoc]
        _ ≤ eligible * factor / root :=
            Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _))
    calc ∑ j ∈ Finset.range state.validators.data.size,
          weight j / increment * (increment * factor / root) * weights / denominator
        ≤ (∑ j ∈ Finset.range state.validators.data.size,
            weight j / increment * (increment * factor / root) * weights) / denominator :=
          sum_div_le _ _ _
      _ ≤ eligible / increment * (increment * factor / root) * weights / denominator := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          exact Nat.div_le_div_right
            (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ increments))
      _ ≤ eligible * factor / root * weights / denominator :=
          Nat.div_le_div_right (Nat.mul_le_mul_right _ scaled)
      _ ≤ weights * (eligible * factor) / root / denominator := by
          rw [Nat.mul_comm _ weights]
          exact Nat.div_le_div_right (Nat.mul_div_le_mul_div_assoc _ _ _)
      _ = weights * factor * eligible / (denominator * root) := by
          rw [Nat.div_div_eq_div_mul, Nat.mul_comm root, Nat.mul_assoc, Nat.mul_comm eligible]
  have scorePart : ∑ j ∈ Finset.range state.validators.data.size,
      weight j * maxScore / quotient ≤ eligible * maxScore / quotient := by
    refine Nat.le_trans (sum_div_le _ _ _) (Nat.le_of_eq ?_)
    rw [← Finset.sum_mul, hsum]
  calc balanceDebits state after
      = ∑ j ∈ Finset.range state.balances.data.size, debit j := rfl
    _ = ∑ j ∈ (Finset.range state.balances.data.size).filter
          (· < state.validators.data.size), debit j := (Finset.sum_filter_of_ne outside).symm
    _ ≤ ∑ j ∈ Finset.range state.validators.data.size, debit j :=
        Finset.sum_le_sum_of_subset fun j member => by
          simp only [Finset.mem_filter, Finset.mem_range] at member ⊢
          exact member.2
    _ ≤ ∑ j ∈ Finset.range state.validators.data.size,
          (weight j / increment * (increment * factor / root) * weights / denominator +
            weight j * maxScore / quotient) := Finset.sum_le_sum point
    _ ≤ weights * factor * eligible / (denominator * root) + eligible * maxScore / quotient := by
        rw [Finset.sum_add_distrib]
        exact Nat.add_le_add rewardsPart scorePart

/-! ## No deposit credit to a withdrawable consolidation source

`withdrawnConsolidationCredit` is what a deposit event credits to pending consolidation sources.

It counts only the sources that can already withdraw at the current epoch.

On a run from genesis it is zero at every deposit event.

From Electra, a block deposit only queues a pending deposit, so its event credits nothing.

The pass of the pending deposits starts at a state of the epoch replay.

The stages before it keep `PendingConsolidationsOrdered` at the current epoch.

So every pending source there withdraws after the current epoch, slashed or not.
-/

/-- The credit to withdrawable pending sources is part of the credits of the event. -/
private theorem withdrawnConsolidationCredit_le_credits (event : BalanceEvent preset) :
    withdrawnConsolidationCredit event ≤ event.credits := by
  unfold withdrawnConsolidationCredit BalanceEvent.credits
  split
  · rename_i electra
    rw [funding_sum_zipIdx event.before.state.validators.data.toList (fun v i =>
      if decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch event.before.state).toNat) &&
          (event.before.state.pendingConsolidations electra).data.any
            (fun c => c.sourceIndex.toNat == i) then
        actualBalanceAt event.after i - actualBalanceAt event.before i else 0)]
    let credit := fun i => actualBalanceAt event.after i - actualBalanceAt event.before i
    -- A position past the balances after the event credits nothing.
    have outside : ∀ i ∈ Finset.range event.before.state.validators.data.toList.length,
        credit i ≠ 0 → i < event.after.state.balances.data.size := by
      intro i _ positive
      by_contra past
      apply positive
      simp [credit, actualBalanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt past)]
    calc _ ≤ ∑ i ∈ Finset.range event.before.state.validators.data.toList.length, credit i :=
          Finset.sum_le_sum fun i _ => by
            cases event.before.state.validators.data.toList[i]? with
            | none => exact Nat.zero_le _
            | some v =>
              simp only [Option.map_some, Option.getD_some]
              split
              · exact Nat.le_refl _
              · exact Nat.zero_le _
      _ = ∑ i ∈ (Finset.range event.before.state.validators.data.toList.length).filter
            (· < event.after.state.balances.data.size), credit i :=
          (Finset.sum_filter_of_ne outside).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset fun i member => by
          simp only [Finset.mem_filter, Finset.mem_range] at member ⊢
          exact member.2
  · exact Nat.zero_le _

/-- An event that starts at an ordered state credits no withdrawable pending source.

Every pending source there withdraws after the current epoch. -/
private theorem withdrawnConsolidationCredit_eq_zero_of_ordered {s t : BeaconState preset fork}
    {source : BalanceSource} {credit debit : Nat}
    (holds : PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s) :
    withdrawnConsolidationCredit ⟨source, ⟨fork, s⟩, ⟨fork, t⟩, credit, debit⟩ = 0 := by
  unfold withdrawnConsolidationCredit
  split
  · rename_i electra
    obtain ⟨-, sources⟩ := holds.2 electra
    refine List.sum_eq_zero fun x mem => ?_
    obtain ⟨⟨v, i⟩, member, rfl⟩ := List.mem_map.mp mem
    have read : s.validators.data[i]? = some v := by
      simpa using List.mem_zipIdx_iff_getElem?.mp member
    dsimp only
    split
    · rename_i due
      simp only [Bool.and_eq_true, decide_eq_true_eq, ← Array.any_toList, List.any_eq_true,
        beq_iff_eq] at due
      obtain ⟨withdrawable, c, mem, index⟩ := due
      obtain ⟨-, -, late⟩ := sources c mem v (by rw [index]; exact read)
      omega
    · rfl
  · rfl

/-- The epoch replay of an ordered state credits no withdrawable pending source.

Each stage keeps the order at the current epoch, so the deposit event starts at an ordered state. -/
private theorem epochBalanceReplay_withdrawnConsolidationCredit {checks : SignatureChecks}
    {s : BeaconState preset fork} {post : BalanceReplay preset fork}
    (holds : PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s)
    (ok : epochBalanceReplay (config := config) (checks := checks) s = .ok post) :
    ∀ e ∈ post.2, e.source = .deposits → withdrawnConsolidationCredit e = 0 := by
  let Settled (pre : BalanceReplay preset fork) : Prop :=
    PendingConsolidationsOrdered config (getCurrentEpoch pre.1).toNat pre.1 ∧
      ∀ e ∈ pre.2, e.source = .deposits → withdrawnConsolidationCredit e = 0
  -- A stage moves the state along its edge and records events that are not deposits.
  have moved {k : EpochStage} {pre : BalanceReplay preset fork} {u : BeaconState preset fork}
      (added : List (BalanceEvent preset)) (held : Settled pre)
      (edge : EpochStage.Edge config checks k pre.1 u)
      (quiet : ∀ e ∈ added, e.source ≠ .deposits) : Settled (u, pre.2 ++ added) := by
    refine ⟨edge.pendingConsolidationsOrdered held.1, fun e mem deposit => ?_⟩
    rcases List.mem_append.mp mem with mem | mem
    · exact held.2 e mem deposit
    · exact absurd deposit (quiet e mem)
  -- A carried stage moves the state along its edge and records nothing.
  have carried {k : EpochStage} {action : BeaconState preset fork → Except TransitionError _}
      {pre next : BalanceReplay preset fork} (held : Settled pre)
      (edge : ∀ {u}, action pre.1 = .ok u → EpochStage.Edge config checks k pre.1 u)
      (step : carryBalance action pre = .ok next) : Settled next := by
    simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
    obtain ⟨u, computed, rfl⟩ := step
    have settled := moved [] held (edge computed) (fun _ mem => by cases mem)
    rwa [List.append_nil] at settled
  have done : Settled post := by
    refine (epochBalanceReplay_trace ok).transport (fun a b => Settled a → Settled b)
      (fun _ => id) (fun one two => two ∘ one) ?_ ⟨holds, fun _ mem => by cases mem⟩
    intro k member pre next step held
    cases k <;> simp only [epochReplayAction] at step
    case justification => exact carried (k := .justification) held id step
    case registry => exact carried (k := .registry) held id step
    case inactivity =>
      split at step
      · rename_i present
        exact carried (k := .inactivity) held (fun computed => by
          simp only [EpochStage.Edge, present, ↓reduceDIte]
          exact computed) step
      · cases step
        exact held
    case eth1Reset =>
      split at step
      · rename_i present
        exact carried (k := .eth1Reset) held (fun computed => by
          simp only [EpochStage.Edge, present, ↓reduceDIte]
          exact computed) step
      · cases step
        exact held
    case rewards =>
      refine replayRewards_induction Settled (fun held ok => ?_) (fun penalty held ok => ?_)
        held step
      · simp only [recordBalance, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
          Except.ok.injEq] at ok
        obtain ⟨_, _, u, raised, rfl⟩ := ok
        obtain ⟨_, set⟩ := increaseBalance_ok raised
        obtain ⟨_, rfl⟩ := setBalance_ok set
        refine ⟨held.1, fun e mem deposit => ?_⟩
        rcases List.mem_append.mp mem with mem | mem
        · exact held.2 e mem deposit
        · rw [List.mem_singleton.mp mem] at deposit
          cases deposit
      · simp only [recordBalance, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
          Except.ok.injEq] at ok
        obtain ⟨_, _, u, lowered, rfl⟩ := ok
        obtain ⟨_, rfl⟩ := decreaseBalance_eq_ok_iff.mp lowered
        refine ⟨held.1, fun e mem deposit => ?_⟩
        rcases List.mem_append.mp mem with mem | mem
        · exact held.2 e mem deposit
        · rw [List.mem_singleton.mp mem] at deposit
          rcases penalty with rfl | rfl <;> cases deposit
    case slashings =>
      simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
      obtain ⟨_, _, u, slashed, rfl⟩ := step
      exact moved (k := .slashings) _ held slashed (by simp)
    case pendingDeposits =>
      split at step
      · rename_i electra
        simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
        obtain ⟨u, deposited, rfl⟩ := step
        have edge : EpochStage.Edge config checks .pendingDeposits pre.1 u := by
          simp only [EpochStage.Edge, electra, ↓reduceDIte]
          exact deposited
        refine ⟨edge.pendingConsolidationsOrdered held.1, fun e mem deposit => ?_⟩
        rcases List.mem_append.mp mem with mem | mem
        · exact held.2 e mem deposit
        · rw [List.mem_singleton.mp mem]
          exact withdrawnConsolidationCredit_eq_zero_of_ordered held.1
      · cases step
        exact held
    case pendingConsolidations =>
      split at step
      · rename_i electra
        simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
        obtain ⟨u, consolidated, rfl⟩ := step
        exact moved (k := .pendingConsolidations) _ held
          (by simp only [EpochStage.Edge, electra, ↓reduceDIte]; exact consolidated) (by simp)
      · cases step
        exact held
    all_goals simp [EpochStage.prefixStages] at member
  exact done.2

/-- The deposit events of one step before Gloas credit no withdrawable pending source.

A block deposit has no credit limit from Electra, and its credits are within that limit.

A slot runs the epoch replay from an ordered state, and its upgrades record no deposit. -/
private theorem stepBalanceEvents_withdrawnConsolidationCredit {checks : SignatureChecks}
    {g x y : ForkedBeaconState preset} (shared : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g) (step : Step config checks x y)
    (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {events : List (BalanceEvent preset)} (ok : step.balanceEvents = .ok events)
    (bounded : EventsBounded events) :
    ∀ e ∈ events, e.source = .deposits → withdrawnConsolidationCredit e = 0 := by
  have sourceEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
  cases step with
  | block engine signed due blockOk =>
    have quiet := funding_block_events sourceEarly engine signed.message
      (Step.balanceEvents_block sourceEarly ok)
    intro e mem deposit
    by_cases electra : .pectra ≤ e.before.fork
    · have zero := quiet e mem deposit electra
      have within := (bounded e mem).1
      have part := withdrawnConsolidationCredit_le_credits e
      omega
    · rw [withdrawnConsolidationCredit, dite_eq_right electra]
  | slot across =>
    -- The slot replays the epoch only at its last slot, then records the upgrade crossings.
    obtain ⟨advanced, advanceOk, upgrades⟩ := bind_ok_iff.mp across
    have steps := advanceOk
    simp only [advanceSlot, bind_ok_iff] at steps
    obtain ⟨next, nextOk, cached, cachedOk, epoched, epochedOk, -⟩ := steps
    obtain ⟨crossings, crossingOk, -⟩ := upgradeBalanceReplay_bounded upgrades
    have crossed : ∀ e ∈ crossings, e.source = .deposits →
        withdrawnConsolidationCredit e = 0 := fun e mem deposit =>
      absurd ((upgradeBalanceReplay_crossing crossingOk e mem).symm.trans deposit) (by decide)
    unfold epochIfLast at epochedOk
    split at epochedOk
    · rename_i last
      obtain ⟨_, _, epochEvents, replayOk, -⟩ :=
        epochBalanceReplay_result cached epoched sourceEarly epochedOk
      rw [Step.balanceEvents_epoch_slot across cachedOk nextOk last replayOk advanceOk
        crossingOk] at ok
      cases ok
      intro e mem
      rcases List.mem_append.mp mem with mem | mem
      · have ordered : PendingConsolidationsOrdered config (getCurrentEpoch cached).toNat
            cached := by
          obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
          exact shared.pendingConsolidationsOrdered genesis sourceEarly delay
        exact epochBalanceReplay_withdrawnConsolidationCredit ordered replayOk e mem
      · exact crossed e mem
    · rename_i last
      have replayed : (Step.slot across).balanceEvents = .ok ([] ++ crossings) := by
        simp only [Step.balanceEvents, cachedOk, nextOk, last, ↓reduceIte, advanceOk,
          crossingOk, bind, Except.bind, pure, Except.pure]
      rw [replayed] at ok
      cases ok
      simpa using crossed

/-- Lemma WC: on a run from genesis, no deposit event credits a withdrawable pending source.

Every pending consolidation source of a reachable state withdraws after the current epoch.

The epoch pass of the pending deposits starts at such a state, and block deposits credit nothing.

It covers the deposit events, the only ones whose `fundingCredit` reads this credit. -/
private theorem _root_.EthLib.Consensus.Run.withdrawnConsolidationCredit_eq_zero
    {checks : SignatureChecks} {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {high : Nat} {events : List (BalanceEvent preset)}
    (ok : tail.balanceEvents high = .ok events) :
    ∀ e ∈ events, e.source = .deposits → withdrawnConsolidationCredit e = 0 := by
  -- Every event of the run is within its own limits.
  obtain ⟨recorded, recordedOk, bounded⟩ :=
    Run.balanceEvents_bounded shared tail genesis early high
  rw [ok] at recordedOk
  cases recordedOk
  have key : ∀ {z : ForkedBeaconState preset} (part : Run config checks x z),
      z.fork < .glamsterdam → ∀ {found : List (BalanceEvent preset)},
        part.balanceEvents high = .ok found → EventsBounded found →
          ∀ e ∈ found, e.source = .deposits → withdrawnConsolidationCredit e = 0 := by
    intro z part
    induction part with
    | nil =>
      intro _ found ok _
      simp only [Run.balanceEvents, pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      exact fun _ mem => by cases mem
    | snoc pre step ih =>
      intro early found ok bounded
      simp only [Run.balanceEvents, bind_ok_iff] at ok
      obtain ⟨prior, priorOk, rest⟩ := ok
      have before := Nat.lt_of_le_of_lt step.chainStep.fork_le early
      split at rest
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
        obtain ⟨added, addedOk, rfl⟩ := rest
        intro e mem
        rcases List.mem_append.mp mem with mem | mem
        · exact ih before priorOk (fun e member => bounded e (List.mem_append_left _ member))
            e mem
        · exact stepBalanceEvents_withdrawnConsolidationCredit (shared.append pre) genesis step
            early delay addedOk (fun e member => bounded e (List.mem_append_right _ member)) e mem
      · cases rest
        exact ih before priorOk bounded
  exact key tail early ok bounded

/-! ## The a priori branch drift

The drift `f` of a branch is a function of numbers read at its reference state `x`.

These numbers are the observables below, and the window `H` with the epochs `H₁` before Electra.

`f` itself reads only those numbers and the constants of the preset and the configuration.

Its index `t` runs over the epochs `0` to `H + 1` of the window.

"Before the fork" means `t < H₁`.
-/

/-- The active-count path before the fork: `A_0` is given, and `A_{t+1} = A_t + cc(A_t)`. -/
private def countPath (config : Config) (start : Nat) : Nat → Nat
  | 0 => start
  | t + 1 => countPath config start t + cohortCap config (countPath config start t)

/-- The balance churn `δ(T)` from Electra, in Gwei, at a total active stake `T`.

It is the stake over the churn quotient, rounded down to an increment, and at least the minimum. -/
private def balanceChurn (preset : Preset) (config : Config) (total : Nat) : Nat :=
  max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
    (total / config.CHURN_LIMIT_QUOTIENT.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat)

/-- The activation and exit part `A_E(T)` of the balance churn. -/
private def exitChurn (preset : Preset) (config : Config) (total : Nat) : Nat :=
  min config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat (balanceChurn preset config total)

/-- The consolidation part `C(T)` of the balance churn. -/
private def consolidationChurn (preset : Preset) (config : Config) (total : Nat) : Nat :=
  balanceChurn preset config total - exitChurn preset config total

/-- The whistleblower quotient `WQ` of the window: the quotient before the fork, or from Electra. -/
private def whistleblowerQuotient (preset : Preset) (forkEpochs : Nat) : Nat :=
  if 0 < forkEpochs then preset.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  else preset.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA.toNat

/-- The minimum slashing penalty quotient `MSPQ` of the window.

A window before the fork takes the least quotient of Phase 0, Altair and Bellatrix. -/
private def slashingQuotient (preset : Preset) (forkEpochs : Nat) : Nat :=
  if 0 < forkEpochs then
    min (min preset.MIN_SLASHING_PENALTY_QUOTIENT.toNat
      preset.MIN_SLASHING_PENALTY_QUOTIENT_ALTAIR.toNat)
      preset.MIN_SLASHING_PENALTY_QUOTIENT_BELLATRIX.toNat
  else preset.MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA.toNat

/-- The divisor of the leak penalty: the score bias times the least inactivity penalty quotient. -/
private def leakDivisor (preset : Preset) (config : Config) : Nat :=
  config.INACTIVITY_SCORE_BIAS.toNat *
    min (min preset.INACTIVITY_PENALTY_QUOTIENT.toNat
      preset.INACTIVITY_PENALTY_QUOTIENT_ALTAIR.toNat)
      preset.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX.toNat

/-- The activations of the window, `nAct`.

Before the fork they are the growth of the active-count path.

From Electra each needs `MAX_EFFECTIVE_BALANCE` of funding.

That funding comes from `Pre`, from `K`, or from the deposit churn of each epoch.

A key made eligible before Electra has at least `MAX_EFFECTIVE_BALANCE` effective. -/
private def windowActivations (preset : Preset) (config : Config)
    (count scheduled pending carry horizon forkEpochs : Nat) : Nat :=
  if 0 < forkEpochs then countPath config (count + scheduled) (horizon + 1) - count
  else (pending + carry + config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat * (horizon + 2)) /
    preset.MAX_EFFECTIVE_BALANCE.toNat

/-- The fixed whistleblower allowance `Ω` of the window.

Every key that is slashable in the window pays it at most the window cap over `WQ`, once.

Those keys are active at `x`, activate in the window, or are exited but not yet withdrawable.

`inactive` counts the last kind.

Before the fork the window cap is `MAX_EFFECTIVE_BALANCE`.

From Electra it is `MAX_EFFECTIVE_BALANCE_ELECTRA`, since a key may switch to compounding. -/
private def whistleblowerAllowance (preset : Preset) (config : Config)
    (count scheduled pending carry inactive horizon forkEpochs : Nat) : Nat :=
  (count + windowActivations preset config count scheduled pending carry horizon forkEpochs +
      inactive) *
    (if 0 < forkEpochs then preset.MAX_EFFECTIVE_BALANCE.toNat
      else preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat) /
    whistleblowerQuotient preset forkEpochs

/-- The ceiling `T⁺_t` on the total active stake.

Before the fork it is `MIN_ACTIVATION_BALANCE` times the active-count path.

From Electra it starts at `funded` plus `K` plus `Ω`.

There `funded` is the funded stake plus the stake active only at the previous epoch.

Each epoch then adds twice the issuance envelope and `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT`.

The factor two covers one epoch's rewards, proposer rewards for two epochs of flags, and sync. -/
private def stakeCeiling (preset : Preset) (config : Config)
    (count scheduled pending carry inactive funded horizon forkEpochs : Nat) : Nat → Nat
  | 0 =>
    if 0 < forkEpochs then preset.MIN_ACTIVATION_BALANCE.toNat * (count + scheduled)
    else funded + carry +
      whistleblowerAllowance preset config count scheduled pending carry inactive horizon forkEpochs
  | t + 1 =>
    if 0 < forkEpochs ∧ t + 1 ≤ forkEpochs then
      preset.MIN_ACTIVATION_BALANCE.toNat * countPath config (count + scheduled) (t + 1)
    else
      let previous := stakeCeiling preset config count scheduled pending carry inactive funded
        horizon forkEpochs t
      previous + 2 * issuanceEnvelope preset previous +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat

/-- The exits `nX_t` of epoch `t`.

Before the fork they are the count churn at the end of the path, in `MIN_ACTIVATION_BALANCE`.

From Electra they are `A_E` of the ceiling. -/
private def exitFlow (preset : Preset) (config : Config) (count scheduled horizon forkEpochs : Nat)
    (ceiling : Nat → Nat) (t : Nat) : Nat :=
  if t < forkEpochs then
    preset.MIN_ACTIVATION_BALANCE.toNat *
      cohortCap config (countPath config (count + scheduled) (horizon + 1))
  else exitChurn preset config (ceiling t)

/-- The consolidations `nC_t` of epoch `t`: none before the fork, the constant cap `Cc` after.

`Cc` is the consolidation churn at the last ceiling `T⁺_{H+1}`. -/
private def consolidationFlow (preset : Preset) (config : Config) (horizon forkEpochs : Nat)
    (ceiling : Nat → Nat) (t : Nat) : Nat :=
  if t < forkEpochs then 0 else consolidationChurn preset config (ceiling (horizon + 1))

/-- The non-slashing penalty `λ_t` of epoch `t` over a stake `weight`, at a floor `lower`.

The first part is `ω · BRF · weight / sqrt(lower)`, with `ω = (3 + BRPE) / BRPE`.

The second part is the leak penalty at the score `σ + bias · (t + 1)`. -/
private def epochPenalty (preset : Preset) (config : Config) (score weight lower t : Nat) : Nat :=
  (3 + BASE_REWARDS_PER_EPOCH.toNat) * preset.BASE_REWARD_FACTOR.toNat * weight /
      (BASE_REWARDS_PER_EPOCH.toNat * lower.sqrt) +
    weight * (score + config.INACTIVITY_SCORE_BIAS.toNat * (t + 1)) / leakDivisor preset config

/-- The floor `T⁻_t` on the total active stake.

Each epoch takes its exits, its consolidations and its penalty from it. -/
private def floorPath (preset : Preset) (config : Config) (score : Nat)
    (weight outflow : Nat → Nat) (start : Nat) : Nat → Nat
  | 0 => start
  | t + 1 =>
    let lower := floorPath preset config score weight outflow start t
    lower - outflow t - epochPenalty preset config score (weight t) lower t

/-- The keys that a branch may hold at the end of the window, `N⁺`.

Growth of the ceiling above `W` adds at most one key per `MIN_ACTIVATION_BALANCE`, rounded up. -/
private def finalCount (preset : Preset) (stake count last : Nat) : Nat :=
  count + (last - stake + preset.MIN_ACTIVATION_BALANCE.toNat - 1) /
    preset.MIN_ACTIVATION_BALANCE.toNat

/-- The start `T⁻_0` of the floor.

It is `W` less the slashed stake, the slack and one increment per key of `N⁺`.

It also loses the slashing penalties of the ceiling, the due partials and the departures. -/
private def floorStart (preset : Preset)
    (stake slashed count slack departures partials last forkEpochs : Nat) : Nat :=
  stake - slashed - slack -
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat * finalCount preset stake count last -
    last / slashingQuotient preset forkEpochs - partials - departures

/-- The floor path of a window, with every input read from the observables. -/
private def windowFloor (preset : Preset) (config : Config)
    (stake slashed penalised count score slack carry pending scheduled departures partials
      inactive funded horizon forkEpochs : Nat) : Nat → Nat :=
  let ceiling := stakeCeiling preset config count scheduled pending carry inactive funded horizon
    forkEpochs
  floorPath preset config score (fun t => ceiling t + penalised)
    (fun t => exitFlow preset config count scheduled horizon forkEpochs ceiling t +
      consolidationFlow preset config horizon forkEpochs ceiling t)
    (floorStart preset stake slashed count slack departures partials (ceiling (horizon + 1))
      forkEpochs)

/-- The conditions under which `aprioriDrift` uses its formula.

The divisors are positive, and the whistleblower quotient exceeds one.

The minimum churn per epoch is positive.

With a zero minimum, a queue still lets one validator exit per epoch.

The formula does not charge that exit.

The withdrawal delay is at least two epochs.

The window ends before half the slashings vector, and the floor stays positive through it.

From the fork on, twice the ceiling is at most three times the floor.

That ratio keeps one epoch's issuance below twice the issuance envelope of the ceiling.

The last condition is temporary.

A window from a state before Electra must end before the fork. -/
private abbrev aprioriGuard (preset : Preset) (config : Config)
    (stake slashed penalised count score slack carry pending scheduled departures partials
      inactive funded horizon forkEpochs : Nat) : Prop :=
  0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∧ 0 < config.CHURN_LIMIT_QUOTIENT.toNat ∧
    0 < config.MIN_PER_EPOCH_CHURN_LIMIT.toNat ∧
    0 < preset.MIN_ACTIVATION_BALANCE.toNat ∧ 0 < preset.downwardBand ∧
    0 < leakDivisor preset config ∧ 0 < slashingQuotient preset forkEpochs ∧
    1 < whistleblowerQuotient preset forkEpochs ∧
    2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ∧
    horizon + 2 < preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 ∧
    (∀ t < horizon + 2, 0 < windowFloor preset config stake slashed penalised count score slack
      carry pending scheduled departures partials inactive funded horizon forkEpochs t) ∧
    (∀ t, forkEpochs ≤ t → t ≤ horizon + 1 →
      2 * stakeCeiling preset config count scheduled pending carry inactive funded horizon
        forkEpochs t ≤
      3 * windowFloor preset config stake slashed penalised count score slack carry pending
        scheduled departures partials inactive funded horizon forkEpochs t) ∧
    (forkEpochs = 0 ∨ horizon + 2 ≤ forkEpochs)

/-- The departures `Dnew` that the queues admit in the window, from their ends at `x`.

It is the carry of the queues, and the churn of each epoch from the end of each queue on.

Before the fork the exit churn is the count churn at the end of the active-count path.

From Electra it is `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT`, and consolidations add `Cc`.

Two `MAX_EFFECTIVE_BALANCE_ELECTRA` cover one departure at each end of the window. -/
private def departureBudget (preset : Preset) (config : Config)
    (count scheduled pending carry inactive funded queued exitEnd consolidationEnd horizon
      forkEpochs : Nat) : Nat :=
  let ceiling := stakeCeiling preset config count scheduled pending carry inactive funded
    horizon forkEpochs
  let exitRate := if 0 < forkEpochs then
      preset.MIN_ACTIVATION_BALANCE.toNat *
        cohortCap config (countPath config (count + scheduled) (horizon + 1))
    else config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat
  let consolidationRate := if 0 < forkEpochs then 0
    else consolidationChurn preset config (ceiling (horizon + 1))
  queued + (horizon + 2 - exitEnd) * exitRate +
    (horizon + 2 - consolidationEnd) * consolidationRate +
    2 * preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat

/-- The a priori drift `f` of a branch, from the observables of its reference state.

```text
f = 2 (dep + D + Λ + ρ) + act + cred + 2 B
```

`dep` is every departure of the window, `D` the non-slashing penalties and `Λ` the slack.

`ρ` is one increment for each key whose effective balance may fall.

`act` is the stake that may activate, `cred` the credits and `B` the boundary stake.

Without the guard, `f` is the unslashed stake `W - Z`, which makes the bound trivial. -/
private def aprioriDrift (preset : Preset) (config : Config)
    (stake slashed penalised count high score slack excess carry pending scheduled departures
      partials credits exitEnd consolidationEnd queued boundary inactive funded
      horizon forkEpochs : Nat) : Nat :=
  if aprioriGuard preset config stake slashed penalised count score slack carry pending scheduled
      departures partials inactive funded horizon forkEpochs then
    let increment := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    let down := preset.downwardBand
    let ceiling := stakeCeiling preset config count scheduled pending carry inactive funded
      horizon forkEpochs
    let last := ceiling (horizon + 1)
    let exits := exitFlow preset config count scheduled horizon forkEpochs ceiling
    let consolidations := consolidationFlow preset config horizon forkEpochs ceiling
    let floor := windowFloor preset config stake slashed penalised count score slack carry pending
      scheduled departures partials inactive funded horizon forkEpochs
    let allowance := whistleblowerAllowance preset config count scheduled pending carry inactive
      horizon forkEpochs
    -- Dnew: the queue carry and the churn of each epoch from the ends of the queues.
    let queues := departureBudget preset config count scheduled pending carry inactive funded
      queued exitEnd consolidationEnd horizon forkEpochs
    let dep := queues + partials + departures
    -- D: the non-slashing penalties of the epochs `0` to `H`.
    let penalties := ((List.range (horizon + 1)).map fun t =>
      epochPenalty preset config score (ceiling t + penalised) (floor t) t).sum
    -- ρ: one increment per key whose effective balance may fall below its value at `x`.
    let paid := partials +
      (((List.range (horizon + 2)).filter (max exitEnd forkEpochs ≤ ·)).map exits).sum
    let grown := (last - stake + increment - 1) / increment
    let falling := min (finalCount preset stake count last)
      ((slack + penalties) / down + min (paid / down) (high + grown))
    let rounding := increment * falling
    -- act: activations, including the headroom of each key below the cap before the fork.
    let headroom := if 0 < forkEpochs then
      preset.MIN_ACTIVATION_BALANCE.toNat * count - stake else 0
    let act := pending + carry + ((List.range (horizon + 1)).map exits).sum + headroom
    -- cred: excess, due consolidation credits, Ω, issuance and new consolidation credits.
    let issuance := (((List.range (horizon + 1)).filter (forkEpochs ≤ ·)).map
      fun t => 2 * issuanceEnvelope preset (ceiling t)).sum
    let moved := (((List.range
      (horizon + 2 - config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)).filter
        (max consolidationEnd forkEpochs ≤ ·)).map consolidations).sum
    let cred := excess + credits + allowance + issuance + moved
    -- B: the boundary stake at the end of the window.
    let edge := boundary + 2 * max (exits horizon + consolidations horizon)
      (exits (horizon + 1) + consolidations (horizon + 1)) +
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
    2 * (dep + penalties + slack + rounding) + act + cred + 2 * edge
  else stake - slashed

/-! ## The observables of a reference state

Each observable is a number read at the reference state `x` of a branch.

It is a parameter of `aprioriDrift`, not a premise.
-/

/-- `W`: the active effective stake at `x`, slashed keys included. -/
private noncomputable def refStake (x : ForkedBeaconState preset) : Nat :=
  Models.stake (effectiveWeight x.state) (activeKeys x.state)

/-- `Z`: the active effective stake at `x` of the slashed keys. -/
private noncomputable def slashedActiveStake (x : ForkedBeaconState preset) : Nat :=
  refStake x - Models.stake (effectiveWeight x.state) (unslashedKeys x.state)

/-- `Y`: the effective stake of slashed, inactive keys that are not yet withdrawable. -/
private def slashedPenalisedStake (x : ForkedBeaconState preset) : Nat :=
  (x.state.validators.data.toList.map fun v =>
    if v.slashed && !isActiveValidator v (getCurrentEpoch x.state) &&
        decide (getCurrentEpoch x.state < v.withdrawableEpoch) then
      v.effectiveBalance.toNat else 0).sum

/-- `N`: the number of active keys at `x`. -/
private noncomputable def refCount (x : ForkedBeaconState preset) : Nat :=
  (activeKeys x.state).card

/-- `Nhi`: the number of active keys at `x` with more than `MIN_ACTIVATION_BALANCE` effective. -/
private noncomputable def highKeys (x : ForkedBeaconState preset) : Nat := by
  classical
  exact ((activeKeys x.state).filter fun key =>
    preset.MIN_ACTIVATION_BALANCE.toNat < effectiveWeight x.state key).card

/-- `σ`: the larger of the largest inactivity score and the bias times the finality delay.

Before Altair there is no score. -/
private def startScore (config : Config) (x : ForkedBeaconState preset) : Nat :=
  max (if altair : .altair ≤ x.fork then
      ((x.state.inactivityScores altair).data.toList.map (·.toNat)).foldr max 0 else 0)
    (config.INACTIVITY_SCORE_BIAS.toNat *
      ((getPreviousEpoch x.state).toNat - x.state.finalizedCheckpoint.epoch.toNat))

/-- `Λ`: the effective balance above the balance, summed over the active validators at `x`. -/
private def startSlack (x : ForkedBeaconState preset) : Nat :=
  ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
    effectiveAt x i.toNat - actualBalanceAt x i.toNat).sum

/-- `Pre`: the stake of validators that are neither active nor exited at `x`.

Each counts the larger of its effective balance and its balance up to its cap. -/
private def preActiveStake (x : ForkedBeaconState preset) : Nat :=
  (x.state.validators.data.toList.zipIdx.map fun (v, i) =>
    if !isActiveValidator v (getCurrentEpoch x.state) &&
        decide (getCurrentEpoch x.state < v.exitEpoch) then
      max (effectiveAt x i)
        (min (actualBalanceAt x i) (withdrawalMaxEffectiveBalance preset x.fork v).toNat)
    else 0).sum

/-- `Sx`: the number of validators whose activation epoch is set and after `x`. -/
private def scheduledCount (x : ForkedBeaconState preset) : Nat :=
  x.state.validators.data.toList.countP fun v =>
    decide (getCurrentEpoch x.state < v.activationEpoch) && v.activationEpoch != FAR_FUTURE_EPOCH

/-- `Sch`: the effective balance of active validators whose exit epoch is within the window. -/
private def scheduledDepartures (x : ForkedBeaconState preset) (horizon : Nat) : Nat :=
  (x.state.validators.data.toList.map fun v =>
    if isActiveValidator v (getCurrentEpoch x.state) &&
        decide (v.exitEpoch.toNat ≤ (getCurrentEpoch x.state).toNat + horizon + 1) then
      v.effectiveBalance.toNat else 0).sum

/-- `Πp`: the pending partial withdrawals that are withdrawable within the window.

Overdue entries count too, and there are none before Electra. -/
private def duePartials (x : ForkedBeaconState preset) (horizon : Nat) : Nat :=
  if electra : .pectra ≤ x.fork then
    ((x.state.pendingPartialWithdrawals electra).data.toList.map fun w =>
      if w.withdrawableEpoch.toNat ≤ (getCurrentEpoch x.state).toNat + horizon + 1 then
        w.amount.toNat else 0).sum
  else 0

/-- `Πc`: the credits of pending consolidations whose source is withdrawable within the window.

Each credit is the smaller of the balance and the effective balance of its source. -/
private def dueCredits (x : ForkedBeaconState preset) (horizon : Nat) : Nat :=
  if electra : .pectra ≤ x.fork then
    ((x.state.pendingConsolidations electra).data.toList.map fun c =>
      match x.state.validators.data[c.sourceIndex.toNat]? with
      | some v =>
        if v.withdrawableEpoch.toNat ≤ (getCurrentEpoch x.state).toNat + horizon + 1 then
          min (actualBalanceAt x c.sourceIndex.toNat) v.effectiveBalance.toNat else 0
      | none => 0).sum
  else 0

/-- `Bd`: the largest effective balance that exits in two adjacent epochs of the window. -/
private def boundaryLoad (x : ForkedBeaconState preset) (horizon : Nat) : Nat :=
  ((List.range (horizon + 1)).map fun t =>
    (x.state.validators.data.toList.map fun v =>
      if v.exitEpoch.toNat = (getCurrentEpoch x.state).toNat + t ∨
          v.exitEpoch.toNat = (getCurrentEpoch x.state).toNat + t + 1 then
        v.effectiveBalance.toNat else 0).sum).foldr max 0

/-- `nXS`: the number of unslashed validators that have exited but are not yet withdrawable. -/
private def slashableInactiveCount (x : ForkedBeaconState preset) : Nat :=
  x.state.validators.data.toList.countP fun v =>
    !v.slashed && decide (v.exitEpoch ≤ getCurrentEpoch x.state) &&
      decide (getCurrentEpoch x.state < v.withdrawableEpoch)

/-- The effective stake at `x` of the validators active at the previous epoch but not at `x`.

Slashed validators count too.

Their attestations of the previous epoch still pay proposers in the first epoch of a branch. -/
private def previousOnlyStake (x : ForkedBeaconState preset) : Nat :=
  (x.state.validators.data.toList.map fun v =>
    if isActiveValidator v (getPreviousEpoch x.state) &&
        !isActiveValidator v (getCurrentEpoch x.state) then
      v.effectiveBalance.toNat else 0).sum

/-- `H₁`: the epochs of the window before Electra, and zero from Electra on.

A state before Electra whose epoch has reached the fork epoch never upgrades.

The upgrade fires only at the boundary of that epoch.

`H₁ = 1` then fails the no-crossing clause of the guard, so the drift falls back to `W - Z`. -/
private def forkEpochs (config : Config) (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  if x.fork < .pectra then
    if (getCurrentEpoch x.state).toNat < config.ELECTRA_FORK_EPOCH.toNat then
      min (driftHorizon x high + 2)
        (config.ELECTRA_FORK_EPOCH.toNat - (getCurrentEpoch x.state).toNat)
    else 1
  else 0

/-- The guard of a branch from `x` through `high + 1`, with every observable read at `x`. -/
private noncomputable def aprioriGuardAt (config : Config) (x : ForkedBeaconState preset)
    (high : Nat) : Prop :=
  aprioriGuard preset config (refStake x) (slashedActiveStake x) (slashedPenalisedStake x)
    (refCount x) (startScore config x) (startSlack x) (fundingCarry x) (preActiveStake x)
    (scheduledCount x) (scheduledDepartures x (driftHorizon x high))
    (duePartials x (driftHorizon x high)) (slashableInactiveCount x)
    (fundedStake x + previousOnlyStake x) (driftHorizon x high) (forkEpochs config x high)

/-- The drift `f` of a branch from `x` through `high + 1`, with every observable read at `x`. -/
private noncomputable def aprioriDriftAt (config : Config) (x : ForkedBeaconState preset)
    (high : Nat) : Nat :=
  aprioriDrift preset config (refStake x) (slashedActiveStake x) (slashedPenalisedStake x)
    (refCount x) (highKeys x) (startScore config x) (startSlack x) (initialExcess x)
    (fundingCarry x) (preActiveStake x) (scheduledCount x)
    (scheduledDepartures x (driftHorizon x high)) (duePartials x (driftHorizon x high))
    (dueCredits x (driftHorizon x high))
    -- `eX` and `eC`: the start of each queue less the current epoch, zero before Electra.
    (exitQueueStart x - (getCurrentEpoch x.state).toNat)
    (consolidationQueueStart x - (getCurrentEpoch x.state).toNat)
    (queueCarry x high) (boundaryLoad x (driftHorizon x high)) (slashableInactiveCount x)
    (fundedStake x + previousOnlyStake x) (driftHorizon x high) (forkEpochs config x high)

/-! ## The departures of a branch

The departures that a branch charges in its window fit the budget `Dnew` of the drift.

This is the bound of `departure_charges_le_window_from` with the counts and rates of the drift.

Two facts of the window are hypotheses here, since the ceiling of the active stake gives them.

Before the fork each step of the window starts with at most `A_{H+1}` active validators.

From Electra each step of the window starts with a consolidation churn of at most `Cc`.
-/

/-- A tail splits after its last step that starts by epoch `high + 1`.

The second part starts after `high + 1`, so it charges only exits after `high + 1`. -/
private theorem window_cut {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (high : Nat) :
    ∃ (m : ForkedBeaconState preset) (cut : Run config checks x m) (rest : Run config checks m y),
      tail = cut.append rest ∧
      (∀ {u w : ForkedBeaconState preset} (step : Step config checks u w), cut.Contains step →
        (getCurrentEpoch u.state).toNat ≤ high + 1) ∧
      (∀ {u w : ForkedBeaconState preset} (step : Step config checks u w), rest.Contains step →
        high + 1 < (getCurrentEpoch u.state).toNat) ∧
      ∀ charge ∈ rest.departureCharges, high + 1 < charge.epoch := by
  induction tail with
  | nil => exact ⟨x, .nil, .nil, rfl, fun _ member => (by cases member),
      fun _ member => (by cases member),
      fun _ member => by simp [Run.departureCharges] at member⟩
  | @snoc b c pre step ih =>
    obtain ⟨m, cut, rest, rfl, inside, outside, later⟩ :=
      ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early)
    by_cases within : (getCurrentEpoch b.state).toNat ≤ high + 1
    · -- The tail so far starts by `high + 1` at its end, so its second part is empty.
      cases rest with
      | nil =>
        refine ⟨c, cut.snoc step, .nil, rfl, fun later member => ?_,
          fun _ member => (by cases member),
          fun _ member => by simp [Run.departureCharges] at member⟩
        cases member with
        | last => exact within
        | earlier member => exact inside later member
      | snoc rest last =>
        have after := outside last (.last _ _)
        have ordered := UInt64.le_iff_toNat_le.mp last.chainStep.currentEpoch_le
        omega
    · refine ⟨m, cut, rest.snoc step, rfl, inside, fun later member => ?_, fun charge member => ?_⟩
      · cases member with
        | last => omega
        | earlier member => exact outside later member
      · rcases List.mem_append.mp member with old | latest
        · exact later charge old
        · have lower := departureCharges_epoch_ge step early charge latest
          omega

/-- The departures that a branch charges in its window fit the budget `Dnew`.

The window runs from the current epoch of `x` to `high + 1`.

A branch from Electra is charged its queue carry and the Electra churn from each queue end.

A branch before Electra ends before the fork epoch, so it is charged only the count churn. -/
private theorem departures_le_budget {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (early : y.fork < .glamsterdam) (high : Nat) (guard : aprioriGuardAt config x high)
    (counted : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → (getCurrentEpoch u.state).toNat ≤ high + 1 → u.fork < .pectra →
        activeCount u.state ≤
          countPath config (refCount x + scheduledCount x) (driftHorizon x high + 1))
    (rates : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → (getCurrentEpoch u.state).toNat ≤ high + 1 → .pectra ≤ u.fork →
        ∀ rate : Gwei, getConsolidationChurnLimit config u.state = .ok rate →
        rate.toNat ≤ consolidationChurn preset config
          (stakeCeiling preset config (refCount x) (scheduledCount x) (preActiveStake x)
            (fundingCarry x) (slashableInactiveCount x) (fundedStake x + previousOnlyStake x)
            (driftHorizon x high) (forkEpochs config x high) (driftHorizon x high + 1))) :
    ((tail.departureCharges.filter fun c => c.epoch ≤ high + 1).map (·.amount)).sum ≤
      departureBudget preset config (refCount x) (scheduledCount x) (preActiveStake x)
        (fundingCarry x) (slashableInactiveCount x) (fundedStake x + previousOnlyStake x)
        (queueCarry x high)
        (exitQueueStart x - (getCurrentEpoch x.state).toNat)
        (consolidationQueueStart x - (getCurrentEpoch x.state).toNat)
        (driftHorizon x high) (forkEpochs config x high) := by
  -- D-Q reads only the steps of the window, and the steps after it charge later exits.
  obtain ⟨m, cut, rest, rfl, inside, -, later⟩ := window_cut tail early high
  have cutEarly : m.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) early
  have bound := departure_charges_le_window_from shared cut genesis caps cutEarly high _ _
    (fun step member => counted step ((Run.contains_append _ _ _).mpr (.inl member))
      (inside step member))
    (fun step member => rates step ((Run.contains_append _ _ _).mpr (.inl member))
      (inside step member))
  have after : ((rest.departureCharges.filter fun c => c.epoch ≤ high + 1).map
      (·.amount)).sum = 0 := by
    rw [List.filter_eq_nil_iff.mpr fun c member => by
      simpa using later c member]
    rfl
  rw [Run.departureCharges_append, List.filter_append, List.map_append, List.sum_append, after,
    Nat.add_zero]
  obtain ⟨-, -, minimum, -, -, -, -, -, -, -, -, -, crossing⟩ := guard
  -- The written-out carry of D-Q is `queueCarry`.
  change _ ≤ queueCarry x high + _ + _ + _ at bound
  simp only [departureBudget]
  generalize countPath config (refCount x + scheduledCount x) (driftHorizon x high + 1) = A
    at bound ⊢
  generalize consolidationChurn preset config (stakeCeiling preset config (refCount x)
    (scheduledCount x) (preActiveStake x) (fundingCarry x) (slashableInactiveCount x)
    (fundedStake x + previousOnlyStake x) (driftHorizon x high) (forkEpochs config x high)
    (driftHorizon x high + 1)) = Cc at bound ⊢
  have horizon : driftHorizon x high = high + 2 - (getCurrentEpoch x.state).toNat := rfl
  rw [horizon] at crossing ⊢
  by_cases electra : .pectra ≤ x.fork
  · -- From Electra the count term is off, and each churn counts from its queue end on.
    have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
    have zero : forkEpochs config x high = 0 := by simp [forkEpochs, notBefore]
    simp only [zero, lt_self_iff_false, ↓reduceIte, notBefore, Nat.mul_zero,
      Nat.add_zero] at bound ⊢
    have from_ (start : Nat) : high + 2 - max (getCurrentEpoch x.state).toNat
        (max start config.ELECTRA_FORK_EPOCH.toNat) ≤
          high + 2 - (getCurrentEpoch x.state).toNat + 2 -
            (start - (getCurrentEpoch x.state).toNat) := by omega
    have exitTerm := Nat.mul_le_mul_right
      config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat (from_ (exitQueueStart x))
    have consolidationTerm := Nat.mul_le_mul_right Cc (from_ (consolidationQueueStart x))
    omega
  · -- Before Electra the no-crossing clause puts the fork epoch after the window.
    have before : x.fork < .pectra := Nat.lt_of_not_ge electra
    have positive : 0 < forkEpochs config x high := by
      simp only [forkEpochs, before, ↓reduceIte, driftHorizon]
      split <;> omega
    have ends : high + 2 - (getCurrentEpoch x.state).toNat + 2 ≤ forkEpochs config x high :=
      crossing.resolve_left (Nat.ne_of_gt positive)
    have late : ¬ config.ELECTRA_FORK_EPOCH.toNat ≤ high + 1 := by
      simp only [forkEpochs, before, ↓reduceIte, driftHorizon] at ends
      split at ends <;> omega
    have starts : exitQueueStart x = (getCurrentEpoch x.state).toNat := by
      simp [exitQueueStart, electra]
    -- A positive minimum churn makes the floor of one in the count churn redundant.
    have floor : max 1 (cohortCap config A) = cohortCap config A :=
      Nat.max_eq_right (Nat.le_trans minimum (Nat.le_max_left _ _))
    have rate := Nat.mul_le_mul_left (cohortCap config A)
      (UInt64.le_iff_toNat_le.mp caps.activation)
    have empty (start : Nat) : high + 2 - max (getCurrentEpoch x.state).toNat
        (max start config.ELECTRA_FORK_EPOCH.toNat) = 0 := by omega
    simp only [before, ↓reduceIte, starts, Nat.max_self, Nat.add_zero, positive, floor,
      Nat.sub_self, empty, Nat.zero_mul] at bound ⊢
    have horizon := Nat.mul_le_mul
      (show high + 2 - (getCurrentEpoch x.state).toNat ≤
        high + 2 - (getCurrentEpoch x.state).toNat + 2 - 0 by omega)
      (show cohortCap config A * preset.MAX_EFFECTIVE_BALANCE.toNat ≤
        preset.MIN_ACTIVATION_BALANCE.toNat * cohortCap config A by
        rw [Nat.mul_comm preset.MIN_ACTIVATION_BALANCE.toNat]; exact rate)
    omega


/-! ## The count path before Electra -/

/-- The active validators at `x` are at most its active keys, since registry keys are distinct. -/
private theorem activeCount_le_refCount {g x : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (early : x.fork < .glamsterdam) : activeCount x.state ≤ refCount x := by
  have within := x.state.validators.bound early
  have inside : ∀ i ∈ getActiveValidatorIndices x.state (getCurrentEpoch x.state),
      i.toNat < x.state.validators.data.size := fun i member => by
    obtain ⟨v, found, _⟩ := (mem_getActiveValidatorIndices within).mp member
    exact (Array.getElem?_eq_some_iff.mp found).1
  have nodup : (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).Nodup :=
    (getActiveValidatorIndices_sorted within _).imp fun {a b} less (same : a = b) => by
      subst same; exact UInt64.lt_irrefl _ less
  rw [activeCount, refCount, activeKeys, Finset.card_eq_sum_ones,
    keys_sum x.state _ (shared.pubkeysDistinct genesis) inside fun _ => 1,
    ← List.toFinset_card_of_nodup nodup, Finset.card_eq_sum_ones]
  exact (Finset.sum_congr rfl fun i member => by
    simp [Array.getElem?_eq_getElem (inside i (List.mem_toFinset.mp member))]).ge

/-- Before Electra, the validators given an activation epoch in the window follow `A_t`.

They are counted at the end `z` of a run from `x`, without those already exited at `x`.

`A_t` is the count path from the active and scheduled validators at `x`, after `t` epochs. -/
private theorem windowActivations_le_countPath {g x z : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x z) (early : z.fork < .pectra) :
    ((Finset.range z.state.validators.data.size).filter fun i =>
      (z.state.validators.data[i]?).any (·.activationEpoch != FAR_FUTURE_EPOCH) &&
        (x.state.validators.data[i]?).all fun w => w.activationEpoch == FAR_FUTURE_EPOCH ||
          decide (getCurrentEpoch x.state < w.exitEpoch)).card ≤
      countPath config (refCount x + scheduledCount x)
        ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat) :=
  windowActivations_le tail early _ (Nat.add_le_add_right (activeCount_le_refCount shared genesis
    (Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) (Nat.lt_trans early (by decide))))
    _) fun _ => Nat.le_refl _


/-! ## The ceiling of the funding -/

/-- The funding at a state `y` of a branch from `v` is at most its start bound plus the churn.

The funding is the funded stake plus the deposit carry, and `start` bounds it at `v`.

Each epoch from `v` to `y` adds its deposit churn, and the replay adds its funding credits.

From an Electra `x`, `v` is `x` and `start` is `fundedStake x + fundingCarry x`. -/
private theorem funding_le_ceiling {g v y : ForkedBeaconState preset}
    (shared : Run config checks g v) (tail : Run config checks v y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events)
    {start : Nat} (funded : fundedStake v + fundingCarry v ≤ start) :
    fundedStake y + fundingCarry y ≤
      start + ((getCurrentEpoch y.state).toNat - (getCurrentEpoch v.state).toNat) *
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        (events.map fundingCredit).sum := by
  have bound := funding_run_bound (fun s => fundedStake s + fundingCarry s) (fun _ => 0)
    fundingCredit tail early high endEpoch events replayed (fun pre step early added ok => by
      simpa using funding_step_of_run (shared.append pre) genesis step early delay added ok)
  rw [show ∀ l : List (BalanceEvent preset), (l.map fun _ => 0).sum = 0 by simp,
    Nat.add_zero] at bound
  omega

/-! ## The participating balance of a rewards pass

The rewards pass at the end of epoch `t` reads the participants of epoch `t - 1`.

Each is active at `t - 1`, and its effective balance has not changed since an earlier state `u`.

So their balance is at most the effective stake at `u` of the keys active at `t - 1`.

For `t ≥ 1`, `u` is the output of the epoch transition that ends `t - 1`.

Its current epoch is still `t - 1`, so its funded stake counts every such key.

For `t = 0`, `u` is the start `x` of the branch.

The keys active at the epoch before `x` but not at `x` are then counted by `previousOnlyStake x`.
-/

/-- The participants of the previous epoch weigh at most the stake at `u` of its active keys.

The pass must keep the activity of `u` at that epoch, and its effective balances. -/
private theorem participating_le_reference {f h : Fork} {u : BeaconState preset f}
    {pass : BeaconState preset h} (early : f < .glamsterdam) (altair : .altair ≤ h)
    (active : ActiveKept (getPreviousEpoch pass) u pass)
    (effective : ∀ i, i < u.validators.data.size →
      effectiveAt ⟨h, pass⟩ i = effectiveAt ⟨f, u⟩ i)
    {flag : UInt64} {participating : List ValidatorIndex} {balance : Gwei}
    (flagged : getUnslashedParticipatingIndices pass altair flag (getPreviousEpoch pass) =
      .ok participating)
    (weighed : getTotalBalance pass participating = .ok balance) :
    balance.toNat ≤ max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (∑ i ∈ (getActiveValidatorIndices u (getPreviousEpoch pass)).toFinset,
        effectiveAt ⟨f, u⟩ i.toNat) := by
  obtain ⟨-, -, total⟩ := getTotalBalance_ok_iff_stake.mp weighed
  rw [total]
  refine max_le_max_left _ ?_
  have same := active.getActiveValidatorIndices_eq (UInt64.le_refl _)
  -- Each participant is active at `u`, so it is inside the registry of `u`.
  have among (i : ValidatorIndex) (member : i ∈ participating.toFinset) :
      i ∈ (getActiveValidatorIndices u (getPreviousEpoch pass)).toFinset := by
    have chosen := (mem_getUnslashedParticipatingIndices flagged i
      (List.mem_toFinset.mp member)).1
    rw [same] at chosen
    exact List.mem_toFinset.mpr chosen
  calc Models.stake (fun i => balanceAt pass i.toNat) participating.toFinset
      = ∑ i ∈ participating.toFinset, effectiveAt ⟨f, u⟩ i.toNat := by
        refine Finset.sum_congr rfl fun i member => ?_
        obtain ⟨v, found, _⟩ := (mem_getActiveValidatorIndices (u.validators.bound early)).mp
          (List.mem_toFinset.mp (among i member))
        exact effective i.toNat (Array.getElem?_eq_some_iff.mp found).1
    _ ≤ _ := Finset.sum_le_sum_of_subset among

/-- The effective balances of the active validators of a state sum to at most its funded stake.

The keys of the registry must be distinct. -/
private theorem activeEffective_le_funded (x : ForkedBeaconState preset)
    (early : x.fork < .glamsterdam) (unique : PubkeysDistinct x.state) :
    ∑ i ∈ (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset,
      effectiveAt x i.toNat ≤ fundedStake x := by
  have inside : ∀ i ∈ getActiveValidatorIndices x.state (getCurrentEpoch x.state),
      i.toNat < x.state.validators.data.size := fun i member => by
    obtain ⟨v, found, _⟩ := (mem_getActiveValidatorIndices (x.state.validators.bound early)).mp
      member
    exact (Array.getElem?_eq_some_iff.mp found).1
  have bound := funding_active_le x early unique
  rw [activeKeys, keys_weight _ _ unique inside] at bound
  exact bound

/-- A run inside one epoch, then the stages of the next slot up to the rewards pass.

They keep the activity of the start `r`, its effective balances and its current epoch. -/
private theorem pass_kept {r s : ForkedBeaconState preset} (inner : Run config checks r s)
    (electra : .pectra ≤ r.fork) (early : s.fork < .glamsterdam)
    (same : getCurrentEpoch s.state = getCurrentEpoch r.state)
    {cached just pass : BeaconState preset s.fork} (cachedOk : processSlot s.state = .ok cached)
    (justified : EpochStage.Edge config checks .justification cached just)
    (scored : EpochStage.Edge config checks .inactivity just pass) :
    ActiveKept (activityFixedEpoch r.state) r.state pass ∧
      (∀ i, i < r.state.validators.data.size →
        effectiveAt ⟨s.fork, pass⟩ i = effectiveAt r i) ∧
      getCurrentEpoch pass = getCurrentEpoch r.state := by
  -- The stages before the rewards keep the validators and the slot.
  have one := justified.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have two := scored.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  have validators : pass.validators = s.state.validators := two.1.trans one.1
  have slot : pass.slot = s.state.slot := two.2.2.2.2.trans one.2.2.2.2
  refine ⟨(activeKept_of_chainSteps inner.chainSteps).trans fun _ _ _ => by
      simp only [isActiveAt, validators], fun i inside => ?_, ?_⟩
  · rw [← run_same_epoch_effective inner electra early same i inside]
    simp only [effectiveAt, validators]
  · rw [← same]
    simp only [getCurrentEpoch, slot]

/-- At the rewards pass of an epoch `t ≥ 1`, each flag's participants weigh at most the funding.

That is the funding at the last state `z` of epoch `t - 1`, one epoch of churn and the credits.

The credits are the funding credits of the slot from `z`, whose epoch transition ends `t - 1`.

The run from the next state `w` to `s` stays inside epoch `t`.

The pass follows the stages of the next slot from `s` before the rewards. -/
private theorem participating_le_ceiling {g z w s : ForkedBeaconState preset}
    (shared : Run config checks g z) (genesis : Genesis (config := config) (checks := checks) g)
    (boundary : advanceSlotAcross config checks z = .ok w)
    (crossing : getCurrentEpoch z.state < getCurrentEpoch w.state)
    (inner : Run config checks w s) (same : getCurrentEpoch s.state = getCurrentEpoch w.state)
    (electra : .pectra ≤ z.fork) (early : s.fork < .glamsterdam)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.slot boundary).balanceEvents = .ok events)
    {cached just pass : BeaconState preset s.fork} (cachedOk : processSlot s.state = .ok cached)
    (justified : EpochStage.Edge config checks .justification cached just)
    (scored : EpochStage.Edge config checks .inactivity just pass) (altair : .altair ≤ s.fork)
    {flag : UInt64} {participating : List ValidatorIndex} {balance : Gwei}
    (flagged : getUnslashedParticipatingIndices pass altair flag (getPreviousEpoch pass) =
      .ok participating)
    (weighed : getTotalBalance pass participating = .ok balance) :
    balance.toNat ≤ max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (fundedStake z + fundingCarry z + config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        (events.map fundingCredit).sum) := by
  have wEarly : w.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps inner.chainSteps) early
  have zEarly : z.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Step.slot boundary).chainStep.fork_le wEarly
  have wElectra : .pectra ≤ w.fork := Nat.le_trans electra (Step.slot boundary).chainStep.fork_le
  obtain ⟨advanced, advanceOk, upgrades⟩ := bind_ok_iff.mp boundary
  have advanceCopy := advanceOk
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at advanceCopy
  obtain ⟨next, nextOk, cachedZ, cachedZOk, e, epochOk, advancedEq⟩ := advanceCopy
  have sum := (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp (liftAccessor_ok.mp nextOk))).2
  simp only [UInt64.toNat_one] at sum
  have wSlot : w.state.slot = next := by rw [processUpgrades_slot upgrades, ← advancedEq]
  have registry : w.state.validators.data = e.validators.data := by
    rw [processUpgrades_validators_of_electra (s := ⟨z.fork, advanced⟩) electra wEarly upgrades,
      ← advancedEq]
  obtain ⟨_, _, _, _, cachedZEq⟩ := processSlot_ok cachedZOk
  -- The slot from `z` ends epoch `t - 1`, so it runs the epoch transition.
  have last : next % preset.SLOTS_PER_EPOCH = 0 := by
    by_contra inside
    have epochs := nextSlot_epoch_of_inside sum inside
    have later := UInt64.lt_iff_toNat_lt.mp crossing
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, wSlot] at later
    omega
  have epochs := nextSlot_epoch_of_boundary sum last
  simp only [epochIfLast, last, ↓reduceIte] at epochOk
  obtain ⟨_, justifiedZ, frame⟩ := processEpoch_frame epochOk
  have eSlot : e.slot = z.state.slot := by
    rw [frame.slot, (EpochStage.Edge.records (config := config) (checks := checks)
      (stage := .justification) justifiedZ ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩).2.2.2.2,
      cachedZEq]
  obtain ⟨activeKept, effectiveKept, passEpoch⟩ := pass_kept inner wElectra early same cachedOk
    justified scored
  -- The previous epoch of the pass is the current epoch of `e`.
  have previous : getPreviousEpoch pass = getCurrentEpoch e := by
    apply UInt64.toNat_inj.mp
    have passValue := getPreviousEpoch_toNat pass
    have wValue := getCurrentEpoch_toNat w.state
    have eValue := getCurrentEpoch_toNat e
    rw [passEpoch] at passValue
    rw [wSlot] at wValue
    rw [eSlot] at eValue
    omega
  have toE : ActiveKept (getPreviousEpoch pass) e pass := fun epoch le position => by
    have bound : epoch ≤ activityFixedEpoch w.state := UInt64.le_trans le (UInt64.le_trans
      (passEpoch ▸ getPreviousEpoch_le pass) (getCurrentEpoch_le_activityFixedEpoch _))
    rw [activeKept epoch bound position]
    simp only [isActiveAt, registry]
  have unique : PubkeysDistinct e := by
    have distinct := (shared.snoc (.slot boundary)).pubkeysDistinct genesis
    unfold PubkeysDistinct validatorKeys at distinct ⊢
    rwa [registry] at distinct
  have bound := participating_le_reference zEarly altair toE (fun i inside => by
      rw [effectiveKept i (by rw [registry]; exact inside)]
      simp only [effectiveAt, registry]) flagged weighed
  rw [previous] at bound
  have active : ∑ i ∈ (getActiveValidatorIndices e (getCurrentEpoch e)).toFinset,
      effectiveAt ⟨z.fork, e⟩ i.toNat ≤ fundedStake ⟨z.fork, e⟩ :=
    activeEffective_le_funded ⟨z.fork, e⟩ zEarly unique
  -- The epoch transition raises the funding by one epoch of churn and its credits.
  have holds := (run_justified_separated shared genesis).1
  obtain ⟨middle, -, epochEvents, epochReplay, -⟩ :=
    epochBalanceReplay_result cachedZ e zEarly epochOk
  have funded := funding_epoch zEarly delay
    ((frame_processSlot cachedZOk).balancesMatch holds.balancesMatch)
    ((frame_processSlot cachedZOk).exitsOrdered holds.exitsOrdered)
    (by rw [cachedZEq]; exact shared.activationExitOrder genesis)
    (by rw [cachedZEq]; exact fun witness =>
      shared.pendingConsolidation_invariant genesis zEarly witness (by omega))
    epochOk epochEvents epochReplay
  obtain ⟨crossings, crossingOk, _⟩ := upgradeBalanceReplay_bounded upgrades
  have split := Step.balanceEvents_epoch_slot boundary cachedZOk nextOk last epochReplay
    advanceOk crossingOk
  obtain rfl := Except.ok.inj (replayed.symm.trans split)
  have startFunded : fundedStake ⟨z.fork, cachedZ⟩ = fundedStake z := by rw [cachedZEq]; rfl
  have startCarry : fundingCarry ⟨z.fork, cachedZ⟩ = fundingCarry z := by rw [cachedZEq]; rfl
  rw [startFunded, startCarry] at funded
  rw [List.map_append, List.sum_append]
  refine bound.trans (max_le_max_left _ ?_)
  omega

/-- At the first rewards pass of a branch from `x`, each flag's participants weigh at most a sum.

It is the funded stake of `x` and the stake at `x` of the keys active only at the epoch before.

The run from `x` to `s` stays inside the epoch of `x`.

The pass follows the stages of the next slot from `s` before the rewards. -/
private theorem participating_le_start {g x s : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (inner : Run config checks x s) (same : getCurrentEpoch s.state = getCurrentEpoch x.state)
    (electra : .pectra ≤ x.fork) (early : s.fork < .glamsterdam)
    {cached just pass : BeaconState preset s.fork} (cachedOk : processSlot s.state = .ok cached)
    (justified : EpochStage.Edge config checks .justification cached just)
    (scored : EpochStage.Edge config checks .inactivity just pass) (altair : .altair ≤ s.fork)
    {flag : UInt64} {participating : List ValidatorIndex} {balance : Gwei}
    (flagged : getUnslashedParticipatingIndices pass altair flag (getPreviousEpoch pass) =
      .ok participating)
    (weighed : getTotalBalance pass participating = .ok balance) :
    balance.toNat ≤ max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (fundedStake x + previousOnlyStake x) := by
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps inner.chainSteps) early
  have within := x.state.validators.bound xEarly
  obtain ⟨activeKept, effectiveKept, passEpoch⟩ := pass_kept inner electra early same cachedOk
    justified scored
  have previous : getPreviousEpoch pass = getPreviousEpoch x.state := by
    apply UInt64.toNat_inj.mp
    rw [getPreviousEpoch_toNat, getPreviousEpoch_toNat, passEpoch]
  have kept : ActiveKept (getPreviousEpoch pass) x.state pass :=
    activeKept.mono (UInt64.le_trans (passEpoch ▸ getPreviousEpoch_le pass)
      (getCurrentEpoch_le_activityFixedEpoch _))
  have bound := participating_le_reference xEarly altair kept effectiveKept flagged weighed
  rw [previous] at bound
  refine bound.trans (max_le_max_left _ ?_)
  change ∑ i ∈ (getActiveValidatorIndices x.state (getPreviousEpoch x.state)).toFinset,
    effectiveAt x i.toNat ≤ _
  -- Split the keys of the previous epoch by whether they are still active at `x`.
  set current := (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset
  set before := (getActiveValidatorIndices x.state (getPreviousEpoch x.state)).toFinset
  rw [← Finset.sum_filter_add_sum_filter_not before (· ∈ current)]
  have stillActive : ∑ i ∈ before.filter (· ∈ current), effectiveAt x i.toNat ≤
      ∑ i ∈ current, effectiveAt x i.toNat :=
    Finset.sum_le_sum_of_subset fun i member => (Finset.mem_filter.mp member).2
  have funded : ∑ i ∈ current, effectiveAt x i.toNat ≤ fundedStake x :=
    activeEffective_le_funded x xEarly (shared.pubkeysDistinct genesis)
  -- The others are the keys that `previousOnlyStake` counts.
  have leaving : ∑ i ∈ before.filter (· ∉ current), effectiveAt x i.toNat ≤
      previousOnlyStake x := by
    let weight (v : Validator) : Nat :=
      if isActiveValidator v (getPreviousEpoch x.state) &&
          !isActiveValidator v (getCurrentEpoch x.state) then v.effectiveBalance.toNat else 0
    have sum := funding_sum_zipIdx x.state.validators.data.toList fun v _ => weight v
    have shape : (x.state.validators.data.toList.zipIdx.map fun (v, _) => weight v) =
        x.state.validators.data.toList.map weight := by
      have first := congrArg (List.map weight)
        (List.zipIdx_map_fst 0 x.state.validators.data.toList)
      rw [List.map_map] at first
      rw [← first]
      exact List.map_congr_left fun ⟨_, _⟩ _ => rfl
    rw [shape] at sum
    unfold previousOnlyStake
    change _ ≤ (x.state.validators.data.toList.map weight).sum
    rw [sum]
    simp only [Array.length_toList, Array.getElem?_toList]
    apply Finset.sum_le_sum_of_injOn (fun i => i.toNat)
    · intro i _ j _ eq
      exact UInt64.toNat_inj.mp eq
    · intro i member
      obtain ⟨j, chosen, rfl⟩ := Finset.mem_image.mp member
      obtain ⟨v, found, _⟩ := (mem_getActiveValidatorIndices within).mp
        (List.mem_toFinset.mp (Finset.mem_filter.mp chosen).1)
      exact Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1
    · intro i member
      obtain ⟨inPrevious, notCurrent⟩ := Finset.mem_filter.mp member
      obtain ⟨v, found, activePrevious⟩ := (mem_getActiveValidatorIndices within).mp
        (List.mem_toFinset.mp inPrevious)
      have inactive : isActiveValidator v (getCurrentEpoch x.state) = false := by
        by_contra activeNow
        exact notCurrent (List.mem_toFinset.mpr ((mem_getActiveValidatorIndices within).mpr
          ⟨v, found, by simpa using activeNow⟩))
      simp [weight, found, effectiveAt, activePrevious, inactive]
    · intro _ _ _
      exact Nat.zero_le _
  omega

/-! ## The proposer and sync credits of one epoch

From Altair, an attestation pays its proposer for each flag that it newly sets.

Each flag of one validator and one epoch is set at most once, since no step clears it.

So the proposer credits of an epoch are bounded by a potential over two sets of keys.

The keys active at the previous epoch of a start `r`, and those active at its current epoch.

Each key weighs its base reward times the weights of the flags it holds.

A missing entry counts as every flag set, so that no step can lower the potential.

An attestation raises it by at least its numerator, which is `448` times its proposer credit.

Every other step keeps or raises it, and it never exceeds `54` times the base rewards.

The sync aggregate of each block pays at most the issuance envelope over `28` per slot.

A slot holds at most one block, so an epoch pays at most the envelope over `28` for sync.
-/

/-- The weights of the flags that are set. -/
private def flagWeight (flags : ParticipationFlags) : Nat :=
  ((List.finRange PARTICIPATION_FLAG_WEIGHTS.length).map fun flag =>
    if hasFlag flags flag.val.toUInt64 then PARTICIPATION_FLAG_WEIGHTS[flag].toNat else 0).sum

/-- The weight of an entry of the flags, with a missing entry counted as every flag set. -/
private def entryWeight (entry : Option ParticipationFlags) : Nat :=
  (entry.map flagWeight).getD 54

/-- The flag potential of a state: the weighted flags of the two sets of keys.

Each key counts its base reward, in the flags of the previous epoch or of the current one. -/
private def flagPotential (previous current : Finset ValidatorIndex) (base : ValidatorIndex → Nat)
    (u : ForkedBeaconState preset) : Nat :=
  if altair : .altair ≤ u.fork then
    ∑ i ∈ previous,
        entryWeight ((u.state.previousEpochParticipation altair).data[i.toNat]?) * base i +
      ∑ i ∈ current,
        entryWeight ((u.state.currentEpochParticipation altair).data[i.toNat]?) * base i
  else 0

/-- The credit limits of the events of one source. -/
private def sourceCredits (source : BalanceSource) (events : List (BalanceEvent preset)) : Nat :=
  (events.map fun e => if e.source = source then e.creditLimit else 0).sum

private theorem sourceCredits_append (source : BalanceSource)
    (first second : List (BalanceEvent preset)) :
    sourceCredits source (first ++ second) =
      sourceCredits source first + sourceCredits source second := by
  simp [sourceCredits]

private theorem finRange_flags :
    List.finRange PARTICIPATION_FLAG_WEIGHTS.length =
      [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩] := rfl

private theorem flagWeights_sum :
    PARTICIPATION_FLAG_WEIGHTS[(⟨0, by decide⟩ : Fin PARTICIPATION_FLAG_WEIGHTS.length)].toNat +
      PARTICIPATION_FLAG_WEIGHTS[(⟨1, by decide⟩ : Fin PARTICIPATION_FLAG_WEIGHTS.length)].toNat +
      PARTICIPATION_FLAG_WEIGHTS[(⟨2, by decide⟩ : Fin PARTICIPATION_FLAG_WEIGHTS.length)].toNat =
      54 := rfl

/-- An entry weighs at most `54`, the sum of the weights. -/
private theorem entryWeight_le (entry : Option ParticipationFlags) : entryWeight entry ≤ 54 := by
  cases entry with
  | none => exact Nat.le_refl _
  | some flags =>
    have weights := flagWeights_sum
    simp only [entryWeight, Option.map_some, Option.getD_some, flagWeight, finRange_flags,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    split <;> split <;> split <;> omega

/-- Setting the earned flags raises the weight by the weights of the newly set ones. -/
private theorem flagWeight_set {old new : ParticipationFlags} {earned : List UInt64}
    (set : ∀ flag : Fin PARTICIPATION_FLAG_WEIGHTS.length, hasFlag new flag.val.toUInt64 =
      (hasFlag old flag.val.toUInt64 || decide (flag.val.toUInt64 ∈ earned))) (base : Nat) :
    flagWeight new * base = flagWeight old * base +
      ((List.finRange PARTICIPATION_FLAG_WEIGHTS.length).map fun flag =>
        if flag.val.toUInt64 ∈ earned ∧ hasFlag old flag.val.toUInt64 = false then
          base * PARTICIPATION_FLAG_WEIGHTS[flag].toNat else 0).sum := by
  -- Each flag adds its weight once set, and it is newly set when earned and not held before.
  have term (held : Bool) (earnedFlag : Prop) [Decidable earnedFlag] (weight : Nat) :
      (if (held || decide earnedFlag) = true then weight else 0) * base =
        (if held = true then weight else 0) * base +
          (if earnedFlag ∧ held = false then base * weight else 0) := by
    cases held <;> by_cases chosen : earnedFlag <;> simp [chosen, Nat.mul_comm]
  have zero := set ⟨0, by decide⟩
  have one := set ⟨1, by decide⟩
  have two := set ⟨2, by decide⟩
  simp only [flagWeight, finRange_flags, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero, Nat.add_mul]
  rw [zero, one, two, term, term, term]
  ring

/-- The flags of one attester after its flags are set in turn: its flags, and every earned one. -/
private theorem foldlM_addFlagReward_hasFlag {f : Fork} {s : BeaconState preset f}
    {total : Gwei} {earned : List UInt64} {index : ValidatorIndex} :
    ∀ {flagList : List (Fin PARTICIPATION_FLAG_WEIGHTS.length)} {flags flags' : ParticipationFlags}
      {numerator numerator' : Gwei},
      flagList.foldlM (addFlagReward s total earned index) (flags, numerator) =
        .ok (flags', numerator') →
      ∀ flag, hasFlag flags' flag.val.toUInt64 =
        (hasFlag flags flag.val.toUInt64 || decide (flag ∈ flagList ∧ flag.val.toUInt64 ∈ earned))
  | [], flags, flags', numerator, numerator', computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨rfl, rfl⟩ := computed
    intro flag
    simp
  | added :: flagList, flags, flags', numerator, numerator', computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨⟨middleFlags, middle⟩, stepped, folded⟩ := computed
    have rest := foldlM_addFlagReward_hasFlag folded
    -- One step sets at most its own flag, and only when the attestation earns it.
    have step : ∀ flag, hasFlag middleFlags flag.val.toUInt64 =
        (hasFlag flags flag.val.toUInt64 ||
          decide (flag = added ∧ added.val.toUInt64 ∈ earned)) := by
      intro flag
      simp only [addFlagReward] at stepped
      split at stepped
      · rename_i newly
        simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq,
          Prod.mk.injEq] at stepped
        obtain ⟨_, _, _, _, _, _, rfl, _⟩ := stepped
        by_cases same : flag = added
        · subst same
          simp [hasFlag_addFlag, newly.1]
        · rw [hasFlag_addFlag_of_ne flags same]
          simp [same]
      · rename_i old
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at stepped
        obtain ⟨rfl, _⟩ := stepped
        by_cases same : flag = added
        · subst same
          by_cases earnedFlag : flag.val.toUInt64 ∈ earned
          · have set : hasFlag flags flag.val.toUInt64 = true := by
              by_contra unset
              exact old ⟨earnedFlag, by simpa using unset⟩
            simp [set]
          · simp [earnedFlag]
        · simp [same]
    intro flag
    rw [rest flag, step flag]
    by_cases same : flag = added
    · subst same
      cases hasFlag flags flag.val.toUInt64 <;> simp
    · simp [same]

/-- After the flags of some attesters are set, each attester holds its flags and the earned ones.

Each attester must be named once. -/
private theorem foldlM_addAttesterFlags_hasFlag {f : Fork} {s : BeaconState preset f}
    {total : Gwei} {earned : List UInt64} :
    ∀ {attesters : List ValidatorIndex} {participation : EpochParticipation preset f}
      {numerator : Gwei} {result : EpochParticipation preset f × Gwei},
      (attesters.map UInt64.toNat).Nodup →
      attesters.foldlM (addAttesterFlags s total earned) (participation, numerator) =
        .ok result →
      ∀ attester ∈ attesters, ∃ old new, participation.data[attester.toNat]? = some old ∧
        result.1.data[attester.toNat]? = some new ∧
        ∀ flag : Fin PARTICIPATION_FLAG_WEIGHTS.length, hasFlag new flag.val.toUInt64 =
          (hasFlag old flag.val.toUInt64 || decide (flag.val.toUInt64 ∈ earned))
  | [], _, _, _, _, _ => fun _ absent => absurd absent List.not_mem_nil
  | first :: rest, participation, numerator, result, distinct, computed => by
    rw [List.map_cons, List.nodup_cons] at distinct
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨⟨middle, middleNumerator⟩, stepped, folded⟩ := computed
    have later := foldlM_addAttesterFlags_hasFlag distinct.2 folded
    have kept := (foldlM_addAttesterFlags distinct.2 folded).1
    unfold addAttesterFlags at stepped
    dsimp only at stepped
    split at stepped
    · rename_i inside
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at stepped
      obtain ⟨⟨flags, raised⟩, loop, written, rfl⟩ := stepped
      have flagsSet := foldlM_addFlagReward_hasFlag loop
      have other : ∀ i, first.toNat ≠ i → middle.data[i]? = participation.data[i]? := by
        intro i different
        rw [← written]
        simp [different]
      intro attester member
      rcases List.mem_cons.mp member with rfl | member
      · refine ⟨participation.data[attester.toNat], flags, Array.getElem?_eq_getElem inside,
          ?_, fun flag => ?_⟩
        · rw [kept attester.toNat fun later member same => distinct.1 (same ▸
            List.mem_map_of_mem member), ← written]
          simp
        · rw [flagsSet flag]
          simp [List.mem_finRange]
      · obtain ⟨old, new, found, result, flagsOk⟩ := later attester member
        refine ⟨old, new, ?_, result, flagsOk⟩
        rw [← other attester.toNat fun same => distinct.1 (same ▸ List.mem_map_of_mem member)]
        exact found
    · cases stepped

/-- Setting the flags of some attesters raises the weighted flags of a set of keys.

The rise is at least the numerator of the attestation.

The keys must hold every attester.

Each base reward that the attestation reads must be at most the key's own. -/
private theorem participation_gain {f : Fork} {s : BeaconState preset f} {total : Gwei}
    {earned : List UInt64} {attesters : List ValidatorIndex}
    {participation : EpochParticipation preset f} {result : EpochParticipation preset f × Gwei}
    (distinct : (attesters.map UInt64.toNat).Nodup)
    (computed : attesters.foldlM (addAttesterFlags s total earned) (participation, 0) =
      .ok result)
    (keys : Finset ValidatorIndex) (base : ValidatorIndex → Nat)
    (among : ∀ a ∈ attesters, a ∈ keys)
    (based : ∀ a ∈ attesters, ∀ reward, getBaseReward s total a = .ok reward →
      reward.toNat ≤ base a) :
    ∑ i ∈ keys, entryWeight (participation.data[i.toNat]?) * base i + result.2.toNat ≤
      ∑ i ∈ keys, entryWeight (result.1.data[i.toNat]?) * base i := by
  classical
  obtain ⟨keptOthers, shares, named, facts, sum⟩ := foldlM_addAttesterFlags distinct computed
  have flagsAfter := foldlM_addAttesterFlags_hasFlag distinct computed
  -- The weights of the flags that the attestation sets for one attester.
  let gain (a : ValidatorIndex) : Nat :=
    ((List.finRange PARTICIPATION_FLAG_WEIGHTS.length).map fun flag =>
      if flag.val.toUInt64 ∈ earned ∧
          hasFlag ((participation.data[a.toNat]?).getD 0) flag.val.toUInt64 = false then
        base a * PARTICIPATION_FLAG_WEIGHTS[flag].toNat else 0).sum
  -- The numerator reads a base reward only for a newly set flag, so it is at most the gain.
  have shared : result.2.toNat ≤ ∑ a ∈ attesters.toFinset, gain a := by
    rw [sum, List.sum_toFinset _ (List.Nodup.of_map _ distinct), ← named, List.map_map]
    simp only [UInt64.toNat_zero, Nat.zero_add]
    apply List.sum_le_sum
    intro share member
    obtain ⟨found, reads⟩ := facts share member
    have inside : share.1 ∈ attesters := named ▸ List.mem_map_of_mem member
    simp only [Function.comp, gain, found, Option.getD_some, newFlagsNumerator]
    apply List.sum_le_sum
    intro flag _
    split_ifs with newly
    · exact Nat.mul_le_mul_right _ (based share.1 inside _ (reads flag newly.1 newly.2))
    · exact Nat.le_refl _
  -- Each attester gains exactly its newly set flags, and every other key keeps its entry.
  have each (i : ValidatorIndex) : entryWeight (participation.data[i.toNat]?) * base i +
      (if i ∈ attesters.toFinset then gain i else 0) ≤
      entryWeight (result.1.data[i.toNat]?) * base i := by
    split_ifs with chosen
    · obtain ⟨old, new, found, after, set⟩ := flagsAfter i (List.mem_toFinset.mp chosen)
      simp only [entryWeight, found, after, Option.map_some, Option.getD_some, gain]
      rw [flagWeight_set set]
    · rw [keptOthers i.toNat fun a member same =>
        chosen (List.mem_toFinset.mpr (UInt64.toNat_inj.mp same ▸ member)), Nat.add_zero]
  calc ∑ i ∈ keys, entryWeight (participation.data[i.toNat]?) * base i + result.2.toNat
      ≤ ∑ i ∈ keys, entryWeight (participation.data[i.toNat]?) * base i +
          ∑ i ∈ keys, (if i ∈ attesters.toFinset then gain i else 0) := by
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr fun a member =>
          among a (List.mem_toFinset.mp member)]
        exact Nat.add_le_add_left shared _
    _ = ∑ i ∈ keys, (entryWeight (participation.data[i.toNat]?) * base i +
          (if i ∈ attesters.toFinset then gain i else 0)) := Finset.sum_add_distrib.symm
    _ ≤ _ := Finset.sum_le_sum fun i _ => each i

/-- An attestation raises the flag potential by at least `448` times its proposer credit.

Its attesters are active at its target, the previous or the current epoch of its state.

So they lie in the sets of keys, if those hold the active keys of the two epochs. -/
private theorem attestation_flagPotential {f : Fork} {u u' : BeaconState preset f}
    (early : f < .glamsterdam) (altair : .altair ≤ f)
    {att : Attestation preset f} {parent : Slot} {credit : Nat}
    (ok : processAttestation config checks u parent att = .ok u')
    (credited : attestationCredit u att parent = .ok credit)
    {previous current : Finset ValidatorIndex} {base : ValidatorIndex → Nat}
    (previousActive : ∀ i ∈ getActiveValidatorIndices u (getPreviousEpoch u), i ∈ previous)
    (currentActive : ∀ i ∈ getActiveValidatorIndices u (getCurrentEpoch u), i ∈ current)
    (based : ∀ total i reward, i ∈ previous ∨ i ∈ current →
      getTotalActiveBalance u = .ok total → getBaseReward u total i = .ok reward →
      reward.toNat ≤ base i) :
    flagPotential previous current base ⟨f, u⟩ + 448 * credit ≤
      flagPotential previous current base ⟨f, u'⟩ := by
  rw [processAttestation_of_altair altair] at ok
  simp only [processAttestationAltair, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, recent, _, slotEpoch, _, _, _, _, _, _, _, _, earned, earnedOk, _, _, _, _, _, _,
    total, totalOk, attesters, attestersOk, pair, flagsOk, proposer, _, raisedState, raised,
    final⟩ := ok
  rw [ensure_ok_iff] at recent slotEpoch
  have notGloas : ¬ .glamsterdam ≤ f := Nat.not_le_of_lt early
  simp only [notGloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at final
  subst final
  -- The credit is the numerator over `448`, rounding down.
  have value : attestationCredit u att parent = .ok (pair.2 /
      ((WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR / PROPOSER_WEIGHT)).toNat := by
    simp only [attestationCredit, altair, ↓reduceDIte, liftAccessor, earnedOk, totalOk,
      attestersOk, Except.mapError, bind, Except.bind, flagsOk]
    rfl
  obtain rfl := Except.ok.inj (credited.symm.trans value)
  have scaled : 448 * (pair.2 /
      ((WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR / PROPOSER_WEIGHT)).toNat ≤
      pair.2.toNat := by
    rw [UInt64.toNat_div, show ((WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR /
      PROPOSER_WEIGHT : UInt64).toNat = 448 from rfl, Nat.mul_comm]
    exact Nat.div_mul_le_self _ _
  obtain ⟨_, set⟩ := increaseBalance_ok raised
  obtain ⟨_, rfl⟩ := setBalance_ok set
  have distinct := getAttestingIndices_nodup attestersOk
  -- Each attester is in a committee of the target, so it is active at the target.
  have active (a : ValidatorIndex) (member : a ∈ attesters) :
      a ∈ getActiveValidatorIndices u att.data.target.epoch := by
    obtain ⟨_, _, _, committeeOk, inCommittee⟩ :=
      exists_mem_getBeaconCommittee_of_getAttestingIndices attestersOk member
    rw [slotEpoch]
    exact mem_getActiveValidatorIndices_of_getBeaconCommittee committeeOk inCommittee
  have reads (keys : Finset ValidatorIndex) (inKeys : ∀ a ∈ attesters, a ∈ keys)
      (side : ∀ a ∈ keys, a ∈ previous ∨ a ∈ current) :
      ∀ a ∈ attesters, ∀ reward, getBaseReward u total a = .ok reward → reward.toNat ≤ base a :=
    fun a member reward rewardOk => based total a reward (side a (inKeys a member)) totalOk rewardOk
  simp only [flagPotential, altair, ↓reduceDIte, BeaconState.putBalance]
  by_cases chosen : (att.data.target.epoch == getCurrentEpoch u) = true
  · -- The attestation sets flags of the current epoch.
    have target : att.data.target.epoch = getCurrentEpoch u := beq_iff_eq.mp chosen
    simp only [chosen, ↓reduceIte] at flagsOk
    have inKeys (a : ValidatorIndex) (member : a ∈ attesters) : a ∈ current :=
      currentActive a (target ▸ active a member)
    have gain := participation_gain distinct flagsOk current base inKeys
      (reads current inKeys fun _ member => .inr member)
    simp only [setEpochParticipation, chosen, ↓reduceIte]
    omega
  · -- The attestation sets flags of the previous epoch.
    have target : att.data.target.epoch = getPreviousEpoch u :=
      recent.resolve_right fun same => chosen (beq_iff_eq.mpr same)
    simp only [chosen, Bool.false_eq_true, ↓reduceIte] at flagsOk
    have inKeys (a : ValidatorIndex) (member : a ∈ attesters) : a ∈ previous :=
      previousActive a (target ▸ active a member)
    have gain := participation_gain distinct flagsOk previous base inKeys
      (reads previous inKeys fun _ member => .inl member)
    simp only [setEpochParticipation, chosen, Bool.false_eq_true, ↓reduceIte]
    omega


/-- A step that keeps or zeroes each byte of flags keeps or raises the flag potential.

The keys must be inside the registry before the step, where no byte is zeroed. -/
private theorem flagPotential_le_of_flags {f : Fork} {a b : BeaconState preset f}
    (flags : FlagsKeptOrZero a b) {previous current : Finset ValidatorIndex}
    {base : ValidatorIndex → Nat} (inside : ∀ i ∈ previous ∪ current,
      i.toNat < a.validators.data.size) :
    flagPotential previous current base ⟨f, a⟩ ≤ flagPotential previous current base ⟨f, b⟩ := by
  simp only [flagPotential]
  split
  · rename_i altair
    -- An entry kept by the step weighs as before, and a missing one weighs the most.
    have entry {before after : Option ParticipationFlags} (position : Nat)
        (small : position < a.validators.data.size)
        (read : ∀ value, after = some value →
          before = some value ∨ value = 0 ∧ a.validators.data.size ≤ position) :
        entryWeight before ≤ entryWeight after := by
      cases found : after with
      | none => exact entryWeight_le _
      | some value =>
        rcases read value found with same | ⟨_, late⟩
        · rw [same]
        · omega
    apply Nat.add_le_add
    · exact Finset.sum_le_sum fun i member => Nat.mul_le_mul_right _
        (entry i.toNat (inside i (Finset.mem_union_left _ member))
          fun value => (flags altair i.toNat value).1)
    · exact Finset.sum_le_sum fun i member => Nat.mul_le_mul_right _
        (entry i.toNat (inside i (Finset.mem_union_right _ member))
          fun value => (flags altair i.toNat value).2)
  · exact Nat.le_refl _

/-- The facts that a replay of a block keeps, from the start `b` of the block.

The potential rises by `448` times the proposer credits, and no sync credit is recorded yet.

The registry does not shrink. -/
private def BlockKept {f : Fork} (b : BeaconState preset f)
    (previous current : Finset ValidatorIndex)
    (base : ValidatorIndex → Nat) (pre : BalanceReplay preset f) : Prop :=
  flagPotential previous current base ⟨f, b⟩ + 448 * sourceCredits .rewards pre.2 ≤
      flagPotential previous current base ⟨f, pre.1⟩ ∧
    sourceCredits .sync pre.2 = 0 ∧ b.validators.data.size ≤ pre.1.validators.data.size

/-- A replayed step that forms a block frame and records neither reward nor sync credit. -/
private theorem BlockKept.step {f : Fork} {b : BeaconState preset f}
    {previous current : Finset ValidatorIndex} {base : ValidatorIndex → Nat}
    (inside : ∀ i ∈ previous ∪ current, i.toNat < b.validators.data.size)
    {pre : BalanceReplay preset f} {u : BeaconState preset f} {added : List (BalanceEvent preset)}
    (held : BlockKept b previous current base pre) (frame : BlockFrame pre.1 u)
    (quiet : sourceCredits .rewards added = 0) (silent : sourceCredits .sync added = 0) :
    BlockKept b previous current base (u, pre.2 ++ added) := by
  have raised := flagPotential_le_of_flags (base := base) frame.flags
    fun i member => Nat.lt_of_lt_of_le (inside i member) held.2.2
  refine ⟨?_, ?_, held.2.2.trans frame.registryGrows⟩
  · simp only [sourceCredits_append, quiet, Nat.add_zero]
    exact held.1.trans raised
  · simp only [sourceCredits_append, silent, held.2.1]

private theorem BlockKept.carry {f : Fork} {b : BeaconState preset f}
    {previous current : Finset ValidatorIndex} {base : ValidatorIndex → Nat}
    (inside : ∀ i ∈ previous ∪ current, i.toNat < b.validators.data.size)
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    (frame : ∀ x y, action x = .ok y → BlockFrame x y) {pre post : BalanceReplay preset f}
    (ok : carryBalance action pre = .ok post) (held : BlockKept b previous current base pre) :
    BlockKept b previous current base post := by
  simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨u, computed, rfl⟩ := ok
  have kept := held.step inside (frame _ _ computed) (added := []) rfl rfl
  rwa [List.append_nil] at kept

private theorem BlockKept.record {f : Fork} {b : BeaconState preset f}
    {previous current : Finset ValidatorIndex} {base : ValidatorIndex → Nat}
    (inside : ∀ i ∈ previous ∪ current, i.toNat < b.validators.data.size)
    {source : BalanceSource}
    {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    (frame : ∀ x y, action x = .ok y → BlockFrame x y) {pre post : BalanceReplay preset f}
    (ok : recordBalance source limits action pre = .ok post)
    (other : source ≠ .rewards ∧ source ≠ .sync)
    (held : BlockKept b previous current base pre) : BlockKept b previous current base post := by
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, u, computed, rfl⟩ := ok
  exact held.step inside (frame _ _ computed) (by simp [sourceCredits, other.1])
    (by simp [sourceCredits, other.2])

private theorem BlockKept.fold {f : Fork} {b : BeaconState preset f}
    {previous current : Finset ValidatorIndex} {base : ValidatorIndex → Nat} {α : Type}
    {step : BalanceReplay preset f → α → Except TransitionError (BalanceReplay preset f)}
    (kept : ∀ pre x post, step pre x = .ok post → BlockKept b previous current base pre →
      BlockKept b previous current base post)
    {items : List α} {pre post : BalanceReplay preset f} (ok : items.foldlM step pre = .ok post)
    (held : BlockKept b previous current base pre) : BlockKept b previous current base post :=
  foldlM_ok_invariant (BlockKept b previous current base) (fun _ _ _ prior computed =>
    kept _ _ _ computed prior) held ok

/-- The steps of a block before its attestations keep the effective balances and the activity. -/
private def SiteKept {f : Fork} (b : BeaconState preset f) (pre : BalanceReplay preset f) : Prop :=
  EffectiveKept b pre.1 ∧ ActiveStep b pre.1 ∧ b.validators.data.size ≤ pre.1.validators.data.size

/-- A step of a block that keeps the effective balances and the activity, and is a block frame. -/
private def SiteStep {f : Fork} (x y : BeaconState preset f) : Prop :=
  BlockFrame x y ∧ EffectiveKept x y ∧ ActiveStep x y

private theorem SiteKept.step {f : Fork} {b : BeaconState preset f}
    {pre : BalanceReplay preset f} {u : BeaconState preset f} (held : SiteKept b pre)
    (effective : EffectiveKept pre.1 u) (active : ActiveStep pre.1 u)
    (grows : pre.1.validators.data.size ≤ u.validators.data.size)
    (added : List (BalanceEvent preset)) : SiteKept b (u, added) :=
  ⟨effectiveKept_trans held.1 effective held.2.2, held.2.1.trans active, held.2.2.trans grows⟩

private theorem SiteKept.carry {f : Fork} {b : BeaconState preset f}
    {previous current : Finset ValidatorIndex} {base : ValidatorIndex → Nat}
    (inside : ∀ i ∈ previous ∪ current, i.toNat < b.validators.data.size)
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    (step : ∀ x y, action x = .ok y → SiteStep x y) {pre post : BalanceReplay preset f}
    (ok : carryBalance action pre = .ok post)
    (held : BlockKept b previous current base pre ∧ SiteKept b pre) :
    BlockKept b previous current base post ∧ SiteKept b post := by
  refine ⟨held.1.carry inside (fun x y computed => (step x y computed).1) ok, ?_⟩
  simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨u, computed, rfl⟩ := ok
  have kept := step _ _ computed
  exact held.2.step kept.2.1 kept.2.2 kept.1.registryGrows _

private theorem SiteKept.record {f : Fork} {b : BeaconState preset f}
    {previous current : Finset ValidatorIndex} {base : ValidatorIndex → Nat}
    (inside : ∀ i ∈ previous ∪ current, i.toNat < b.validators.data.size)
    {source : BalanceSource}
    {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    (step : ∀ x y, action x = .ok y → SiteStep x y) {pre post : BalanceReplay preset f}
    (ok : recordBalance source limits action pre = .ok post)
    (other : source ≠ .rewards ∧ source ≠ .sync)
    (held : BlockKept b previous current base pre ∧ SiteKept b pre) :
    BlockKept b previous current base post ∧ SiteKept b post := by
  refine ⟨held.1.record inside (fun x y computed => (step x y computed).1) ok other, ?_⟩
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, u, computed, rfl⟩ := ok
  have kept := step _ _ computed
  exact held.2.step kept.2.1 kept.2.2 kept.1.registryGrows _

/-- The replay of one block raises the flag potential by `448` times its proposer credits.

Its sync credit, times `28` per slot of an epoch, is at most the issuance envelope of the total.

That total is the one after the block, which the sync aggregate reads.

Each attestation must raise the potential, at every state that keeps the start of the block. -/
private theorem block_credits_le {f : Fork} {b t : BeaconState preset f}
    (early : f < .glamsterdam) (electra : .pectra ≤ f)
    {engine : ExecutionEngine preset f} {block : BeaconBlock preset f}
    {events : List (BalanceEvent preset)}
    (replay : blockBalanceReplay (config := config) (checks := checks) early engine b block =
      .ok (t, events))
    {previous current : Finset ValidatorIndex} {base : ValidatorIndex → Nat}
    (inside : ∀ i ∈ previous ∪ current, i.toNat < b.validators.data.size)
    (attest : ∀ {u u' : BeaconState preset f} {att : Attestation preset f} {credit : Nat},
      EffectiveKept b u → ActiveStep b u →
      processAttestation config checks u b.latestBlockHeader.slot att = .ok u' →
      attestationCredit u att b.latestBlockHeader.slot = .ok credit →
      flagPotential previous current base ⟨f, u⟩ + 448 * credit ≤
        flagPotential previous current base ⟨f, u'⟩)
    {total : Gwei} (totalEnd : getTotalActiveBalance t = .ok total) :
    flagPotential previous current base ⟨f, b⟩ + 448 * sourceCredits .rewards events ≤
        flagPotential previous current base ⟨f, t⟩ ∧
      sourceCredits .sync events * (28 * preset.SLOTS_PER_EPOCH.toNat) ≤
        issuanceEnvelope preset total.toNat ∧ 0 < preset.SLOTS_PER_EPOCH.toNat := by
  have bellatrix : .bellatrix ≤ f := Nat.le_trans (by decide) electra
  have altair : .altair ≤ f := Nat.le_trans (by decide) electra
  simp only [blockBalanceReplay, bellatrix, electra, altair, ↓reduceDIte, bind_ok_iff,
    ensure_ok_iff] at replay
  obtain ⟨headed, headedOk, executed, executedOk, revealed, revealedOk, voted, votedOk, _, _, _,
    _, proposed, proposedOk, slashed, slashedOk, attested, attestedOk, deposited, depositedOk,
    exited, exitedOk, changed, changedOk, requested, requestedOk, withdrawn, withdrawnOk,
    consolidated, consolidatedOk, syncOk⟩ := replay
  have start : BlockKept b previous current base (b, []) ∧ SiteKept b (b, []) :=
    ⟨⟨by simp [sourceCredits], rfl, Nat.le_refl _⟩, effectiveKept_refl _, .refl _, Nat.le_refl _⟩
  -- The steps before the attestations keep the effective balances and the activity.
  have one := SiteKept.carry inside (fun _ _ ok => ⟨frame_processBlockHeader ok,
    effectiveKept_data (by obtain ⟨_, _, same⟩ := processBlockHeader_eq ok; rw [same]),
    activeStep_processBlockHeader ok⟩) headedOk start
  have two := SiteKept.record inside (fun _ _ ok =>
    ⟨frame_processBlockExecution ok,
      effectiveKept_data (congrArg (·.data) (processBlockExecution_validators ok)),
      activeStep_processBlockExecution ok⟩) executedOk ⟨by decide, by decide⟩ one
  have three := SiteKept.carry inside (fun _ _ ok => ⟨frame_processRandao ok,
    effectiveKept_data (by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, same⟩ := processRandao_eq ok
      rw [same]), activeStep_processRandao ok⟩) revealedOk two
  have four := SiteKept.carry inside (fun _ _ ok => ⟨frame_processEth1Data ok,
    by obtain ⟨_, _, rest⟩ := processEth1Data_eq ok
       exact effectiveKept_data (congrArg (·.validators.data) rest),
    activeStep_processEth1Data ok⟩) votedOk three
  have five := foldlM_ok_invariant
    (fun pre => BlockKept b previous current base pre ∧ SiteKept b pre)
    (fun _ _ _ prior computed => SiteKept.record inside (fun _ _ ok =>
      ⟨frame_processProposerSlashing ok, effectiveKept_proposerSlashing ok,
        activeStep_processProposerSlashing ok⟩) computed ⟨by decide, by decide⟩ prior)
    four proposedOk
  have six := foldlM_ok_invariant
    (fun pre => BlockKept b previous current base pre ∧ SiteKept b pre)
    (fun _ _ _ prior computed => SiteKept.record inside (fun _ _ ok =>
      ⟨frame_processAttesterSlashing ok, effectiveKept_attesterSlashing ok,
        activeStep_processAttesterSlashing ok⟩) computed ⟨by decide, by decide⟩ prior)
    five slashedOk
  -- Each attestation raises the potential by `448` times the credit that it records.
  have seven := foldlM_ok_invariant
    (fun pre => BlockKept b previous current base pre ∧ SiteKept b pre)
    (fun pre _ _ prior computed => by
      simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
      obtain ⟨⟨credit, debit⟩, limitsOk, u, processed, rfl⟩ := computed
      obtain ⟨_, creditOk, rfl, rfl⟩ := limitsOk
      have raised := attest prior.2.1 prior.2.2.1 processed creditOk
      have before := prior.1.1
      refine ⟨⟨?_, ?_, prior.1.2.2.trans (frame_processAttestation processed).registryGrows⟩,
        prior.2.step (effectiveKept_data (by rw [(processAttestation_registry processed).1]))
          (activeStep_processAttestation processed)
          (frame_processAttestation processed).registryGrows _⟩
      · simp only [sourceCredits_append] at before ⊢
        simp only [sourceCredits, List.map_cons, List.map_nil, ↓reduceIte, List.sum_cons,
          List.sum_nil, Nat.add_zero] at before ⊢
        omega
      · simp only [sourceCredits_append, prior.1.2.1]
        simp [sourceCredits]) six attestedOk
  -- The steps after the attestations are block frames that record no credit of either kind.
  have eight := BlockKept.fold (fun _ _ _ computed prior => prior.record inside
    (fun _ _ ok => frame_processDeposit ok) computed ⟨by decide, by decide⟩) depositedOk seven.1
  have nine := BlockKept.carry inside (fun _ _ ok => by
    rw [← Array.foldlM_toList] at ok
    exact BlockFrame.foldlM (fun _ _ _ h => frame_processVoluntaryExit h) ok) exitedOk eight
  have ten := BlockKept.carry inside (fun _ _ ok => by
    unfold processBlsToExecutionChanges at ok
    split at ok
    · rw [← Array.foldlM_toList] at ok
      exact BlockFrame.foldlM (fun _ _ _ h => frame_processBlsToExecutionChange h) ok
    · cases ok
      exact .refl _) changedOk nine
  have eleven := BlockKept.carry inside (fun _ _ ok => by
    rw [← Array.foldlM_toList] at ok
    exact BlockFrame.foldlM (fun _ _ _ h => frame_processDepositRequest h) ok) requestedOk ten
  have twelve := BlockKept.carry inside (fun _ _ ok => by
    rw [← Array.foldlM_toList] at ok
    exact BlockFrame.foldlM (fun _ _ _ h => frame_processWithdrawalRequest h) ok)
    withdrawnOk eleven
  have thirteen := BlockKept.fold (fun _ _ _ computed prior => prior.record inside
    (fun _ _ ok => frame_processConsolidationRequest ok) computed ⟨by decide, by decide⟩)
    consolidatedOk twelve
  -- The sync aggregate changes only the balances, and records the one sync credit.
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq] at syncOk
  obtain ⟨⟨credit, debit⟩, limitsOk, u, synced, rfl, rfl⟩ := syncOk
  obtain ⟨balances, rfl⟩ := processSyncAggregate_eq synced
  obtain ⟨reward, rewardOk, proposer, proposerOk, rfl, rfl⟩ := limitsOk
  simp only [liftAccessor_ok, liftArith, mapError_ok_iff, bind_ok_iff, mulChecked_ok_iff,
    divChecked_ok_iff] at proposerOk
  obtain ⟨scaled, ⟨_, scaledValue⟩, _, proposerValue⟩ := proposerOk
  have share : proposer.toNat * 7 ≤ reward.toNat := by
    rw [proposerValue, scaledValue, show PROPOSER_WEIGHT.toNat = 8 from rfl,
      show (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT).toNat = 56 from rfl]
    omega
  obtain ⟨bound, positive⟩ := syncCredit_le rewardOk share totalEnd
  refine ⟨?_, ?_, positive⟩
  · calc _ = flagPotential previous current base ⟨f, b⟩ +
          448 * sourceCredits .rewards consolidated.2 := by
          simp [sourceCredits]
      _ ≤ flagPotential previous current base ⟨f, consolidated.1⟩ := thirteen.1
      _ = _ := rfl
  · simp only [sourceCredits_append, thirteen.2.1, Nat.zero_add]
    simpa [sourceCredits] using bound

/-- A step of a run inside an epoch from Electra raises the flag potential by its proposer credits.

The potential reads the keys active at the previous and the current epoch of the start `r`.

Each key weighs its base reward at the total of `r`.

A slot step records no credit and moves the slot on, keeping the slot of the latest header.

A block step stays at its slot, after the slot of the latest header, and makes that header its own.

Its sync credit, times `28` per slot of an epoch, is at most the issuance envelope of the total. -/
private theorem step_credits {r m l : ForkedBeaconState preset} (pre : Run config checks r m)
    (step : Step config checks m l) (electra : .pectra ≤ r.fork) (early : l.fork < .glamsterdam)
    (same : getCurrentEpoch l.state = getCurrentEpoch r.state)
    {total perIncrement : Gwei} (totalOk : getTotalActiveBalance r.state = .ok total)
    (per : getBaseRewardPerIncrement preset total = .ok perIncrement)
    {previous current : Finset ValidatorIndex} {base : ValidatorIndex → Nat}
    (previousEq :
      previous = (getActiveValidatorIndices r.state (getPreviousEpoch r.state)).toFinset)
    (currentEq : current = (getActiveValidatorIndices r.state (getCurrentEpoch r.state)).toFinset)
    (baseEq : ∀ i, base i =
      effectiveAt r i.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * perIncrement.toNat)
    {added : List (BalanceEvent preset)} (addedOk : step.balanceEvents = .ok added) :
    flagPotential previous current base m + 448 * sourceCredits .rewards added ≤
        flagPotential previous current base l ∧
      ((sourceCredits .sync added = 0 ∧ l.state.slot.toNat = m.state.slot.toNat + 1 ∧
          l.state.latestBlockHeader.slot = m.state.latestBlockHeader.slot) ∨
        (sourceCredits .sync added * (28 * preset.SLOTS_PER_EPOCH.toNat) ≤
            issuanceEnvelope preset total.toNat ∧ 0 < preset.SLOTS_PER_EPOCH.toNat ∧
          l.state.slot = m.state.slot ∧
          m.state.latestBlockHeader.slot.toNat < m.state.slot.toNat ∧
          l.state.latestBlockHeader.slot = l.state.slot)) := by
  have mEarly : m.fork < .glamsterdam := Nat.lt_of_le_of_lt step.chainStep.fork_le early
  have rEarly : r.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps pre.chainSteps) mEarly
  have mElectra : .pectra ≤ m.fork := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
  have mEpoch : getCurrentEpoch m.state = getCurrentEpoch r.state :=
    UInt64.le_antisymm (same ▸ step.chainStep.currentEpoch_le)
      (currentEpoch_le_of_chainSteps pre.chainSteps)
  cases step with
  | slot ok =>
    obtain ⟨advanced, advanceOk, upgrades⟩ := bind_ok_iff.mp ok
    have advanceCopy := advanceOk
    simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at advanceCopy
    obtain ⟨next, nextOk, cached, cachedOk, epoched, epochOk, advancedEq⟩ := advanceCopy
    have sum := (Uint64.addChecked_ok_iff.mp
      (mapError_ok_iff.mp (liftAccessor_ok.mp nextOk))).2
    simp only [UInt64.toNat_one] at sum
    have lSlot : l.state.slot = next := by rw [processUpgrades_slot upgrades, ← advancedEq]
    -- The slot stays inside the epoch, so it runs no epoch transition and no upgrade.
    have notLast : ¬ next % preset.SLOTS_PER_EPOCH = 0 := by
      intro last
      have epochs := nextSlot_epoch_of_boundary sum last
      have equal := congrArg UInt64.toNat (same.trans mEpoch.symm)
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, lSlot] at equal
      omega
    simp only [epochIfLast, notLast, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochOk
    subst epochOk
    have due : upgradeDue config ⟨m.fork, advanced⟩ = false := by
      simp [upgradeDue, ← advancedEq, notLast]
    have kept : l = ⟨m.fork, advanced⟩ := by
      unfold processUpgrades at upgrades
      simp only [due, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at upgrades
      exact upgrades.symm
    have none : added = [] := by
      have crossings : upgradeBalanceReplay (config := config) (checks := checks)
          ⟨m.fork, advanced⟩ = .ok [] := by
        unfold upgradeBalanceReplay
        simp [due, pure, Except.pure]
      simp only [Step.balanceEvents, cachedOk, nextOk, notLast, ↓reduceIte, advanceOk,
        crossings, bind, Except.bind, pure, Except.pure, List.append_nil,
        Except.ok.injEq] at addedOk
      exact addedOk.symm
    subst kept none
    obtain ⟨root, _, header⟩ := advanceSlot_latestBlockHeader advanceOk
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    refine ⟨Nat.le_of_eq ?_, .inl ⟨by simp [sourceCredits], by rw [← advancedEq]; exact sum,
      by rw [header]; split <;> rfl⟩⟩
    simp only [sourceCredits, List.map_nil, List.sum_nil, Nat.mul_zero, Nat.add_zero]
    rw [← advancedEq]
    rfl
  | @block f before after engine signed due ok =>
    have altair : .altair ≤ f := Nat.le_trans (by decide) mElectra
    have processed := (applySignedBlock_ok ok).2.1
    have replay := Step.balanceEvents_block mEarly addedOk
    have within := r.state.validators.bound rEarly
    -- The block starts with the effective balances, the activity and the total of `r`.
    have effective := run_same_epoch_effective pre electra mEarly mEpoch
    have activeR := activeKept_of_chainSteps pre.chainSteps
    have sizeR := registryGrows_of_chainSteps pre.chainSteps
    have totalBefore : getTotalActiveBalance before = .ok total :=
      (total_active_congr rEarly mEarly
        (activeR.mono (getCurrentEpoch_le_activityFixedEpoch _)) mEpoch effective).trans totalOk
    have afterSlot := (frame_processBlock processed).slot
    have totalAfter : getTotalActiveBalance after = .ok total :=
      (total_active_congr mEarly mEarly ((activeKept_processBlock processed).mono
        (getCurrentEpoch_le_activityFixedEpoch _)) (by simp only [getCurrentEpoch, afterSlot])
        (effectiveKept_processBlock processed)).trans totalBefore
    have insideR : ∀ i ∈ previous ∪ current, i.toNat < r.state.validators.data.size := by
      intro i member
      rw [previousEq, currentEq] at member
      rcases Finset.mem_union.mp member with chosen | chosen <;>
      · obtain ⟨_, found, _⟩ := (mem_getActiveValidatorIndices within).mp
          (List.mem_toFinset.mp chosen)
        exact (Array.getElem?_eq_some_iff.mp found).1
    -- An attestation of the block reads the same activity, balances and total as `r`.
    have attest {u u' : BeaconState preset f} {att : Attestation preset f} {credit : Nat}
        (siteEffective : EffectiveKept before u) (siteActive : ActiveStep before u)
        (attested : processAttestation config checks u before.latestBlockHeader.slot att =
          .ok u')
        (credited : attestationCredit u att before.latestBlockHeader.slot = .ok credit) :
        flagPotential previous current base ⟨f, u⟩ + 448 * credit ≤
          flagPotential previous current base ⟨f, u'⟩ := by
      have uEpoch : getCurrentEpoch u = getCurrentEpoch r.state := by
        rw [← mEpoch]
        simp only [getCurrentEpoch, siteActive.1]
      have reads (epoch : Epoch) (low : epoch ≤ getCurrentEpoch r.state) :
          getActiveValidatorIndices u epoch = getActiveValidatorIndices r.state epoch := by
        rw [siteActive.2.getActiveValidatorIndices_eq (UInt64.le_trans low
            (mEpoch ▸ getCurrentEpoch_le_activityFixedEpoch before)),
          activeR.getActiveValidatorIndices_eq
            (UInt64.le_trans low (getCurrentEpoch_le_activityFixedEpoch _))]
      have previousSame : getPreviousEpoch u = getPreviousEpoch r.state := by
        simp only [getPreviousEpoch, uEpoch]
      have siteTotal : getTotalActiveBalance u = .ok total :=
        (total_active_congr mEarly mEarly
          (siteActive.2.mono (getCurrentEpoch_le_activityFixedEpoch _))
          (by simp only [getCurrentEpoch, siteActive.1]) siteEffective).trans totalBefore
      refine attestation_flagPotential mEarly altair attested credited
        (fun i member => by
          rw [previousSame, reads _ (getPreviousEpoch_le _)] at member
          exact previousEq ▸ List.mem_toFinset.mpr member)
        (fun i member => by
          rw [uEpoch, reads _ (UInt64.le_refl _)] at member
          exact currentEq ▸ List.mem_toFinset.mpr member)
        (fun total' i reward member totalU rewardOk => ?_)
      obtain rfl := Except.ok.inj (totalU.symm.trans siteTotal)
      obtain ⟨v, found, value⟩ := getBaseReward_eq_mul_of_altair altair per rewardOk
      have small := insideR i (Finset.mem_union.mpr member)
      have read : v.effectiveBalance.toNat = effectiveAt r i.toNat := by
        rw [← effective i.toNat small, ← siteEffective i.toNat (Nat.lt_of_lt_of_le small sizeR)]
        simp [effectiveAt, found]
      rw [value, read, baseEq]
    obtain ⟨potential, sync, positive⟩ := block_credits_le mEarly mElectra replay
      (fun i member => Nat.lt_of_lt_of_le (insideR i member) sizeR) attest totalAfter
    obtain ⟨atSlot, newer, -⟩ := processBlock_parentRoot processed
    obtain ⟨_, -, header⟩ := latestBlockHeader_processBlock processed
    exact ⟨potential, .inr ⟨sync, positive, afterSlot, atSlot ▸ UInt64.lt_iff_toNat_lt.mp newer,
      by rw [header, afterSlot, atSlot]⟩⟩

/-- The flag potential is at most `54` times the base rewards of the two sets of keys. -/
private theorem flagPotential_le (previous current : Finset ValidatorIndex)
    (base : ValidatorIndex → Nat) (u : ForkedBeaconState preset) :
    flagPotential previous current base u ≤
      54 * (∑ i ∈ previous, base i + ∑ i ∈ current, base i) := by
  simp only [flagPotential]
  split
  · rw [Nat.mul_add, Finset.mul_sum, Finset.mul_sum]
    exact Nat.add_le_add
      (Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (entryWeight_le _))
      (Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (entryWeight_le _))
  · exact Nat.zero_le _

/-- The proposer and sync credits of the blocks of a run inside one epoch, from Electra.

The proposer credits, times `448`, are at most `54` base rewards per increment for each increment.

The increments are those of the effective stakes at the start `r` of two sets of keys.

The sets are the keys active at the previous epoch of `r`, and those active at its current epoch.

The sync credits, times `28`, are at most the issuance envelope of the total active balance of `r`.

A slot holds at most one block, so the epoch has at most `SLOTS_PER_EPOCH` of them. -/
private theorem epoch_credits_le {r s : ForkedBeaconState preset} (inner : Run config checks r s)
    (electra : .pectra ≤ r.fork) (early : s.fork < .glamsterdam)
    (same : getCurrentEpoch s.state = getCurrentEpoch r.state)
    {total perIncrement : Gwei} (totalOk : getTotalActiveBalance r.state = .ok total)
    (per : getBaseRewardPerIncrement preset total = .ok perIncrement)
    (high : Nat) {events : List (BalanceEvent preset)}
    (replayed : inner.balanceEvents high = .ok events) :
    sourceCredits .rewards events * 448 ≤ 54 * perIncrement.toNat *
      ((∑ i ∈ (getActiveValidatorIndices r.state (getPreviousEpoch r.state)).toFinset,
          effectiveAt r i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
        (∑ i ∈ (getActiveValidatorIndices r.state (getCurrentEpoch r.state)).toFinset,
          effectiveAt r i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ∧
      sourceCredits .sync events * 28 ≤ issuanceEnvelope preset total.toNat := by
  set previous := (getActiveValidatorIndices r.state (getPreviousEpoch r.state)).toFinset
  set current := (getActiveValidatorIndices r.state (getCurrentEpoch r.state)).toFinset
  let base (i : ValidatorIndex) : Nat :=
    effectiveAt r i.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * perIncrement.toNat
  -- The potential rises by the proposer credits, and the blocks are at most one per slot.
  have key : ∀ {u : ForkedBeaconState preset} (tail : Run config checks r u),
      u.fork < .glamsterdam → getCurrentEpoch u.state = getCurrentEpoch r.state →
      ∀ found, tail.balanceEvents high = .ok found →
      flagPotential previous current base r + 448 * sourceCredits .rewards found ≤
          flagPotential previous current base u ∧
        ∃ count, sourceCredits .sync found * (28 * preset.SLOTS_PER_EPOCH.toNat) ≤
            count * issuanceEnvelope preset total.toNat ∧
          count + r.state.slot.toNat ≤ u.state.slot.toNat + 1 ∧
          (count + r.state.slot.toNat = u.state.slot.toNat + 1 →
            u.state.latestBlockHeader.slot.toNat = u.state.slot.toNat) ∧
          (sourceCredits .sync found = 0 ∨ 0 < preset.SLOTS_PER_EPOCH.toNat) := by
    intro u tail
    induction tail with
    | nil =>
      intro _ _ found ok
      cases ok
      exact ⟨by simp [sourceCredits], 0, by simp [sourceCredits], by omega, by omega,
        .inl (by simp [sourceCredits])⟩
    | @snoc m l pre step ih =>
      intro lEarly lEpoch found ok
      have mEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le lEarly
      have mEpoch : getCurrentEpoch m.state = getCurrentEpoch r.state :=
        UInt64.le_antisymm (lEpoch ▸ step.chainStep.currentEpoch_le)
          (currentEpoch_le_of_chainSteps pre.chainSteps)
      simp only [Run.balanceEvents, bind_ok_iff] at ok
      obtain ⟨prior, priorOk, rest⟩ := ok
      obtain ⟨potential, count, sync, counted, full, positive⟩ := ih mEarly mEpoch prior priorOk
      obtain ⟨added, addedOk⟩ := step.balanceEvents_ok lEarly
      obtain ⟨raised, kind⟩ := step_credits pre step electra lEarly lEpoch totalOk per
        (previous := previous) (current := current) (base := base) rfl rfl (fun _ => rfl) addedOk
      -- The step's events count only if it starts by `high + 1`.
      have events : ∃ taken, found = prior ++ taken ∧
          (taken = [] ∨ taken = added) := by
        split at rest
        · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, addedOk] at rest
          obtain ⟨_, rfl, rfl⟩ := rest
          exact ⟨added, rfl, .inr rfl⟩
        · cases rest
          exact ⟨[], (List.append_nil _).symm, .inl rfl⟩
      obtain ⟨taken, rfl, choice⟩ := events
      have bounded : sourceCredits .rewards taken ≤ sourceCredits .rewards added ∧
          sourceCredits .sync taken ≤ sourceCredits .sync added := by
        rcases choice with rfl | rfl
        · simp [sourceCredits]
        · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
      simp only [sourceCredits_append]
      refine ⟨by omega, ?_⟩
      rcases kind with ⟨silent, slot, header⟩ | ⟨blockSync, slotsPositive, slot, newer, header⟩
      · have none : sourceCredits .sync taken = 0 := by omega
        refine ⟨count, by rw [none, Nat.add_zero]; exact sync, by omega, by omega, ?_⟩
        rcases positive with zero | holds
        · exact .inl (by omega)
        · exact .inr holds
      · refine ⟨count + 1, ?_, ?_, ?_, .inr slotsPositive⟩
        · rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
          exact Nat.add_le_add sync ((Nat.mul_le_mul_right _ bounded.2).trans blockSync)
        · have : count + r.state.slot.toNat ≠ m.state.slot.toNat + 1 := fun equal => by
            have := full equal
            omega
          rw [slot]
          omega
        · intro _
          rw [header]
  obtain ⟨potential, count, sync, counted, -, positive⟩ :=
    key inner early same events replayed
  refine ⟨?_, ?_⟩
  · -- The potential at `s` is at most `54` base rewards for each key.
    have most := flagPotential_le previous current base s
    have stakes (keys : Finset ValidatorIndex) : ∑ i ∈ keys, base i ≤
        perIncrement.toNat *
          ((∑ i ∈ keys, effectiveAt r i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
      rw [← Finset.sum_mul, Nat.mul_comm]
      exact Nat.mul_le_mul_left _ (sum_div_le _ _ _)
    have one := stakes previous
    have two := stakes current
    have joined := Nat.mul_le_mul_left 54 (Nat.add_le_add one two)
    rw [← Nat.mul_add] at joined
    rw [Nat.mul_assoc]
    omega
  · -- The blocks of the epoch are at most one per slot.
    rcases positive with zero | slotsPositive
    · rw [zero]
      exact Nat.zero_le _
    have epochs := congrArg UInt64.toNat same
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat] at epochs
    generalize preset.SLOTS_PER_EPOCH.toNat = slots at *
    have sDiv := Nat.div_add_mod s.state.slot.toNat slots
    have rDiv := Nat.div_add_mod r.state.slot.toNat slots
    have sMod := Nat.mod_lt s.state.slot.toNat slotsPositive
    rw [epochs] at sDiv
    have fewer : count ≤ slots := by omega
    have scaled : sourceCredits .sync events * 28 * slots ≤
        issuanceEnvelope preset total.toNat * slots := by
      calc sourceCredits .sync events * 28 * slots =
            sourceCredits .sync events * (28 * slots) := by ring
        _ ≤ count * issuanceEnvelope preset total.toNat := sync
        _ ≤ slots * issuanceEnvelope preset total.toNat := Nat.mul_le_mul_right _ fewer
        _ = issuanceEnvelope preset total.toNat * slots := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_right scaled slotsPositive

end EthLib.Consensus.DirectSafety
