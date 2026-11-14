module

public import EthLib.Consensus.Proofs.DirectSafety.Core
public import EthLib.Consensus.Proofs.Transition.TargetUpgrades
public import EthLib.Consensus.Proofs.Transition.SlashedPersistence

/-!
# Drift computed from the concrete transitions

Charge active departures and balance losses separately from recent arrivals and balance gains.

Recent means unslashed and active in either of the two epochs that justification may count.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

open Classical in
attribute [local instance] propDecidable

/-- Exact loss of the unslashed reference stake, outside keys already slashed at this state.

A key already slashed at `x` is not in the reference set, so it is not charged here. -/
noncomputable def referenceLoss (x y : ForkedBeaconState preset) : Nat := by
  classical
  exact ∑ k ∈ (unslashedKeys x.state).filter (¬ SlashedAt y.state ·),
    (effectiveWeight x.state k - Models.supported (recentKeys y.state)
      (effectiveWeight y.state) k)

/-- Exact gains on the voting support over the unslashed reference stake.

Reference stake that just exited is not charged.

A key already slashed at `x` is outside the reference set.

Along a run, slashed flags stay set, so such a key cannot enter the later voting support. -/
noncomputable def referenceGain (x y : ForkedBeaconState preset) : Nat :=
  ∑ k ∈ recentKeys y.state,
    (effectiveWeight y.state k - Models.supported (unslashedKeys x.state)
      (effectiveWeight x.state) k)

private theorem slashedAt_of_run {x y : ForkedBeaconState preset}
    (run : Run config checks x y) {key : BLSPubkey}
    (slashed : SlashedAt x.state key) : SlashedAt y.state key := by
  obtain ⟨v, member, keyEq, flag⟩ := slashed
  obtain ⟨i, found⟩ := List.mem_iff_getElem?.mp member
  have read : x.state.validators.data[i]? = some v := by simpa using found
  obtain ⟨w, later, marked⟩ := run.slashedPersistence i v read flag
  obtain ⟨u, held, same⟩ := validators_getElem?_of_validatorKeys_prefix
    (validatorKeys_prefix_and_distinct_of_chainSteps run.chainSteps).1 read
  rw [later, Option.some.injEq] at held
  subst u
  exact ⟨w, by simpa using (Array.mem_of_getElem? later), same.trans keyEq, marked⟩

/-- Along a run, excluding keys slashed at the later endpoint also excludes earlier slashings. -/
theorem referenceLoss_eq_of_run {x y : ForkedBeaconState preset}
    (run : Run config checks x y) :
    referenceLoss x y = ∑ key ∈ (activeKeys x.state).filter (¬ SlashedAt y.state ·),
      (effectiveWeight x.state key - Models.supported (recentKeys y.state)
        (effectiveWeight y.state) key) := by
  classical
  unfold referenceLoss unslashedKeys
  congr 1
  ext key
  simp only [Finset.mem_filter]
  constructor
  · exact fun ⟨⟨active, _⟩, clean⟩ => ⟨active, clean⟩
  · exact fun ⟨active, clean⟩ =>
      ⟨⟨active, fun old => clean (slashedAt_of_run run old)⟩, clean⟩

/-- Later voting support contains no key slashed at the reference endpoint of the run. -/
theorem referenceGain_eq_of_run {x y : ForkedBeaconState preset}
    (run : Run config checks x y) :
    referenceGain x y = ∑ key ∈ recentKeys y.state,
      (effectiveWeight y.state key - Models.supported (activeKeys x.state)
        (effectiveWeight x.state) key) := by
  classical
  unfold referenceGain
  apply Finset.sum_congr rfl
  intro key member
  have clean := (Finset.mem_filter.mp member).2
  have oldClean : ¬ SlashedAt x.state key := fun old => clean (slashedAt_of_run run old)
  simp [Models.supported, unslashedKeys, oldClean]

/-- Unslashed previous-epoch stake that is not active at the current epoch, at one boundary only. -/
noncomputable def boundaryStake (y : ForkedBeaconState preset) : Nat :=
  Models.stake (effectiveWeight y.state) (recentKeys y.state \ activeKeys y.state)

/-- The combined transfer assigns coefficients two, one and two to loss, gain and boundary stake.

In the bound, twice the drift divided by three weighs loss and gain at four thirds and two thirds.

These are the weights of exits and of activations in [EIP-8061], Security Considerations.

[EIP-8061]: https://eips.ethereum.org/EIPS/eip-8061#weak-subjectivity-period
-/
noncomputable def stateDrift (x y : ForkedBeaconState preset) : Nat :=
  2 * referenceLoss x y + referenceGain x y + 2 * boundaryStake y

/-- Persistence identifies the unslashed-reference budget with the full-active-reference budget. -/
theorem stateDrift_eq_of_run {x y : ForkedBeaconState preset}
    (run : Run config checks x y) :
    stateDrift x y =
      2 * (∑ key ∈ (activeKeys x.state).filter (¬ SlashedAt y.state ·),
        (effectiveWeight x.state key - Models.supported (recentKeys y.state)
          (effectiveWeight y.state) key)) +
      (∑ key ∈ recentKeys y.state,
        (effectiveWeight y.state key - Models.supported (activeKeys x.state)
          (effectiveWeight x.state) key)) + 2 * boundaryStake y := by
  rw [stateDrift, referenceLoss_eq_of_run run, referenceGain_eq_of_run run]

/-- Maximum observed state budget, including the initial state and excluding later epochs. -/
noncomputable def derivedDrift {x : ForkedBeaconState preset} (high : Nat) :
    {y : ForkedBeaconState preset} → Run config checks x y → Nat
  | _, .nil => stateDrift x x
  | y, .snoc pre _ =>
    if (getCurrentEpoch y.state).toNat ≤ high + 1 then
      max (derivedDrift high pre) (stateDrift x y)
    else derivedDrift high pre

/-- A quorum call of a prefix and a tail is in the tail when its target is not before epoch `low`.

The prefix must end no later than the first slot of epoch `low`.

An epoch has a slot. -/
theorem call_after_reference {g x a : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x a)
    (parameters : Parameters preset) (low : Nat)
    (starts : x.state.slot.toNat ≤ low * preset.SLOTS_PER_EPOCH.toNat)
    (call : QuorumCall (shared.append tail)) (later : low ≤ call.target.epoch.toNat) :
    tail.Contains (.slot call.advanced) := by
  rcases (shared.contains_append tail (.slot call.advanced)).mp call.member with member | member
  · exfalso
    -- A call in the shared prefix finishes strictly before the reference slot bound permits.
    obtain ⟨pre, post, _⟩ := shared.contains_split (.slot call.advanced) member
    have afterEnd := post.slot_le
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp call.advanced
    have next := advanceSlot_slot advancedOk
    have kept := processUpgrades_slot upgraded
    have cachedSlot := (frame_processSlot call.cachedOk).slot
    have targetBound : call.target.epoch.toNat ≤
        call.before.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      rw [call.targetEpoch]
      cases call.current <;>
        simp [getPreviousEpoch_toNat, getCurrentEpoch_toNat, cachedSlot]
    have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by
      have := parameters.slots
      omega
    have lowerSlot := (Nat.le_div_iff_mul_le positive).mp (later.trans targetBound)
    rw [← kept] at next
    omega
  · exact member

end EthLib.Consensus.DirectSafety
