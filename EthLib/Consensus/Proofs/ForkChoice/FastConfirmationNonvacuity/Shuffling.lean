module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.FirstBlock

/-! The custom zero-round shuffle pairs validators 3 and 4 at every slot.

This fact applies to arbitrary successful committee reads, not only reads before the horizon.

It prepares the committee-range Byzantine bound in the witness for Theorem 1.

Theorem 1 is in arXiv 2405.00549v4, Section 4. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.FiveValidatorWitness

open Base

/-- Every slot's epoch is strictly before the registry's unscheduled exit epoch. -/
theorem slot_epoch_below_exit (slot : Slot) :
    computeEpochAtSlot preset slot < FAR_FUTURE_EPOCH := by
  rw [UInt64.lt_iff_toNat_lt]
  change (slot / (4 : UInt64)).toNat < 18446744073709551615
  rw [UInt64.toNat_div]
  have bound := slot.toNat_lt
  change slot.toNat / 4 < 18446744073709551615
  omega

/-- The same five validators are active at every representable duty slot. -/
theorem active_at_slot (root : Root) (slot : Slot) :
    getActiveValidatorIndices (state root) (computeEpochAtSlot preset slot) = [0, 1, 2, 3, 4] := by
  have active (weight : UInt64) :
      isActiveValidator (validator weight) (computeEpochAtSlot preset slot) = true := by
    simp [isActiveValidator, validator, slot_epoch_below_exit slot]
  change ([(validator 200, 0), (validator 200, 1), (validator 200, 2),
    (validator 100, 3), (validator 200, 4)].filterMap fun (v, i) =>
      if isActiveValidator v (computeEpochAtSlot preset slot) then some i.toUInt64 else none) = _
  simp only [List.filterMap_cons, List.filterMap_nil, active, ↓reduceIte]
  rfl

/-- The custom preset assigns one committee per slot to this registry. -/
theorem slot_committee_count (root : Root) (slot : Slot) :
    getCommitteeCountPerSlot (state root) (computeEpochAtSlot preset slot) = 1 := by
  rw [getCommitteeCountPerSlot, active_at_slot]
  rfl

/-- The ordered registry is divided among the four slots, with the final pair together. -/
def seats (slot : Slot) : Array ValidatorIndex :=
  if slot % 4 = 0 then #[0] else if slot % 4 = 1 then #[1]
  else if slot % 4 = 2 then #[2] else #[3, 4]

/-- With zero rounds, committee membership does not depend on the seed bytes. -/
theorem zero_round_committee (seed : Bytes32) {slot : Slot} :
    computeCommittee preset #[0, 1, 2, 3, 4] seed (slot % 4) 4 = .ok (seats slot) := by
  have shuffle : computeShuffledPermutation preset 5 seed = .ok #[0, 1, 2, 3, 4] := by
    change Except.ok ((Array.range 5).map UInt64.ofNat) = _
    rw [Array.range_eq_range']
    simp only [Array.range'_succ, Array.range'_zero]
    simp
  have rem : (slot % 4).toNat < 4 := by
    rw [UInt64.toNat_mod]
    exact Nat.mod_lt _ (by decide)
  have cases : slot % 4 = 0 ∨ slot % 4 = 1 ∨ slot % 4 = 2 ∨ slot % 4 = 3 := by
    simp only [← UInt64.toNat_inj]
    change (slot % 4).toNat = 0 ∨ (slot % 4).toNat = 1 ∨
      (slot % 4).toNat = 2 ∨ (slot % 4).toNat = 3
    omega
  rw [computeCommittee, show (#[0, 1, 2, 3, 4] : Array ValidatorIndex).size = 5 from rfl,
    show UInt64.ofNat 5 = 5 from rfl, shuffle]
  rcases cases with eq | eq | eq | eq <;> rw [eq] <;>
    simp only [seats, eq] <;> rfl

/-- Any state with this registry returns these seats whenever its committee read succeeds. -/
theorem committee_at_slot {s : BeaconState preset .phase0} {slot : Slot}
    {committee : Array ValidatorIndex} (registry : s.validators = (state bodyRoot).validators)
    (read : getBeaconCommittee s slot 0 = .ok committee) : committee = seats slot := by
  have active : getActiveValidatorIndices s (computeEpochAtSlot preset slot) =
      [0, 1, 2, 3, 4] := by
    unfold getActiveValidatorIndices
    rw [registry]
    exact active_at_slot bodyRoot slot
  have perSlot : getCommitteeCountPerSlot s (computeEpochAtSlot preset slot) = 1 := by
    rw [getCommitteeCountPerSlot, active]
    rfl
  obtain ⟨seed, position, count, _, positionEq, countEq, computed⟩ := getBeaconCommittee_ok read
  rw [perSlot] at positionEq countEq
  have pos : position = slot % 4 := UInt64.toNat_inj.mp (by
    change position.toNat = (slot % 4).toNat * 1 + 0 at positionEq
    simpa using positionEq)
  have countValue : count = 4 := UInt64.toNat_inj.mp (by exact countEq)
  rw [pos, countValue, active, zero_round_committee, Except.ok.injEq] at computed
  exact computed.symm

/-- Every committee containing the Byzantine validator also contains honest validator 4. -/
theorem seats_paired (slot : Slot) : (3 : ValidatorIndex) ∈ seats slot →
    (4 : ValidatorIndex) ∈ seats slot := by
  unfold seats
  split <;> (first | simp | split <;> (first | simp | split <;> simp))

end EthLib.Consensus.Models.Network.FiveValidatorWitness
