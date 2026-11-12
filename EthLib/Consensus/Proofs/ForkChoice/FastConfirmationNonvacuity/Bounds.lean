module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Basic

/-! Bounds on the epochs reached before the five-validator witness's last time. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.FiveValidatorWitness

open Base

/-- A store with genesis zero cannot reach epoch two by time 4000 milliseconds.

The witness has four slots per epoch and 1000 milliseconds per slot. -/
theorem current_epoch_le_one {store : Store preset .phase0} {epoch : Epoch}
    (genesis : store.genesisTimeMs = 0) (bounded : store.timeMs.toNat ≤ 4000)
    (current : store.getCurrentStoreEpoch config = .ok epoch) : epoch.toNat ≤ 1 := by
  unfold Store.getCurrentStoreEpoch at current
  cases slotRead : store.getCurrentSlot config with
  | error error => simp [slotRead, bind, Except.bind] at current
  | ok slot =>
    have epochEq : computeEpochAtSlot preset slot = epoch := by
      simpa [slotRead, bind, Except.bind, pure, Except.pure] using current
    have slotted : computeSlotAtTimeMs config 0 store.timeMs = .ok slot := by
      unfold Store.getCurrentSlot at slotRead
      rw [genesis] at slotRead
      cases result : computeSlotAtTimeMs config 0 store.timeMs <;>
        simp_all [Except.mapError]
    have latest : computeSlotAtTimeMs config 0 4000 = .ok 4 := rfl
    have below := computeSlotAtTimeMs_mono
      (show store.timeMs ≤ 4000 from UInt64.le_iff_toNat_le.mpr bounded) slotted latest
    have slotBound : slot.toNat ≤ 4 := UInt64.le_iff_toNat_le.mp below
    rw [← epochEq]
    change (slot / (4 : UInt64)).toNat ≤ 1
    rw [UInt64.toNat_div]
    change slot.toNat / 4 ≤ 1
    omega

/-- Every up-to-date receiver before the witness limit is at most in epoch one.

Genesis zero is required only initially: the network handlers preserve it. -/
theorem receiver_epoch_le_one {checks : SignatureChecks}
    {sources : BlockSources preset .phase0} {anchorState : BeaconState preset .phase0}
    {anchorBlock : BeaconBlock preset .phase0} {assignment : Assignment preset}
    {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J)
    (genesis : ∀ w ∈ J, (e.start w).genesisTimeMs = 0)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} {epoch : Epoch}
    (bounded : (e.world k).time ≤ 4000)
    (updated : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    (current : ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch) :
    epoch.toNat ≤ 1 :=
  current_epoch_le_one ((e.clock_bounds w k).1.trans (genesis w receiver))
    (updated.1 ▸ bounded) current

/-- Target inclusion is vacuous on the witness's short horizon.

Its receiver must be at least two epochs after a target, but cannot be past epoch one.

This includes descendant-relative instances at later receivers.

The result assumes an execution and does not construct one. -/
theorem target_included {checks : SignatureChecks}
    {sources : BlockSources preset .phase0} {anchorState : BeaconState preset .phase0}
    {anchorBlock : BeaconBlock preset .phase0} {assignment : Assignment preset}
    {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J)
    (genesis : ∀ w ∈ J, (e.start w).genesisTimeMs = 0) : TargetIncluded e 4000 := by
  intro u caller n nBound head state total target voters stateOk totalOk epochOk signed quorum
    w receiver k current kBound later updated currentOk aged
  have upper := receiver_epoch_le_one e genesis receiver kBound updated currentOk
  omega

end EthLib.Consensus.Models.Network.FiveValidatorWitness
