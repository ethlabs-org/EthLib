module

import all EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound
import all EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinSum

namespace EthLib.Consensus.Models.Network
namespace PinSum

open Base Uint64 Models DirectSafety PinSplit

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- A key's balance along a run from a stake bound, the credits and the gain at the bound. -/
private theorem c_ceiling_abstract {n y : ForkedBeaconState preset}
    (post : Run config checks n y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ n.fork)
    (i : ℕ) (inside : i < n.state.validators.data.size) (high P capHigh : ℕ)
    (alignedCap : capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (startCap : effectiveAt n i ≤ capHigh)
    (capCeil : ∀ z ∈ post.balancePath, PinSplit2.capAt z i ≤ capHigh)
    (rate : ∀ z ∈ post.balancePath, ∀ total perIncrement : Gwei,
      getTotalActiveBalance z.state = .ok total →
      getBaseRewardPerIncrement preset total = .ok perIncrement →
      perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices z.state
        (getPreviousEpoch z.state)).toFinset, effectiveAt z j.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
        P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (depth Cr E e0 C S U1 U2 : ℕ)
    (hE : E = e0 + C + preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (alignedE : E % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (epochs : (getCurrentEpoch y.state).toNat - (getCurrentEpoch n.state).toNat ≤ depth)
    (startBal : min (actualBalanceAt n i) capHigh ≤ S)
    (startEff : effectiveAt n i ≤ E)
    (credits : netScan i high post +
      (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high post).1 ≤ Cr)
    (base : depth * (e0 / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) ≤ U1)
    (unit : depth * (P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum /
      WEIGHT_DENOMINATOR.toNat + 2) ≤ U2)
    (closed : S + Cr + (gainOn preset depth P C + (U1 + U2)) <
      E + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) :
    ∀ z ∈ post.balancePath,
      min (actualBalanceAt z i) capHigh ≤ S + Cr + (gainOn preset depth P C + (U1 + U2)) := by
  have split := gain_split preset.EFFECTIVE_BALANCE_INCREMENT.toNat WEIGHT_DENOMINATOR.toNat
    (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum P e0 C
    ((getCurrentEpoch y.state).toNat - (getCurrentEpoch n.state).toNat) depth incPos epochs
  rw [← hE] at split
  have bound : PinSplit2.creditBound post i high E P capHigh ≤
      S + Cr + (gainOn preset depth P C + (U1 + U2)) := by
    unfold PinSplit2.creditBound gainOn
    omega
  have fixpoint : max (effectiveAt n i) (min capHigh
      (PinSplit2.creditBound post i high E P capHigh -
        PinSplit2.creditBound post i high E P capHigh %
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ E := by
    refine max_le startEff (Nat.le_trans (Nat.min_le_right _ _) ?_)
    have lt : PinSplit2.creditBound post i high E P capHigh <
        E + preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by omega
    obtain ⟨u, hu⟩ := Nat.dvd_of_mod_eq_zero alignedE
    have div := Nat.div_add_mod (PinSplit2.creditBound post i high E P capHigh)
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    generalize PinSplit2.creditBound post i high E P capHigh = B at lt div ⊢
    generalize preset.EFFECTIVE_BALANCE_INCREMENT.toNat = I at lt div incPos hu
    have qlt : B / I < u + 1 := (Nat.div_lt_iff_lt_mul incPos).mpr (by
      have : (u + 1) * I = E + I := by rw [hu]; ring
      omega)
    have mul : I * (B / I) ≤ I * u := Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨-, -, -, fourth⟩ := PinSplit2.Run.effective_floor_pair post early fulu i inside 0 0 0
    capHigh high E P
  have balances := fourth alignedCap startCap capCeil rate endEpoch fixpoint
  intro z member
  exact Nat.le_trans (balances z member) bound

end PinSum
end EthLib.Consensus.Models.Network
