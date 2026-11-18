module

public import EthLib.Consensus.Proofs.Transition.BalanceCappedWithdrawals

/-!
# A block's withdrawals leave a key that is not yet withdrawable at least the activation balance

From Electra and before Gloas, a block pays a key that is not yet withdrawable from two places.

A queued partial withdrawal pays only the part above the activation balance.

The sweep pays only the part above the key's largest effective balance, which is at least the activation balance.

Only a withdrawable key is paid in full.

So the balance after the block is at least the lesser of the balance before and the activation balance.

[EIP-7251](https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1) defines the queue and the larger balances.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network.PinSplit3

open Base Uint64 Models

variable {preset : Preset} {fork : Fork}

/-- The loop of the queued partial withdrawals keeps a floor of a key's balance.

What the withdrawals take from the key, plus a floor at most the activation balance, stays within its balance.

Each entry pays at most the balance left above the activation balance. -/
private theorem getPendingPartialWithdrawals_loop_floor {state : BeaconState preset fork}
    {prior : Array Withdrawal} {epoch : Epoch} {limit : Nat} {index : ValidatorIndex}
    {balance : Gwei} {floor : Nat}
    (found : state.balances.data[index.toNat]? = some balance)
    (capped : floor ≤ preset.MIN_ACTIVATION_BALANCE.toNat) :
    ∀ (queue : List PendingPartialWithdrawal) (withdrawals : Array Withdrawal)
      (next : WithdrawalIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    withdrawnFrom (prior ++ withdrawals) index + floor ≤ balance.toNat →
    getPendingPartialWithdrawals.loop state prior epoch limit queue withdrawals next processed =
      .ok result →
    withdrawnFrom (prior ++ result.1) index + floor ≤ balance.toNat
  | [], _, _, _, _, bounded, computed => by
    simp only [getPendingPartialWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact bounded
  | pending :: rest, _, _, _, _, bounded, computed => by
    simp only [getPendingPartialWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact bounded
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, left, leftOk, computed⟩ := computed
      have leftOk := liftAccessor_ok.mp leftOk
      split at computed
      · rename_i eligible
        simp only [isEligibleForPartialWithdrawals, Bool.and_eq_true, decide_eq_true_eq]
          at eligible
        simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨⟨appended, following⟩, appendedOk, rest'⟩ := computed
        refine getPendingPartialWithdrawals_loop_floor found capped rest _ _ _ ?_ rest'
        rw [appendWithdrawal_withdrawnFrom_eq appendedOk]
        split
        · rename_i named
          subst named
          obtain ⟨read, readAt, sum⟩ := getBalanceAfterWithdrawals_ok leftOk
          rw [found, Option.some.injEq] at readAt
          subst readAt
          have above := UInt64.lt_iff_toNat_lt.mp eligible.2
          have paid : (min (left - preset.MIN_ACTIVATION_BALANCE) pending.amount).toNat ≤
              left.toNat - preset.MIN_ACTIVATION_BALANCE.toNat := by
            have := UInt64.toNat_sub_of_le left preset.MIN_ACTIVATION_BALANCE
              (UInt64.le_of_lt eligible.2)
            rw [UInt64.min_def]
            split
            · omega
            · have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp ‹_›)
              omega
          omega
        · simpa using bounded
      · exact getPendingPartialWithdrawals_loop_floor found capped rest _ _ _ bounded computed

/-- From Electra and before Gloas, a block's withdrawals leave a key that is not yet withdrawable
with at least the least of its balance before and `MIN_ACTIVATION_BALANCE`.

A pending partial pays at most the balance above `MIN_ACTIVATION_BALANCE`.
The sweep pays at most the balance above the key's cap, which is at least `MIN_ACTIVATION_BALANCE` because `compounding` bounds the cap of a compounding key.
Only a withdrawable key is paid in full. -/
theorem processWithdrawals_balance_floor {state after : BeaconState preset fork}
    (capella : .shapella ≤ fork) (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after)
    (i : Nat) (v : Validator) (found : state.validators.data[i]? = some v)
    (notWithdrawable : getCurrentEpoch state < v.withdrawableEpoch) :
    min (((state.balances.data[i]?).map (·.toNat)).getD 0) preset.MIN_ACTIVATION_BALANCE.toNat ≤
      ((after.balances.data[i]?).map (·.toNat)).getD 0 := by
  obtain ⟨expected, expectedOk, -, appliedOk⟩ := processWithdrawals_expected early computed
  obtain ⟨applied, appliedFold, balances, -⟩ := applyExpectedWithdrawals_balances appliedOk
  unfold applyWithdrawals at appliedFold
  rw [← Array.foldlM_toList] at appliedFold
  rw [balances]
  cases held : state.balances.data[i]? with
  | none => simp
  | some balance =>
    simp only [Option.map_some, Option.getD_some]
    by_cases small : i < 2 ^ 64
    · have same : i.toUInt64.toNat = i := UInt64.toNat_ofNat_of_lt' small
      rw [← same] at found held
      have bounded := getExpectedWithdrawals_withdrawnFrom (.inl early) expectedOk held
      have lowered := applyWithdrawals_balance (.inl early) _ _ _ _ appliedFold held
        (by simpa using bounded)
      -- the cap of the key is at least the activation balance
      have cap : preset.MIN_ACTIVATION_BALANCE.toNat ≤
          (withdrawalMaxEffectiveBalance preset fork v).toNat := by
        unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance
        simp only [electra, ↓reduceIte]
        split
        · exact UInt64.le_iff_toNat_le.mp compounding
        · exact Nat.le_refl _
      obtain ⟨partials, next, partialsOk, sweepFloor⟩ :=
        getExpectedWithdrawals_sweep_floor early expectedOk found notWithdrawable held
      simp only [electra, ↓reduceDIte] at partialsOk
      have partialFloor : withdrawnFrom partials i.toUInt64 +
          min balance.toNat preset.MIN_ACTIVATION_BALANCE.toNat ≤ balance.toNat := by
        unfold getPendingPartialWithdrawals at partialsOk
        simp only [bind_ok_iff, ensure_ok_iff] at partialsOk
        obtain ⟨_, _, _, _, loopOk⟩ := partialsOk
        simpa using getPendingPartialWithdrawals_loop_floor held (Nat.min_le_right _ _) _ _ _ _
          (by
            have : withdrawnFrom (#[] ++ #[]) i.toUInt64 = 0 := by simp [withdrawnFrom]
            omega) loopOk
      rw [same] at lowered
      simp only [Array.toArray_toList] at lowered
      cases atLater : applied.balances.data[i]? with
      | none => simp [atLater] at lowered
      | some later =>
        simp only [atLater, Option.map_some, Option.some.injEq] at lowered
        simp only [Option.map_some, Option.getD_some]
        omega
    · -- No withdrawal names the index, so the balance is unchanged.
      have unchanged := applyWithdrawals_unnamed (index := i) _ _ _ appliedFold
        fun withdrawal _ atIndex => by
          have := UInt64.toNat_lt_size withdrawal.validatorIndex
          simp only [UInt64.size] at this
          omega
      rw [unchanged, held]
      simp only [Option.map_some, Option.getD_some]
      exact Nat.min_le_left _ _

end EthLib.Consensus.Models.Network.PinSplit3
