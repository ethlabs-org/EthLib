module

public import EthLib.Consensus.Proofs.Transition.BalanceDrift
import Mathlib.Data.Nat.Notation
import EthLib.Consensus.Proofs.Transition.EpochUpdates
import EthLib.Consensus.Proofs.Transition.ForkBoundary
import EthLib.Consensus.Proofs.Transition.StateTransition
import EthLib.Consensus.Proofs.Transition.Trace

/-!
# A balance floor along a run gives an effective-balance floor

An effective balance changes only in the update of the effective balances.

That update runs at the last slot step of an epoch.

It keeps the old value, or it sets the balance rounded down to an increment, at most the cap.

Rounding a balance of at least `floor` down to an increment leaves at least `floor + 1 - inc`.

So a balance floor and a cap floor along a run keep the effective balance above a bound.

The bound is the least of its start, the cap floor and `floor + 1 - inc`.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network.PinSplit2

open Base Uint64 Models

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- A key's cap at a state, `0` past the registry. -/
def capAt (z : ForkedBeaconState preset) (i : ℕ) : ℕ :=
  ((z.state.validators.data[i]?).map fun v =>
    (withdrawalMaxEffectiveBalance preset z.fork v).toNat).getD 0

/-- The update of the effective balances keeps a lower bound on the effective balance of a key.

The balance must be at least `floor` and the cap at least `capLow`.

The bound must be at most `capLow` and at most `floor + 1` less one increment.

The new value is the old one, or the balance rounded down to an increment, at most the cap.

The rounding leaves less than one increment. -/
private theorem effective_floor_update {f : Fork} {s t : BeaconState preset f}
    (ok : processEffectiveBalanceUpdates s = .ok t) (i floor capLow low : ℕ)
    (positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (lowCap : low ≤ capLow)
    (lowFloor : low ≤ floor + 1 - preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (funded : floor ≤ actualBalanceAt ⟨f, s⟩ i) (previous : low ≤ effectiveAt ⟨f, s⟩ i)
    (cap : ∀ v, t.validators.data[i]? = some v →
      capLow ≤ (withdrawalMaxEffectiveBalance preset f v).toNat) :
    low ≤ effectiveAt ⟨f, t⟩ i := by
  have one {a b : BeaconState preset f} {j : Nat}
      (step : updateEffectiveBalance a j = .ok b) :
      b.balances = a.balances ∧
      (∀ v, b.validators.data[i]? = some v →
        capLow ≤ (withdrawalMaxEffectiveBalance preset f v).toNat) →
      (∀ v, a.validators.data[i]? = some v →
        capLow ≤ (withdrawalMaxEffectiveBalance preset f v).toNat) ∧
      (floor ≤ actualBalanceAt ⟨f, a⟩ i → low ≤ effectiveAt ⟨f, a⟩ i →
        low ≤ effectiveAt ⟨f, b⟩ i) := by
    simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at step
    obtain ⟨v, found, balance, read, next, changed, set⟩ := step
    obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
    intro premise
    have located := getValidatorAt_eq_ok_iff.mp found
    by_cases eq : i = j
    · subst i
      have nextRead :
          (a.putValidator j inside { v with effectiveBalance := next }).validators.data[j]? =
          some { v with effectiveBalance := next } := by
        simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set]
      have capped := premise.2 _ nextRead
      change capLow ≤ (withdrawalMaxEffectiveBalance preset f v).toNat at capped
      constructor
      · intro w wRead
        rw [located, Option.some.injEq] at wRead
        subst w
        exact capped
      · intro funded previous
        simp only [actualBalanceAt, getBalanceAt_eq_ok_iff.mp read, effectiveAt, located,
          Option.map_some, Option.getD_some] at funded previous
        simp only [effectiveAt, nextRead, Option.map_some, Option.getD_some]
        rcases updatedEffectiveBalance_cases changed with rfl | rfl
        · exact previous
        · have rounded : balance % preset.EFFECTIVE_BALANCE_INCREMENT ≤ balance :=
            UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_mod]; exact Nat.mod_le _ _)
          have remainder := Nat.mod_lt balance.toNat positive
          rw [Base.Uint64.toNat_min, UInt64.toNat_sub_of_le _ _ rounded, UInt64.toNat_mod]
          omega
    · have same :
          (a.putValidator j inside { v with effectiveBalance := next }).validators.data[i]? =
          a.validators.data[i]? := by
        simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, Ne.symm eq]
      constructor
      · simpa only [same] using premise.2
      · intro _ previous
        simpa only [effectiveAt, same] using previous
  have fold : ∀ (xs : List Nat) {a b : BeaconState preset f},
      xs.foldlM updateEffectiveBalance a = .ok b →
      (∀ v, b.validators.data[i]? = some v →
        capLow ≤ (withdrawalMaxEffectiveBalance preset f v).toNat) →
      (∀ v, a.validators.data[i]? = some v →
        capLow ≤ (withdrawalMaxEffectiveBalance preset f v).toNat) ∧
      (floor ≤ actualBalanceAt ⟨f, a⟩ i → low ≤ effectiveAt ⟨f, a⟩ i →
        low ≤ effectiveAt ⟨f, b⟩ i) := by
    intro xs
    induction xs with
    | nil => intro a b ok cap; cases ok; exact ⟨cap, fun _ previous => previous⟩
    | cons j xs ih =>
      intro a b ok cap
      obtain ⟨middle, updated, rest⟩ := bind_ok_iff.mp ok
      have tail := ih rest cap
      have balances : middle.balances = a.balances := by
        simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at updated
        obtain ⟨_, _, _, _, _, _, set⟩ := updated
        obtain ⟨_, rfl⟩ := setValidatorAt_ok set
        rfl
      have head := one updated ⟨balances, tail.1⟩
      exact ⟨head.1, fun funded previous => tail.2
        (by simpa only [actualBalanceAt, balances] using funded) (head.2 funded previous)⟩
  unfold processEffectiveBalanceUpdates at ok
  exact (fold _ ok cap).2 funded previous

/-- One slot step keeps the lower bound, given the balance and the cap after it.

Only the epoch transition changes an effective balance, in its update. -/
private theorem effective_floor_slot {f : Fork} {s t : BeaconState preset f}
    (ok : advanceSlot config checks s = .ok t) (i floor capLow low : ℕ)
    (inside : i < s.validators.data.size)
    (positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (lowCap : low ≤ capLow)
    (lowFloor : low ≤ floor + 1 - preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (funded : floor ≤ actualBalanceAt ⟨f, t⟩ i) (previous : low ≤ effectiveAt ⟨f, s⟩ i)
    (cap : ∀ v, t.validators.data[i]? = some v →
      capLow ≤ (withdrawalMaxEffectiveBalance preset f v).toNat) :
    low ≤ effectiveAt ⟨f, t⟩ i := by
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨next, _, cached, cache, advanced, advance, rfl⟩ := ok
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
  unfold epochIfLast at advance
  split at advance
  · obtain ⟨before, after, kept, updated, validators, balances⟩ := balanceDrift_epoch advance
    have prior : low ≤ effectiveAt ⟨f, before⟩ i := by
      rw [kept i inside]
      exact previous
    have bound := effective_floor_update updated i floor capLow low positive lowCap lowFloor
      (by simpa only [actualBalanceAt, balances] using funded) prior
      (fun v read => cap v (by rw [validators]; exact read))
    simpa only [effectiveAt, validators] using bound
  · cases advance
    exact previous

/-- Between the first fork of Fulu and Gloas, the upgrades leave the state as it is.

The only upgrade from a fork of that range leads to Gloas. -/
private theorem processUpgrades_eq_of_window {z z' : ForkedBeaconState preset}
    (ok : processUpgrades config checks z = .ok z') (fulu : .fusaka ≤ z.fork)
    (early : z'.fork < .glamsterdam) : z' = z := by
  have stays : z'.fork ≤ z.fork := by
    rw [processUpgrades] at ok
    split at ok
    · obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
      have later := processUpgrades_fork_le rest
      have reached : Fork.glamsterdam ≤ next.val.fork := by
        obtain ⟨fork, state⟩ := z
        cases fork <;> dsimp only at fulu <;>
          first
            | exact absurd fulu (by decide)
            | (simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
                throwThe, MonadExceptOf.throw, reduceCtorEq] at nextOk
               all_goals first
                 | (obtain ⟨_, -, rfl⟩ := nextOk; exact Nat.le_refl _)
                 | (obtain ⟨_, -, rfl⟩ := nextOk
                    exact Nat.le_of_lt (by decide : Fork.glamsterdam < Fork.hegota)))
      exact absurd (Nat.lt_of_le_of_lt (Nat.le_trans reached later) early) (Nat.lt_irrefl _)
    · cases ok
      exact Nat.le_refl _
  exact processUpgrades_eq_of_fork_le ok stays

/-- H4. A balance floor and a cap floor along a run give an effective-balance floor.

Suppose a key's balance stays at least `floor` at every state of a run.

Suppose also that its cap stays at least `capLow`.

Then its effective balance at the end is at least the least of three values.

They are its effective balance at the start, `capLow`, and `floor` less one increment of rounding.

An update moves the effective balance only at an epoch's first slot.

It moves it down to the balance rounded to an increment, which is at least `floor + 1 - inc`.

It moves it up to at most the cap, and never below where it was. -/
theorem Run.effective_floor_of_balance_floor {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ x.fork)
    (bands : preset.IncrementWithinUpwardBand) (i : ℕ) (inside : i < x.state.validators.data.size)
    (floor capLow : ℕ)
    (balanceFloor : ∀ z ∈ tail.balancePath, floor ≤ actualBalanceAt z i)
    (capFloor : ∀ z ∈ tail.balancePath, capLow ≤ capAt z i) :
    min (effectiveAt x i) (min capLow (floor + 1 - preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
      effectiveAt y i := by
  have positive := bands.1
  induction tail with
  | nil => exact Nat.min_le_left _ _
  | @snoc middle last pre step ih =>
    have middleEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have prior := ih middleEarly (fun p member => balanceFloor p (List.mem_append_left _ member))
      (fun p member => capFloor p (List.mem_append_left _ member))
    have room : i < middle.state.validators.data.size :=
      Nat.lt_of_lt_of_le inside pre.registryLifecycle.size_le
    cases step with
    | @block fork before after engine signed due ok =>
      rw [effectiveKept_processBlock (applySignedBlock_ok ok).2.1 i room]
      exact prior
    | slot ok =>
      obtain ⟨next, advanced, upgraded⟩ := bind_ok_iff.mp ok
      have onPath : (⟨middle.fork, next⟩ : ForkedBeaconState preset) ∈
          (Step.slot ok).balancePath := by
        simp [Step.balancePath, advanced, Except.toOption]
      have funded := balanceFloor _ (List.mem_append_right _ onPath)
      have capped := capFloor _ (List.mem_append_right _ onPath)
      have fuluMiddle : Fork.fusaka ≤ middle.fork :=
        Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
      have same := processUpgrades_eq_of_window upgraded fuluMiddle early
      subst same
      refine effective_floor_slot advanced i floor capLow _ room positive
        (Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)) ?_ funded prior ?_
      · exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)
      · intro v read
        simpa [capAt, read] using capped

end EthLib.Consensus.Models.Network.PinSplit2
