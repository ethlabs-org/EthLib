module

public import EthLib.Consensus.Proofs.Transition.BalanceDrift
public import EthLib.Consensus.Proofs.Transition.Trace
public import EthLib.Consensus.Proofs.Transition.FfgStake
public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.Operations
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.EpochPassAtCall
import EthLib.Consensus.Proofs.Transition.Totality.FlagsActive
import EthLib.Consensus.Proofs.Transition.SlashedPersistence
import EthLib.Consensus.Proofs.Transition.BlockRewards
import EthLib.Consensus.Proofs.Transition.Committees
import EthLib.Consensus.Proofs.Transition.ForkBoundary
import EthLib.Consensus.Proofs.Transition.PayloadInputs
import EthLib.Consensus.Proofs.Transition.Requests
import EthLib.Consensus.Proofs.Transition.SyncCommitteeProvenance
import EthLib.Consensus.Proofs.Transition.WithdrawalAmounts
import EthLib.Consensus.Proofs.Transition.Withdrawals
import EthLib.Consensus.Proofs.Transition.BalanceNotRaisedBlock
import EthLib.Consensus.Proofs.Participation

/-!
# The balances along a branch inside one epoch

The branch corrections cover a branch inside one epoch, from Altair and before Gloas.

They read every balance change from the last state.

Withdrawals and conversions debit a counted set.

The sync committee moves each member by its seats.

The other credits go to the proposers of the blocks and to the recipients of deposits.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The proposer search reads only the effective balances of the validators it draws.

Each candidate is one of the indices, or index zero when the order leaves them. -/
private theorem proposerSearch_congr_validators {fork : Fork} {first second : Array Validator}
    {indices : Array ValidatorIndex} {order : Nat → Nat} {seed : Bytes32}
    (positive : 0 < first.size) (inside : ∀ index ∈ indices, index.toNat < first.size)
    (agree : ∀ j < first.size, (first[j]?).map (·.effectiveBalance) =
      (second[j]?).map (·.effectiveBalance)) :
    ∀ {i : Nat}, proposerSearch preset fork first indices order seed i =
      proposerSearch preset fork second indices order seed i := by
  intro i
  obtain ⟨left, leftEq⟩ : ∃ left, left = 2 ^ 64 - i := ⟨_, rfl⟩
  induction left using Nat.strongRecOn generalizing i with
  | _ left ih =>
    unfold proposerSearch
    have small : (indices.getD (order (i % indices.size)) 0).toNat < first.size := by
      rw [Array.getD_eq_getD_getElem?]
      by_cases within : order (i % indices.size) < indices.size
      · rw [Array.getElem?_eq_getElem within, Option.getD_some]
        exact inside _ (Array.getElem_mem within)
      · rw [Array.getElem?_eq_none (Nat.le_of_not_lt within), Option.getD_none]
        exact positive
    have same := agree _ small
    generalize indices.getD (order (i % indices.size)) 0 = candidate at same ⊢
    cases hf : first[candidate.toNat]? <;> cases hs : second[candidate.toNat]? <;>
      simp only [hf, hs, Option.map_none, Option.map_some, reduceCtorEq,
        Option.some.injEq] at same
    · simp only [hf, hs]
    · simp only [hf, hs, same]
      by_cases next : i + 1 < 2 ^ 64
      · rw [ih (2 ^ 64 - (i + 1)) (by omega) rfl]
      · have far : ¬ i + 1 < 18446744073709551616 := by omega
        simp only [far, dite_false]

/-- The proposer of a slot reads the slot, the RANDAO mixes and the proposer lookahead.

It also reads the active validators of the epoch and their effective balances. -/
private theorem getBeaconProposerIndex_congr {fork : Fork} {s w : BeaconState preset fork}
    (slot : w.slot = s.slot) (mixes : w.randaoMixes = s.randaoMixes)
    (lookahead : ∀ fulu : .fusaka ≤ fork, w.proposerLookahead fulu = s.proposerLookahead fulu)
    (active : getActiveValidatorIndicesChecked w (getCurrentEpoch s) =
      getActiveValidatorIndicesChecked s (getCurrentEpoch s))
    (effective : ∀ j < s.validators.data.size, (s.validators.data[j]?).map (·.effectiveBalance) =
      (w.validators.data[j]?).map (·.effectiveBalance)) :
    getBeaconProposerIndex w = getBeaconProposerIndex s := by
  have epoch : getCurrentEpoch w = getCurrentEpoch s := by simp only [getCurrentEpoch, slot]
  unfold getBeaconProposerIndex
  split
  · rename_i fulu
    simp only [slot, lookahead fulu]
  · have seed : getSeed w (getCurrentEpoch s) DOMAIN_BEACON_PROPOSER =
        getSeed s (getCurrentEpoch s) DOMAIN_BEACON_PROPOSER := by
      unfold getSeed getRandaoMix
      rw [mixes]
    dsimp only
    rw [epoch, seed, active, slot]
    cases checked : getActiveValidatorIndicesChecked s (getCurrentEpoch s) with
    | error => simp only [bind, Except.bind]
    | ok indices =>
      simp only [bind, Except.bind]
      cases getSeed s (getCurrentEpoch s) DOMAIN_BEACON_PROPOSER with
      | error => simp only
      | ok mix =>
        simp only
        unfold computeProposerIndex
        by_cases empty : indices.toArray.size = 0
        · simp [empty, bind, Except.bind, throw, throwThe, MonadExcept.throw,
            MonadExceptOf.throw]
        have inside : ∀ index ∈ indices.toArray, index.toNat < s.validators.data.size := by
          intro index member
          obtain ⟨v, found, _⟩ :=
            (mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mp (by simpa using member)
          exact (Array.getElem?_eq_some_iff.mp found).1
        have positive : 0 < s.validators.data.size := by
          obtain ⟨index, member⟩ := List.exists_mem_of_ne_nil indices
            (fun nil => empty (by simp [nil]))
          exact Nat.lt_of_le_of_lt (Nat.zero_le _) (inside index (by simpa using member))
        simp only [empty, ↓reduceIte]
        rw [proposerSearch_congr_validators positive inside effective]

/-! ## The balance ledger of a block -/

/-- How the balances move from one state to another, read at each validator.

A balance rises by at most its participant sync amount and its other credits.

Off the paid and converted validators, a balance falls by at most the sum of two amounts.

These are its participant sync amount and its slashing penalty.

A converted validator falls only to the activation balance, and then rises by its credits.

Off the converted validators, whether the credentials compound stays.

A converted validator did not compound before, and compounds after. -/
private structure Ledger {fork : Fork} (s t : BeaconState preset fork)
    (paid conv : Finset ValidatorIndex) (sync other slash : ValidatorIndex → ℕ) : Prop where
  up : ∀ v, actualBalanceAt ⟨fork, t⟩ v.toNat ≤
    actualBalanceAt ⟨fork, s⟩ v.toNat + sync v + other v
  down : ∀ v, v ∉ paid → v ∉ conv →
    actualBalanceAt ⟨fork, s⟩ v.toNat ≤ actualBalanceAt ⟨fork, t⟩ v.toNat + sync v + slash v
  converted : ∀ v ∈ conv, actualBalanceAt ⟨fork, t⟩ v.toNat ≤
    preset.MIN_ACTIVATION_BALANCE.toNat + sync v + other v
  lowered : ∀ v ∈ conv, v ∉ paid → min (actualBalanceAt ⟨fork, s⟩ v.toNat)
      preset.MIN_ACTIVATION_BALANCE.toNat ≤ actualBalanceAt ⟨fork, t⟩ v.toNat + sync v + slash v
  kept : ∀ (v : ValidatorIndex) validator, v ∉ conv → s.validators.data[v.toNat]? = some validator →
    ∃ later, t.validators.data[v.toNat]? = some later ∧
      hasCompoundingWithdrawalCredential later = hasCompoundingWithdrawalCredential validator
  fresh : ∀ v ∈ conv, ∀ validator, s.validators.data[v.toNat]? = some validator →
    hasCompoundingWithdrawalCredential validator = false
  switched : ∀ v ∈ conv, ∃ later, t.validators.data[v.toNat]? = some later ∧
    hasCompoundingWithdrawalCredential later = true

private theorem Ledger.trans {fork : Fork} {s u t : BeaconState preset fork}
    {paid conv paid' conv' : Finset ValidatorIndex} {sync other slash sync' other' slash' :
      ValidatorIndex → ℕ}
    (one : Ledger s u paid conv sync other slash)
    (two : Ledger u t paid' conv' sync' other' slash') :
    Ledger s t (paid ∪ paid') (conv ∪ conv') (sync + sync') (other + other') (slash + slash') where
  up v := by have := one.up v; have := two.up v; simp only [Pi.add_apply]; omega
  down v notPaid notConv := by
    simp only [Finset.mem_union, not_or] at notPaid notConv
    have := one.down v notPaid.1 notConv.1
    have := two.down v notPaid.2 notConv.2
    simp only [Pi.add_apply]; omega
  converted v member := by
    simp only [Pi.add_apply]
    rcases Finset.mem_union.mp member with first | second
    · have := one.converted v first; have := two.up v; omega
    · have := two.converted v second; omega
  lowered v member notPaid := by
    simp only [Pi.add_apply]
    simp only [Finset.mem_union, not_or] at notPaid
    -- No validator is converted twice: the first conversion makes it compound.
    have apart : v ∈ conv → v ∉ conv' := by
      intro first second
      obtain ⟨later, found, compounds⟩ := one.switched v first
      rw [two.fresh v second later found] at compounds
      cases compounds
    rcases Finset.mem_union.mp member with first | second
    · have := one.lowered v first notPaid.1
      have := two.down v notPaid.2 (apart first)
      omega
    · have first : v ∉ conv := fun first => apart first second
      have := one.down v notPaid.1 first
      have := two.lowered v second notPaid.2
      omega
  kept v validator notConv found := by
    simp only [Finset.mem_union, not_or] at notConv
    obtain ⟨middle, middleFound, same⟩ := one.kept v validator notConv.1 found
    obtain ⟨later, laterFound, same'⟩ := two.kept v middle notConv.2 middleFound
    exact ⟨later, laterFound, same'.trans same⟩
  fresh v member validator found := by
    rcases Finset.mem_union.mp member with first | second
    · exact one.fresh v first validator found
    · by_cases converted : v ∈ conv
      · exact one.fresh v converted validator found
      · obtain ⟨middle, middleFound, same⟩ := one.kept v validator converted found
        rw [← same]
        exact two.fresh v second middle middleFound
  switched v member := by
    rcases Finset.mem_union.mp member with first | second
    · obtain ⟨middle, middleFound, compounds⟩ := one.switched v first
      by_cases again : v ∈ conv'
      · exact two.switched v again
      · obtain ⟨later, laterFound, same⟩ := two.kept v middle again middleFound
        exact ⟨later, laterFound, same.trans compounds⟩
    · exact two.switched v second

/-- A step that keeps every balance and whether each existing validator compounds. -/
private theorem Ledger.of_kept {fork : Fork} {s t : BeaconState preset fork}
    (balances : t.balances.data = s.balances.data)
    (kept : ∀ (v : ValidatorIndex) validator, s.validators.data[v.toNat]? = some validator →
      ∃ later, t.validators.data[v.toNat]? = some later ∧
        hasCompoundingWithdrawalCredential later = hasCompoundingWithdrawalCredential validator) :
    Ledger s t ∅ ∅ 0 0 0 where
  up v := by simp [actualBalanceAt, balances]
  down v _ _ := by simp [actualBalanceAt, balances]
  converted v member := absurd member (Finset.notMem_empty v)
  lowered v member := absurd member (Finset.notMem_empty v)
  kept v validator _ found := kept v validator found
  fresh v member := absurd member (Finset.notMem_empty v)
  switched v member := absurd member (Finset.notMem_empty v)

/-- A step that keeps every balance and every validator. -/
private theorem Ledger.of_eq {fork : Fork} {s t : BeaconState preset fork}
    (balances : t.balances.data = s.balances.data)
    (validators : t.validators.data = s.validators.data) : Ledger s t ∅ ∅ 0 0 0 :=
  Ledger.of_kept balances fun v validator found =>
    ⟨validator, by rw [validators]; exact found, rfl⟩

private theorem Ledger.refl {fork : Fork} (s : BeaconState preset fork) : Ledger s s ∅ ∅ 0 0 0 :=
  Ledger.of_eq rfl rfl

/-- A ledger with larger sets and amounts. -/
private theorem Ledger.mono {fork : Fork} {s t : BeaconState preset fork}
    {paid conv : Finset ValidatorIndex} {sync other slash other' slash' : ValidatorIndex → ℕ}
    (ledger : Ledger s t paid conv sync other slash) (paid' : Finset ValidatorIndex)
    (morePaid : paid ⊆ paid') (moreOther : ∀ v, other v ≤ other' v)
    (moreSlash : ∀ v, slash v ≤ slash' v) : Ledger s t paid' conv sync other' slash' where
  up v := by have := ledger.up v; have := moreOther v; omega
  down v notPaid notConv := by
    have := ledger.down v (fun member => notPaid (morePaid member)) notConv
    have := moreSlash v; omega
  converted v member := by have := ledger.converted v member; have := moreOther v; omega
  lowered v member notPaid := by
    have := ledger.lowered v member (fun inside => notPaid (morePaid inside))
    have := moreSlash v; omega
  kept := ledger.kept
  fresh := ledger.fresh
  switched := ledger.switched

private theorem Ledger.zero_left {fork : Fork} {s u t : BeaconState preset fork}
    {paid conv : Finset ValidatorIndex} {sync other slash : ValidatorIndex → ℕ}
    (one : Ledger s u ∅ ∅ 0 0 0) (two : Ledger u t paid conv sync other slash) :
    Ledger s t paid conv sync other slash := by
  simpa using one.trans two

private theorem Ledger.zero_right {fork : Fork} {s u t : BeaconState preset fork}
    {paid conv : Finset ValidatorIndex} {sync other slash : ValidatorIndex → ℕ}
    (one : Ledger s u paid conv sync other slash) (two : Ledger u t ∅ ∅ 0 0 0) :
    Ledger s t paid conv sync other slash := by
  simpa using one.trans two

/-- The seats of a validator in the current sync committee: the members that hold its key. -/
private def seatsOf {fork : Fork} (s : BeaconState preset fork) (altair : .altair ≤ fork)
    (v : ValidatorIndex) : ℕ :=
  ((s.currentSyncCommittee altair).value.pubkeys.toList.filter fun key =>
    (s.validators.data[v.toNat]?).any (·.pubkey == key)).length

/-- The total active balance as a number: the active effective balances, at least one increment.

A successful read of `getTotalActiveBalance` returns it (`getTotalActiveBalance_toNat`). -/
private def activeTotal {fork : Fork} (s : BeaconState preset fork) : ℕ :=
  max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (∑ i ∈ (Finset.range s.validators.data.size).filter
        (fun i => isActiveAt s (getCurrentEpoch s) i = true),
      ((s.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0)

/-- Two states agree on the total when they agree on activity and the effective balances. -/
private theorem activeTotal_eq {fork : Fork} {a s : BeaconState preset fork}
    (epoch : getCurrentEpoch s = getCurrentEpoch a)
    (active : ActiveKept (activityFixedEpoch a) a s) (kept : EffectiveKept a s)
    (size : a.validators.data.size ≤ s.validators.data.size) : activeTotal s = activeTotal a := by
  unfold activeTotal
  rw [epoch, activeSum_eq (fun i => active _ (getCurrentEpoch_le_activityFixedEpoch a) i) kept size]

/-- The participant reward of the sync committee, as a number read from the total. -/
private def rewardRead {fork : Fork} (a : BeaconState preset fork) : ℕ :=
  preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat /
      (activeTotal a).sqrt * (activeTotal a / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) *
    SYNC_REWARD_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat / preset.SLOTS_PER_EPOCH.toNat /
      preset.SYNC_COMMITTEE_SIZE.toNat

/-- A read of the base reward per increment at the total of a state. -/
private def PerIncrementRead {fork : Fork} (a : BeaconState preset fork) : Prop :=
  ∃ total perIncrement : Gwei, total.toNat = activeTotal a ∧
    getBaseRewardPerIncrement preset total = .ok perIncrement ∧
    perIncrement.toNat = preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      preset.BASE_REWARD_FACTOR.toNat / total.toNat.sqrt

/-- A successful read of the participant reward is `rewardRead`.

It also reads the base reward per increment at the total. -/
private theorem rewardRead_of_ok {fork : Fork} {a : BeaconState preset fork} {reward : Gwei}
    (computed : syncParticipantReward a = .ok reward) :
    reward.toNat = rewardRead a ∧ PerIncrementRead a := by
  obtain ⟨total, perIncrement, totalOk, perOk, perValue, rewardValue⟩ :=
    syncParticipantReward_ok computed
  have totalValue : total.toNat = activeTotal a := getTotalActiveBalance_toNat totalOk
  refine ⟨?_, total, perIncrement, totalValue, perOk, perValue⟩
  rw [rewardValue, perValue, totalValue]
  rfl

/-! ### Validators later in an epoch -/

section Lives

variable {fork : Fork} {s u t : BeaconState preset fork}

/-- Once the exit of a validator is set, its withdrawable epoch only rises.

It moves only when the later record is slashed.

The states may be of different forks.

Reader: EffectiveRise. -/
def WithdrawableKept {f g : Fork} (s : BeaconState preset f) (t : BeaconState preset g) : Prop :=
  ∀ (i : ℕ) (v w : Validator), s.validators.data[i]? = some v → t.validators.data[i]? = some w →
    v.exitEpoch ≠ FAR_FUTURE_EPOCH →
      v.withdrawableEpoch ≤ w.withdrawableEpoch ∧
        (w.slashed = true ∨ w.withdrawableEpoch = v.withdrawableEpoch)

/-- One validator later inside an epoch keeps its activation epoch.

Once its exit is set, its withdrawable epoch only rises, and moves only when it is slashed.

Its slashed flag and its exit epoch are read from master's frame and lifecycle. -/
private structure Later (old w : Validator) : Prop where
  activation : w.activationEpoch = old.activationEpoch
  withdrawable : old.exitEpoch ≠ FAR_FUTURE_EPOCH →
    old.withdrawableEpoch ≤ w.withdrawableEpoch ∧
      (w.slashed = true ∨ w.withdrawableEpoch = old.withdrawableEpoch)

/-- Every validator is later than itself. -/
private theorem Later.refl (v : Validator) : Later v v :=
  ⟨rfl, fun _ => ⟨UInt64.le_refl _, .inr rfl⟩⟩

/-- The withdrawable epoch of one validator over two steps.

The first step keeps the exit, and the second keeps the slash. -/
private theorem withdrawable_trans {a b c : Validator}
    (one : a.exitEpoch ≠ FAR_FUTURE_EPOCH → a.withdrawableEpoch ≤ b.withdrawableEpoch ∧
      (b.slashed = true ∨ b.withdrawableEpoch = a.withdrawableEpoch))
    (two : b.exitEpoch ≠ FAR_FUTURE_EPOCH → b.withdrawableEpoch ≤ c.withdrawableEpoch ∧
      (c.slashed = true ∨ c.withdrawableEpoch = b.withdrawableEpoch))
    (exit : a.exitEpoch ≠ FAR_FUTURE_EPOCH → b.exitEpoch = a.exitEpoch)
    (slashed : b.slashed = true → c.slashed = true) (far : a.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    a.withdrawableEpoch ≤ c.withdrawableEpoch ∧
      (c.slashed = true ∨ c.withdrawableEpoch = a.withdrawableEpoch) := by
  obtain ⟨le, moved⟩ := one far
  obtain ⟨le', moved'⟩ := two (by rw [exit far]; exact far)
  refine ⟨UInt64.le_trans le le', ?_⟩
  rcases moved' with flag | same'
  · exact .inl flag
  · rcases moved with flag | same
    · exact .inl (slashed flag)
    · exact .inr (same'.trans same)

/-- Two later steps make one, given the exit kept by the first and the slash kept by the second. -/
private theorem Later.trans {a b c : Validator} (one : Later a b) (two : Later b c)
    (exit : a.exitEpoch ≠ FAR_FUTURE_EPOCH → b.exitEpoch = a.exitEpoch)
    (slashed : b.slashed = true → c.slashed = true) : Later a c where
  activation := two.activation.trans one.activation
  withdrawable := withdrawable_trans one.withdrawable two.withdrawable exit slashed

/-- A later registry inside an epoch keeps each old validator later.

Its new validators are not activated. -/
private structure Lives (s t : BeaconState preset fork) : Prop where
  later : ∀ (index : ℕ) old w, s.validators.data[index]? = some old →
    t.validators.data[index]? = some w → Later old w
  fresh : ∀ (index : ℕ) w, s.validators.data[index]? = none →
    t.validators.data[index]? = some w → w.activationEpoch = FAR_FUTURE_EPOCH

/-- The withdrawable epochs of a later registry. -/
private theorem Lives.withdrawableKept (lives : Lives s t) : WithdrawableKept s t :=
  fun i v w found read far => (lives.later i v w found read).withdrawable far

/-- Every state lives on in itself. -/
private theorem Lives.refl (s : BeaconState preset fork) : Lives s s :=
  ⟨fun _ old w found read => by rw [found, Option.some.injEq] at read; exact read ▸ .refl old,
    fun _ _ none found => by rw [none] at found; cases found⟩

/-- Two later registries make one.

The exits of the first come from master's lifecycle.

The slashes of the second come from its frame. -/
private theorem Lives.trans (one : Lives s u) (two : Lives u t) (life : RegistryLifecycle s u)
    (slashed : SlashedPersistence u t) : Lives s t where
  later index old w found read := by
    obtain ⟨middle, middleFound, kept⟩ := life.validators index old found
    exact (one.later index old middle found middleFound).trans
      (two.later index middle w middleFound read) kept.exitEpoch fun flag => by
        obtain ⟨w', read', marked⟩ := slashed index middle middleFound flag
        rw [read, Option.some.injEq] at read'
        exact read' ▸ marked
  fresh index w none found := by
    cases middle : u.validators.data[index]? with
    | none => exact two.fresh index w middle found
    | some m =>
      rw [(two.later index m w middle found).activation]
      exact one.fresh index m none middle

/-- A registry that keeps every old position lives on, when its new validators are not active. -/
private theorem Lives.of_prefix
    (same : ∀ (index : ℕ) old, s.validators.data[index]? = some old →
      t.validators.data[index]? = some old)
    (fresh : ∀ (index : ℕ) w, s.validators.data[index]? = none →
      t.validators.data[index]? = some w → w.activationEpoch = FAR_FUTURE_EPOCH) : Lives s t :=
  ⟨fun index old w found read => by
    rw [same index old found, Option.some.injEq] at read; exact read ▸ .refl old, fresh⟩

/-- A state with the same validators lives on. -/
private theorem Lives.of_data (same : t.validators.data = s.validators.data) : Lives s t :=
  Lives.of_prefix (fun _ _ found => by rw [same]; exact found)
    (fun _ _ none found => by rw [same, none] at found; cases found)

/-- A step before a state with the same validators. -/
private theorem Lives.of_data_left (same : u.validators.data = s.validators.data)
    (two : Lives u t) : Lives s t :=
  ⟨fun index old w found => two.later index old w (by rw [same]; exact found),
    fun index w none => two.fresh index w (by rw [same]; exact none)⟩

/-- A step after a state with the same validators. -/
private theorem Lives.of_data_right (one : Lives s u)
    (same : t.validators.data = u.validators.data) : Lives s t :=
  ⟨fun index old w found read => one.later index old w found (by rw [← same]; exact read),
    fun index w none read => one.fresh index w none (by rw [← same]; exact read)⟩

/-- A fold whose steps live on, keep master's lifecycle and keep each slash, does all three. -/
private theorem Lives.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (each : ∀ a x b, step a x = .ok b →
      Lives a b ∧ RegistryLifecycle a b ∧ SlashedPersistence a b) {items : List α}
    (computed : items.foldlM step s = .ok t) : Lives s t :=
  (foldlM_ok_invariant (fun b => Lives s b ∧ RegistryLifecycle s b)
    (fun _ _ _ before ok => by
      obtain ⟨lives, life, slashed⟩ := each _ _ _ ok
      exact ⟨before.1.trans lives before.2 slashed, before.2.trans life⟩)
    ⟨Lives.refl s, .refl s⟩ computed).1

/-- Replacing a validator, read by its index, by one later than it. -/
private theorem Lives.setValidator {index : ValidatorIndex} {old validator : Validator}
    (found : getValidator s index = .ok old) (set : s.setValidator index validator = .ok t)
    (step : Later old validator) : Lives s t := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  have read : s.validators.data[index.toNat]? = some old := getValidator_eq_ok_iff.mp found
  refine ⟨fun other v w found' read' => ?_, fun other w none read' => ?_⟩
  · simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set] at read'
    split at read'
    · rename_i same
      subst same
      rw [read, Option.some.injEq] at found'
      cases Option.some.inj read'
      exact found' ▸ step
    · rw [found', Option.some.injEq] at read'
      exact read' ▸ .refl v
  · simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set] at read'
    split at read'
    · rename_i same
      subst same
      rw [read] at none
      cases none
    · rw [none] at read'
      cases read'

private theorem lives_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config s index = .ok t) : Lives s t := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨far, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact Lives.refl _
  · have same := (exitQueue_validators queue).1
    exact Lives.of_data_left (by rw [same]) <|
      Lives.setValidator ((getValidator_of_validators_eq same index).trans found) set
        ⟨rfl, fun set => absurd far set⟩

private theorem lives_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config s slashedIndex whistleblowerIndex = .ok t) : Lives s t := by
  obtain ⟨exited, validator, withdrawal, marked, _, _, _, _, _, _, _, last, exitedOk,
    found, _, markedOk, _, _, _, lowered, _, _, raised, final, done⟩ := slashValidator_ok computed
  have same := (slashValidator_last (last := last) (after := t) (index := slashedIndex)
    (by subst done; rfl)).1.trans ((increaseBalance_validators final).trans
    ((increaseBalance_validators raised).trans (decreaseBalance_validators lowered)))
  have later : validator.withdrawableEpoch ≤ max validator.withdrawableEpoch withdrawal := by
    rw [UInt64.max_def]
    split
    · assumption
    · exact UInt64.le_refl _
  -- The write marks the validator, so every slash stays.
  have slashed : SlashedPersistence exited marked := by
    obtain ⟨inside, rfl⟩ := setValidator_ok markedOk
    intro j x read flag
    simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set]
    split
    · exact ⟨_, rfl, rfl⟩
    · exact ⟨x, read, flag⟩
  exact ((lives_initiateValidatorExit exitedOk).trans
    (Lives.setValidator found markedOk ⟨rfl, fun _ => ⟨later, .inl rfl⟩⟩)
    (registryLifecycle_initiateValidatorExit exitedOk) slashed).of_data_right
      (congrArg (·.data) same)

private theorem lives_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks s slashing = .ok t) : Lives s t := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact lives_slashValidator slashed

private theorem lives_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    Lives step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact lives_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Lives.refl _

private theorem lives_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks s slashing = .ok t) : Lives s t := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact (foldlM_ok_invariant (fun step => Lives s step.1 ∧ RegistryLifecycle s step.1)
    (fun _ _ _ before ok => ⟨before.1.trans (lives_slashIfSlashable ok) before.2
        (.of_frame (frame_slashIfSlashable ok).toFrame),
      before.2.trans (registryLifecycle_slashIfSlashable ok)⟩)
    (show Lives s (s, false).1 ∧ RegistryLifecycle s (s, false).1 from
      ⟨Lives.refl s, .refl s⟩) folded).1

/-- From Electra a deposit keeps every old validator.

Master's `UnassignedKept` reads the new one. -/
private theorem lives_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (electra : .pectra ≤ fork)
    (computed : processDeposit config checks before s deposit = .ok t) : Lives s t := by
  refine Lives.of_prefix ?_ fun index w none read =>
    (UnassignedKept.processDeposit computed s.validators.data.size (unassignedFrom_size s) index w
      (Nat.le_of_not_lt fun inside => by
        rw [Array.getElem?_eq_getElem inside] at none; cases none) read).1
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  intro index old found
  unfold applyDeposit at applied
  simp only [electra, ↓reduceDIte] at applied
  unfold applyDepositElectra at applied
  split at applied
  · simp only [bind_ok_iff] at applied
    obtain ⟨_, _, applied⟩ := applied
    split at applied
    · simp only [bind_ok_iff, liftAccessor_ok] at applied
      obtain ⟨_, added, pushed⟩ := applied
      obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
      have inside := (Array.getElem?_eq_some_iff.mp found).1
      simpa [addValidatorToRegistry_validators_eq_push added, Array.getElem?_push,
        Nat.ne_of_lt inside] using found
    · cases applied
      exact found
  · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp applied)
    exact found

private theorem lives_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks s signed = .ok t) : Lives s t := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact lives_initiateValidatorExit exited

private theorem lives_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config s electra index validator amount owed = .ok t) :
    Lives s t := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    exact Lives.of_data (by rw [(computeExitEpochAndUpdateChurn_earliest churned).2.1])
  · cases computed
    exact Lives.refl _

private theorem lives_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config s electra request = .ok t) : Lives s t := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact Lives.refl _)
    | exact lives_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact lives_requestPartialWithdrawal computed

private theorem lives_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator s electra index = .ok t) : Lives s t := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨validator, found, _, set, queued⟩ := computed
  exact (Lives.setValidator found set ⟨rfl, fun _ => ⟨UInt64.le_refl _, .inr rfl⟩⟩).of_data_right
    (congrArg (·.data) (queueExcessActiveBalance_validators queued))

private theorem lives_queueConsolidation {electra : .pectra ≤ fork} {sourceIndex : ValidatorIndex}
    {source : Validator} {targetIndex : ValidatorIndex}
    (found : s.validators.data[sourceIndex.toNat]? = some source)
    (far : source.exitEpoch = FAR_FUTURE_EPOCH)
    (computed : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    Lives s t := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at computed
  obtain ⟨⟨churnedState, exitEpoch⟩, churned, withdrawable, _, _, set, _, _, computed⟩ :=
    computed
  simp only [Except.ok.injEq] at computed
  subst computed
  have same := congrArg (·.data) (computeConsolidationEpochAndUpdateChurn_earliest churned).2.1
  exact (Lives.of_data_left same <|
    Lives.setValidator (old := source) (by simp [getValidator, same, found]) set
      ⟨rfl, fun set => absurd far set⟩).of_data_right rfl

private theorem lives_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config s electra request = .ok t) : Lives s t := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact Lives.refl _)
    | exact lives_switchToCompoundingValidator (liftAccessor_ok.mp computed)
    | exact lives_queueConsolidation (getElem?_toNat_of_ofNatChecked (by assumption))
        (by clear computed; simp_all) computed

private theorem lives_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config s body electra = .ok t) : Lives s t := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  -- The deposit requests only queue, so they keep the registry.
  have deposits := foldlM_ok_invariant
    (fun u : BeaconState preset fork => u.validators = s.validators)
    (fun _ _ _ before ok => (processDepositRequest_ok ok).2.1.trans before) rfl depositsOk
  have withdrawals := Lives.foldlM (fun _ _ _ ok => ⟨lives_processWithdrawalRequest ok,
    registryLifecycle_processWithdrawalRequest ok,
    .of_frame (frame_processWithdrawalRequest ok).toFrame⟩)
    withdrawalsOk
  have consolidations := Lives.foldlM (fun _ _ _ ok => ⟨lives_processConsolidationRequest ok,
    registryLifecycle_processConsolidationRequest ok,
    .of_frame (frame_processConsolidationRequest ok).toFrame⟩) consolidationsOk
  exact Lives.of_data_left (congrArg (·.data) deposits) <| withdrawals.trans consolidations
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processWithdrawalRequest ok)
      withdrawalsOk)
    (.of_frame (Frame.foldlM (fun _ _ _ ok => (frame_processConsolidationRequest ok).toFrame)
      consolidationsOk))

/-- A validator that a slashing could still slash at an epoch, or whose exit is unset. -/
private def Eligible (E : Epoch) (w : Validator) : Prop :=
  w.slashed = false ∧ w.activationEpoch ≤ E ∧ E < FAR_FUTURE_EPOCH ∧
    (w.exitEpoch = FAR_FUTURE_EPOCH ∨ E < w.withdrawableEpoch)

/-- A slashable validator is eligible. -/
private theorem eligible_of_slashable {E : Epoch} {w : Validator}
    (slashable : isSlashableValidator w E = true) : Eligible E w := by
  simp only [isSlashableValidator, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
    at slashable
  obtain ⟨⟨unslashed, active⟩, before⟩ := slashable
  refine ⟨unslashed, active, ?_, Or.inr before⟩
  have bound := w.withdrawableEpoch.toNat_lt
  have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  rw [UInt64.lt_iff_toNat_lt] at before ⊢
  omega

/-- An eligible validator of a later registry was eligible before.

Its slashed flag comes from master's frame and its exit epoch from master's lifecycle. -/
private theorem Lives.back (lives : Lives s t) (life : RegistryLifecycle s t)
    (slashed : SlashedPersistence s t) {E : Epoch} {i : ℕ} {w : Validator}
    (found : t.validators.data[i]? = some w) (eligible : Eligible E w) :
    ∃ old, s.validators.data[i]? = some old ∧ Eligible E old := by
  obtain ⟨unslashed, active, below, window⟩ := eligible
  cases read : s.validators.data[i]? with
  | none =>
    have pending := lives.fresh i w read found
    rw [pending] at active
    exact absurd (UInt64.lt_of_le_of_lt active below) (UInt64.lt_irrefl _)
  | some old =>
    have step := lives.later i old w read found
    obtain ⟨later, laterFound, kept⟩ := life.validators i old read
    rw [found] at laterFound
    cases laterFound
    refine ⟨old, rfl, ?_, step.activation ▸ active, below, ?_⟩
    · cases flag : old.slashed
      · rfl
      · obtain ⟨w', read', marked⟩ := slashed i old read flag
        rw [found, Option.some.injEq] at read'
        rw [read', marked] at unslashed; cases unslashed
    · by_cases far : old.exitEpoch = FAR_FUTURE_EPOCH
      · exact Or.inl far
      · right
        rcases window with exitFar | early
        · exact absurd ((kept.exitEpoch far).symm.trans exitFar) far
        · obtain ⟨-, moved⟩ := step.withdrawable far
          rcases moved with flag | same
          · rw [flag] at unslashed; cases unslashed
          · rw [← same]; exact early

end Lives

/-! ### The steps of a block, one by one -/

section Steps

variable {fork : Fork} {s t : BeaconState preset fork}

private theorem ledger_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader s block = .ok t) : Ledger s t ∅ ∅ 0 0 0 := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact Ledger.of_eq rfl rfl

private theorem ledger_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks s body = .ok t) : Ledger s t ∅ ∅ 0 0 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact Ledger.of_eq rfl rfl

private theorem ledger_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before s body = .ok t) : Ledger s t ∅ ∅ 0 0 0 := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  exact Ledger.of_eq (by rw [← rest]) (by rw [← rest])

/-- Applying the expected withdrawals keeps the registry of validators. -/
private theorem applyExpectedWithdrawals_validators {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals s capella expected = .ok t) :
    t.validators = s.validators := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : applied.validators = s.validators := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact foldlM_ok_invariant (fun x : BeaconState preset fork => x.validators = s.validators)
      (fun _ _ _ same ok => by rw [applyWithdrawal_eq ok]; exact same) rfl appliedOk
  have two : indexed.validators = applied.validators := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      rfl
    · cases indexedOk
      rfl
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → finished.validators = kept.validators := by
    intro kept ok
    split at ok
    · unfold updateNextWithdrawalBuilderIndex at ok
      dsimp only at ok
      split at ok
      · cases ok
        rfl
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, rfl⟩ := ok
        rfl
    · cases ok
      rfl
  have three := swept _ sweptOk
  have queued : (if electra : .pectra ≤ fork then
      updatePendingPartialWithdrawals (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals indexed gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else indexed) electra expected.processedPartialWithdrawalsCount
    else if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals indexed gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else indexed).validators = indexed.validators := by
    split <;> split <;> rfl
  have four : t.validators = finished.validators := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last
      rfl
  rw [four, three, queued, two, one]

/-- Before Gloas, the withdrawal step pays only some validators.

These are the validators that the withdrawals of the payload name. -/
private theorem ledger_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)} (early : fork < .glamsterdam)
    (computed : processWithdrawals s capella payload = .ok t) :
    Ledger s t (((payload early).withdrawals capella).data.toList.map (·.validatorIndex)).toFinset
      ∅ 0 0 0 := by
  obtain ⟨expected, -, -, appliedOk⟩ := processWithdrawals_expected early computed
  have validators := applyExpectedWithdrawals_validators appliedOk
  have sizes := (sameSizes_processWithdrawals computed).2
  have balance : ∀ v : ValidatorIndex, actualBalanceAt ⟨fork, t⟩ v.toNat =
      actualBalanceAt ⟨fork, s⟩ v.toNat -
        withdrawnFrom ((payload early).withdrawals capella).data v := by
    intro v
    cases found : s.balances.data[v.toNat]? with
    | none =>
      have missing : t.balances.data[v.toNat]? = none := by
        rw [Array.getElem?_eq_none_iff] at found ⊢
        omega
      simp [actualBalanceAt, found, missing]
    | some balance =>
      have lowered := processWithdrawals_balance early computed found
      cases later : t.balances.data[v.toNat]? <;> simp_all [actualBalanceAt]
  exact {
    up := fun v => by simp only [balance v, Pi.zero_apply]; omega
    down := fun v notPaid _ => by
      rw [balance v, withdrawnFrom_eq_zero fun w member same =>
        notPaid (List.mem_toFinset.mpr (List.mem_map.mpr ⟨w, member, same⟩))]
      simp
    converted := fun v member => absurd member (Finset.notMem_empty v)
    lowered := fun v member => absurd member (Finset.notMem_empty v)
    kept := fun v validator _ found => ⟨validator, by rw [validators]; exact found, rfl⟩
    fresh := fun v member => absurd member (Finset.notMem_empty v)
    switched := fun v member => absurd member (Finset.notMem_empty v) }

/-- The withdrawals of a payload pay at most as many validators as the payload has withdrawals. -/
private theorem ledger_processBlockExecution {engine : ExecutionEngine preset fork}
    {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (early : fork < .glamsterdam)
    (computed : processBlockExecution config checks engine s body bellatrix = .ok t) :
    ∃ paid : Finset ValidatorIndex, Ledger s t paid ∅ 0 0 0 ∧
      paid.card ≤ if .shapella ≤ fork then preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat else 0 := by
  unfold processBlockExecution at computed
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [notGloas, ↓reduceDIte] at computed
  split at computed
  · rename_i capella
    simp only [bind_ok_iff] at computed
    obtain ⟨middle, withdrawnOk, paidOk⟩ := computed
    obtain ⟨-, header, -, rfl⟩ := processExecutionPayload_ok paidOk
    have ledger := (ledger_processWithdrawals early withdrawnOk).trans
      (Ledger.of_eq (t := { middle with latestExecutionPayloadHeader := fun _ => header })
        rfl rfl)
    rw [Finset.union_empty, Finset.union_empty, add_zero] at ledger
    refine ⟨_, ledger, ?_⟩
    simp only [capella, ↓reduceIte]
    refine (List.toFinset_card_le _).trans ?_
    rw [List.length_map, Array.length_toList]
    exact ((body.executionPayload _).withdrawals capella).bound early
  · rename_i capella
    simp only [capella, ↓reduceIte, nonpos_iff_eq_zero, Finset.card_eq_zero, exists_eq_right]
    split at computed
    · obtain ⟨-, header, -, rfl⟩ := processExecutionPayload_ok computed
      exact Ledger.of_eq rfl rfl
    · cases computed
      exact Ledger.refl s

/-- Before Gloas, the execution part of a block keeps the registry. -/
private theorem validators_processBlockExecution {engine : ExecutionEngine preset fork}
    {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (early : fork < .glamsterdam)
    (computed : processBlockExecution config checks engine s body bellatrix = .ok t) :
    t.validators = s.validators := by
  unfold processBlockExecution at computed
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [notGloas, ↓reduceDIte] at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨middle, withdrawnOk, paidOk⟩ := computed
    obtain ⟨-, header, -, rfl⟩ := processExecutionPayload_ok paidOk
    obtain ⟨expected, -, -, appliedOk⟩ := processWithdrawals_expected early withdrawnOk
    have same := applyExpectedWithdrawals_validators appliedOk
    exact same
  · split at computed
    · obtain ⟨-, header, -, rfl⟩ := processExecutionPayload_ok computed
      rfl
    · cases computed
      rfl

/-- A balance increase adds its amount at its own index and keeps every other balance.

Readers: EffectiveRise. -/
theorem actualBalanceAt_increaseBalance {u w : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei} (computed : increaseBalance u index delta = .ok w)
    (j : Nat) : actualBalanceAt ⟨fork, w⟩ j =
      actualBalanceAt ⟨fork, u⟩ j + if index.toNat = j then delta.toNat else 0 := by
  cases found : u.balances.data[j]? with
  | none =>
    obtain ⟨inside, _, rfl⟩ := increaseBalance_eq_ok_iff.mp computed
    have apart : index.toNat ≠ j := by
      rintro rfl
      rw [Array.getElem?_eq_getElem inside] at found
      cases found
    simp [actualBalanceAt, BeaconState.putBalance, found, apart]
  | some balance =>
    obtain ⟨raised, located, value⟩ := balance_increaseBalance computed found
    simp only [actualBalanceAt, found, located, Option.map_some, Option.getD_some, value]

/-- A balance decrease subtracts its amount at its own index and keeps every other balance.

Readers: EffectiveRise. -/
theorem actualBalanceAt_decreaseBalance {u w : BeaconState preset fork}
    {index : ValidatorIndex} {delta : Gwei} (computed : decreaseBalance u index delta = .ok w)
    (j : Nat) : actualBalanceAt ⟨fork, w⟩ j =
      actualBalanceAt ⟨fork, u⟩ j - if index.toNat = j then delta.toNat else 0 := by
  cases found : u.balances.data[j]? with
  | none =>
    obtain ⟨inside, rfl⟩ := decreaseBalance_eq_ok_iff.mp computed
    have apart : index.toNat ≠ j := by
      rintro rfl
      rw [Array.getElem?_eq_getElem inside] at found
      cases found
    simp [actualBalanceAt, BeaconState.putBalance, found, apart]
  | some balance =>
    obtain ⟨lowered, located, value⟩ := balance_decreaseBalance computed found
    simp only [actualBalanceAt, found, located, Option.map_some, Option.getD_some, value]
    split <;> omega

/-- Replace a validator by one with the same credentials.

This keeps the credentials of every validator. -/
private theorem credentials_setValidator {u w : BeaconState preset fork}
    {index : ValidatorIndex} {old new : Validator} (found : getValidator u index = .ok old)
    (set : u.setValidator index new = .ok w)
    (same : new.withdrawalCredentials = old.withdrawalCredentials) (j : ValidatorIndex)
    (before : Validator) (read : getValidator u j = .ok before) :
    ∃ later, getValidator w j = .ok later ∧
      later.withdrawalCredentials = before.withdrawalCredentials := by
  by_cases equal : j = index
  · subst equal
    have := Except.ok.inj (read.symm.trans found)
    subst this
    exact ⟨new, getValidator_setValidator_self set, same⟩
  · exact ⟨before, (getValidator_setValidator_of_ne set equal).trans read, rfl⟩

/-- Slashing a validator keeps the withdrawal credentials of every validator. -/
private theorem credentials_slashValidator {u w : BeaconState preset fork}
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (computed : slashValidator config u index whistleblower = .ok w) (j : ValidatorIndex)
    (before : Validator) (read : u.validators.data[j.toNat]? = some before) :
    ∃ later, w.validators.data[j.toNat]? = some later ∧
      later.withdrawalCredentials = before.withdrawalCredentials := by
  obtain ⟨exited, validator, _, marked, _, _, slashings, lowered, _, _, raised, last, exitOk,
    validatorOk, _, markedOk, _, _, _, loweredOk, _, _, raisedOk, lastOk, done⟩ :=
    slashValidator_ok computed
  have exitedRead : ∃ middle, getValidator exited j = .ok middle ∧
      middle.withdrawalCredentials = before.withdrawalCredentials := by
    obtain ⟨old, found, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
      initiateValidatorExit_ok exitOk
    · exact ⟨before, getValidator_eq_ok_iff.mpr read, rfl⟩
    · have same := getValidator_of_validators_eq (exitQueue_validators queue).1
      exact credentials_setValidator ((same index).trans found) set rfl j before
        ((same j).trans (getValidator_eq_ok_iff.mpr read))
  obtain ⟨middle, middleRead, middleSame⟩ := exitedRead
  obtain ⟨later, laterRead, laterSame⟩ :=
    credentials_setValidator validatorOk markedOk rfl j middle middleRead
  have registry : w.validators = marked.validators := by
    have cancelled := slashValidator_last (last := last) (after := w) (index := index)
      (by subst done; rfl)
    rw [cancelled.1, increaseBalance_validators lastOk, increaseBalance_validators raisedOk,
      decreaseBalance_validators loweredOk]
  refine ⟨later, ?_, laterSame.trans middleSame⟩
  rw [registry]
  exact getValidator_eq_ok_iff.mp laterRead

/-- A state reads the same proposer as an earlier state when it keeps four things of it.

These are the slot, the payload inputs, activity and effective balances. -/
private theorem getBeaconProposerIndex_of_kept {r w : BeaconState preset fork}
    (keeps : StepKeeps r w) (inputs : PayloadInputs r w) (effective : EffectiveKept r w) :
    getBeaconProposerIndex w = getBeaconProposerIndex r := by
  apply getBeaconProposerIndex_congr inputs.slot inputs.randaoMixes
    (fun fulu => by rw [inputs.proposerLookahead])
    (keeps.2.2.getActiveValidatorIndicesChecked_eq (getCurrentEpoch_le_activityFixedEpoch r))
  intro j inside
  have same := effective j inside
  have inside' := Nat.lt_of_lt_of_le inside keeps.1
  simp only [effectiveAt, Array.getElem?_eq_getElem inside, Array.getElem?_eq_getElem inside',
    Option.map_some, Option.getD_some] at same
  rw [Array.getElem?_eq_getElem inside, Array.getElem?_eq_getElem inside', Option.map_some,
    Option.map_some, UInt64.toNat_inj.mp same]

/-- A slashing with the proposer as whistleblower debits the slashed validator its initial penalty.

It credits the whistleblower reward to the proposer that an earlier kept state reads. -/
private theorem ledger_slashValidator {r u w : BeaconState preset fork} {index : ValidatorIndex}
    {validator : Validator} (early : fork < .glamsterdam)
    (keeps : StepKeeps r u) (inputs : PayloadInputs r u) (effective : EffectiveKept r u)
    (found : u.validators.data[index.toNat]? = some validator)
    (computed : slashValidator config u index none = .ok w) :
    ∃ proposer, getBeaconProposerIndex r = .ok proposer ∧
      Ledger u w ∅ ∅ 0
        (fun v => if v = proposer then validator.effectiveBalance.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0)
        (fun v => if v = index then validator.effectiveBalance.toNat /
          (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0) := by
  obtain ⟨exited, current, _, marked, _, _, slashings, lowered, proposer, reward, raised, last,
    exitOk, currentOk, _, markedOk, _, _, _, lowerOk, proposerOk, share, raiseOk, lastOk,
    final⟩ := slashValidator_ok computed
  have inside : index.toNat < u.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
  have sameEffective : current.effectiveBalance = validator.effectiveBalance := by
    have kept := effectiveKept_exit exitOk index.toNat inside
    simp only [effectiveAt, getValidator_eq_ok_iff.mp currentOk, found, Option.map_some,
      Option.getD_some] at kept
    exact UInt64.toNat_inj.mp kept
  -- The proposer is read after the exit, the slashed mark, the slashings write and the debit.
  have exitGrows := (frame_initiateValidatorExit exitOk).registryGrows
  have markedSize := (sameSizes_setValidator markedOk).1
  have keepsLowered : StepKeeps r lowered :=
    ((keeps.trans (stepKeeps_initiateValidatorExit exitOk)).trans
      ((stepKeeps_setValidator currentOk (fun _ _ => by rfl) markedOk).trans
        (StepKeeps.of_validators (state := marked) (after := { marked with slashings })))).trans
      (stepKeeps_decreaseBalance lowerOk)
  have inputsLowered : PayloadInputs r lowered :=
    ((inputs.trans (payloadInputs_initiateValidatorExit exitOk)).trans
      ((payloadInputs_setValidator markedOk).trans
        (⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ :
          PayloadInputs marked { marked with slashings }))).trans
      (payloadInputs_decreaseBalance lowerOk)
  have effectiveLowered : EffectiveKept r lowered :=
    effectiveKept_trans effective
      (effectiveKept_trans
        (effectiveKept_trans (effectiveKept_exit exitOk)
          (effectiveKept_setValidator currentOk markedOk rfl) exitGrows)
        (effectiveKept_trans (effectiveKept_data (s := marked) (t := { marked with slashings }))
          (effectiveKept_decrease lowerOk) (Nat.le_refl _))
        (exitGrows.trans (Nat.le_of_eq markedSize.symm)))
      keeps.1
  have proposerRead : getBeaconProposerIndex r = .ok proposer := by
    rw [← getBeaconProposerIndex_of_kept keepsLowered inputsLowered effectiveLowered]
    exact proposerOk
  refine ⟨proposer, proposerRead, ?_⟩
  -- The balances move only by the debit and the two credits.
  have exitBalances : exited.balances = u.balances := by
    obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok exitOk
    · rfl
    · obtain ⟨_, rfl⟩ := setValidator_ok set
      exact (exitQueue_validators queue).2
  have markedBalances : marked.balances = u.balances := by
    obtain ⟨_, rfl⟩ := setValidator_ok markedOk
    exact exitBalances
  have shareLe : reward.toNat ≤
      (current.effectiveBalance /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT).toNat := by
    unfold proposerShare at share
    split at share
    · simp only [bind_ok_iff, liftArith, mapError_ok_iff, pure, Except.pure,
        Except.ok.injEq] at share
      obtain ⟨product, productOk, rfl⟩ := share
      have productEq := (mulChecked_ok_iff.mp productOk).2
      rw [UInt64.toNat_div, productEq]
      change _ * 8 / 64 ≤ _
      omega
    · simp only [pure, Except.pure, Except.ok.injEq] at share
      subst reward
      exact Nat.div_le_self _ _
  have leftReward : (current.effectiveBalance /
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT - reward).toNat =
        (current.effectiveBalance /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT).toNat - reward.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr shareLe)
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [notGloas, ↓reduceDIte] at final
  subst w
  have point (v : ValidatorIndex) :
      actualBalanceAt ⟨fork, last⟩ v.toNat =
        (actualBalanceAt ⟨fork, u⟩ v.toNat - if v = index then
          validator.effectiveBalance.toNat /
            (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0) +
          (if v = proposer then reward.toNat else 0) +
          (if v = proposer then validator.effectiveBalance.toNat /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - reward.toNat
            else 0) := by
    rw [actualBalanceAt_increaseBalance lastOk, actualBalanceAt_increaseBalance raiseOk,
      actualBalanceAt_decreaseBalance lowerOk, leftReward]
    have start : actualBalanceAt ⟨fork, { marked with slashings }⟩ v.toNat =
        actualBalanceAt ⟨fork, u⟩ v.toNat := by
      simp only [actualBalanceAt, markedBalances]
    simp only [start, Option.getD_none, UInt64.toNat_inj, eq_comm (a := index),
      eq_comm (a := proposer), UInt64.toNat_div, sameEffective]
  have shareLe' : reward.toNat ≤ validator.effectiveBalance.toNat /
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := by
    simpa only [UInt64.toNat_div, sameEffective] using shareLe
  exact {
    up := fun v => by
      rw [point v]
      simp only [Pi.zero_apply]
      generalize validator.effectiveBalance.toNat /
        (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat = penalty at *
      generalize validator.effectiveBalance.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat = whistle at *
      split_ifs <;> omega
    down := fun v _ _ => by
      rw [point v]
      simp only [Pi.zero_apply]
      generalize validator.effectiveBalance.toNat /
        (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat = penalty at *
      generalize validator.effectiveBalance.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat = whistle at *
      split_ifs <;> omega
    converted := fun v member => absurd member (Finset.notMem_empty v)
    lowered := fun v member => absurd member (Finset.notMem_empty v)
    kept := fun v before _ read => by
      obtain ⟨later, laterRead, same⟩ := credentials_slashValidator computed v before read
      exact ⟨later, laterRead, by simp only [hasCompoundingWithdrawalCredential, same]⟩
    fresh := fun v member => absurd member (Finset.notMem_empty v)
    switched := fun v member => absurd member (Finset.notMem_empty v) }

/-- A proposer slashing debits the slashed validator its initial penalty.

The penalty is read at the effective balance of that validator.

The slashing credits the whistleblower reward to the proposer of the slot. -/
private theorem ledger_processProposerSlashing {slashing : ProposerSlashing}
    (early : fork < .glamsterdam)
    (computed : processProposerSlashing config checks s slashing = .ok t) :
    ∃ (proposer slashed : ValidatorIndex) (validator : Validator),
      getBeaconProposerIndex s = .ok proposer ∧
      s.validators.data[slashed.toNat]? = some validator ∧ validator.slashed = false ∧
      (∃ later, t.validators.data[slashed.toNat]? = some later ∧ later.slashed = true) ∧
      Ledger s t ∅ ∅ 0
        (fun v => if v = proposer then validator.effectiveBalance.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0)
        (fun v => if v = slashed then validator.effectiveBalance.toNat /
          (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0) ∧
      Eligible (getCurrentEpoch s) validator := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, validator, found, _, slashable, _, _, _, _, slashed⟩ := computed
  have read := getValidator_eq_ok_iff.mp found
  obtain ⟨proposer, proposerRead, ledger⟩ := ledger_slashValidator early (StepKeeps.refl s)
    (PayloadInputs.refl s) (effectiveKept_refl s) read slashed
  refine ⟨proposer, _, validator, proposerRead, read, ?_, ?_, ledger,
    eligible_of_slashable slashable⟩
  · simp only [isSlashableValidator, Bool.and_eq_true, Bool.not_eq_true'] at slashable
    exact slashable.1.1
  · have flag := (slashValidator_slashedFlag slashed).1
    cases later : t.validators.data[slashing.signedHeader1.message.proposerIndex.toNat]? with
    | none => simp [slashedFlag, getValidator, later, Except.map] at flag
    | some entry =>
      simp only [slashedFlag, getValidator, later, Except.map, Except.ok.injEq] at flag
      exact ⟨entry, rfl, flag⟩

/-- Take a state that keeps what the proposer of an earlier state reads.

From it, slashing each slashable index of a list in turn debits each slashed validator.

It also credits the proposer of the earlier state. -/
private theorem ledger_foldSlashIfSlashable {r : BeaconState preset fork}
    (early : fork < .glamsterdam) (chosen : ValidatorIndex)
    (choice : ∀ p, getBeaconProposerIndex r = .ok p → p = chosen) :
    ∀ (indices : List ValidatorIndex) {u w : BeaconState preset fork} {flag flag' : Bool},
      StepKeeps r u → PayloadInputs r u → EffectiveKept r u →
      u.validators.data.size = r.validators.data.size →
      indices.foldlM (slashIfSlashable config) (u, flag) = .ok (w, flag') →
      ∃ slashed : Finset ValidatorIndex,
        (slashed.Nonempty → getBeaconProposerIndex r = .ok chosen) ∧
        (∀ v ∈ slashed, ∃ validator later, u.validators.data[v.toNat]? = some validator ∧
          validator.slashed = false ∧ w.validators.data[v.toNat]? = some later ∧
          later.slashed = true) ∧
        (∀ v ∈ slashed, ∃ validator, u.validators.data[v.toNat]? = some validator ∧
          Eligible (getCurrentEpoch r) validator) ∧
        Ledger u w ∅ ∅ 0
          (fun v => if v = chosen then ∑ x ∈ slashed, effectiveAt ⟨fork, r⟩ x.toNat /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0)
          (fun v => if v ∈ slashed then effectiveAt ⟨fork, r⟩ v.toNat /
            (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0)
  | [], u, w, flag, flag', _, _, _, _, ok => by
    cases ok
    refine ⟨∅, fun empty => absurd empty Finset.not_nonempty_empty,
      fun v member => absurd member (Finset.notMem_empty v),
      fun v member => absurd member (Finset.notMem_empty v), ?_⟩
    exact (Ledger.refl u).mono ∅ (subset_refl _) (fun _ => Nat.zero_le _)
      (fun _ => Nat.zero_le _)
  | index :: rest, u, w, flag, flag', keeps, inputs, effective, size, ok => by
    obtain ⟨⟨middle, nextFlag⟩, first, tail⟩ := bind_ok_iff.mp ok
    simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at first
    obtain ⟨validator, found, first⟩ := first
    split at first
    · rename_i slashable
      simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at first
      obtain ⟨next, slashed, rfl, rfl⟩ := first
      have read := getValidator_eq_ok_iff.mp found
      obtain ⟨proposer, proposerRead, one⟩ :=
        ledger_slashValidator early keeps inputs effective read slashed
      rw [choice proposer proposerRead] at one proposerRead
      obtain ⟨set, _, marks, eligibles, two⟩ := ledger_foldSlashIfSlashable early chosen choice rest
        (keeps.trans (stepKeeps_slashValidator slashed))
        (inputs.trans (payloadInputs_slashValidator slashed))
        (effectiveKept_trans effective (effectiveKept_slash slashed) keeps.1)
        ((sameSizes_slashValidator slashed).1.trans size) tail
      have flagNext := slashValidator_slashedFlag slashed
      -- Each later member is unslashed when its fold starts, while this index is slashed by now.
      have fresh : index ∉ set := by
        intro member
        obtain ⟨entry, _, entryRead, entrySlashed, _⟩ := marks index member
        have marked := flagNext.1
        simp [slashedFlag, getValidator, entryRead, Except.map, entrySlashed] at marked
      have unslashed : validator.slashed = false := by
        simp only [isSlashableValidator, Bool.and_eq_true, Bool.not_eq_true'] at slashable
        exact slashable.1.1
      have effectiveIndex : effectiveAt ⟨fork, r⟩ index.toNat =
          validator.effectiveBalance.toNat := by
        rw [← effective index.toNat (size ▸ (Array.getElem?_eq_some_iff.mp read).1)]
        simp [effectiveAt, read]
      refine ⟨insert index set, fun _ => proposerRead, ?_, ?_, ?_⟩
      · intro v member
        rcases Finset.mem_insert.mp member with rfl | inside
        · have persist := (foldlM_slashIfSlashable rest tail).2.1 v flagNext.1
          cases later : w.validators.data[v.toNat]? with
          | none => simp [slashedFlag, getValidator, later, Except.map] at persist
          | some entry =>
            simp only [slashedFlag, getValidator, later, Except.map, Except.ok.injEq] at persist
            exact ⟨validator, entry, read, unslashed, rfl, persist⟩
        · obtain ⟨entry, later, entryRead, entrySlashed, laterRead, laterSlashed⟩ :=
            marks v inside
          have apart : v ≠ index := fun equal => fresh (equal ▸ inside)
          have before := flagNext.2 v.toNat (fun equal => apart (UInt64.toNat_inj.mp equal))
          cases old : u.validators.data[v.toNat]? with
          | none => simp [slashedFlagAt, old, entryRead] at before
          | some original =>
            simp [slashedFlagAt, old, entryRead, entrySlashed] at before
            exact ⟨original, later, rfl, before, laterRead, laterSlashed⟩
      · intro v member
        rcases Finset.mem_insert.mp member with rfl | inside
        · refine ⟨validator, read, ?_⟩
          have epoch : getCurrentEpoch u = getCurrentEpoch r := by
            simp only [getCurrentEpoch, keeps.2.1]
          rw [← epoch]
          exact eligible_of_slashable slashable
        · obtain ⟨entry, entryRead, entryEligible⟩ := eligibles v inside
          exact (lives_slashValidator slashed).back (registryLifecycle_slashValidator slashed)
            (.of_frame (frame_slashValidator slashed).toFrame) entryRead entryEligible
      · have both := one.trans two
        rw [add_zero] at both
        refine both.mono ∅ (subset_refl _) (fun v => ?_) (fun v => ?_)
        · simp only [Pi.add_apply, Finset.sum_insert fresh, effectiveIndex]
          split_ifs <;> omega
        · simp only [Pi.add_apply, Finset.mem_insert]
          by_cases equal : v = index
          · subst equal
            simp [fresh, effectiveIndex]
          · simp [equal]
    · cases first
      exact ledger_foldSlashIfSlashable early chosen choice rest keeps inputs effective size tail

/-- An attester slashing slashes some validators, each not slashed before.

It debits each its initial penalty and credits the whistleblower rewards to the proposer. -/
private theorem ledger_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (early : fork < .glamsterdam)
    (computed : processAttesterSlashing config checks s slashing = .ok t) :
    ∃ (proposer : ValidatorIndex) (slashed : Finset ValidatorIndex),
      (slashed.Nonempty → getBeaconProposerIndex s = .ok proposer) ∧
      (∀ v ∈ slashed, ∃ validator later, s.validators.data[v.toNat]? = some validator ∧
        validator.slashed = false ∧ t.validators.data[v.toNat]? = some later ∧
        later.slashed = true) ∧
      (∀ v ∈ slashed, ∃ validator, s.validators.data[v.toNat]? = some validator ∧
        Eligible (getCurrentEpoch s) validator) ∧
      Ledger s t ∅ ∅ 0
        (fun v => if v = proposer then ∑ x ∈ slashed, effectiveAt ⟨fork, s⟩ x.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0)
        (fun v => if v ∈ slashed then effectiveAt ⟨fork, s⟩ v.toNat /
          (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0) := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨u, flag⟩, folded, _, _, rfl⟩ := computed
  obtain ⟨chosen, choice⟩ : ∃ chosen : ValidatorIndex,
      ∀ p, getBeaconProposerIndex s = .ok p → p = chosen := by
    cases read : getBeaconProposerIndex s with
    | ok p => exact ⟨p, fun q found => (Except.ok.inj found).symm⟩
    | error _ => exact ⟨0, fun q found => by cases found⟩
  obtain ⟨slashed, nonempty, marks, eligibles, ledger⟩ :=
    ledger_foldSlashIfSlashable early chosen choice _
      (StepKeeps.refl s) (PayloadInputs.refl s) (effectiveKept_refl s) rfl folded
  exact ⟨chosen, slashed, nonempty, marks, eligibles, ledger⟩

/-- A step that keeps every validator, lowers no balance and raises each by at most its credit. -/
private theorem Ledger.of_rise {other : ValidatorIndex → ℕ}
    (validators : t.validators.data = s.validators.data)
    (rise : ∀ v : ValidatorIndex, actualBalanceAt ⟨fork, s⟩ v.toNat ≤
      actualBalanceAt ⟨fork, t⟩ v.toNat ∧
      actualBalanceAt ⟨fork, t⟩ v.toNat ≤ actualBalanceAt ⟨fork, s⟩ v.toNat + other v) :
    Ledger s t ∅ ∅ 0 other 0 where
  up v := by have := (rise v).2; simp only [Pi.zero_apply]; omega
  down v _ _ := by have := (rise v).1; simp only [Pi.zero_apply]; omega
  converted v member := absurd member (Finset.notMem_empty v)
  lowered v member := absurd member (Finset.notMem_empty v)
  kept v validator _ found := ⟨validator, by rw [validators]; exact found, rfl⟩
  fresh v member := absurd member (Finset.notMem_empty v)
  switched v member := absurd member (Finset.notMem_empty v)

/-- Take a step that keeps the registry or appends one validator.

If it moves each balance by at most a credit, it gives a ledger with only that credit. -/
private theorem Ledger.of_append {credit : ValidatorIndex → ℕ}
    (validators : t.validators.data = s.validators.data ∨
      ∃ added, t.validators.data = s.validators.data.push added)
    (balances : ∀ v : ValidatorIndex,
      actualBalanceAt ⟨fork, t⟩ v.toNat ≤ actualBalanceAt ⟨fork, s⟩ v.toNat + credit v ∧
      actualBalanceAt ⟨fork, s⟩ v.toNat ≤ actualBalanceAt ⟨fork, t⟩ v.toNat) :
    Ledger s t ∅ ∅ 0 credit 0 where
  up v := by have := (balances v).1; simp only [Pi.zero_apply]; omega
  down v _ _ := by have := (balances v).2; simp only [Pi.zero_apply]; omega
  converted v member := absurd member (Finset.notMem_empty v)
  lowered v member := absurd member (Finset.notMem_empty v)
  kept v validator _ found := by
    refine ⟨validator, ?_, rfl⟩
    rcases validators with same | ⟨added, pushed⟩
    · rw [same]; exact found
    · rw [pushed, Array.getElem?_push]
      have inside := (Array.getElem?_eq_some_iff.mp found).1
      rw [ite_eq_right_iff.mpr (fun h => absurd h (Nat.ne_of_lt inside))]
      exact found
  fresh v member := absurd member (Finset.notMem_empty v)
  switched v member := absurd member (Finset.notMem_empty v)

/-- Appending a balance keeps every balance below and reads the new one at the end. -/
private theorem actualBalanceAt_push {balance : Gwei}
    (pushed : t.balances.data = s.balances.data.push balance) (i : ℕ) :
    actualBalanceAt ⟨fork, t⟩ i = if i = s.balances.data.size then balance.toNat
      else actualBalanceAt ⟨fork, s⟩ i := by
  simp only [actualBalanceAt, pushed, Array.getElem?_push]
  split
  · simp
  · rfl

/-- From Electra a deposit moves no balance, since it only queues the amount.

A new validator gets a zero balance, which reads like no balance.

The balances must match the validators, so that a new validator gets a new balance. -/
private theorem ledger_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (electra : .pectra ≤ fork) (matched : BalancesMatch s)
    (computed : processDeposit config checks before s deposit = .ok t) :
    Ledger s t ∅ ∅ 0 0 0 := by
  obtain ⟨-, -, next, -, applied⟩ := processDeposit_ok computed
  generalize hs' : { s with eth1DepositIndex := fun _ => next } = s' at applied
  have balances' : s'.balances = s.balances := by rw [← hs']
  have validators' : s'.validators = s.validators := by rw [← hs']
  have matched' : BalancesMatch s' := by
    unfold BalancesMatch at matched ⊢; rw [balances', validators']; exact matched
  have actual' (i : ℕ) : actualBalanceAt ⟨fork, s'⟩ i = actualBalanceAt ⟨fork, s⟩ i := by
    simp only [actualBalanceAt, balances']
  unfold applyDeposit at applied
  simp only [electra, ↓reduceDIte] at applied
  unfold applyDepositElectra at applied
  split at applied
  · simp only [bind_ok_iff] at applied
    obtain ⟨_, _, applied⟩ := applied
    split at applied
    · simp only [bind_ok_iff, liftAccessor_ok] at applied
      obtain ⟨registered, added, queued⟩ := applied
      obtain ⟨_, queuedEq⟩ := addPendingDeposit_eq queued
      obtain ⟨validatorsPushed, balancesPushed⟩ := addValidatorToRegistry_push added matched'
      have finalBalances : t.balances.data = s'.balances.data.push 0 := by
        rw [queuedEq]; exact balancesPushed
      refine Ledger.of_append (.inr ⟨_, by rw [queuedEq, ← validators']; exact validatorsPushed⟩)
        fun v => ?_
      -- An appended zero balance reads like no balance.
      have zero : actualBalanceAt ⟨fork, t⟩ v.toNat = actualBalanceAt ⟨fork, s⟩ v.toNat := by
        rw [actualBalanceAt_push finalBalances, ← actual' v.toNat]
        split
        · rename_i at_end
          simp [actualBalanceAt, at_end]
        · rfl
      exact ⟨by simp [zero], by omega⟩
    · cases applied
      exact Ledger.of_append (.inl (by rw [validators'])) fun v => by
        have := actual' v.toNat; exact ⟨by simp; omega, by omega⟩
  · obtain ⟨_, queuedEq⟩ := addPendingDeposit_eq (liftAccessor_ok.mp applied)
    have finalBalances : t.balances = s'.balances := by rw [queuedEq]
    exact Ledger.of_append (.inl (by rw [queuedEq, validators'])) fun v => by
      have := actual' v.toNat
      simp only [actualBalanceAt, finalBalances] at this ⊢
      exact ⟨by simp; omega, by omega⟩

/-- Writing a validator that compounds exactly when the old one did moves no balance. -/
private theorem Ledger.setValidator {i : ValidatorIndex} {old new : Validator}
    (found : getValidator s i = .ok old)
    (same : hasCompoundingWithdrawalCredential new = hasCompoundingWithdrawalCredential old)
    (set : s.setValidator i new = .ok t) : Ledger s t ∅ ∅ 0 0 0 := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  have read := getValidator_eq_ok_iff.mp found
  refine Ledger.of_kept rfl fun v validator located => ?_
  by_cases eq : v.toNat = i.toNat
  · rw [eq, read, Option.some.injEq] at located
    subst located
    exact ⟨new, by simp [BeaconState.putValidator, eq], same⟩
  · exact ⟨validator, by simpa [BeaconState.putValidator, Ne.symm eq] using located, rfl⟩

/-- The start of an exit moves no balance, and keeps the credentials. -/
private theorem Ledger.exit {i : ValidatorIndex}
    (computed : initiateValidatorExit config s i = .ok t) : Ledger s t ∅ ∅ 0 0 0 := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact Ledger.refl _
  · have same := exitQueue_validators queue
    have one : Ledger s queued ∅ ∅ 0 0 0 := Ledger.of_eq (by rw [same.2]) (by rw [same.1])
    have two := Ledger.setValidator (old := validator)
      (by rw [getValidator_of_validators_eq same.1]; exact found) (by rfl) set
    simpa only [Finset.empty_union, add_zero] using one.trans two

private theorem ledger_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks s signed = .ok t) : Ledger s t ∅ ∅ 0 0 0 := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact Ledger.exit exited

/-- A fold whose every step moves no balance and keeps the credentials does the same. -/
private theorem Ledger.foldlM {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)} {items : List α}
    (kept : ∀ u x u', step u x = .ok u' → Ledger u u' ∅ ∅ 0 0 0)
    (computed : items.foldlM step s = .ok t) : Ledger s t ∅ ∅ 0 0 0 :=
  foldlM_ok_invariant (fun u => Ledger s u ∅ ∅ 0 0 0)
    (fun _ _ _ before ok => by
      simpa only [Finset.empty_union, add_zero] using before.trans (kept _ _ _ ok))
    (Ledger.refl s) computed

private theorem ledger_processBlsToExecutionChanges {body : BeaconBlockBody preset fork}
    (computed : processBlsToExecutionChanges config checks s body = .ok t) :
    Ledger s t ∅ ∅ 0 0 0 := by
  unfold processBlsToExecutionChanges at computed
  split at computed
  · rw [← Array.foldlM_toList] at computed
    refine Ledger.foldlM (fun u signed u' ok => ?_) computed
    obtain ⟨validator, found, bls, _, _, set⟩ := processBlsToExecutionChange_ok ok
    -- Credentials of either prefix do not compound.
    refine Ledger.setValidator found ?_ set
    simp [hasCompoundingWithdrawalCredential, isCompoundingWithdrawalCredential, bls,
      executionCredentials_prefix, BLS_WITHDRAWAL_PREFIX, ETH1_ADDRESS_WITHDRAWAL_PREFIX,
      COMPOUNDING_WITHDRAWAL_PREFIX]
  · cases computed
    exact Ledger.refl _

/-- Queueing the excess caps one balance at the activation balance, and keeps the registry. -/
private theorem queueExcessActiveBalance_capped {electra : .pectra ≤ fork} {i : ValidatorIndex}
    (computed : queueExcessActiveBalance s electra i = .ok t) :
    t.validators.data = s.validators.data ∧ ∀ j, actualBalanceAt ⟨fork, t⟩ j =
      if j = i.toNat then min (actualBalanceAt ⟨fork, s⟩ j) preset.MIN_ACTIVATION_BALANCE.toNat
      else actualBalanceAt ⟨fork, s⟩ j := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨balance, read, computed⟩ := computed
  rw [getBalance_eq_ok_iff] at read
  split at computed
  · rename_i above
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
    obtain ⟨inside, rfl⟩ := setBalance_ok set
    have := UInt64.lt_iff_toNat_lt.mp above
    refine ⟨rfl, fun j => ?_⟩
    by_cases eq : j = i.toNat
    · subst eq
      simp [actualBalanceAt, BeaconState.putBalance, read]
      omega
    · simp [actualBalanceAt, BeaconState.putBalance, eq, Ne.symm eq]
  · rename_i below
    cases computed
    have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp below)
    refine ⟨rfl, fun j => ?_⟩
    by_cases eq : j = i.toNat
    · subst eq
      simp [actualBalanceAt, read]
      omega
    · simp [eq]

/-- A switch to compounding converts one validator that did not compound before. -/
private theorem Ledger.switch {electra : .pectra ≤ fork} {i : ValidatorIndex}
    {validator : Validator}
    (found : s.validators.data[i.toNat]? = some validator)
    (fresh : hasCompoundingWithdrawalCredential validator = false)
    (computed : switchToCompoundingValidator s electra i = .ok t) : Ledger s t ∅ {i} 0 0 0 := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨old, read, _, set, queued⟩ := computed
  rw [getValidator_eq_ok_iff, found, Option.some.injEq] at read
  subst read
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  obtain ⟨same, capped⟩ := queueExcessActiveBalance_capped queued
  have balances : ∀ j, actualBalanceAt ⟨fork, t⟩ j = if j = i.toNat then
      min (actualBalanceAt ⟨fork, s⟩ j) preset.MIN_ACTIVATION_BALANCE.toNat
      else actualBalanceAt ⟨fork, s⟩ j := capped
  have apart {v : ValidatorIndex} (notConv : v ∉ ({i} : Finset ValidatorIndex)) :
      v.toNat ≠ i.toNat := fun eq =>
    notConv (Finset.mem_singleton.mpr (UInt64.toNat_inj.mp eq))
  constructor
  · intro v
    rw [balances]
    split <;> simp
  · intro v _ notConv
    simp [balances, apart notConv]
  · intro v member
    rw [Finset.mem_singleton.mp member, balances]
    simp
  · intro v member _
    rw [Finset.mem_singleton.mp member, balances]
    simp
  · intro v validator' notConv located
    exact ⟨validator', by
      simpa [same, BeaconState.putValidator, Ne.symm (apart notConv)] using located, rfl⟩
  · intro v member validator' located
    rw [Finset.mem_singleton.mp member, found, Option.some.injEq] at located
    exact located ▸ fresh
  · intro v member
    rw [Finset.mem_singleton.mp member, same]
    simp [BeaconState.putValidator, hasCompoundingWithdrawalCredential,
      isCompoundingWithdrawalCredential]

/-- Queueing a consolidation moves no balance, and keeps the credentials. -/
private theorem Ledger.consolidate {electra : .pectra ≤ fork}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (found : s.validators.data[sourceIndex.toNat]? = some source)
    (computed : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    Ledger s t ∅ ∅ 0 0 0 := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, Base.Uint64.addChecked_ok_iff, pure, Except.pure] at computed
  obtain ⟨⟨churned, epoch⟩, churn, _, _, marked, set, pending, _, computed⟩ := computed
  simp only [Except.ok.injEq] at computed
  subst computed
  have same := computeConsolidationEpochAndUpdateChurn_earliest churn
  have one : Ledger s churned ∅ ∅ 0 0 0 := Ledger.of_eq (by rw [same.2.2]) (by rw [same.2.1])
  have two := Ledger.setValidator (old := source)
    (by rw [getValidator_eq_ok_iff, same.2.1]; exact found) (by rfl) set
  simpa only [Finset.empty_union, add_zero] using (one.trans two).trans
    (Ledger.of_eq (t := { marked with pendingConsolidations := fun _ => pending }) rfl rfl)

/-- A consolidation request converts at most one validator, and moves no other balance. -/
private theorem ledger_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config s electra request = .ok t) :
    ∃ conv : Finset ValidatorIndex, Ledger s t ∅ conv 0 0 0 ∧ conv.card ≤ 1 := by
  -- A validator valid for a switch has the execution address prefix, so it does not compound.
  have fresh : ∀ validator, isValidSwitchToCompoundingRequest s request validator = true →
      hasCompoundingWithdrawalCredential validator = false := by
    intro validator valid
    simp only [isValidSwitchToCompoundingRequest, hasEth1WithdrawalCredential, Bool.and_eq_true,
      beq_iff_eq] at valid
    simp [hasCompoundingWithdrawalCredential, isCompoundingWithdrawalCredential, valid.1.1.2,
      ETH1_ADDRESS_WITHDRAWAL_PREFIX, COMPOUNDING_WITHDRAWAL_PREFIX]
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals try first
    | (cases computed; done)
    | (cases computed; exact ⟨∅, Ledger.refl _, by simp⟩)
  · rename_i checked valid
    exact ⟨_, Ledger.switch (getElem?_toNat_of_ofNatChecked checked) (fresh _ valid)
      (liftAccessor_ok.mp computed), (Finset.card_singleton _).le⟩
  · rename_i checked _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    exact ⟨∅, Ledger.consolidate (getElem?_toNat_of_ofNatChecked checked) computed, by simp⟩

/-- The requests of the execution layer convert at most one validator per consolidation request.

They move no other balance. -/
private theorem ledger_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config s body electra = .ok t) :
    ∃ conv : Finset ValidatorIndex, Ledger s t ∅ conv 0 0 0 ∧
      conv.card ≤ preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨deposited, deposits, withdrawn, withdrawals, consolidations⟩ := computed
  have one : Ledger s deposited ∅ ∅ 0 0 0 := Ledger.foldlM (fun _ _ _ ok =>
    Ledger.of_eq (by rw [(processDepositRequest_ok ok).2.2.1])
      (by rw [(processDepositRequest_ok ok).2.1])) deposits
  have two : Ledger deposited withdrawn ∅ ∅ 0 0 0 := by
    refine Ledger.foldlM (fun _ _ _ ok => ?_) withdrawals
    unfold processWithdrawalRequest at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    repeat' split at ok
    all_goals try first
      | (cases ok; done)
      | (cases ok; exact Ledger.refl _)
      | exact Ledger.exit (liftAccessor_ok.mp ok)
    -- A partial withdrawal only spends exit churn and queues the withdrawal.
    simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at ok
    obtain ⟨_, _, _, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
      obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
      have same := computeExitEpochAndUpdateChurn_earliest churned
      exact Ledger.of_eq (by rw [same.2.2]) (by rw [same.2.1])
    · cases ok
      exact Ledger.refl _
  -- Each consolidation request converts at most one validator.
  have three : ∀ (requests : List ConsolidationRequest) (u : BeaconState preset fork),
      requests.foldlM (processConsolidationRequest config · electra.1 ·) u = .ok t →
      ∃ conv : Finset ValidatorIndex, Ledger u t ∅ conv 0 0 0 ∧ conv.card ≤ requests.length := by
    intro requests
    induction requests with
    | nil =>
      intro u ok
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at ok
      exact ⟨∅, ok ▸ Ledger.refl u, by simp⟩
    | cons request rest ih =>
      intro u ok
      rw [List.foldlM_cons, bind_ok_iff] at ok
      obtain ⟨middle, first, others⟩ := ok
      obtain ⟨conv, ledger, card⟩ := ledger_processConsolidationRequest first
      obtain ⟨conv', ledger', card'⟩ := ih middle others
      refine ⟨conv ∪ conv', ?_, ?_⟩
      · simpa only [Finset.empty_union, add_zero] using ledger.trans ledger'
      have := Finset.card_union_le conv conv'
      simp only [List.length_cons]
      omega
  obtain ⟨conv, ledger, card⟩ := three _ _ consolidations
  have bound := (body.executionRequests electra).consolidations.bound electra.2
  refine ⟨conv, ?_, ?_⟩
  · simpa only [Finset.empty_union, add_zero] using (one.trans two).trans ledger
  simp only [Array.length_toList] at card
  omega

/-- The sync aggregate step keeps the registry and the current sync committee. -/
private theorem processSyncAggregate_kept {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks s altair aggregate = .ok t) :
    t.validators = s.validators ∧ t.currentSyncCommittee = s.currentSyncCommittee := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine foldlM_ok_invariant (fun x : BeaconState preset fork =>
    x.validators = s.validators ∧ x.currentSyncCommittee = s.currentSyncCommittee)
    (fun _ _ _ held ok => ?_) ⟨rfl, rfl⟩ folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    obtain ⟨_, set⟩ := increaseBalance_ok raised
    obtain ⟨_, rfl⟩ := setBalance_ok set
    obtain ⟨_, set'⟩ := increaseBalance_ok paid
    obtain ⟨_, rfl⟩ := setBalance_ok set'
    exact held
  · obtain ⟨_, set⟩ := decreaseBalance_ok (liftAccessor_ok.mp ok)
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact held

/-- Each member index found for a list of keys stands for one of those keys.

Its validator holds that key. -/
private theorem countP_validatorIndexOfPubkey_le (v : ValidatorIndex) :
    ∀ {keys : List Cryptography.Bls.BLSPubkey} {members : List ValidatorIndex},
      keys.mapM (validatorIndexOfPubkey s) = .ok members →
      members.countP (fun m => m.toNat = v.toNat) ≤
        (keys.filter fun key => (s.validators.data[v.toNat]?).any (·.pubkey == key)).length
  | [], members, ok => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at ok
    subst ok
    simp
  | key :: keys, members, ok => by
    obtain ⟨m, rest, head, tail, rfl⟩ := mapM_cons_ok.mp ok
    have ih := countP_validatorIndexOfPubkey_le v tail
    by_cases same : m.toNat = v.toNat
    · have holds : (s.validators.data[v.toNat]?).any (·.pubkey == key) = true := by
        unfold validatorIndexOfPubkey at head
        split at head
        · rename_i position found
          simp only [liftAccessor_ok, liftArith, mapError_ok_iff] at head
          have position_eq := (Base.Uint64.ofNatChecked_ok_iff.mp head).2
          obtain ⟨inside, matching, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp found
          rw [← same, position_eq, Array.getElem?_eq_getElem inside]
          simpa using matching
        · cases head
      simp only [List.countP_cons, same, decide_true, ↓reduceIte, List.filter_cons, holds,
        List.length_cons]
      omega
    · simp only [List.countP_cons, same, decide_false, Bool.false_eq_true, ↓reduceIte,
        Nat.add_zero, List.filter_cons]
      split <;> (try simp only [List.length_cons]) <;> omega

/-- In the fold of the sync rewards, a balance moves by at most the reward for each seat.

These seats are the seats of its validator.

When that validator is the proposer, the bound adds the proposer share for each signed seat. -/
private theorem foldl_syncReward_bounds (r p : ℕ) (chosen : ValidatorIndex) (j : ℕ) :
    ∀ (members : List (ValidatorIndex × Bool)) (b : ℕ),
      members.foldl (fun balance member =>
          if member.2 then balance + (if member.1.toNat = j then r else 0) +
            (if chosen.toNat = j then p else 0)
          else if member.1.toNat = j then balance - r else balance) b ≤
        b + r * members.countP (fun m => m.1.toNat = j) +
          (if chosen.toNat = j then p * members.countP (·.2) else 0) ∧
      b ≤ members.foldl (fun balance member =>
          if member.2 then balance + (if member.1.toNat = j then r else 0) +
            (if chosen.toNat = j then p else 0)
          else if member.1.toNat = j then balance - r else balance) b +
        r * members.countP (fun m => m.1.toNat = j)
  | [], b => by simp
  | ⟨index, signed⟩ :: members, b => by
    obtain ⟨up, down⟩ := foldl_syncReward_bounds r p chosen j members
      (if signed then b + (if index.toNat = j then r else 0) +
        (if chosen.toNat = j then p else 0)
      else if index.toNat = j then b - r else b)
    simp only [List.foldl_cons, List.countP_cons]
    cases signed <;> by_cases h1 : index.toNat = j <;> by_cases h2 : chosen.toNat = j <;>
      simp only [h1, h2, Bool.false_eq_true, decide_true, decide_false, ↓reduceIte,
        Nat.mul_add, Nat.mul_one, Nat.add_zero] at up down ⊢ <;>
      omega

/-- The sync aggregate pays each member the participant reward for each seat it signed.

It charges each member for each seat it did not sign.

The proposer of the slot earns its share for each signed seat, which no participant amount counts.
-/
private theorem ledger_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks s altair aggregate = .ok t) :
    ∃ (proposer : ValidatorIndex) (reward : Gwei) (share : ℕ) (sync : ValidatorIndex → ℕ),
      syncParticipantReward s = .ok reward ∧
      (0 < share → getBeaconProposerIndex s = .ok proposer) ∧
      share ≤ preset.SYNC_COMMITTEE_SIZE.toNat *
        (reward.toNat * PROPOSER_WEIGHT.toNat /
          (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat)) ∧
      (∀ v, sync v ≤ seatsOf t altair v * reward.toNat) ∧
      Ledger s t ∅ ∅ sync (fun v => if v = proposer then share else 0) 0 := by
  obtain ⟨reward, proposerReward, members, chosen, rewardOk, proposerValue, membersOk, signed,
    balances⟩ := processSyncAggregate_balance computed
  have kept := processSyncAggregate_kept computed
  have sizes := (sameSizes_processSyncAggregate computed).2
  obtain ⟨pairs, pairsDef⟩ :
      ∃ pairs, pairs = (members.zip aggregate.syncCommitteeBits.bits.toArray).toList := ⟨_, rfl⟩
  rw [← pairsDef] at signed balances
  have membersSize := (array_mapM_ok membersOk).1
  rw [Vector.size_toArray] at membersSize
  have pairsLength : pairs.length ≤ preset.SYNC_COMMITTEE_SIZE.toNat := by
    rw [pairsDef, Array.length_toList, Array.size_zip]
    exact (Nat.min_le_left _ _).trans membersSize.le
  refine ⟨chosen, reward, proposerReward.toNat * pairs.countP (·.2),
    fun v => reward.toNat * pairs.countP (fun m => m.1.toNat = v.toNat), rewardOk, ?_, ?_, ?_, ?_⟩
  · intro positive
    apply signed
    have count : 0 < pairs.countP (·.2) :=
      Nat.pos_of_ne_zero fun zero => by simp [zero] at positive
    obtain ⟨member, member_in, holds⟩ := List.countP_pos_iff.mp count
    exact ⟨member, member_in, by simpa using holds⟩
  · rw [← proposerValue, Nat.mul_comm]
    exact Nat.mul_le_mul_right _ ((List.countP_le_length).trans pairsLength)
  · intro v
    dsimp only
    rw [Nat.mul_comm (seatsOf t altair v)]
    apply Nat.mul_le_mul_left
    rw [Array.mapM_eq_mapM_toList] at membersOk
    cases listed : (s.currentSyncCommittee altair).value.pubkeys.toArray.toList.mapM
        (validatorIndexOfPubkey s) with
    | error => rw [listed] at membersOk; cases membersOk
    | ok list =>
      rw [listed] at membersOk
      have same : list.toArray = members := Except.ok.inj membersOk
      subst same
      -- The first entries of the pairs are a prefix of the members.
      have zipped : ((list.zip aggregate.syncCommitteeBits.bits.toArray.toList).countP
          fun m => decide (m.1.toNat = v.toNat)) ≤
          list.countP fun m => decide (m.toNat = v.toNat) := by
        have firsts : List.Sublist
            ((list.zip aggregate.syncCommitteeBits.bits.toArray.toList).map Prod.fst) list := by
          rw [List.zip_eq_zip_take_min, List.map_fst_zip (by simp)]
          exact List.take_sublist _ _
        simpa [List.countP_map, Function.comp_def] using firsts.countP_le
          (p := fun m : ValidatorIndex => decide (m.toNat = v.toNat))
      have seats := countP_validatorIndexOfPubkey_le v listed
      rw [pairsDef, Array.toList_zip]
      simp only [seatsOf, kept.1, kept.2]
      exact zipped.trans seats
  · have bounds := fun v : ValidatorIndex =>
      foldl_syncReward_bounds reward.toNat proposerReward.toNat chosen v.toNat pairs
    have equal : ∀ v : ValidatorIndex, chosen.toNat = v.toNat ↔ v = chosen :=
      fun v => ⟨fun h => (UInt64.toNat_inj.mp h).symm, fun h => h ▸ rfl⟩
    have moved : ∀ v : ValidatorIndex,
        actualBalanceAt ⟨fork, t⟩ v.toNat ≤ actualBalanceAt ⟨fork, s⟩ v.toNat +
          reward.toNat * pairs.countP (fun m => m.1.toNat = v.toNat) +
          (if v = chosen then proposerReward.toNat * pairs.countP (·.2) else 0) ∧
        actualBalanceAt ⟨fork, s⟩ v.toNat ≤ actualBalanceAt ⟨fork, t⟩ v.toNat +
          reward.toNat * pairs.countP (fun m => m.1.toNat = v.toNat) := by
      intro v
      cases found : s.balances.data[v.toNat]? with
      | none =>
        have missing : t.balances.data[v.toNat]? = none := by
          rw [Array.getElem?_eq_none_iff] at found ⊢
          omega
        simp [actualBalanceAt, found, missing]
      | some balance =>
        obtain ⟨final, finalFound, finalValue⟩ := balances v.toNat balance found
        obtain ⟨up, down⟩ := bounds v balance.toNat
        rw [← finalValue] at up down
        simp only [actualBalanceAt, found, finalFound, Option.map_some, Option.getD_some]
        by_cases isChosen : v = chosen
        · subst isChosen
          simp only [↓reduceIte] at up ⊢
          exact ⟨up, down⟩
        · simp only [isChosen, ↓reduceIte, Nat.add_zero] at up ⊢
          simp only [mt (equal v).mp isChosen, ↓reduceIte, Nat.add_zero] at up
          exact ⟨up, down⟩
    exact {
      up := fun v => (moved v).1
      down := fun v _ _ => by have := (moved v).2; simp only [Pi.zero_apply]; omega
      converted := fun v member => absurd member (Finset.notMem_empty v)
      lowered := fun v member => absurd member (Finset.notMem_empty v)
      kept := fun v validator _ found => ⟨validator, by rw [kept.1]; exact found, rfl⟩
      fresh := fun v member => absurd member (Finset.notMem_empty v)
      switched := fun v member => absurd member (Finset.notMem_empty v) }

end Steps

/-! ### The participation flags behind the proposer rewards of attestations -/

/-- The weight of the flags that a byte of participation flags has set. -/
private def flagWeight (flags : ParticipationFlags) : ℕ :=
  ((List.finRange PARTICIPATION_FLAG_WEIGHTS.length).map fun flag =>
    if hasFlag flags flag.val.toUInt64 then PARTICIPATION_FLAG_WEIGHTS[flag].toNat else 0).sum

/-- The flags of both epochs at the first positions, each weighed by a base reward. -/
private def flagPotential {fork : Fork} (s : BeaconState preset fork) (altair : .altair ≤ fork)
    (base : ℕ → ℕ) (count : ℕ) : ℕ :=
  ∑ i ∈ Finset.range count, base i *
    (flagWeight (((s.previousEpochParticipation altair).data[i]?).getD 0) +
      flagWeight (((s.currentEpochParticipation altair).data[i]?).getD 0))

/-- No flag is cleared, in either epoch. -/
private def FlagsGrow {fork : Fork} (s t : BeaconState preset fork) : Prop :=
  ∀ (altair : .altair ≤ fork) (i : ℕ) (flag : Fin PARTICIPATION_FLAG_WEIGHTS.length),
    (hasFlag (((s.previousEpochParticipation altair).data[i]?).getD 0) flag.val.toUInt64 = true →
      hasFlag (((t.previousEpochParticipation altair).data[i]?).getD 0) flag.val.toUInt64 = true) ∧
    (hasFlag (((s.currentEpochParticipation altair).data[i]?).getD 0) flag.val.toUInt64 = true →
      hasFlag (((t.currentEpochParticipation altair).data[i]?).getD 0) flag.val.toUInt64 = true)

private theorem FlagsGrow.refl {fork : Fork} (s : BeaconState preset fork) : FlagsGrow s s :=
  fun _ _ _ => ⟨id, id⟩

private theorem FlagsGrow.trans {fork : Fork} {s u t : BeaconState preset fork}
    (one : FlagsGrow s u) (two : FlagsGrow u t) : FlagsGrow s t :=
  fun altair i flag => ⟨fun set => (two altair i flag).1 ((one altair i flag).1 set),
    fun set => (two altair i flag).2 ((one altair i flag).2 set)⟩

/-- Flags that grow raise the potential. -/
private theorem flagPotential_mono {fork : Fork} {s t : BeaconState preset fork}
    (grow : FlagsGrow s t) (altair : .altair ≤ fork) (base : ℕ → ℕ) (count : ℕ) :
    flagPotential s altair base count ≤ flagPotential t altair base count := by
  unfold flagPotential
  apply Finset.sum_le_sum
  intro i _
  apply Nat.mul_le_mul_left
  have weight (a b : ParticipationFlags)
      (more : ∀ flag : Fin PARTICIPATION_FLAG_WEIGHTS.length,
        hasFlag a flag.val.toUInt64 = true → hasFlag b flag.val.toUInt64 = true) :
      flagWeight a ≤ flagWeight b := by
    unfold flagWeight
    apply List.sum_le_sum
    intro flag _
    by_cases set : hasFlag a flag.val.toUInt64 = true
    · simp [set, more flag set]
    · simp only [Bool.not_eq_true] at set
      simp [set]
  exact Nat.add_le_add (weight _ _ fun flag => (grow altair i flag).1)
    (weight _ _ fun flag => (grow altair i flag).2)

/-- No flag of an existing validator is cleared, in either epoch. -/
private def FlagsGrowBelow {fork : Fork} (s t : BeaconState preset fork) : Prop :=
  ∀ (altair : .altair ≤ fork) (i : ℕ) (flag : Fin PARTICIPATION_FLAG_WEIGHTS.length),
    i < s.validators.data.size →
    (hasFlag (((s.previousEpochParticipation altair).data[i]?).getD 0) flag.val.toUInt64 = true →
      hasFlag (((t.previousEpochParticipation altair).data[i]?).getD 0) flag.val.toUInt64 = true) ∧
    (hasFlag (((s.currentEpochParticipation altair).data[i]?).getD 0) flag.val.toUInt64 = true →
      hasFlag (((t.currentEpochParticipation altair).data[i]?).getD 0) flag.val.toUInt64 = true)

private theorem FlagsGrow.below {fork : Fork} {s t : BeaconState preset fork}
    (grow : FlagsGrow s t) : FlagsGrowBelow s t := fun altair i flag _ => grow altair i flag

private theorem FlagsGrowBelow.trans {fork : Fork} {s u t : BeaconState preset fork}
    (one : FlagsGrowBelow s u) (two : FlagsGrowBelow u t)
    (grows : s.validators.data.size ≤ u.validators.data.size) : FlagsGrowBelow s t :=
  fun altair i flag inside =>
    ⟨fun set => (two altair i flag (Nat.lt_of_lt_of_le inside grows)).1
        ((one altair i flag inside).1 set),
      fun set => (two altair i flag (Nat.lt_of_lt_of_le inside grows)).2
        ((one altair i flag inside).2 set)⟩

/-- Flags of existing validators that grow raise a potential weighed on existing validators. -/
private theorem flagPotential_mono_below {fork : Fork} {s t : BeaconState preset fork}
    (grow : FlagsGrowBelow s t) (altair : .altair ≤ fork) (base : ℕ → ℕ) (count : ℕ)
    (support : ∀ i, s.validators.data.size ≤ i → base i = 0) :
    flagPotential s altair base count ≤ flagPotential t altair base count := by
  unfold flagPotential
  apply Finset.sum_le_sum
  intro i _
  by_cases inside : i < s.validators.data.size
  · apply Nat.mul_le_mul_left
    have weight (a b : ParticipationFlags)
        (more : ∀ flag : Fin PARTICIPATION_FLAG_WEIGHTS.length,
          hasFlag a flag.val.toUInt64 = true → hasFlag b flag.val.toUInt64 = true) :
        flagWeight a ≤ flagWeight b := by
      unfold flagWeight
      apply List.sum_le_sum
      intro flag _
      by_cases set : hasFlag a flag.val.toUInt64 = true
      · simp [set, more flag set]
      · simp only [Bool.not_eq_true] at set
        simp [set]
    exact Nat.add_le_add (weight _ _ fun flag => (grow altair i flag inside).1)
      (weight _ _ fun flag => (grow altair i flag inside).2)
  · rw [support i (Nat.le_of_not_lt inside)]
    simp

section Grow

variable {fork : Fork} {s t : BeaconState preset fork}

/-- A step that keeps both lists of flags clears no flag. -/
private theorem FlagsGrow.of_eq
    (previous : t.previousEpochParticipation = s.previousEpochParticipation := by rfl)
    (current : t.currentEpochParticipation = s.currentEpochParticipation := by rfl) :
    FlagsGrow s t := fun _ _ _ => by
  rw [previous, current]
  exact ⟨id, id⟩

/-- A fold whose every step clears no flag clears no flag. -/
private theorem FlagsGrow.foldlM {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (grow : ∀ u x u', step u x = .ok u' → FlagsGrow u u') {items : List α}
    (computed : items.foldlM step s = .ok t) : FlagsGrow s t :=
  foldlM_ok_invariant (FlagsGrow s) (fun _ _ _ before ok => before.trans (grow _ _ _ ok))
    (FlagsGrow.refl s) computed

/-- A balance increase clears no flag. -/
private theorem grow_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance s index delta = .ok t) : FlagsGrow s t := by
  obtain ⟨_, set⟩ := increaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact FlagsGrow.of_eq

/-- A balance decrease clears no flag. -/
private theorem grow_decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance s index delta = .ok t) : FlagsGrow s t := by
  obtain ⟨_, set⟩ := decreaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact FlagsGrow.of_eq

/-- A validator write clears no flag. -/
private theorem grow_setValidator {index : ValidatorIndex} {validator : Validator}
    (computed : s.setValidator index validator = .ok t) : FlagsGrow s t := by
  obtain ⟨_, rfl⟩ := setValidator_ok computed
  exact FlagsGrow.of_eq

/-- The exit queue clears no flag. -/
private theorem grow_exitQueue {exitBalance : Gwei} {exitEpoch : Epoch}
    (computed : exitQueue config s exitBalance = .ok (t, exitEpoch)) : FlagsGrow s t := by
  unfold exitQueue at computed
  split at computed
  · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := computed
    exact FlagsGrow.of_eq
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, rfl, _⟩ := computed
    exact FlagsGrow.refl _

/-- Starting an exit clears no flag. -/
private theorem grow_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config s index = .ok t) : FlagsGrow s t := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok computed
  · exact FlagsGrow.refl _
  · exact (grow_exitQueue queue).trans (grow_setValidator set)

/-- Slashing a validator clears no flag. -/
private theorem grow_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config s slashedIndex whistleblowerIndex = .ok t) :
    FlagsGrow s t := by
  obtain ⟨_, _, _, marked, _, _, slashings, _, _, _, _, last, exitedOk, -, -, markedOk, -, -, -,
    loweredOk, -, -, raisedOk, lastOk, done⟩ := slashValidator_ok computed
  refine (grow_initiateValidatorExit exitedOk).trans <| (grow_setValidator markedOk).trans <|
    (FlagsGrow.of_eq (s := marked) (t := { marked with slashings })).trans <|
    (grow_decreaseBalance loweredOk).trans <| (grow_increaseBalance raisedOk).trans <|
    (grow_increaseBalance lastOk).trans ?_
  subst done
  split
  · exact FlagsGrow.of_eq
  · exact FlagsGrow.refl _

private theorem grow_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader s block = .ok t) : FlagsGrow s t := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact FlagsGrow.of_eq

/-- One withdrawal clears no flag. -/
private theorem grow_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal s withdrawal = .ok t) : FlagsGrow s t := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact FlagsGrow.of_eq
  · exact grow_decreaseBalance computed

/-- The withdrawals that a block expects clear no flag. -/
private theorem grow_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals s capella expected = .ok t) : FlagsGrow s t := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : FlagsGrow s applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact FlagsGrow.foldlM (fun _ _ _ ok => grow_applyWithdrawal ok) appliedOk
  have two : FlagsGrow applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact FlagsGrow.of_eq
    · cases indexedOk
      exact FlagsGrow.refl _
  have queued : ∀ kept : BeaconState preset fork,
      FlagsGrow kept (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals kept gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact FlagsGrow.of_eq
    · exact FlagsGrow.refl _
  have partials : ∀ kept : BeaconState preset fork,
      FlagsGrow kept (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals kept electra expected.processedPartialWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact FlagsGrow.of_eq
    · exact FlagsGrow.refl _
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → FlagsGrow kept finished := by
    intro kept ok
    split at ok
    · unfold updateNextWithdrawalBuilderIndex at ok
      dsimp only at ok
      split at ok
      · cases ok
        exact FlagsGrow.of_eq
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, rfl⟩ := ok
        exact FlagsGrow.of_eq
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ FlagsGrow.refl _
  have final : FlagsGrow finished t := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last
      exact FlagsGrow.of_eq
  exact one.trans <| two.trans <| (queued _).trans <| (partials _).trans <|
    (swept _ sweptOk).trans final

/-- The withdrawals of a block clear no flag. -/
private theorem grow_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals s capella payload = .ok t) : FlagsGrow s t := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact grow_applyExpectedWithdrawals applied
    · cases computed
      exact FlagsGrow.refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact grow_applyExpectedWithdrawals applied

/-- The execution payload of a block clears no flag. -/
private theorem grow_processExecutionPayload {engine : ExecutionEngine preset fork}
    {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine s body bellatrix = .ok t) :
    FlagsGrow s t := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  exact FlagsGrow.of_eq

private theorem grow_processBlockExecution {engine : ExecutionEngine preset fork}
    {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (early : fork < .glamsterdam)
    (computed : processBlockExecution config checks engine s body bellatrix = .ok t) :
    FlagsGrow s t := by
  unfold processBlockExecution at computed
  split at computed
  · exact absurd early (Nat.not_lt_of_le (by assumption))
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (grow_processWithdrawals withdrawnOk).trans (grow_processExecutionPayload paid)
  · dsimp only at computed
    split at computed
    · exact grow_processExecutionPayload computed
    · cases computed
      exact FlagsGrow.refl _

private theorem grow_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks s body = .ok t) : FlagsGrow s t := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact FlagsGrow.of_eq

private theorem grow_processEth1Data {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before s body = .ok t) : FlagsGrow s t := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  rw [← rest]
  exact FlagsGrow.of_eq

private theorem grow_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks s slashing = .ok t) : FlagsGrow s t := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact grow_slashValidator slashed

/-- Slashing a validator if it is slashable clears no flag. -/
private theorem grow_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    FlagsGrow step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact grow_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ FlagsGrow.refl _

private theorem grow_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks s slashing = .ok t) : FlagsGrow s t := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step : BeaconState preset fork × Bool => FlagsGrow s step.1)
    (fun _ _ _ before ok => FlagsGrow.trans before (grow_slashIfSlashable ok))
    (show FlagsGrow s (s, false).1 from FlagsGrow.refl s) folded

/-- Adding a flag that was not set adds its weight. -/
private theorem flagWeight_addFlag {flags : ParticipationFlags}
    {added : Fin PARTICIPATION_FLAG_WEIGHTS.length}
    (unset : hasFlag flags added.val.toUInt64 = false) :
    flagWeight (addFlag flags added.val.toUInt64) =
      flagWeight flags + PARTICIPATION_FLAG_WEIGHTS[added].toNat := by
  have self := hasFlag_addFlag flags added.val.toUInt64
  have other : ∀ flag : Fin PARTICIPATION_FLAG_WEIGHTS.length, flag ≠ added →
      hasFlag (addFlag flags added.val.toUInt64) flag.val.toUInt64 =
        hasFlag flags flag.val.toUInt64 := fun _ different => hasFlag_addFlag_of_ne flags different
  unfold flagWeight
  have range : List.finRange PARTICIPATION_FLAG_WEIGHTS.length =
      [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩] := by decide
  rw [range]
  match added with
  | ⟨0, _⟩ =>
    have one := other ⟨1, by decide⟩ (by simp)
    have two := other ⟨2, by decide⟩ (by simp)
    simp only at self one two unset
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, self, one, two, unset]
    simp only [ite_true, ite_false, Bool.false_eq_true]
    omega
  | ⟨1, _⟩ =>
    have zero := other ⟨0, by decide⟩ (by simp)
    have two := other ⟨2, by decide⟩ (by simp)
    simp only at self zero two unset
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, self, zero, two, unset]
    simp only [ite_true, ite_false, Bool.false_eq_true]
    omega
  | ⟨2, _⟩ =>
    have zero := other ⟨0, by decide⟩ (by simp)
    have one := other ⟨1, by decide⟩ (by simp)
    simp only at self zero one unset
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, self, zero, one, unset]
    simp only [ite_true, ite_false, Bool.false_eq_true]
    omega

/-- Setting the flags of one attester clears none of them.

Weighed by its base reward, the flags gain at least the added numerator. -/
private theorem foldlM_addFlagReward_grow {total : Gwei} {earned : List UInt64}
    {index : ValidatorIndex} {base : ℕ} :
    ∀ {flagList : List (Fin PARTICIPATION_FLAG_WEIGHTS.length)} {flags flags' : ParticipationFlags}
      {numerator numerator' : Gwei},
      flagList.foldlM (addFlagReward s total earned index) (flags, numerator) =
        .ok (flags', numerator') →
      (∀ flag : Fin PARTICIPATION_FLAG_WEIGHTS.length, hasFlag flags flag.val.toUInt64 = true →
        hasFlag flags' flag.val.toUInt64 = true) ∧
      ((∀ reward, getBaseReward s total index = .ok reward → reward.toNat = base) →
        numerator'.toNat + base * flagWeight flags ≤ numerator.toNat + base * flagWeight flags')
  | [], flags, flags', numerator, numerator', computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨rfl, rfl⟩ := computed
    exact ⟨fun _ => id, fun _ => Nat.le_refl _⟩
  | flag :: flagList, flags, flags', numerator, numerator', computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨⟨middleFlags, middle⟩, stepped, folded⟩ := computed
    obtain ⟨kept, gained⟩ := foldlM_addFlagReward_grow folded
    simp only [addFlagReward] at stepped
    split at stepped
    · rename_i newly
      simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff, pure, Except.pure,
        Except.ok.injEq, Prod.mk.injEq] at stepped
      obtain ⟨reward, rewardOk, weighted, weightedOk, added, addedOk, rfl, rfl⟩ := stepped
      rw [mulChecked_ok_iff] at weightedOk
      rw [addChecked_ok_iff] at addedOk
      refine ⟨fun other set => kept other ?_, fun reads => ?_⟩
      · by_cases same : other = flag
        · subst same
          exact hasFlag_addFlag _ _
        · rw [hasFlag_addFlag_of_ne _ same]
          exact set
      have more := gained reads
      have weight := flagWeight_addFlag newly.2
      rw [weight] at more
      rw [addedOk.2, weightedOk.2, reads reward rewardOk] at more
      rw [Nat.mul_add] at more
      omega
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at stepped
      obtain ⟨rfl, rfl⟩ := stepped
      exact ⟨kept, gained⟩

/-- Setting the flags of attesters in turn clears none of them.

Suppose that each attester is in range and that its weight is its base reward.

Then the weighed flags gain at least the added numerator. -/
private theorem foldlM_addAttesterFlags_grow {total : Gwei} {earned : List UInt64}
    {base : ℕ → ℕ} {count : ℕ} :
    ∀ {attesters : List ValidatorIndex}
      {participation participation' : EpochParticipation preset fork}
      {numerator numerator' : Gwei},
      attesters.foldlM (addAttesterFlags s total earned) (participation, numerator) =
        .ok (participation', numerator') →
      (∀ (i : ℕ) (flag : Fin PARTICIPATION_FLAG_WEIGHTS.length),
        hasFlag ((participation.data[i]?).getD 0) flag.val.toUInt64 = true →
          hasFlag ((participation'.data[i]?).getD 0) flag.val.toUInt64 = true) ∧
      ((∀ attester ∈ attesters, attester.toNat < count ∧
          ∀ reward, getBaseReward s total attester = .ok reward →
            reward.toNat = base attester.toNat) →
        numerator'.toNat + ∑ i ∈ Finset.range count,
            base i * flagWeight ((participation.data[i]?).getD 0) ≤
          numerator.toNat + ∑ i ∈ Finset.range count,
            base i * flagWeight ((participation'.data[i]?).getD 0))
  | [], participation, participation', numerator, numerator', computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨rfl, rfl⟩ := computed
    exact ⟨fun _ _ => id, fun _ => Nat.le_refl _⟩
  | attester :: attesters, participation, participation', numerator, numerator', computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨⟨middle, middleNumerator⟩, stepped, folded⟩ := computed
    obtain ⟨kept, gained⟩ := foldlM_addAttesterFlags_grow (base := base) (count := count) folded
    unfold addAttesterFlags at stepped
    dsimp only at stepped
    split at stepped
    · rename_i inside
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at stepped
      obtain ⟨⟨flags, raised⟩, loop, written, rfl⟩ := stepped
      subst written
      obtain ⟨flagsKept, flagsGained⟩ :=
        foldlM_addFlagReward_grow (base := base attester.toNat) loop
      have read : ∀ i, (((participation.data.set attester.toNat flags inside)[i]?).getD 0) =
          if i = attester.toNat then flags else (participation.data[i]?).getD 0 := by
        intro i
        by_cases same : i = attester.toNat
        · subst same
          simp [inside]
        · simp [Ne.symm same, same]
      have own : (participation.data[attester.toNat]?).getD 0 =
          participation.data[attester.toNat] := by
        rw [Array.getElem?_eq_getElem inside]
        rfl
      refine ⟨fun i flag set => ?_, fun facts => ?_⟩
      · apply kept i flag
        dsimp only
        rw [read i]
        split
        · rename_i same
          subst same
          rw [own] at set
          exact flagsKept flag set
        · exact set
      · obtain ⟨below, reads⟩ := facts attester List.mem_cons_self
        have rest := gained fun later member => facts later (List.mem_cons_of_mem _ member)
        have step := flagsGained reads
        have member : attester.toNat ∈ Finset.range count := Finset.mem_range.mpr below
        dsimp only at rest
        have others : ∑ i ∈ (Finset.range count).erase attester.toNat,
            base i * flagWeight
              (((participation.data.set attester.toNat flags inside)[i]?).getD 0) =
            ∑ i ∈ (Finset.range count).erase attester.toNat,
              base i * flagWeight ((participation.data[i]?).getD 0) := by
          apply Finset.sum_congr rfl
          intro i erased
          rw [read i, ite_eq_right_iff.mpr fun same => absurd same (Finset.ne_of_mem_erase erased)]
        have after := (Finset.add_sum_erase _ (fun i => base i * flagWeight
          (((participation.data.set attester.toNat flags inside)[i]?).getD 0)) member).symm
        have before := (Finset.add_sum_erase _ (fun i => base i * flagWeight
          ((participation.data[i]?).getD 0)) member).symm
        rw [others, read attester.toNat] at after
        simp only [↓reduceIte] at after
        rw [own] at before
        omega
    · cases stepped

private theorem grow_processAttestation {attestation : Attestation preset fork} {parent : Slot}
    (early : fork < .glamsterdam)
    (computed : processAttestation config checks s parent attestation = .ok t) :
    FlagsGrow s t := by
  unfold processAttestation at computed
  split at computed
  · simp only [processAttestationAltair, bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      ⟨updated, numerator⟩, folded, _, _, raised, raisedOk, final⟩ := computed
    have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
    simp only [notGloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at final
    subst final
    obtain ⟨kept, -⟩ := foldlM_addAttesterFlags_grow (base := fun _ => 0) (count := 0) folded
    refine FlagsGrow.trans (fun _ i flag => ?_) (grow_increaseBalance raisedOk)
    unfold setEpochParticipation
    split
    · rename_i current
      simp only [current, ↓reduceIte] at kept
      exact ⟨id, kept i flag⟩
    · rename_i current
      simp only [current, Bool.false_eq_true, ↓reduceIte] at kept
      exact ⟨kept i flag, id⟩
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept
  all_goals
    obtain ⟨_, rest⟩ := kept
    rw [← rest]
    exact FlagsGrow.of_eq

/-- A new validator clears no flag of an existing validator. -/
private theorem growBelow_addValidatorToRegistry {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry s pubkey withdrawalCredentials amount = .ok t) :
    FlagsGrowBelow s t := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨index, indexOk, _, _, _, _, previous, previousOk, current, currentOk, _, _, rfl⟩ :=
      computed
    have atEnd := (getIndexForNewValidator_ok_iff.mp indexOk).2
    intro _ i _ inside
    have other : i ≠ index.toNat := by omega
    refine ⟨fun set => ?_, fun set => ?_⟩
    · dsimp only
      simpa only [setOrAppendList_getElem? previousOk, other, ↓reduceIte] using set
    · dsimp only
      simpa only [setOrAppendList_getElem? currentOk, other, ↓reduceIte] using set
  split at computed
  · cases computed
    exact (FlagsGrow.of_eq).below
  · cases computed

/-- A step that clears no flag of an existing validator, and never shrinks the registry. -/
private def Grows (s t : BeaconState preset fork) : Prop :=
  FlagsGrowBelow s t ∧ s.validators.data.size ≤ t.validators.data.size

/-- The steps of an epoch that `EpochFrameLaws` names clear no flag of an existing validator. -/
private theorem growsLaws : EpochFrameLaws (@Grows preset fork) where
  refl s := ⟨(FlagsGrow.refl s).below, Nat.le_refl _⟩
  trans one two := ⟨one.1.trans two.1 one.2, Nat.le_trans one.2 two.2⟩
  setValidatorAt set _ _ _ _ _ := by
    have size := Nat.le_of_eq (sameSizes_setValidatorAt set).1.symm
    obtain ⟨_, rfl⟩ := setValidatorAt_ok set
    exact ⟨(FlagsGrow.of_eq).below, size⟩
  increaseBalance ok := ⟨(grow_increaseBalance ok).below, (frame_increaseBalance ok).registryGrows⟩
  decreaseBalance ok := ⟨(grow_decreaseBalance ok).below, (frame_decreaseBalance ok).registryGrows⟩
  initiateValidatorExit ok :=
    ⟨(grow_initiateValidatorExit ok).below, (frame_initiateValidatorExit ok).registryGrows⟩
  addValidatorToRegistry ok fresh :=
    ⟨growBelow_addValidatorToRegistry ok, (frame_addValidatorToRegistry ok fresh).registryGrows⟩
  eth1DataVotes _ _ := ⟨(FlagsGrow.of_eq).below, Nat.le_refl _⟩
  inactivityScores _ _ := ⟨(FlagsGrow.of_eq).below, Nat.le_refl _⟩
  slashings _ _ := ⟨(FlagsGrow.of_eq).below, Nat.le_refl _⟩
  randaoMixes _ _ := ⟨(FlagsGrow.of_eq).below, Nat.le_refl _⟩
  historicalRoots _ _ := ⟨(FlagsGrow.of_eq).below, Nat.le_refl _⟩
  historicalSummaries _ _ := ⟨(FlagsGrow.of_eq).below, Nat.le_refl _⟩
  participationRecords _ := ⟨(FlagsGrow.of_eq).below, Nat.le_refl _⟩
  pendingDeposits _ _ _ := ⟨(FlagsGrow.of_eq).below, Nat.le_refl _⟩
  pendingConsolidations _ _ := ⟨(FlagsGrow.of_eq).below, Nat.le_refl _⟩
  syncCommittees _ _ _ := ⟨(FlagsGrow.of_eq).below, Nat.le_refl _⟩
  proposerLookahead _ _ := ⟨(FlagsGrow.of_eq).below, Nat.le_refl _⟩
  ptcWindow _ _ := ⟨(FlagsGrow.of_eq).below, Nat.le_refl _⟩

/-- A deposit clears no flag of an existing validator.

A new validator writes its zero flags at the position after the registry.

That position may already hold flags when the lists are longer than the registry. -/
private theorem grow_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before s deposit = .ok t) : FlagsGrowBelow s t := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact FlagsGrowBelow.trans (u := { s with eth1DepositIndex := fun _ => next })
    (FlagsGrow.of_eq).below (growsLaws.applyDeposit applied).1 (Nat.le_refl _)

/-- A deposit request clears no flag. -/
private theorem grow_processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (computed : processDepositRequest s electra request = .ok t) : FlagsGrow s t := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := s) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact FlagsGrow.of_eq

/-- The churn of exits clears no flag. -/
private theorem grow_computeExitEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {exitBalance : Gwei} {epoch : Epoch}
    (computed : computeExitEpochAndUpdateChurn config s electra exitBalance = .ok (t, epoch)) :
    FlagsGrow s t := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact FlagsGrow.of_eq

/-- The churn of consolidations clears no flag. -/
private theorem grow_computeConsolidationEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {balance : Gwei} {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config s electra balance = .ok (t, epoch)) :
    FlagsGrow s t := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact FlagsGrow.of_eq

/-- A partial withdrawal request clears no flag. -/
private theorem grow_requestPartialWithdrawal {electra : .pectra ≤ fork} {index : ValidatorIndex}
    {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config s electra index validator amount owed = .ok t) :
    FlagsGrow s t := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    exact (grow_computeExitEpochAndUpdateChurn churned).trans FlagsGrow.of_eq
  · cases computed
    exact FlagsGrow.refl _

/-- A withdrawal request clears no flag. -/
private theorem grow_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config s electra request = .ok t) : FlagsGrow s t := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact FlagsGrow.refl _)
    | exact grow_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact grow_requestPartialWithdrawal computed

/-- Moving the excess balance to the deposit queue clears no flag. -/
private theorem grow_queueExcessActiveBalance {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queueExcessActiveBalance s electra index = .ok t) : FlagsGrow s t := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact FlagsGrow.of_eq
  · cases computed
    exact FlagsGrow.refl _

/-- Switching to compounding credentials clears no flag. -/
private theorem grow_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator s electra index = .ok t) : FlagsGrow s t := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨_, _, _, set, queued⟩ := computed
  exact (grow_setValidator set).trans (grow_queueExcessActiveBalance queued)

/-- Queueing a consolidation clears no flag. -/
private theorem grow_queueConsolidation {electra : .pectra ≤ fork} {sourceIndex : ValidatorIndex}
    {source : Validator} {targetIndex : ValidatorIndex}
    (computed : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    FlagsGrow s t := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure] at computed
  obtain ⟨⟨_, _⟩, churned, _, _, _, set, _, _, computed⟩ := computed
  simp only [Except.ok.injEq] at computed
  subst computed
  exact (grow_computeConsolidationEpochAndUpdateChurn churned).trans <|
    (grow_setValidator set).trans FlagsGrow.of_eq

/-- A consolidation request clears no flag. -/
private theorem grow_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config s electra request = .ok t) : FlagsGrow s t := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact FlagsGrow.refl _)
    | exact grow_switchToCompoundingValidator (liftAccessor_ok.mp computed)
    | exact grow_queueConsolidation computed

private theorem grow_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config s body electra = .ok t) : FlagsGrow s t := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact (FlagsGrow.foldlM (fun _ _ _ ok => grow_processDepositRequest ok) depositsOk).trans <|
    (FlagsGrow.foldlM (fun _ _ _ ok => grow_processWithdrawalRequest ok) withdrawalsOk).trans <|
    FlagsGrow.foldlM (fun _ _ _ ok => grow_processConsolidationRequest ok) consolidationsOk

/-- From Altair an attestation credits the proposer of the slot its reward, and nothing else.

448 times that reward is at most what the newly set flags add to the potential.

Take each validator active in the previous or the current epoch.

Its weight must be the base reward that the attestation reads for it. -/
private theorem attestation_credit {attestation : Attestation preset fork}
    {parent : Slot} (altair : .altair ≤ fork) (early : fork < .glamsterdam)
    (computed : processAttestation config checks s parent attestation = .ok t) :
    ∃ (proposer : ValidatorIndex) (credit : ℕ), getBeaconProposerIndex s = .ok proposer ∧
      Ledger s t ∅ ∅ 0 (fun v => if v = proposer then credit else 0) 0 ∧
      ∀ (base : ℕ → ℕ) {count : ℕ}, 2 ^ 64 ≤ count →
        (∀ (index : ValidatorIndex) (total reward : Gwei),
          (isActiveAt s (getPreviousEpoch s) index.toNat = true ∨
            isActiveAt s (getCurrentEpoch s) index.toNat = true) →
          total.toNat = activeTotal s → getBaseReward s total index = .ok reward →
          reward.toNat = base index.toNat) →
        credit * ((WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) * WEIGHT_DENOMINATOR.toNat /
            PROPOSER_WEIGHT.toNat) + flagPotential s altair base count ≤
          flagPotential t altair base count := by
  have registry := (processAttestation_registry computed).1
  simp only [processAttestation, altair, ↓reduceDIte, processAttestationAltair, bind_ok_iff,
    ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, recent, _, slotEpoch, _, _, _, _, _, _, _, _, earned, earnedOk, _, _, _, _, _, _,
    total, totalOk, attesters, attestersOk, ⟨updated, numerator⟩, folded, proposer, proposerOk,
    raised, raisedOk, final⟩ := computed
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [notGloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at final
  subst final
  rw [getBeaconProposerIndex_setEpochParticipation] at proposerOk
  have denominator : ((WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR /
      PROPOSER_WEIGHT).toNat = 448 := by decide
  have denominatorNat : (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) *
      WEIGHT_DENOMINATOR.toNat / PROPOSER_WEIGHT.toNat = 448 := by decide
  refine ⟨proposer, (numerator /
      ((WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR / PROPOSER_WEIGHT)).toNat,
    proposerOk, ?_, fun base count big reads => ?_⟩
  · have kept : (setEpochParticipation s
        (attestation.data.target.epoch == getCurrentEpoch s) updated).balances = s.balances := by
      unfold setEpochParticipation
      split <;> rfl
    have sizes := (sameSizes_increaseBalance raisedOk).2
    rw [kept] at sizes
    refine Ledger.of_rise (by rw [registry]) fun v => ?_
    cases found : s.balances.data[v.toNat]? with
    | none =>
      have missing : raised.balances.data[v.toNat]? = none := by
        rw [Array.getElem?_eq_none_iff] at found ⊢
        omega
      simp [actualBalanceAt, found, missing]
    | some balance =>
      obtain ⟨final, finalFound, finalValue⟩ :=
        balance_increaseBalance raisedOk (j := v.toNat) (by rw [kept]; exact found)
      have same : proposer.toNat = v.toNat ↔ v = proposer :=
        ⟨fun h => (UInt64.toNat_inj.mp h).symm, fun h => h ▸ rfl⟩
      simp only [actualBalanceAt, found, finalFound, Option.map_some, Option.getD_some,
        finalValue]
      by_cases equal : v = proposer <;> simp [equal, same]
  rw [UInt64.toNat_div, denominator, denominatorNat]
  have key : ∀ a b c d : ℕ, a + c ≤ d → a / 448 * 448 + (c + b) ≤ d + b := by
    intro a b c d le
    calc a / 448 * 448 + (c + b) ≤ a + (c + b) :=
          Nat.add_le_add_right (Nat.div_mul_le_self a 448) _
      _ = a + c + b := (Nat.add_assoc _ _ _).symm
      _ ≤ d + b := Nat.add_le_add_right le b
  -- Each attester is inside the range and reads its weight as its base reward.
  have facts : ∀ attester ∈ attesters, attester.toNat < count ∧
      ∀ reward, getBaseReward s total attester = .ok reward →
        reward.toNat = base attester.toNat := by
    intro attester member
    refine ⟨Nat.lt_of_lt_of_le attester.toNat_lt big, fun reward rewardOk => ?_⟩
    have active := isActiveAt_of_getAttestingIndices attestersOk member
    rw [← slotEpoch] at active
    refine reads attester total reward ?_ (getTotalActiveBalance_toNat totalOk) rewardOk
    rcases recent with previous | current
    · exact .inl (previous ▸ active)
    · exact .inr (current ▸ active)
  obtain ⟨-, gained⟩ := foldlM_addAttesterFlags_grow (base := base) (count := count) folded
  have more := gained facts
  -- The balance step keeps both lists of flags.
  obtain ⟨_, set⟩ := increaseBalance_ok raisedOk
  obtain ⟨_, rfl⟩ := setBalance_ok set
  simp only [UInt64.toNat_zero, Nat.zero_add] at more
  unfold flagPotential
  simp only [Nat.mul_add, Finset.sum_add_distrib]
  unfold setEpochParticipation
  split
  · rename_i current
    simp only [current, ↓reduceIte] at more
    dsimp only [BeaconState.putBalance]
    rw [Nat.add_comm (∑ x ∈ Finset.range count, _ * flagWeight
      (((s.previousEpochParticipation altair).data[x]?).getD 0)),
      Nat.add_comm _ (∑ x ∈ Finset.range count, _ * flagWeight
        ((updated.data[x]?).getD 0))]
    exact key _ _ _ _ more
  · rename_i current
    simp only [current, Bool.false_eq_true, ↓reduceIte] at more
    dsimp only [BeaconState.putBalance]
    exact key _ _ _ _ more

end Grow

/-! ### Steps that keep the proposer, the active validators and the base rewards -/

section Kept

variable {fork : Fork} {s u t : BeaconState preset fork}

/-- A step that keeps the inputs of the proposer draw, activity and effective balances. -/
private structure Kept (s t : BeaconState preset fork) : Prop where
  frame : Frame s t
  inputs : PayloadInputs s t
  keeps : StepKeeps s t
  effective : EffectiveKept s t
  lifecycle : RegistryLifecycle s t
  lives : Lives s t

private theorem Kept.refl (s : BeaconState preset fork) : Kept s s :=
  ⟨Frame.refl s, PayloadInputs.refl s, StepKeeps.refl s, effectiveKept_refl s, .refl s,
    Lives.refl s⟩

private theorem Kept.trans (one : Kept s u) (two : Kept u t) : Kept s t :=
  ⟨one.frame.trans two.frame, one.inputs.trans two.inputs, one.keeps.trans two.keeps,
    effectiveKept_trans one.effective two.effective one.keeps.1,
    one.lifecycle.trans two.lifecycle,
    one.lives.trans two.lives one.lifecycle (.of_frame two.frame)⟩

/-- A step that keeps the slot, activity up to the fixed epoch and effective balances. -/
private structure Steady (s t : BeaconState preset fork) : Prop where
  keeps : StepKeeps s t
  effective : EffectiveKept s t

private theorem Steady.trans (one : Steady s u) (two : Steady u t) : Steady s t :=
  ⟨one.keeps.trans two.keeps, effectiveKept_trans one.effective two.effective one.keeps.1⟩

private theorem Kept.steady (kept : Kept s t) : Steady s t := ⟨kept.keeps, kept.effective⟩

/-- The effective balances below the old registry size, read as options. -/
private theorem Steady.effective_map (kept : Steady s t) (j : ℕ)
    (inside : j < s.validators.data.size) :
    (s.validators.data[j]?).map (·.effectiveBalance) =
      (t.validators.data[j]?).map (·.effectiveBalance) := by
  have same := kept.effective j inside
  have later : j < t.validators.data.size := Nat.lt_of_lt_of_le inside kept.keeps.1
  simp only [effectiveAt, Array.getElem?_eq_getElem inside, Array.getElem?_eq_getElem later,
    Option.map_some, Option.getD_some] at same ⊢
  exact congrArg some (UInt64.toNat_inj.mp same.symm)

/-- A steady step keeps the epochs. -/
private theorem Steady.epoch (kept : Steady s t) : getCurrentEpoch t = getCurrentEpoch s := by
  simp only [getCurrentEpoch, kept.keeps.2.1]

/-- A steady step keeps the total active balance. -/
private theorem Steady.activeTotal (kept : Steady s t) : activeTotal t = activeTotal s :=
  activeTotal_eq kept.epoch kept.keeps.2.2 kept.effective kept.keeps.1

/-- The base reward reads only the effective balance of its validator and the total. -/
private theorem getBaseReward_congr {total : Gwei} {index : ValidatorIndex}
    (same : (t.validators.data[index.toNat]?).map (·.effectiveBalance) =
      (s.validators.data[index.toNat]?).map (·.effectiveBalance)) :
    getBaseReward t total index = getBaseReward s total index := by
  unfold getBaseReward getValidator
  cases hs : s.validators.data[index.toNat]? <;> cases ht : t.validators.data[index.toNat]? <;>
    simp only [hs, ht, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at same
  · simp
  · simp only [bind, Except.bind, same]

/-- The base rewards that a kept step reads at the active validators.

These validators are active in the previous or the current epoch. -/
private def Reads (s : BeaconState preset fork) (base : ℕ → ℕ) : Prop :=
  ∀ (index : ValidatorIndex) (total reward : Gwei),
    (isActiveAt s (getPreviousEpoch s) index.toNat = true ∨
      isActiveAt s (getCurrentEpoch s) index.toNat = true) →
    total.toNat = activeTotal s → getBaseReward s total index = .ok reward →
    reward.toNat = base index.toNat

private theorem Steady.reads (kept : Steady s t) {base : ℕ → ℕ} (reads : Reads s base) :
    Reads t base := by
  intro index total reward recent totalOk rewardOk
  have previous : getPreviousEpoch t = getPreviousEpoch s := by
    unfold getPreviousEpoch; rw [kept.epoch]
  have fixed := getCurrentEpoch_le_activityFixedEpoch s
  have previousLe : getPreviousEpoch s ≤ activityFixedEpoch s := by
    exact UInt64.le_trans (getPreviousEpoch_le s) fixed
  rw [previous, kept.epoch, kept.keeps.2.2 _ previousLe, kept.keeps.2.2 _ fixed] at recent
  -- An active validator is in the old registry.
  have inside : index.toNat < s.validators.data.size := by
    rcases recent with active | active <;>
    · unfold isActiveAt at active
      cases found : s.validators.data[index.toNat]? with
      | none => simp [found] at active
      | some _ => exact (Array.getElem?_eq_some_iff.mp found).1
  rw [kept.activeTotal] at totalOk
  rw [getBaseReward_congr (kept.effective_map _ inside).symm] at rewardOk
  exact reads index total reward recent totalOk rewardOk


private theorem Kept.effective_map (kept : Kept s t) (j : ℕ) (inside : j < s.validators.data.size) :
    (s.validators.data[j]?).map (·.effectiveBalance) =
      (t.validators.data[j]?).map (·.effectiveBalance) := kept.steady.effective_map j inside

private theorem Kept.reads (kept : Kept s t) {base : ℕ → ℕ} (reads : Reads s base) :
    Reads t base := kept.steady.reads reads

/-- A kept step keeps the proposer of the slot. -/
private theorem Kept.proposer (kept : Kept s t) :
    getBeaconProposerIndex t = getBeaconProposerIndex s :=
  getBeaconProposerIndex_congr kept.inputs.slot kept.inputs.randaoMixes
    (fun fulu => by rw [kept.inputs.proposerLookahead])
    (kept.keeps.2.2.getActiveValidatorIndicesChecked_eq (getCurrentEpoch_le_activityFixedEpoch s))
    kept.effective_map

end Kept


section KeptSteps

variable {fork : Fork} {s t : BeaconState preset fork}

private theorem Kept.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (each : ∀ a x b, step a x = .ok b → Kept a b) {items : List α}
    (computed : items.foldlM step s = .ok t) : Kept s t :=
  foldlM_ok_invariant (Kept s) (fun _ _ _ before ok => before.trans (each _ _ _ ok))
    (Kept.refl s) computed

private theorem kept_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks s slashing = .ok t) : Kept s t :=
  ⟨(frame_processProposerSlashing computed).toFrame, payloadInputs_processProposerSlashing computed,
    stepKeeps_processProposerSlashing computed, effectiveKept_proposerSlashing computed,
    registryLifecycle_processProposerSlashing computed, lives_processProposerSlashing computed⟩

private theorem kept_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks s slashing = .ok t) : Kept s t :=
  ⟨(frame_processAttesterSlashing computed).toFrame,
    payloadInputs_processAttesterSlashing computed, stepKeeps_processAttesterSlashing computed,
    effectiveKept_attesterSlashing computed, registryLifecycle_processAttesterSlashing computed,
    lives_processAttesterSlashing computed⟩

private theorem kept_processAttestation {attestation : Attestation preset fork} {parent : Slot}
    (computed : processAttestation config checks s parent attestation = .ok t) : Kept s t :=
  ⟨frame_processAttestation computed, payloadInputs_processAttestation computed,
    stepKeeps_processAttestation computed,
    effectiveKept_data (by rw [(processAttestation_registry computed).1]),
    registryLifecycle_processAttestation computed,
    Lives.of_data (by rw [(processAttestation_registry computed).1])⟩

/-- A new validator keeps the inputs of a payload. -/
private theorem payloadInputs_addValidatorToRegistry' {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry s pubkey withdrawalCredentials amount = .ok t) :
    PayloadInputs s t := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  split at computed
  · cases computed
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases computed

private theorem payloadInputs_processDeposit' {before : fork < .hegota} {deposit : Deposit}
    (electra : .pectra ≤ fork)
    (computed : processDeposit config checks before s deposit = .ok t) : PayloadInputs s t := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  refine PayloadInputs.trans (second := { s with eth1DepositIndex := fun _ => next })
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_
  unfold applyDeposit at applied
  simp only [electra, ↓reduceDIte] at applied
  unfold applyDepositElectra at applied
  split at applied
  · simp only [bind_ok_iff] at applied
    obtain ⟨_, _, applied⟩ := applied
    split at applied
    · simp only [bind_ok_iff, liftAccessor_ok] at applied
      obtain ⟨_, added, pushed⟩ := applied
      obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
      exact (payloadInputs_addValidatorToRegistry' added).trans
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases applied
      exact PayloadInputs.refl _
  · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp applied)
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem kept_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (electra : .pectra ≤ fork) (computed : processDeposit config checks before s deposit = .ok t) :
    Kept s t :=
  ⟨(frame_processDeposit computed).toFrame, payloadInputs_processDeposit' electra computed,
    stepKeeps_processDeposit computed, effectiveKept_processDeposit computed,
    registryLifecycle_processDeposit computed, lives_processDeposit electra computed⟩

private theorem kept_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks s signed = .ok t) : Kept s t :=
  ⟨(frame_processVoluntaryExit computed).toFrame, payloadInputs_processVoluntaryExit computed,
    stepKeeps_processVoluntaryExit computed, effectiveKept_voluntaryExit computed,
    registryLifecycle_processVoluntaryExit computed, lives_processVoluntaryExit computed⟩

private theorem kept_processBlsToExecutionChanges {body : BeaconBlockBody preset fork}
    (computed : processBlsToExecutionChanges config checks s body = .ok t) : Kept s t := by
  unfold processBlsToExecutionChanges at computed
  split at computed
  · rw [← Array.foldlM_toList] at computed
    exact Kept.foldlM (fun _ _ _ ok => ⟨(frame_processBlsToExecutionChange ok).toFrame,
      payloadInputs_processBlsToExecutionChange ok, stepKeeps_processBlsToExecutionChange ok,
      effectiveKept_blsChange ok, registryLifecycle_processBlsToExecutionChange ok,
      (by obtain ⟨validator, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
          exact Lives.setValidator found set ⟨rfl, fun _ => ⟨UInt64.le_refl _, .inr rfl⟩⟩)⟩)
      computed
  · cases computed; exact Kept.refl _

private theorem kept_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config s body electra = .ok t) : Kept s t := by
  have inputs : PayloadInputs s t := by
    have ok := computed
    simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
    obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
    exact (PayloadInputs.foldlM (fun _ _ _ ok => payloadInputs_processDepositRequest ok)
      deposits).trans <| (PayloadInputs.foldlM
        (fun _ _ _ ok => payloadInputs_processWithdrawalRequest ok) withdrawals).trans <|
      PayloadInputs.foldlM (fun _ _ _ ok => payloadInputs_processConsolidationRequest ok)
        consolidations
  exact ⟨(frame_processExecutionRequests computed).toFrame, inputs,
    stepKeeps_processExecutionRequests computed, effectiveKept_requests computed,
    registryLifecycle_processExecutionRequests computed, lives_processExecutionRequests computed⟩

end KeptSteps

/-! ### The operations of a block -/

/-- The divisor of the proposer reward of an attestation, `(64 - 8) * 64 / 8 = 448`. -/
private abbrev proposerDenominator : ℕ :=
  (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) * WEIGHT_DENOMINATOR.toNat /
    PROPOSER_WEIGHT.toNat

/-- What some operations of a block do to the balances.

The credits other than sync go to the proposer of the slot, from attestations and slashings.

Before Electra, they also go to the recipients of deposits.

The slashed validators were not slashed before, and pay their initial penalty.

The proposer reward of the attestations is bounded by the flags they set. -/
private structure Credited {fork : Fork} (o t : BeaconState preset fork)
    (proposer : ValidatorIndex) (credit : ℕ) (slashed conv : Finset ValidatorIndex)
    (other slash : ValidatorIndex → ℕ) : Prop where
  ledger : Ledger o t ∅ conv 0 other slash
  kept : Kept o t
  grow : FlagsGrowBelow o t
  read : 0 < credit ∨ slashed.Nonempty → getBeaconProposerIndex o = .ok proposer
  credited : ∀ v, other v ≤ if v = proposer then
    credit + ∑ x ∈ slashed, effectiveAt ⟨fork, t⟩ x.toNat /
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0
  penalized : ∀ v, slash v ≤ if v ∈ slashed then effectiveAt ⟨fork, t⟩ v.toNat /
    (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0
  newly : ∀ v ∈ slashed, (∀ validator, o.validators.data[v.toNat]? = some validator →
      validator.slashed = false) ∧
    ∃ later, t.validators.data[v.toNat]? = some later ∧ later.slashed = true
  potential : ∀ (altair : .altair ≤ fork) (base : ℕ → ℕ) (count : ℕ), 2 ^ 64 ≤ count →
    Reads o base → (∀ i, o.validators.data.size ≤ i → base i = 0) →
    credit * proposerDenominator + flagPotential o altair base count ≤
      flagPotential t altair base count
  eligible : ∀ v ∈ slashed, ∃ old, o.validators.data[v.toNat]? = some old ∧
    Eligible (getCurrentEpoch o) old

section Credited

variable {fork : Fork} {o u t : BeaconState preset fork}

/-- A kept step that moves no balance credits nothing. -/
private theorem Credited.of_ledger (ledger : Ledger o t ∅ ∅ 0 0 0) (kept : Kept o t)
    (grow : FlagsGrowBelow o t) : Credited o t 0 0 ∅ ∅ 0 0 where
  ledger := ledger
  kept := kept
  grow := grow
  read hyp := by simp at hyp
  credited v := by simp
  penalized v := by simp
  newly v member := absurd member (Finset.notMem_empty v)
  potential altair base count _ _ support := by
    simpa using flagPotential_mono_below grow altair base count support
  eligible v member := absurd member (Finset.notMem_empty v)

/-- An effective balance at a later kept state is the one before, for an existing validator. -/
private theorem effectiveAt_of_kept (kept : Kept u t) {v : ValidatorIndex} {validator : Validator}
    (found : u.validators.data[v.toNat]? = some validator) :
    effectiveAt ⟨fork, t⟩ v.toNat = effectiveAt ⟨fork, u⟩ v.toNat :=
  kept.effective v.toNat (Array.getElem?_eq_some_iff.mp found).1

private theorem Credited.trans {proposer proposer' : ValidatorIndex} {credit credit' : ℕ}
    {slashed slashed' conv conv' : Finset ValidatorIndex}
    {other other' slash slash' : ValidatorIndex → ℕ}
    (one : Credited o u proposer credit slashed conv other slash)
    (two : Credited u t proposer' credit' slashed' conv' other' slash') :
    Credited o t (if 0 < credit' ∨ slashed'.Nonempty then proposer' else proposer)
      (credit + credit') (slashed ∪ slashed') (conv ∪ conv')
      (other + other') (slash + slash') := by
  -- No validator is slashed in both parts.
  have apart : ∀ v ∈ slashed, v ∉ slashed' := by
    intro v first second
    obtain ⟨later, found, marked⟩ := (one.newly v first).2
    rw [(two.newly v second).1 later found] at marked
    cases marked
  have disjoint : Disjoint slashed slashed' := Finset.disjoint_left.mpr apart
  -- The effective balance of a validator slashed in the first part stays to the end.
  have kept : ∀ v ∈ slashed, effectiveAt ⟨fork, t⟩ v.toNat = effectiveAt ⟨fork, u⟩ v.toNat := by
    intro v member
    obtain ⟨later, found, _⟩ := (one.newly v member).2
    exact effectiveAt_of_kept two.kept found
  have sumKept : ∑ x ∈ slashed, effectiveAt ⟨fork, u⟩ x.toNat /
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat =
      ∑ x ∈ slashed, effectiveAt ⟨fork, t⟩ x.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
    Finset.sum_congr rfl fun x member => by rw [kept x member]
  have proposerSame : getBeaconProposerIndex u = getBeaconProposerIndex o := one.kept.proposer
  refine ⟨by simpa using one.ledger.trans two.ledger, one.kept.trans two.kept,
    one.grow.trans two.grow one.kept.frame.registryGrows, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro positive
    split
    · rename_i later
      exact proposerSame ▸ two.read later
    · rename_i none
      have zero : credit' = 0 ∧ slashed' = ∅ := by
        simp only [not_or, Nat.not_lt, Nat.le_zero, Finset.not_nonempty_iff_eq_empty] at none
        exact none
      apply one.read
      rcases positive with positive | nonempty
      · left; omega
      · right; rw [zero.2, Finset.union_empty] at nonempty; exact nonempty
  · -- Each part credits the proposer of the whole, or nothing.
    have moved {x c : ℕ} {q : ValidatorIndex} (v : ValidatorIndex)
        (bound : x ≤ if v = q then c else 0)
        (same : c = 0 ∨ q = (if 0 < credit' ∨ slashed'.Nonempty then proposer' else proposer)) :
        x ≤ if v = (if 0 < credit' ∨ slashed'.Nonempty then proposer' else proposer) then c
          else 0 := by
      rcases same with zero | same
      · subst zero; split at bound <;> simp_all
      · rw [← same]; exact bound
    intro v
    have first := one.credited v
    have second := two.credited v
    rw [sumKept] at first
    have first' := moved v first (by
      by_cases earlier : 0 < credit ∨ slashed.Nonempty
      · right
        split
        · rename_i later
          have := one.read earlier
          rw [← proposerSame, two.read later] at this
          exact (Except.ok.inj this).symm
        · rfl
      · left
        simp only [not_or, Nat.not_lt, Nat.le_zero, Finset.not_nonempty_iff_eq_empty] at earlier
        simp [earlier.1, earlier.2])
    have second' := moved v second (by
      by_cases later : 0 < credit' ∨ slashed'.Nonempty
      · right; simp only [later, ↓reduceIte]
      · left
        simp only [not_or, Nat.not_lt, Nat.le_zero, Finset.not_nonempty_iff_eq_empty] at later
        simp [later.1, later.2])
    simp only [Pi.add_apply]
    rw [Finset.sum_union disjoint]
    have total := Nat.add_le_add first' second'
    generalize (if 0 < credit' ∨ slashed'.Nonempty then proposer' else proposer) = chosen at total ⊢
    by_cases same : v = chosen
    · simp only [same, ↓reduceIte] at total ⊢; omega
    · simp only [same, ↓reduceIte] at total ⊢; omega
  · intro v
    simp only [Pi.add_apply]
    have first := one.penalized v
    have second := two.penalized v
    by_cases member : v ∈ slashed
    · have notSecond := apart v member
      simp only [member, notSecond, ↓reduceIte, Finset.mem_union, true_or] at first second ⊢
      rw [kept v member]
      omega
    · by_cases member' : v ∈ slashed'
      · simp only [member, member', ↓reduceIte, Finset.mem_union, or_true] at first second ⊢
        omega
      · simp only [member, member', ↓reduceIte, Finset.mem_union, or_self] at first second ⊢
        omega
  · intro v member
    rcases Finset.mem_union.mp member with first | second
    · obtain ⟨unslashed, later, found, marked⟩ := one.newly v first
      obtain ⟨final, finalFound, -⟩ :=
        (two.kept.frame.registryGrows) |> fun _ => (⟨later, found, marked⟩ :
          ∃ later, u.validators.data[v.toNat]? = some later ∧ later.slashed = true)
      have inside : v.toNat < t.validators.data.size :=
        Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp found).1 two.kept.frame.registryGrows
      refine ⟨unslashed, t.validators.data[v.toNat], Array.getElem?_eq_getElem inside, ?_⟩
      exact two.kept.frame.slashed v.toNat later _ found (Array.getElem?_eq_getElem inside) marked
    · refine ⟨fun validator found => ?_, (two.newly v second).2⟩
      have inside := (Array.getElem?_eq_some_iff.mp found).1
      have middle : v.toNat < u.validators.data.size :=
        Nat.lt_of_lt_of_le inside one.kept.frame.registryGrows
      have unslashed := (two.newly v second).1 _ (Array.getElem?_eq_getElem middle)
      cases flag : validator.slashed
      · rfl
      · have := one.kept.frame.slashed v.toNat validator _ found
          (Array.getElem?_eq_getElem middle) flag
        rw [unslashed] at this
        cases this
  · intro altair base count big reads support
    have first := one.potential altair base count big reads support
    have second := two.potential altair base count big (one.kept.reads reads) fun i outside =>
      support i (Nat.le_trans one.kept.frame.registryGrows outside)
    rw [Nat.add_mul]
    omega
  · intro v member
    rcases Finset.mem_union.mp member with first | second
    · exact one.eligible v first
    · obtain ⟨w, found, eligible⟩ := two.eligible v second
      have epoch : getCurrentEpoch u = getCurrentEpoch o := by
        simp only [getCurrentEpoch, one.kept.inputs.slot]
      rw [epoch] at eligible
      exact one.kept.lives.back one.kept.lifecycle (.of_frame one.kept.frame) found eligible

/-- A fold of steps that each credit like operations, and convert nothing, does so too. -/
private theorem Credited.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (each : ∀ a x b, BalancesMatch a → step a x = .ok b →
      ∃ p c sl o sh, Credited a b p c sl ∅ o sh)
    {items : List α} (matched : BalancesMatch o) (computed : items.foldlM step o = .ok t) :
    ∃ p c sl o' sh, Credited o t p c sl ∅ o' sh := by
  refine foldlM_ok_invariant (fun b => ∃ p c sl o' sh, Credited o b p c sl ∅ o' sh)
    (fun a x b ⟨_, _, _, _, _, before⟩ ok => ?_)
    ⟨0, 0, ∅, 0, 0, Credited.of_ledger (Ledger.refl o) (Kept.refl o) (FlagsGrow.refl o).below⟩
    computed
  obtain ⟨_, _, _, _, _, next⟩ := each a x b (before.kept.frame.balancesMatch matched) ok
  have joined := before.trans next
  rw [Finset.empty_union] at joined
  exact ⟨_, _, _, _, _, joined⟩

end Credited

section CreditedSteps

variable {fork : Fork} {s t : BeaconState preset fork}

private theorem effectiveAt_eq_of_found {validator : Validator}
    (found : s.validators.data[i]? = some validator) :
    effectiveAt ⟨fork, s⟩ i = validator.effectiveBalance.toNat := by
  simp [effectiveAt, found]

private theorem credited_processProposerSlashing {slashing : ProposerSlashing}
    (early : fork < .glamsterdam)
    (computed : processProposerSlashing config checks s slashing = .ok t) :
    ∃ p c sl o sh, Credited s t p c sl ∅ o sh := by
  obtain ⟨proposer, slashed, validator, read, found, unslashed, ⟨later, laterFound, marked⟩,
    ledger, eligible⟩ := ledger_processProposerSlashing early computed
  have kept := kept_processProposerSlashing computed
  have grow := (grow_processProposerSlashing computed).below
  have effective : effectiveAt ⟨fork, t⟩ slashed.toNat = validator.effectiveBalance.toNat :=
    (effectiveAt_of_kept kept found).trans (effectiveAt_eq_of_found found)
  refine ⟨proposer, 0, {slashed}, _, _, ledger, kept, grow, fun _ => read,
    fun v => ?_, fun v => ?_, fun v member => ?_, fun altair base count _ _ support => ?_,
    fun v member => ?_⟩
  · simp only [Finset.sum_singleton, effective, zero_add]; exact le_rfl
  · by_cases same : v = slashed
    · subst same; simp [effective]
    · simp [same]
  · rw [Finset.mem_singleton.mp member]
    exact ⟨fun other found' => by rw [found] at found'; cases found'; exact unslashed,
      later, laterFound, marked⟩
  · simpa using flagPotential_mono_below grow altair base count support
  · rw [Finset.mem_singleton.mp member]
    exact ⟨validator, found, eligible⟩

private theorem credited_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (early : fork < .glamsterdam)
    (computed : processAttesterSlashing config checks s slashing = .ok t) :
    ∃ p c sl o sh, Credited s t p c sl ∅ o sh := by
  obtain ⟨proposer, slashed, read, newly, eligibles, ledger⟩ :=
    ledger_processAttesterSlashing early computed
  have kept := kept_processAttesterSlashing computed
  have grow := (grow_processAttesterSlashing computed).below
  have effective : ∀ v ∈ slashed, effectiveAt ⟨fork, t⟩ v.toNat = effectiveAt ⟨fork, s⟩ v.toNat :=
    fun v member => by
      obtain ⟨validator, _, found, _⟩ := newly v member
      exact effectiveAt_of_kept kept found
  refine ⟨proposer, 0, slashed, _, _, ledger, kept, grow,
    fun hyp => read (by simpa using hyp), fun v => ?_, fun v => ?_, fun v member => ?_,
    fun altair base count _ _ support => ?_, eligibles⟩
  · have same : ∑ x ∈ slashed, effectiveAt ⟨fork, s⟩ x.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat =
        ∑ x ∈ slashed, effectiveAt ⟨fork, t⟩ x.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
      Finset.sum_congr rfl fun x member => by rw [effective x member]
    simp only [same, zero_add]; exact le_rfl
  · split
    · rename_i member; rw [effective v member]
    · exact le_rfl
  · obtain ⟨validator, later, found, unslashed, laterFound, marked⟩ := newly v member
    exact ⟨fun other found' => by rw [found] at found'; cases found'; exact unslashed,
      later, laterFound, marked⟩
  · simpa using flagPotential_mono_below grow altair base count support

private theorem credited_processAttestation {attestation : Attestation preset fork}
    {parent : Slot} (early : fork < .glamsterdam) (altair : .altair ≤ fork)
    (computed : processAttestation config checks s parent attestation = .ok t) :
    ∃ p c sl o sh, Credited s t p c sl ∅ o sh := by
  obtain ⟨proposer, credit, read, ledger, potential⟩ := attestation_credit altair early computed
  exact ⟨proposer, credit, ∅, _, _, ledger, kept_processAttestation computed,
    (grow_processAttestation early computed).below, fun _ => read,
    fun v => by simp, fun v => by simp, fun v member => absurd member (Finset.notMem_empty v),
    fun _ base count big reads _ => potential base big reads,
    fun v member => absurd member (Finset.notMem_empty v)⟩

private theorem credited_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (electra : .pectra ≤ fork) (matched : BalancesMatch s)
    (computed : processDeposit config checks before s deposit = .ok t) :
    ∃ p c sl o sh, Credited s t p c sl ∅ o sh :=
  ⟨_, _, _, _, _, Credited.of_ledger (ledger_processDeposit electra matched computed)
    (kept_processDeposit electra computed) (grow_processDeposit computed)⟩

private theorem credited_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks s signed = .ok t) :
    ∃ p c sl o sh, Credited s t p c sl ∅ o sh :=
  ⟨_, _, _, _, _, Credited.of_ledger (ledger_processVoluntaryExit computed)
    (kept_processVoluntaryExit computed) (growsLaws.processVoluntaryExit computed).1⟩

private theorem credited_processBlsToExecutionChanges {body : BeaconBlockBody preset fork}
    (computed : processBlsToExecutionChanges config checks s body = .ok t) :
    ∃ p c sl o sh, Credited s t p c sl ∅ o sh :=
  ⟨_, _, _, _, _, Credited.of_ledger (ledger_processBlsToExecutionChanges computed)
    (kept_processBlsToExecutionChanges computed)
    (by
      unfold processBlsToExecutionChanges at computed
      split at computed
      · rw [← Array.foldlM_toList] at computed
        exact (growsLaws.foldlM (fun _ _ _ ok => growsLaws.processBlsToExecutionChange ok)
          computed).1
      · cases computed
        exact (FlagsGrow.refl _).below)⟩

private theorem credited_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config s body electra = .ok t) :
    ∃ conv, Credited s t 0 0 ∅ conv 0 0 ∧
      conv.card ≤ preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat := by
  obtain ⟨conv, ledger, count⟩ := ledger_processExecutionRequests computed
  have grow := (grow_processExecutionRequests computed).below
  exact ⟨conv, ⟨ledger, kept_processExecutionRequests computed, grow, fun hyp => by simp at hyp,
    fun v => by simp, fun v => by simp, fun v member => absurd member (Finset.notMem_empty v),
    fun altair base count _ _ support => by
      simpa using flagPotential_mono_below grow altair base count support,
    fun v member => absurd member (Finset.notMem_empty v)⟩, count⟩

/-- From Fulu and before Gloas, the operations of a block credit like operations.

They convert at most one validator for each consolidation request. -/
private theorem credited_processOperations {body : BeaconBlockBody preset fork} {parent : Slot}
    (early : fork < .glamsterdam) (fulu : .fusaka ≤ fork) (matched : BalancesMatch s)
    (computed : processOperations config checks s body parent = .ok t) :
    ∃ p c sl cv o sh, Credited s t p c sl cv o sh ∧
      cv.card ≤ preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) fulu
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) fulu
  unfold processOperations at computed
  split at computed
  · rename_i later
    exact False.elim (Nat.not_le_of_lt early later)
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, a, proposersOk, b, attestersOk, c, attestationsOk, d, depositsOk, e,
    exitsOk, f, changesOk, requestsOk⟩ := computed
  have step {x y : BeaconState preset fork} {p c sl o sh p' c' sl' cv' o' sh'}
      (one : Credited s x p c sl ∅ o sh) (two : Credited x y p' c' sl' cv' o' sh') :
      ∃ p c sl o sh, Credited s y p c sl cv' o sh := by
    have joined := one.trans two
    rw [Finset.empty_union] at joined
    exact ⟨_, _, _, _, _, joined⟩
  have matchedAt {x : BeaconState preset fork} {p c sl o sh}
      (held : Credited s x p c sl ∅ o sh) : BalancesMatch x :=
    held.kept.frame.balancesMatch matched
  obtain ⟨_, _, _, _, _, one⟩ := Credited.foldlM
    (fun _ _ _ _ ok => credited_processProposerSlashing early ok) matched proposersOk
  obtain ⟨_, _, _, _, _, two⟩ := Credited.foldlM
    (fun _ _ _ _ ok => credited_processAttesterSlashing early ok) (matchedAt one) attestersOk
  obtain ⟨_, _, _, _, _, upTwo⟩ := step one two
  obtain ⟨_, _, _, _, _, three⟩ := Credited.foldlM
    (fun _ _ _ _ ok => credited_processAttestation early altair ok) (matchedAt upTwo)
    attestationsOk
  obtain ⟨_, _, _, _, _, upThree⟩ := step upTwo three
  obtain ⟨_, _, _, _, _, four⟩ := Credited.foldlM
    (fun _ _ _ held ok => credited_processDeposit electra held ok) (matchedAt upThree) depositsOk
  obtain ⟨_, _, _, _, _, upFour⟩ := step upThree four
  obtain ⟨_, _, _, _, _, five⟩ := Credited.foldlM
    (fun _ _ _ _ ok => credited_processVoluntaryExit ok) (matchedAt upFour) exitsOk
  obtain ⟨_, _, _, _, _, upFive⟩ := step upFour five
  obtain ⟨_, _, _, _, _, six⟩ := credited_processBlsToExecutionChanges changesOk
  obtain ⟨_, _, _, _, _, upSix⟩ := step upFive six
  obtain ⟨conv, seven, count⟩ := credited_processExecutionRequests requestsOk
  obtain ⟨_, _, _, _, _, upSeven⟩ := step upSix seven
  exact ⟨_, _, _, _, _, _, upSeven, count⟩

end CreditedSteps

/-- Take a validator that stays unslashed through the operations of a block.

Its effective balance is within its largest.

Before Gloas, the operations keep its balance at least the smaller of two amounts.

They are its balance and its effective balance before the operations.

A conversion to compounding credentials only lowers a balance to the activation balance.

That is the largest effective balance before the conversion. -/
theorem processOperations_floor {fork : Fork} {s t : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (early : fork < .glamsterdam) (fulu : .fusaka ≤ fork) (matched : BalancesMatch s)
    (computed : processOperations config checks s body parentSlot = .ok t)
    {v : ValidatorIndex} {val : Validator} (found : s.validators.data[v.toNat]? = some val)
    (capped : val.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork val)
    (unslashed : ∀ w, t.validators.data[v.toNat]? = some w → w.slashed = false) :
    min (actualBalanceAt ⟨fork, s⟩ v.toNat) val.effectiveBalance.toNat ≤
      actualBalanceAt ⟨fork, t⟩ v.toNat := by
  obtain ⟨_, _, _, conv, _, slash, ops, -⟩ :=
    credited_processOperations early fulu matched computed
  -- The validator stays unslashed, so the operations charge it no slashing penalty.
  have noSlash : slash v = 0 := by
    have bound := ops.penalized v
    split at bound
    · rename_i member
      obtain ⟨w, wFound, marked⟩ := (ops.newly v member).2
      rw [unslashed w wFound] at marked
      cases marked
    · omega
  by_cases converted : v ∈ conv
  · -- A converted validator did not compound, so its effective balance is within the
    -- activation balance, where the conversion leaves its balance.
    have lowered := ops.ledger.lowered v converted (Finset.notMem_empty v)
    have fresh := ops.ledger.fresh v converted val found
    have electra : .pectra ≤ fork := Nat.le_trans (by decide) fulu
    have cap := UInt64.le_iff_toNat_le.mp capped
    simp only [withdrawalMaxEffectiveBalance, electra, ↓reduceIte, getMaxEffectiveBalance,
      fresh, Bool.false_eq_true] at cap
    simp only [Pi.zero_apply, noSlash] at lowered
    omega
  · have down := ops.ledger.down v (Finset.notMem_empty v) converted
    simp only [Pi.zero_apply, noSlash] at down
    omega

/-! ### One block -/

section Block

variable {fork : Fork} {s t : BeaconState preset fork}

private theorem steady_of_validators (validators : t.validators.data = s.validators.data)
    (slot : t.slot = s.slot) : Steady s t :=
  ⟨StepKeeps.of_validators validators slot, effectiveKept_data validators⟩

private theorem steady_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader s block = .ok t) : Steady s t := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact steady_of_validators rfl rfl

private theorem steady_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks s body = .ok t) : Steady s t := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact steady_of_validators rfl rfl

private theorem steady_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before s body = .ok t) : Steady s t :=
  ⟨stepKeeps_processEth1Data computed, effectiveKept_data (by
    obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
    rw [← rest])⟩

private theorem steady_processBlockExecution {engine : ExecutionEngine preset fork}
    {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (_early : fork < .glamsterdam)
    (computed : processBlockExecution config checks engine s body bellatrix = .ok t) :
    Steady s t := by
  refine ⟨stepKeeps_processBlockExecution computed, ?_⟩
  exact effectiveKept_data (congrArg (·.data) (processBlockExecution_validators computed))

private theorem kept_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks s altair aggregate = .ok t) : Kept s t :=
  ⟨(frame_processSyncAggregate computed).toFrame, payloadInputs_processSyncAggregate computed,
    stepKeeps_processSyncAggregate computed,
    effectiveKept_data (congrArg (·.data) (processSyncAggregate_kept computed).1),
    .of_data (by rw [(processSyncAggregate_kept computed).1]),
    Lives.of_data (by rw [(processSyncAggregate_kept computed).1])⟩

/-- The balances of a block from Fulu and before Gloas, read at each validator.

Withdrawals pay at most as many validators as a payload has withdrawals.

Consolidation requests convert at most as many validators as a payload has requests.

The sync committee pays and charges each member at most its seats times the participant reward.

The other credits go to the proposer of the slot.

They are the proposer rewards of attestations and the whistleblower rewards of slashings.

They also include the proposer share of the sync aggregate, which no participant amount counts.

From Electra, deposits credit no balance in the block.

The slashed validators were not slashed before, and pay their initial penalty. -/
private theorem block_balances {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork} (early : fork < .glamsterdam) (fulu : .fusaka ≤ fork)
    (matched : BalancesMatch s) (computed : processBlock config checks engine s block = .ok t) :
    ∃ (paid conv slashed : Finset ValidatorIndex) (sync other slash : ValidatorIndex → ℕ)
      (proposer : ValidatorIndex) (credit share : ℕ),
      Ledger s t paid conv sync other slash ∧
      paid.card ≤ preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat ∧
      conv.card ≤ preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat ∧
      (∀ v, other v ≤ if v = proposer then credit + share +
        ∑ x ∈ slashed, effectiveAt ⟨fork, t⟩ x.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0) ∧
      (∀ v, slash v ≤ if v ∈ slashed then effectiveAt ⟨fork, t⟩ v.toNat /
        (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0) ∧
      (∀ v ∈ slashed, (∀ validator, s.validators.data[v.toNat]? = some validator →
          validator.slashed = false) ∧
        ∃ later, t.validators.data[v.toNat]? = some later ∧ later.slashed = true) ∧
      (∀ altair : .altair ≤ fork, (∀ v, sync v ≤ seatsOf t altair v * rewardRead s) ∧
        share ≤ preset.SYNC_COMMITTEE_SIZE.toNat * (rewardRead s * PROPOSER_WEIGHT.toNat /
          (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat))) ∧
      PerIncrementRead s ∧
      (∀ (altair : .altair ≤ fork) (base : ℕ → ℕ) (count : ℕ), 2 ^ 64 ≤ count → Reads s base →
        (∀ i, s.validators.data.size ≤ i → base i = 0) →
        credit * proposerDenominator + flagPotential s altair base count ≤
          flagPotential t altair base count) ∧
      Lives s t ∧ RegistryLifecycle s t ∧
      (∀ v ∈ slashed, ∃ old, s.validators.data[v.toNat]? = some old ∧
        Eligible (getCurrentEpoch s) old) := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) fulu
  have capella : .shapella ≤ fork := Nat.le_trans (by decide) fulu
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) fulu
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) fulu
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  have hegota : fork < .hegota := Nat.lt_trans early (by decide)
  unfold processBlock at computed
  simp only [altair, ↓reduceDIte] at computed
  unfold processBlockAltair at computed
  simp only [stateBeforeOperations, notGloas, bellatrix, hegota, ↓reduceDIte, pure_bind,
    bind_assoc, bind_ok_iff] at computed
  obtain ⟨headed, headedOk, executed, executedOk, revealed, revealedOk, voted, votedOk, operated,
    operatedOk, synced⟩ := computed
  -- The header, the payload, the reveal and the vote.
  obtain ⟨paid, executedLedger, paidCount⟩ := ledger_processBlockExecution early executedOk
  have toVoted : Ledger s voted paid ∅ 0 0 0 :=
    (ledger_processBlockHeader headedOk).zero_left
      ((executedLedger.zero_right (ledger_processRandao revealedOk)).zero_right
        (ledger_processEth1Data votedOk))
  have steadyVoted : Steady s voted :=
    (steady_processBlockHeader headedOk).trans <|
      (steady_processBlockExecution early executedOk).trans <|
        (steady_processRandao revealedOk).trans (steady_processEth1Data votedOk)
  have growVoted : FlagsGrow s voted :=
    (grow_processBlockHeader headedOk).trans <|
      (grow_processBlockExecution early executedOk).trans <|
        (grow_processRandao revealedOk).trans (grow_processEth1Data votedOk)
  have frameVoted : Frame s voted :=
    (frame_processBlockHeader headedOk).toFrame.trans <|
      (frame_processBlockExecution executedOk).toFrame.trans <|
        (frame_processRandao revealedOk).toFrame.trans (frame_processEth1Data votedOk).toFrame
  have votedValidators : voted.validators.data = s.validators.data := by
    have h1 : headed.validators = s.validators := by
      obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
      rfl
    have h2 : executed.validators = headed.validators :=
      validators_processBlockExecution early executedOk
    have h3 : revealed.validators = executed.validators := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealedOk
      rfl
    have h4 : voted.validators.data = revealed.validators.data := by
      obtain ⟨_, _, rest⟩ := processEth1Data_eq votedOk
      rw [← rest]
    rw [h4, h3, h2, h1]
  -- The operations and the sync aggregate.
  obtain ⟨proposer, credit, slashed, conv, other, slash, ops, convCount⟩ :=
    credited_processOperations early fulu (frameVoted.balancesMatch matched) operatedOk
  obtain ⟨proposer', reward, share, sync, rewardOk, read', shareBound, seats, syncLedger⟩ :=
    ledger_processSyncAggregate synced
  have syncKept := kept_processSyncAggregate synced
  have syncGrow := growsLaws.processSyncAggregate synced
  have totalSame : activeTotal operated = activeTotal s :=
    (steadyVoted.trans ops.kept.steady).activeTotal
  obtain ⟨rewardValue, perRead⟩ := rewardRead_of_ok rewardOk
  rw [rewardRead, totalSame, ← rewardRead] at rewardValue
  -- One proposer earns all the other credits.
  have same : 0 < credit ∨ slashed.Nonempty → 0 < share → proposer' = proposer := by
    intro first second
    have := read' second
    rw [ops.kept.proposer, ops.read first] at this
    exact (Except.ok.inj this).symm
  have effectiveSame : ∀ x ∈ slashed,
      effectiveAt ⟨fork, t⟩ x.toNat = effectiveAt ⟨fork, operated⟩ x.toNat := by
    intro x member
    obtain ⟨later, found, _⟩ := (ops.newly x member).2
    exact effectiveAt_of_kept syncKept found
  refine ⟨paid ∪ ∅ ∪ ∅, ∅ ∪ conv ∪ ∅, slashed, 0 + 0 + sync,
    0 + other + fun v => if v = proposer' then share else 0, 0 + slash + 0,
    if 0 < share then proposer' else proposer, credit, share,
    (toVoted.trans ops.ledger).trans syncLedger, by simpa [capella] using paidCount,
    by simpa using convCount, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    have first := ops.credited v
    have sumSame : ∑ x ∈ slashed, effectiveAt ⟨fork, operated⟩ x.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat =
        ∑ x ∈ slashed, effectiveAt ⟨fork, t⟩ x.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
      Finset.sum_congr rfl fun x member => by rw [effectiveSame x member]
    rw [sumSame] at first
    simp only [Pi.add_apply, zero_add]
    by_cases positive : 0 < share
    · simp only [positive, ↓reduceIte]
      by_cases earlier : 0 < credit ∨ slashed.Nonempty
      · rw [same earlier positive] at *
        split at first <;> split <;> omega
      · simp only [not_or, Nat.not_lt, Nat.le_zero, Finset.not_nonempty_iff_eq_empty] at earlier
        simp only [earlier.1, earlier.2, Finset.sum_empty, add_zero] at first ⊢
        split at first <;> split <;> omega
    · have zero : share = 0 := by omega
      simp only [zero, ite_self, add_zero]
      split at first <;> split <;> omega
  · intro v
    have := ops.penalized v
    simp only [Pi.add_apply, Pi.zero_apply, zero_add, add_zero]
    split at this
    · rename_i member; rw [ite_eq_left member, effectiveSame v member]; exact this
    · rw [ite_eq_right (by assumption)]; exact this
  · intro v member
    obtain ⟨unslashed, later, found, marked⟩ := ops.newly v member
    refine ⟨fun validator found' => ?_, ?_⟩
    · have inside := (Array.getElem?_eq_some_iff.mp found').1
      have middle : v.toNat < voted.validators.data.size :=
        Nat.lt_of_lt_of_le inside frameVoted.registryGrows
      have clear := unslashed _ (Array.getElem?_eq_getElem middle)
      cases flag : validator.slashed
      · rfl
      · have := frameVoted.slashed v.toNat validator _ found' (Array.getElem?_eq_getElem middle)
          flag
        rw [clear] at this
        cases this
    · have inside : v.toNat < t.validators.data.size :=
        Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp found).1 syncKept.frame.registryGrows
      exact ⟨_, Array.getElem?_eq_getElem inside,
        syncKept.frame.slashed v.toNat later _ found (Array.getElem?_eq_getElem inside) marked⟩
  · intro _
    rw [← rewardValue]
    exact ⟨fun v => by simpa using seats v, shareBound⟩
  · obtain ⟨total, per, totalValue, perOk, perValue⟩ := perRead
    exact ⟨total, per, totalValue.trans totalSame, perOk, perValue⟩
  · intro altair' base count big reads support
    have votedReads : Reads voted base := steadyVoted.reads reads
    have first := flagPotential_mono growVoted altair' base count
    have second := ops.potential altair' base count big votedReads fun i outside =>
      support i (Nat.le_trans frameVoted.registryGrows outside)
    have third := flagPotential_mono_below syncGrow.1 altair' base count fun i outside =>
      support i (Nat.le_trans frameVoted.registryGrows
        (Nat.le_trans ops.kept.frame.registryGrows outside))
    omega
  · exact Lives.of_data_left votedValidators
      (ops.kept.lives.trans syncKept.lives ops.kept.lifecycle (.of_frame syncKept.frame))
  · exact (RegistryLifecycle.of_data votedValidators).trans
      (ops.kept.lifecycle.trans syncKept.lifecycle)
  · intro v member
    obtain ⟨old, found, eligible⟩ := ops.eligible v member
    have epoch : getCurrentEpoch voted = getCurrentEpoch s := by
      simp only [getCurrentEpoch, frameVoted.slot]
    rw [epoch] at eligible
    rw [votedValidators] at found
    exact ⟨old, found, eligible⟩


end Block

/-! ### The blocks of one epoch -/

section Epoch

variable {fork : Fork}

/-- A later state of the same epoch.

Its registry grows and keeps activity and effective balances. -/
private structure Within (a s : BeaconState preset fork) : Prop where
  size : a.validators.data.size ≤ s.validators.data.size
  epoch : getCurrentEpoch s = getCurrentEpoch a
  active : ActiveKept (activityFixedEpoch a) a s
  effective : EffectiveKept a s

/-- Every state is within its own epoch. -/
private theorem Within.refl (a : BeaconState preset fork) : Within a a :=
  ⟨Nat.le_refl _, rfl, ActiveKept.refl _ _, effectiveKept_refl _⟩

/-- A steady step stays within the epoch. -/
private theorem Within.steady {a s t : BeaconState preset fork} (w : Within a s)
    (kept : Steady s t) : Within a t where
  size := Nat.le_trans w.size kept.keeps.1
  epoch := kept.epoch.trans w.epoch
  active := by
    have fixed : activityFixedEpoch s = activityFixedEpoch a := by
      simp only [activityFixedEpoch, w.epoch]
    have step := kept.keeps.2.2
    rw [fixed] at step
    exact w.active.trans step
  effective := effectiveKept_trans w.effective kept.effective w.size

/-- The effective balances below the registry size of the start, read as options. -/
private theorem Within.effective_map {a s : BeaconState preset fork} (w : Within a s) (j : ℕ)
    (inside : j < a.validators.data.size) :
    (a.validators.data[j]?).map (·.effectiveBalance) =
      (s.validators.data[j]?).map (·.effectiveBalance) := by
  have same := w.effective j inside
  have later : j < s.validators.data.size := Nat.lt_of_lt_of_le inside w.size
  simp only [effectiveAt, Array.getElem?_eq_getElem inside, Array.getElem?_eq_getElem later,
    Option.map_some, Option.getD_some] at same ⊢
  exact congrArg some (UInt64.toNat_inj.mp same.symm)

/-- A state within the epoch has the total active balance of the start. -/
private theorem Within.activeTotal {a s : BeaconState preset fork} (w : Within a s) :
    activeTotal s = activeTotal a :=
  activeTotal_eq w.epoch w.active w.effective w.size

/-- A state within the epoch has the recent validators of the start. -/
private theorem Within.recent {a s : BeaconState preset fork} (w : Within a s) (i : ℕ) :
    (isActiveAt s (getPreviousEpoch s) i = true ∨ isActiveAt s (getCurrentEpoch s) i = true) ↔
      (isActiveAt a (getPreviousEpoch a) i = true ∨ isActiveAt a (getCurrentEpoch a) i = true) := by
  have previous : getPreviousEpoch s = getPreviousEpoch a := by
    unfold getPreviousEpoch; rw [w.epoch]
  have fixed := getCurrentEpoch_le_activityFixedEpoch a
  have previousLe : getPreviousEpoch a ≤ activityFixedEpoch a :=
    UInt64.le_trans (getPreviousEpoch_le a) fixed
  rw [previous, w.epoch, w.active _ previousLe, w.active _ fixed]

/-- A recent validator is in the registry. -/
private theorem inside_of_recent {a : BeaconState preset fork} {i : ℕ}
    (recent : isActiveAt a (getPreviousEpoch a) i = true ∨
      isActiveAt a (getCurrentEpoch a) i = true) : i < a.validators.data.size := by
  rcases recent with active | active <;>
  · unfold isActiveAt at active
    cases found : a.validators.data[i]? with
    | none => simp [found] at active
    | some _ => exact (Array.getElem?_eq_some_iff.mp found).1

/-- The base rewards read at the start are read at every state within the epoch. -/
private theorem Within.reads {a s : BeaconState preset fork} (w : Within a s) {base : ℕ → ℕ}
    (reads : Reads a base) : Reads s base := by
  intro index total reward recent totalOk rewardOk
  rw [w.recent] at recent
  have inside := inside_of_recent recent
  rw [w.activeTotal] at totalOk
  rw [getBaseReward_congr (w.effective_map _ inside).symm] at rewardOk
  exact reads index total reward recent totalOk rewardOk

/-- The base rewards read at a state within the epoch are read at the start. -/
private theorem Within.reads_back {a s : BeaconState preset fork} (w : Within a s)
    {base : ℕ → ℕ} (reads : Reads s base) : Reads a base := by
  intro index total reward recent totalOk rewardOk
  have inside := inside_of_recent recent
  refine reads index total reward ((w.recent _).mpr recent)
    (by rw [w.activeTotal]; exact totalOk) ?_
  rw [getBaseReward_congr (w.effective_map _ inside).symm]
  exact rewardOk

/-- Whether the validator at an index is slashed, and false outside the registry. -/
private def slashedAt (s : BeaconState preset fork) (v : ValidatorIndex) : Bool :=
  ((s.validators.data[v.toNat]?).map (·.slashed)).getD false

/-- The initial slashing penalty of a slashed validator, read at its effective balance. -/
private def slashBackAt (s : BeaconState preset fork) (v : ValidatorIndex) : ℕ :=
  if slashedAt s v then effectiveAt ⟨fork, s⟩ v.toNat /
    (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0

/-- The sync amount of a validator for one block, its seats times a participant reward. -/
private def syncAt (s : BeaconState preset fork) (reward : ℕ) (v : ValidatorIndex) : ℕ :=
  if altair : .altair ≤ fork then seatsOf s altair v * reward else 0

/-- A slashed validator stays slashed along a frame. -/
private theorem slashedAt_of_frame {s t : BeaconState preset fork} (frame : Frame s t)
    {v : ValidatorIndex} (marked : slashedAt s v = true) : slashedAt t v = true := by
  unfold slashedAt at marked ⊢
  cases found : s.validators.data[v.toNat]? with
  | none => simp [found] at marked
  | some old =>
    simp only [found, Option.map_some, Option.getD_some] at marked
    have later : v.toNat < t.validators.data.size :=
      Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp found).1 frame.registryGrows
    rw [Array.getElem?_eq_getElem later]
    simpa using frame.slashed v.toNat old _ found (Array.getElem?_eq_getElem later) marked

/-- A slashed validator is in the registry. -/
private theorem inside_of_slashedAt {s : BeaconState preset fork} {v : ValidatorIndex}
    (marked : slashedAt s v = true) : v.toNat < s.validators.data.size := by
  unfold slashedAt at marked
  cases found : s.validators.data[v.toNat]? with
  | none => simp [found] at marked
  | some _ => exact (Array.getElem?_eq_some_iff.mp found).1

/-- The slashing penalty read at a state only grows along a frame that keeps effective balances. -/
private theorem slashBackAt_le {s t : BeaconState preset fork} (frame : Frame s t)
    (kept : EffectiveKept s t) (v : ValidatorIndex) : slashBackAt s v ≤ slashBackAt t v := by
  unfold slashBackAt
  by_cases marked : slashedAt s v = true
  · rw [ite_eq_left marked, ite_eq_left (slashedAt_of_frame frame marked),
      kept v.toNat (inside_of_slashedAt marked)]
  · rw [ite_eq_right marked]
    exact Nat.zero_le _

/-- A block before Gloas keeps the current sync committee. -/
private theorem committee_processBlock {s t : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    (early : fork < .glamsterdam) (altair : .altair ≤ fork)
    (computed : processBlock config checks engine s block = .ok t) :
    t.currentSyncCommittee altair = s.currentSyncCommittee altair := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [stateBeforeOperations, bind_assoc, bind_ok_iff] at computed
    obtain ⟨paid0, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, operated, operatedOk, synced⟩ := computed
    have paidSame : paid0 = s := by
      split at paidOk
      · exact False.elim (Nat.not_le_of_lt early (by assumption))
      · cases paidOk; rfl
    subst paid0
    have header : headed.currentSyncCommittee altair = s.currentSyncCommittee altair := by
      obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
      rfl
    have execution : executed.currentSyncCommittee altair =
        headed.currentSyncCommittee altair := by
      split at executedOk
      · exact processBlockExecution_currentSyncCommittee altair executedOk
      · cases executedOk; rfl
    have randao : revealed.currentSyncCommittee altair = executed.currentSyncCommittee altair := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealedOk
      rfl
    have vote : voted.currentSyncCommittee altair = revealed.currentSyncCommittee altair := by
      split at votedOk
      · obtain ⟨_, _, rest⟩ := processEth1Data_eq votedOk
        rw [← rest]
      · cases votedOk; rfl
    rw [congrFun (processSyncAggregate_kept synced).2 altair,
      processOperations_currentSyncCommittee altair operatedOk, vote, randao, execution, header]
  · exact absurd altair (by assumption)

/-- A frame that keeps the committee keeps the seats of every old validator. -/
private theorem seatsOf_le {s t : BeaconState preset fork} (frame : Frame s t)
    (altair : .altair ≤ fork)
    (committee : t.currentSyncCommittee altair = s.currentSyncCommittee altair)
    (v : ValidatorIndex) : seatsOf s altair v ≤ seatsOf t altair v := by
  unfold seatsOf
  rw [committee]
  cases found : s.validators.data[v.toNat]? with
  | none => simp
  | some w =>
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    have keyS : (validatorKeys s)[v.toNat]? = some w.pubkey := by
      simp [validatorKeys, found]
    have keyT : (validatorKeys t)[v.toNat]? = some w.pubkey := by
      obtain ⟨rest, joined⟩ := frame.pubkeysPrefix
      rw [← joined, List.getElem?_append_left (by simpa [validatorKeys] using inside)]
      exact keyS
    cases later : t.validators.data[v.toNat]? with
    | none => simp [validatorKeys, later] at keyT
    | some w' =>
      simp only [validatorKeys, List.getElem?_map, Array.getElem?_toList, later, Option.map_some,
        Option.some.injEq] at keyT
      simp [keyT]

/-- A frame that keeps the committee keeps the sync amount of every old validator. -/
private theorem syncAt_le {s t : BeaconState preset fork} (frame : Frame s t)
    (committee : ∀ altair : .altair ≤ fork,
      t.currentSyncCommittee altair = s.currentSyncCommittee altair)
    (reward : ℕ) (v : ValidatorIndex) : syncAt s reward v ≤ syncAt t reward v := by
  unfold syncAt
  by_cases altair : .altair ≤ fork
  · rw [dite_eq_left altair, dite_eq_left altair]
    exact Nat.mul_le_mul_right _ (seatsOf_le frame altair (committee altair) v)
  · rw [dite_eq_right altair, dite_eq_right altair]

/-- What the blocks of one epoch so far did to the balances, from Fulu.

It is read from the start `a` of the epoch at a later state `s` after `n` blocks. -/
private structure Tally (a s : BeaconState preset fork) (n : ℕ)
    (deb conv props sl : Finset ValidatorIndex) (pc : ValidatorIndex → ℕ)
    (credits shares : ℕ) : Prop where
  within : Within a s
  matched : BalancesMatch s
  persist : ∀ (v : ValidatorIndex) validator, a.validators.data[v.toNat]? = some validator →
    validator.slashed = true → slashedAt s v = true
  debCard : deb.card ≤
    (preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat +
      preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat) *
      n
  convSub : conv ⊆ deb
  down : ∀ v, v ∉ deb → actualBalanceAt ⟨fork, a⟩ v.toNat ≤
    actualBalanceAt ⟨fork, s⟩ v.toNat + slashBackAt s v + n * syncAt s (rewardRead a) v
  up : ∀ v, actualBalanceAt ⟨fork, s⟩ v.toNat ≤
    actualBalanceAt ⟨fork, a⟩ v.toNat + n * syncAt s (rewardRead a) v + pc v
  converted : ∀ v ∈ conv, actualBalanceAt ⟨fork, s⟩ v.toNat ≤
    preset.MIN_ACTIVATION_BALANCE.toNat + n * syncAt s (rewardRead a) v + pc v
  kept : ∀ (v : ValidatorIndex) validator, v ∉ conv →
    a.validators.data[v.toNat]? = some validator →
    ∃ later, s.validators.data[v.toNat]? = some later ∧
      hasCompoundingWithdrawalCredential later = hasCompoundingWithdrawalCredential validator
  pcZero : ∀ v, v ∉ props → pc v = 0
  budget : ∑ v ∈ props, pc v ≤ credits + shares + ∑ v ∈ sl, effectiveAt ⟨fork, s⟩ v.toNat /
    (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  potential : ∀ (altair : .altair ≤ fork) (base : ℕ → ℕ) (count : ℕ), 2 ^ 64 ≤ count →
    Reads a base → (∀ i, a.validators.data.size ≤ i → base i = 0) →
    credits * proposerDenominator + flagPotential a altair base count ≤
      flagPotential s altair base count
  share : shares ≤ n * (preset.SYNC_COMMITTEE_SIZE.toNat *
    (rewardRead a * PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat)))
  newly : ∀ v ∈ sl, (∀ validator, a.validators.data[v.toNat]? = some validator →
    validator.slashed = false) ∧ slashedAt s v = true
  propsCard : props.card ≤ n
  idle : n = 0 → credits = 0
  propsPos : props.Nonempty → 0 < credits ∨ 0 < shares ∨ sl.Nonempty
  perIncrement : 0 < n → PerIncrementRead a
  lives : Lives a s
  life : RegistryLifecycle a s
  persists : SlashedPersistence a s
  eligible : ∀ v ∈ sl, ∃ old, a.validators.data[v.toNat]? = some old ∧
    Eligible (getCurrentEpoch a) old

/-- Before any block, the tally is empty. -/
private theorem Tally.start (a : BeaconState preset fork) (matched : BalancesMatch a) :
    Tally a a 0 ∅ ∅ ∅ ∅ 0 0 0 where
  within := Within.refl a
  matched := matched
  persist v validator found flag := by simp [slashedAt, found, flag]
  debCard := by simp
  convSub := Finset.empty_subset _
  down v _ := by simp
  up v := by simp
  converted v member := absurd member (Finset.notMem_empty v)
  kept v validator _ found := ⟨validator, found, rfl⟩
  pcZero _ _ := rfl
  budget := by simp
  potential _ _ _ _ _ _ := by simp
  share := by simp
  newly v member := absurd member (Finset.notMem_empty v)
  propsCard := by simp
  idle _ := rfl
  propsPos h := absurd h (by simp)
  perIncrement h := absurd h (Nat.lt_irrefl 0)
  lives := Lives.refl a
  life := .refl a
  persists := .refl a
  eligible v member := absurd member (Finset.notMem_empty v)

/-- A slot step inside the epoch keeps the tally. -/
private theorem Tally.slot {a s cached : BeaconState preset fork} {next : Slot} {n : ℕ}
    {deb conv props sl : Finset ValidatorIndex} {pc : ValidatorIndex → ℕ}
    {credits shares : ℕ} (tally : Tally a s n deb conv props sl pc credits shares)
    (computed : processSlot s = .ok cached)
    (epoch : getCurrentEpoch ({ cached with slot := next } : BeaconState preset fork) =
      getCurrentEpoch s) :
    Tally a { cached with slot := next } n deb conv props sl pc credits shares := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok computed
  exact { tally with
    within := { tally.within with epoch := epoch.trans tally.within.epoch
                                  active := tally.within.active }
    lives := tally.lives.of_data_right rfl
    life := tally.life.trans (.of_data rfl)
    persists := tally.persists.trans (.of_data rfl) }

/-- A block from Fulu and before Gloas extends the tally by one block. -/
private theorem Tally.block {a s t : BeaconState preset fork} {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork} {n : ℕ} {deb conv props sl : Finset ValidatorIndex}
    {pc : ValidatorIndex → ℕ} {credits shares : ℕ}
    (tally : Tally a s n deb conv props sl pc credits shares)
    (early : fork < .glamsterdam) (fulu : .fusaka ≤ fork)
    (computed : processBlock config checks engine s block = .ok t) :
    ∃ (deb' conv' props' sl' : Finset ValidatorIndex) (pc' : ValidatorIndex → ℕ)
      (credits' shares' : ℕ), Tally a t (n + 1) deb' conv' props' sl' pc' credits' shares' := by
  obtain ⟨paid, cv, slashed, sync, other, slash, proposer, credit, share, ledger,
    paidCard, convCard, credited, penalized, newly, rewards, perRead, potential, livesB, lifeB,
    eligibleB⟩ := block_balances early fulu tally.matched computed
  have altair : .altair ≤ fork := Nat.le_trans (by decide) fulu
  have frame := frame_processBlock computed
  have steady : Steady s t := ⟨stepKeeps_processBlock computed, effectiveKept_block early computed⟩
  have within := tally.within.steady steady
  have committee : ∀ altair : .altair ≤ fork,
      t.currentSyncCommittee altair = s.currentSyncCommittee altair :=
    fun altair => committee_processBlock early altair computed
  have syncMono : ∀ v, syncAt s (rewardRead a) v ≤ syncAt t (rewardRead a) v :=
    syncAt_le frame committee _
  have backMono : ∀ v, slashBackAt s v ≤ slashBackAt t v := slashBackAt_le frame steady.effective
  -- The participant reward of the block is the one read at the start.
  have rewardEq : rewardRead s = rewardRead a := by
    unfold rewardRead
    rw [tally.within.activeTotal]
  obtain ⟨seats, shareBound⟩ := rewards altair
  rw [rewardEq] at seats shareBound
  have syncLe : ∀ v, sync v ≤ syncAt t (rewardRead a) v := by
    intro v
    unfold syncAt
    rw [dite_eq_left altair]
    exact seats v
  -- The unslashed validators that the block slashes.
  have unslashedS : ∀ v ∈ slashed, slashedAt s v = false := by
    intro v member
    unfold slashedAt
    cases found : s.validators.data[v.toNat]? with
    | none => rfl
    | some w => simp [(newly v member).1 w found]
  have slashedT : ∀ v ∈ slashed, slashedAt t v = true := by
    intro v member
    obtain ⟨later, found, marked⟩ := (newly v member).2
    simp [slashedAt, found, marked]
  have slashLe : ∀ v, slash v + slashBackAt s v ≤ slashBackAt t v := by
    intro v
    have pen := penalized v
    by_cases member : v ∈ slashed
    · rw [ite_eq_left member] at pen
      simp only [slashBackAt, unslashedS v member, slashedT v member, Bool.false_eq_true,
        ↓reduceIte]
      omega
    · rw [ite_eq_right member] at pen
      have := backMono v
      omega
  set whistle := ∑ x ∈ slashed, effectiveAt ⟨fork, t⟩ x.toNat /
    (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat with whistleEq
  refine ⟨deb ∪ (paid ∪ cv), conv ∪ cv,
    if 0 < credit + share + whistle then insert proposer props else props,
    sl ∪ slashed, fun v => pc v + other v, credits + credit, shares + share,
    { within := within
      matched := frame.balancesMatch tally.matched
      persist := fun v validator found flag =>
        slashedAt_of_frame frame (tally.persist v validator found flag)
      debCard := ?_
      convSub := Finset.union_subset_union tally.convSub Finset.subset_union_right
      down := ?_
      up := ?_
      converted := ?_
      kept := ?_
      pcZero := ?_
      budget := ?_
      potential := ?_
      share := ?_
      newly := ?_
      propsCard := ?_
      idle := fun h => absurd h (Nat.succ_ne_zero n)
      propsPos := ?_
      perIncrement := fun _ => by
        obtain ⟨total, per, totalValue, perOk, perValue⟩ := perRead
        exact ⟨total, per, totalValue.trans tally.within.activeTotal, perOk, perValue⟩
      lives := tally.lives.trans livesB tally.life (.of_frame frame)
      life := tally.life.trans lifeB
      persists := tally.persists.trans (.of_frame frame)
      eligible := ?_ }⟩
  · have one := Finset.card_union_le deb (paid ∪ cv)
    have two := Finset.card_union_le paid cv
    have three := tally.debCard
    rw [Nat.mul_succ]
    omega
  · intro v notIn
    simp only [Finset.mem_union, not_or] at notIn
    have h1 := tally.down v notIn.1
    have h2 := ledger.down v notIn.2.1 notIn.2.2
    have h3 := slashLe v
    have h4 := syncLe v
    have h5 := Nat.mul_le_mul_left n (syncMono v)
    rw [Nat.succ_mul]
    omega
  · intro v
    have h1 := tally.up v
    have h2 := ledger.up v
    have h4 := syncLe v
    have h5 := Nat.mul_le_mul_left n (syncMono v)
    rw [Nat.succ_mul]
    omega
  · intro v member
    have h4 := syncLe v
    have h5 := Nat.mul_le_mul_left n (syncMono v)
    rw [Nat.succ_mul]
    by_cases fresh : v ∈ cv
    · have := ledger.converted v fresh
      omega
    · have old : v ∈ conv := by
        rcases Finset.mem_union.mp member with h | h
        · exact h
        · exact absurd h fresh
      have h1 := tally.converted v old
      have h2 := ledger.up v
      omega
  · intro v validator notIn found
    simp only [Finset.mem_union, not_or] at notIn
    obtain ⟨middle, middleFound, same⟩ := tally.kept v validator notIn.1 found
    obtain ⟨later, laterFound, same'⟩ := ledger.kept v middle notIn.2 middleFound
    exact ⟨later, laterFound, same'.trans same⟩
  · intro v notIn
    have notProps : v ∉ props := fun h => notIn (by split <;> simp [h])
    rw [tally.pcZero v notProps, Nat.zero_add]
    have bound := credited v
    split at bound
    · rename_i eq
      subst eq
      have zero : ¬ 0 < credit + share + whistle := fun pos => notIn (by simp [pos])
      omega
    · omega
  · -- The budget: the old credits, and the amount of this block, which goes to its proposer.
    rw [Finset.sum_add_distrib]
    have sub : props ⊆ if 0 < credit + share + whistle then insert proposer props else props := by
      split
      · exact Finset.subset_insert _ _
      · exact Finset.Subset.refl _
    rw [← Finset.sum_subset sub fun v _ notIn => tally.pcZero v notIn]
    have blockPart : ∑ v ∈ (if 0 < credit + share + whistle then insert proposer props else props),
        other v ≤ credit + share + whistle := by
      calc _ ≤ ∑ v ∈ (if 0 < credit + share + whistle then insert proposer props else props),
            (if v = proposer then credit + share + whistle else 0) :=
            Finset.sum_le_sum fun v _ => credited v
        _ ≤ credit + share + whistle := by
            rw [Finset.sum_ite_eq']
            split_ifs <;> omega
    have disjoint : Disjoint sl slashed := by
      rw [Finset.disjoint_left]
      intro v inOld inNew
      have := (tally.newly v inOld).2
      rw [unslashedS v inNew] at this
      cases this
    rw [Finset.sum_union disjoint]
    have oldSame : ∑ v ∈ sl, effectiveAt ⟨fork, t⟩ v.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat =
        ∑ v ∈ sl, effectiveAt ⟨fork, s⟩ v.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
      Finset.sum_congr rfl fun v member => by
        rw [steady.effective v.toNat (inside_of_slashedAt (tally.newly v member).2)]
    rw [oldSame, ← whistleEq]
    have := tally.budget
    omega
  · intro altair base count big reads support
    have readsS : Reads s base := tally.within.reads reads
    have first := tally.potential altair base count big reads support
    have second := potential altair base count big readsS fun i outside =>
      support i (Nat.le_trans tally.within.size outside)
    rw [Nat.add_mul]
    omega
  · have := tally.share
    rw [Nat.succ_mul]
    omega
  · intro v member
    rcases Finset.mem_union.mp member with old | fresh
    · exact ⟨(tally.newly v old).1, slashedAt_of_frame frame (tally.newly v old).2⟩
    · refine ⟨fun validator found => ?_, slashedT v fresh⟩
      cases flag : validator.slashed
      · rfl
      · have := tally.persist v validator found flag
        rw [unslashedS v fresh] at this
        cases this
  · split
    · have := Finset.card_insert_le proposer props
      have := tally.propsCard
      omega
    · have := tally.propsCard
      omega
  · intro nonempty
    split at nonempty
    · rename_i positive
      by_cases c : 0 < credit
      · left; omega
      by_cases d : 0 < share
      · right; left; omega
      right; right
      have : 0 < whistle := by omega
      obtain ⟨v, member⟩ : slashed.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro empty
        rw [whistleEq, empty, Finset.sum_empty] at this
        exact Nat.lt_irrefl 0 this
      exact ⟨v, Finset.mem_union_right _ member⟩
    · rcases tally.propsPos nonempty with h | h | ⟨v, member⟩
      · left; omega
      · right; left; omega
      · right; right; exact ⟨v, Finset.mem_union_left _ member⟩
  · intro v member
    rcases Finset.mem_union.mp member with old | fresh
    · exact tally.eligible v old
    · obtain ⟨w, found, eligible⟩ := eligibleB v fresh
      rw [tally.within.epoch] at eligible
      exact tally.lives.back tally.life tally.persists found eligible

/-- The flags of one byte weigh at most the sum of all flag weights, `54`. -/
private theorem flagWeight_le (flags : ParticipationFlags) : flagWeight flags ≤ 54 := by
  unfold flagWeight
  calc _ ≤ ((List.finRange PARTICIPATION_FLAG_WEIGHTS.length).map fun flag =>
        PARTICIPATION_FLAG_WEIGHTS[flag].toNat).sum := by
        apply List.sum_le_sum
        intro flag _
        split
        · exact Nat.le_refl _
        · exact Nat.zero_le _
    _ = 54 := by decide

/-- The flag potential is at most `108` times the sum of the weights it reads. -/
private theorem flagPotential_le (s : BeaconState preset fork) (altair : .altair ≤ fork)
    (base : ℕ → ℕ) (count : ℕ) :
    flagPotential s altair base count ≤ 108 * ∑ i ∈ Finset.range count, base i := by
  unfold flagPotential
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have one := flagWeight_le (((s.previousEpochParticipation altair).data[i]?).getD 0)
  have two := flagWeight_le (((s.currentEpochParticipation altair).data[i]?).getD 0)
  rw [Nat.mul_comm 108]
  exact Nat.mul_le_mul_left _ (by omega)

/-- A sum of quotients is at most the quotient of the sum. -/
private theorem sum_div_le_div_sum {α : Type} (S : Finset α) (f : α → ℕ) (q : ℕ) :
    ∑ v ∈ S, f v / q ≤ (∑ v ∈ S, f v) / q := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert x S notIn ih =>
    rw [Finset.sum_insert notIn, Finset.sum_insert notIn]
    refine Nat.le_trans (Nat.add_le_add_left ih _) ?_
    rcases Nat.eq_zero_or_pos q with zero | positive
    · simp [zero]
    · rw [Nat.le_div_iff_mul_le positive, Nat.add_mul]
      exact Nat.add_le_add (Nat.div_mul_le_self _ _) (Nat.div_mul_le_self _ _)

end Epoch

/-- The tally of a run inside one epoch, from Fulu and before Gloas, read at its last state. -/
private theorem Run.tally {F : Fork} {a : BeaconState preset F} {y : ForkedBeaconState preset}
    (tail : Run config checks ⟨F, a⟩ y) (early : y.fork < .glamsterdam)
    (same : getCurrentEpoch y.state = getCurrentEpoch a) (matched : BalancesMatch a) :
    ∃ b : BeaconState preset F, y = ⟨F, b⟩ ∧
      (.fusaka ≤ F → ∃ (deb conv props sl : Finset ValidatorIndex) (pc : ValidatorIndex → ℕ)
        (credits shares : ℕ), Tally a b tail.blockCount deb conv props sl pc credits shares) :=
    Run.induction_of_same_epoch (fun z pre => ∃ s : BeaconState preset F, z = ⟨F, s⟩ ∧
      (.fusaka ≤ F → ∃ (deb conv props sl : Finset ValidatorIndex) (pc : ValidatorIndex → ℕ)
        (credits shares : ℕ), Tally a s pre.blockCount deb conv props sl pc credits shares))
      ⟨a, rfl, fun _ => ⟨_, _, _, _, _, _, _,
        by simpa [Run.blockCount] using Tally.start a matched⟩⟩
      (fun engine signed due ok pre early prior => by
        obtain ⟨_, eq, prior⟩ := prior
        cases eq
        refine ⟨_, rfl, fun fulu => ?_⟩
        obtain ⟨_, _, _, _, _, _, _, tally⟩ := prior fulu
        exact tally.block early fulu (applySignedBlock_ok ok).2.1)
      (fun pre ok last computed epoch prior => by
        have count : (pre.snoc (.slot ok)).blockCount = pre.blockCount := rfl
        generalize pre.snoc (.slot ok) = run at count ⊢
        clear ok
        obtain ⟨_, rfl, prior⟩ := prior
        subst last
        rw [count]
        exact ⟨_, rfl, fun fulu => by
          obtain ⟨_, _, _, _, _, _, _, tally⟩ := prior fulu
          exact ⟨_, _, _, _, _, _, _, tally.slot computed epoch⟩⟩)
      tail early same

/-- Inside one epoch, from Fulu and before Gloas, take each validator with an exit set.

Its withdrawable epoch only rises, and moves only for a slashed validator.

Reader: EffectiveRise. -/
theorem Run.withdrawableKept_of_same_epoch {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ y.fork)
    (same : getCurrentEpoch y.state = getCurrentEpoch x.state) (matched : BalancesMatch x.state) :
    WithdrawableKept x.state y.state := by
  obtain ⟨F, a⟩ := x
  obtain ⟨b, rfl, tallied⟩ := Run.tally tail early same matched
  obtain ⟨_, _, _, _, _, _, _, tally⟩ := tallied fulu
  exact tally.lives.withdrawableKept

/-! ## The branch corrections -/

/-- The balances along a branch inside one epoch, from Fulu and before Gloas.

They are read from its last state.

This is the branch correction of the fast confirmation rule.

It is read by `quorumDrift_le_quorumReserve`.

The run moves through the blocks of one epoch.

Read at its last state:

- (BC-g) Off a set of debited validators, a balance falls by at most the sum of its penalties.
  These are the initial slashing penalty and the sync penalties of the blocks.
  The debited validators are those that a withdrawal pays or a consolidation request converts.
  Their number is at most the payload limits per block.
  Off them the largest effective balance stays.
- (BC-l) A balance rises by at most the sync rewards of the blocks and its other credits.
  The other credits are zero off a set of credited validators.
  That set holds the proposers of the blocks that can credit anything.
  From Electra, deposits credit no balance in a block, so the deposit amounts are zero.
- The other credits come from three sources.
  The first is the proposer rewards of attestations.
  The second is the proposer share of the sync aggregates.
  The third is the whistleblower rewards.
  Together they are at most the sum of the proposer credit and some whistleblower rewards.
  These are the whistleblower rewards of the validators slashed at the last state.
  The proposer credit counts the proposer share apart from the participant sync rewards.
  The bound also holds with only the validators slashed within the run.
  Each of those was slashable at the first state, which needs the exits to be ordered there.
- (L4a) A validator whose largest effective balance changed was converted.
  Its balance then ends at most the activation balance above its later credits.
- Effective balances stay. -/
theorem branchCorrections {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ y.fork)
    (same : getCurrentEpoch y.state = getCurrentEpoch x.state)
    (matched : BalancesMatch x.state) (exits : ExitsOrdered x.state) :
    let state := y.state
    let inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    let slots := preset.SLOTS_PER_EPOCH.toNat
    let p := parameters preset y.fork
    let positions := Finset.range state.validators.data.size
    let validator (i : ℕ) := state.validators.data[i]?
    let effective (i : ℕ) := balanceAt state i
    let current (i : ℕ) := isActiveAt state (getCurrentEpoch state) i
    let before (i : ℕ) := isActiveAt state (getPreviousEpoch state) i
    let recent (i : ℕ) := before i || current i
    let slashed (i : ℕ) := ((validator i).map (·.slashed)).getD false
    let total := max inc (∑ i ∈ positions with current i, effective i)
    let root := (integerSquareroot (UInt64.ofNat total)).toNat
    let perIncrement := inc * preset.BASE_REWARD_FACTOR.toNat / root
    let base (i : ℕ) := if .altair ≤ y.fork then effective i / inc * perIncrement
      else effective i * preset.BASE_REWARD_FACTOR.toNat / root / BASE_REWARDS_PER_EPOCH.toNat
    let seatReward := if .altair ≤ y.fork then
        total / inc * perIncrement * SYNC_REWARD_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat /
          slots / preset.SYNC_COMMITTEE_SIZE.toNat
      else 0
    let seats (i : ℕ) := if altair : .altair ≤ y.fork then
        ((state.currentSyncCommittee altair).value.pubkeys.toList.filter fun key =>
          (validator i).any (·.pubkey == key)).length
      else 0
    let sync (i : ℕ) := seats i * seatReward
    let syncProposer := if .altair ≤ y.fork then
        slots * preset.SYNC_COMMITTEE_SIZE.toNat *
          (seatReward * PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat))
      else 0
    let proposerCredit := (∑ i ∈ positions with recent i, base i) + syncProposer
    let whistleblowerP :=
      (∑ i ∈ positions with slashed i, effective i) / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat
    let slashBack (i : ℕ) :=
      if slashed i then effective i / p.MIN_SLASHING_PENALTY_QUOTIENT.toNat else 0
    let blocks := tail.blockCount
    let debited := ((if .shapella ≤ y.fork then preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat else 0) +
      (if .pectra ≤ y.fork then preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat else 0)) *
        blocks
    let blockDeposits := if h : y.fork < .hegota then
        (if .pectra ≤ y.fork then 0
         else min (preset.MAX_DEPOSITS.toNat * blocks) (state.eth1DepositIndex h).toNat)
      else 0
    let creditedP :=
      (if proposerCredit = 0 ∧ seatReward = 0 ∧ positions.filter (slashed ·) = ∅ then 0
        else blocks) + blockDeposits
    ∃ (debitedKeys creditedKeys : Finset ValidatorIndex) (pc deposit : ValidatorIndex → ℕ),
      debitedKeys.card ≤ debited ∧ creditedKeys.card ≤ creditedP ∧
      (∀ v, v ∉ debitedKeys → actualBalanceAt x v.toNat ≤
        actualBalanceAt y v.toNat + slashBack v.toNat + blocks * sync v.toNat) ∧
      (∀ v, actualBalanceAt y v.toNat ≤
        actualBalanceAt x v.toNat + blocks * sync v.toNat + pc v + deposit v) ∧
      (∀ v, v ∉ creditedKeys → pc v = 0 ∧ deposit v = 0) ∧
      (.pectra ≤ y.fork → ∀ v, deposit v = 0) ∧
      ∑ v ∈ creditedKeys, pc v ≤ proposerCredit + whistleblowerP ∧
      (∃ slashedNow : Finset ValidatorIndex,
        (∀ v ∈ slashedNow, (∀ validator, x.state.validators.data[v.toNat]? = some validator →
            validator.slashed = false) ∧ slashed v.toNat = true ∧
          ∃ validator, x.state.validators.data[v.toNat]? = some validator ∧
            validator.activationEpoch ≤ getCurrentEpoch x.state ∧
            getCurrentEpoch x.state < validator.withdrawableEpoch) ∧
        ∑ v ∈ creditedKeys, pc v ≤ (∑ i ∈ positions with recent i, base i) + syncProposer +
          (∑ v ∈ slashedNow, effective v.toNat) / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ∧
      (∀ v validator later, x.state.validators.data[v.toNat]? = some validator →
        y.state.validators.data[v.toNat]? = some later →
        withdrawalMaxEffectiveBalance preset y.fork later ≠
          withdrawalMaxEffectiveBalance preset x.fork validator →
        actualBalanceAt y v.toNat ≤ preset.MIN_ACTIVATION_BALANCE.toNat +
          blocks * sync v.toNat + pc v + deposit v) ∧
      (∃ proposerKeys depositKeys : Finset ValidatorIndex,
        creditedKeys = proposerKeys ∪ depositKeys ∧
        proposerKeys.card ≤ (if proposerCredit = 0 ∧ seatReward = 0 ∧
          positions.filter (slashed ·) = ∅ then 0 else blocks) ∧
        depositKeys.card ≤ blockDeposits ∧
        (∀ v, v ∉ proposerKeys → pc v = 0) ∧ (∀ v, v ∉ depositKeys → deposit v = 0)) ∧
      (∀ v validator, v ∉ debitedKeys → x.state.validators.data[v.toNat]? = some validator →
        ∃ later, y.state.validators.data[v.toNat]? = some later ∧
          withdrawalMaxEffectiveBalance preset y.fork later =
            withdrawalMaxEffectiveBalance preset x.fork validator) ∧
      x.fork = y.fork ∧ EffectiveKept x.state y.state := by
  obtain ⟨F, a⟩ := x
  obtain ⟨b, rfl, tallied⟩ := Run.tally tail early same matched
  obtain ⟨deb, conv, props, sl, pc, credits, shares, tally⟩ := tallied fulu
  intro state inc slots p positions validator effective current before recent slashed total root
    perIncrement base seatReward seats sync syncProposer proposerCredit whistleblowerP slashBack
    blocks debited blockDeposits creditedP
  have altair : .altair ≤ F := Nat.le_trans (by decide) fulu
  have capella : .shapella ≤ F := Nat.le_trans (by decide) fulu
  have electra : .pectra ≤ F := Nat.le_trans (by decide) fulu
  have hegota : F < .hegota := Nat.lt_trans early (by decide)
  have totalEq : activeTotal b = total := rfl
  -- With a block, the base reward per increment was read at the total.
  have perRead : 0 < blocks → ∃ per : Gwei, getBaseRewardPerIncrement preset
      (UInt64.ofNat total) = .ok per ∧ per.toNat = perIncrement ∧ total < 2 ^ 64 := by
    intro positive
    obtain ⟨read, per, readValue, perOk, perValue⟩ := tally.perIncrement positive
    rw [← tally.within.activeTotal, totalEq] at readValue
    have small : total < 2 ^ 64 := readValue ▸ read.toNat_lt
    have readEq : read = UInt64.ofNat total := by
      apply UInt64.toNat_inj.mp
      rw [readValue, UInt64.toNat_ofNat_of_lt' small]
    subst readEq
    refine ⟨per, perOk, ?_, small⟩
    rw [perValue, readValue]
    simp only [perIncrement, root, inc, toNat_integerSquareroot, UInt64.toNat_ofNat_of_lt' small]
  -- The participant reward read at the start is the formula at the end.
  have rewardEq : 0 < blocks → rewardRead a = seatReward := by
    intro positive
    obtain ⟨_, _, _, small⟩ := perRead positive
    have rootEq : root = total.sqrt := by
      simp only [root, toNat_integerSquareroot, UInt64.toNat_ofNat_of_lt' small]
    unfold rewardRead
    rw [← tally.within.activeTotal, totalEq]
    simp only [seatReward, ite_eq_left altair, perIncrement, rootEq, inc, slots]
    rw [Nat.mul_comm (_ / total.sqrt)]
  have syncEq : ∀ v, blocks * syncAt b (rewardRead a) v = blocks * sync v.toNat := by
    intro v
    rcases Nat.eq_zero_or_pos blocks with zero | positive
    · rw [zero, Nat.zero_mul, Nat.zero_mul]
    · rw [rewardEq positive]
      simp only [syncAt, dite_eq_left altair, sync, seats]
      rfl
  -- The proposer credits of attestations are at most the base rewards of the recent validators.
  have creditsLe : credits ≤ ∑ i ∈ positions with recent i, base i := by
    rcases Nat.eq_zero_or_pos blocks with zero | positive
    · rw [tally.idle zero]; exact Nat.zero_le _
    obtain ⟨per, perOk, perValue, small⟩ := perRead positive
    let weight (i : ℕ) := if recent i then base i else 0
    have readsB : Reads b weight := by
      intro index tot reward recentB totValue rewardOk
      have isRecent : recent index.toNat = true := by
        simp only [recent, before, current, Bool.or_eq_true]; exact recentB
      have totEq : tot = UInt64.ofNat total := by
        apply UInt64.toNat_inj.mp
        rw [totValue, totalEq, UInt64.toNat_ofNat_of_lt' small]
      subst totEq
      obtain ⟨found, foundRead, rewardValue⟩ := getBaseReward_eq_mul_of_altair altair perOk rewardOk
      rw [show weight index.toNat = base index.toNat from ite_eq_left isRecent, rewardValue,
        perValue]
      simp only [base, ite_eq_left altair, effective, balanceAt, state, foundRead, Option.map_some,
        Option.getD_some, inc]
    have support : ∀ i, a.validators.data.size ≤ i → weight i = 0 := by
      intro i outside
      by_cases isRecent : recent i = true
      · have recentB : isActiveAt b (getPreviousEpoch b) i = true ∨
            isActiveAt b (getCurrentEpoch b) i = true := by
          simpa [recent, before, current] using isRecent
        have := inside_of_recent ((tally.within.recent i).mp recentB)
        omega
      · exact ite_eq_right isRecent
    have bound := tally.potential altair weight (2 ^ 64) (Nat.le_refl _)
      (tally.within.reads_back readsB) support
    have upper := flagPotential_le b altair weight (2 ^ 64)
    have sumEq : ∑ i ∈ Finset.range (2 ^ 64), weight i =
        ∑ i ∈ positions with recent i, base i := by
      rw [show ∑ i ∈ Finset.range (2 ^ 64), weight i =
        ∑ i ∈ Finset.range (2 ^ 64), (if recent i = true then base i else 0) from rfl,
        ← Finset.sum_filter]
      symm
      apply Finset.sum_subset
      · intro i member
        simp only [Finset.mem_filter, Finset.mem_range, positions] at member ⊢
        exact ⟨Nat.lt_trans member.1 (BeaconState.validators_size_lt_of_lt_glamsterdam early b),
          member.2⟩
      · intro i member notIn
        exfalso
        simp only [Finset.mem_filter, Finset.mem_range, positions, not_and] at member notIn
        have recentB : isActiveAt b (getPreviousEpoch b) i = true ∨
            isActiveAt b (getCurrentEpoch b) i = true := by
          simpa [recent, before, current] using member.2
        exact notIn (inside_of_recent recentB) member.2
    have denominator : proposerDenominator = 448 := by decide
    rw [denominator] at bound
    rw [sumEq] at upper
    omega
  -- A run inside one epoch has at most one block for each slot of the epoch.
  have blocksLe : 0 < slots → blocks ≤ slots := by
    intro positive
    have epochs := congrArg UInt64.toNat same
    simp only [getCurrentEpoch_toNat] at epochs
    have low := Nat.div_mul_le_self a.slot.toNat slots
    have high := Nat.lt_div_mul_add (a := b.slot.toNat) positive
    have count := tail.blocks_le_slots (a := a.slot.toNat / slots * slots)
      (b := a.slot.toNat / slots * slots + slots - 1) low (by
        change b.slot.toNat ≤ _
        change b.slot.toNat / slots = a.slot.toNat / slots at epochs
        rw [epochs] at high
        omega)
    change tail.blockCount ≤ slots
    omega
  -- The proposer shares of the sync aggregates.
  have sharesLe : shares ≤ syncProposer := by
    have bound := tally.share
    have proposerEq : syncProposer = slots * preset.SYNC_COMMITTEE_SIZE.toNat *
        (seatReward * PROPOSER_WEIGHT.toNat /
          (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat)) := ite_eq_left altair
    rw [proposerEq]
    rcases Nat.eq_zero_or_pos blocks with zero | positive
    · change shares ≤ blocks * _ at bound
      rw [zero, Nat.zero_mul] at bound
      omega
    · rw [rewardEq positive] at bound
      change shares ≤ blocks * _ at bound
      rcases Nat.eq_zero_or_pos slots with none | some
      · have : seatReward = 0 := by
          simp only [seatReward, ite_eq_left altair, none, Nat.div_zero, Nat.zero_div]
        rw [this, Nat.zero_mul, Nat.zero_div, Nat.mul_zero, Nat.mul_zero] at bound
        omega
      · calc shares ≤ blocks * _ := bound
          _ ≤ slots * _ := Nat.mul_le_mul_right _ (blocksLe some)
          _ = _ := by rw [Nat.mul_assoc]
  have whistleLe : ∑ v ∈ sl, effectiveAt ⟨F, b⟩ v.toNat /
      (parameters preset F).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤
      (∑ v ∈ sl, effective v.toNat) / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
    sum_div_le_div_sum sl (fun v => effectiveAt ⟨F, b⟩ v.toNat) _
  have slashedSub : ∑ v ∈ sl, effective v.toNat ≤ ∑ i ∈ positions with slashed i, effective i := by
    rw [← Finset.sum_image (f := effective) (s := sl) (g := UInt64.toNat)
      (fun x _ y _ eq => UInt64.toNat_inj.mp eq)]
    apply Finset.sum_le_sum_of_subset
    intro i member
    obtain ⟨v, inSl, rfl⟩ := Finset.mem_image.mp member
    have marked := (tally.newly v inSl).2
    simp only [Finset.mem_filter, Finset.mem_range, positions]
    exact ⟨inside_of_slashedAt marked, marked⟩
  have budget : ∑ v ∈ props, pc v ≤ (∑ i ∈ positions with recent i, base i) +
      syncProposer + (∑ v ∈ sl, effective v.toNat) / p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat := by
    have := tally.budget
    omega
  -- The credited validators.
  have propsCard : props.card ≤ (if proposerCredit = 0 ∧ seatReward = 0 ∧
      positions.filter (slashed ·) = ∅ then 0 else blocks) := by
    split
    · rename_i zero
      obtain ⟨credit0, -, slash0⟩ := zero
      have credit0' : (∑ i ∈ positions with recent i, base i) + syncProposer = 0 := credit0
      suffices empty : props = ∅ by rw [empty]; rfl
      by_contra nonempty
      rcases tally.propsPos (Finset.nonempty_iff_ne_empty.mpr nonempty) with
        positive | positive | ⟨v, member⟩
      · omega
      · omega
      · have marked := (tally.newly v member).2
        have : v.toNat ∈ positions.filter (slashed ·) := by
          simp only [Finset.mem_filter, Finset.mem_range, positions]
          exact ⟨inside_of_slashedAt marked, marked⟩
        rw [slash0] at this
        exact Finset.notMem_empty _ this
    · exact tally.propsCard
  refine ⟨deb, props, pc, fun _ => 0, ?_, Nat.le_trans propsCard (Nat.le_add_right _ _), ?_, ?_,
    fun v notIn => ⟨tally.pcZero v notIn, rfl⟩, fun _ _ => rfl,
    Nat.le_trans budget (Nat.add_le_add_left (Nat.div_le_div_right slashedSub) _), ?_, ?_,
    ⟨props, ∅, (Finset.union_empty props).symm, propsCard, by simp, tally.pcZero,
      fun _ _ => rfl⟩, ?_, rfl, tally.within.effective⟩
  · simpa only [debited, capella, electra, ↓reduceIte] using tally.debCard
  · intro v notIn
    have := tally.down v notIn
    rw [syncEq v] at this
    exact this
  · intro v
    have := tally.up v
    rw [syncEq v] at this
    exact this
  · refine ⟨sl, fun v member => ⟨(tally.newly v member).1, (tally.newly v member).2, ?_⟩,
      budget⟩
    obtain ⟨old, found, -, active, below, window⟩ := tally.eligible v member
    refine ⟨old, found, active, ?_⟩
    rcases window with far | before
    · have ordered := exits old (Array.mem_of_getElem? found)
      rw [far] at ordered
      exact UInt64.lt_of_lt_of_le below ordered
    · exact before
  · intro v validator later found foundB differ
    have member : v ∈ conv := by
      by_contra notConv
      obtain ⟨later', found', same⟩ := tally.kept v validator notConv found
      have : some later' = some later := found'.symm.trans foundB
      cases this
      apply differ
      simp only [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance, same]
    have := tally.converted v member
    rw [syncEq v] at this
    exact this
  · intro v validator notIn found
    obtain ⟨later, foundB, same⟩ := tally.kept v validator (fun h => notIn (tally.convSub h)) found
    exact ⟨later, foundB,
      by simp only [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance, same]⟩


/-- The same registry keeps every withdrawable epoch. -/
private theorem WithdrawableKept.of_data {f g : Fork} {s : BeaconState preset f}
    {t : BeaconState preset g} (same : t.validators.data = s.validators.data) :
    WithdrawableKept s t := by
  intro i v w found read _
  rw [same, found, Option.some.injEq] at read
  exact read ▸ ⟨UInt64.le_refl _, .inr rfl⟩

/-- Steps compose, given master's lifecycle of the first and the slashes the second keeps. -/
private theorem WithdrawableKept.trans {f : Fork} {s u t : BeaconState preset f}
    (one : WithdrawableKept s u) (two : WithdrawableKept u t) (life : RegistryLifecycle s u)
    (slashed : SlashedPersistence u t) : WithdrawableKept s t := by
  intro i v w found read
  obtain ⟨x, middle, kept⟩ := life.validators i v found
  exact withdrawable_trans (one i v x found middle) (two i x w middle read) kept.exitEpoch
    fun flag => by
      obtain ⟨w', read', marked⟩ := slashed i x middle flag
      rw [read, Option.some.injEq] at read'
      exact read' ▸ marked

/-- A write at a position that keeps the withdrawable epoch of an assigned exit. -/
private theorem WithdrawableKept.setAt {f : Fork} {s t : BeaconState preset f} {i : ℕ}
    {old v : Validator} (found : getValidatorAt s i = .ok old)
    (set : s.setValidatorAt i v = .ok t)
    (step : old.exitEpoch ≠ FAR_FUTURE_EPOCH → old.withdrawableEpoch ≤ v.withdrawableEpoch ∧
      (v.slashed = true ∨ v.withdrawableEpoch = old.withdrawableEpoch)) :
    WithdrawableKept s t := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  intro j u w read read' far
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set] at read'
  split at read'
  · rename_i here
    subst here
    rw [getValidatorAt_eq_ok_iff.mp found, Option.some.injEq] at read
    subst read
    cases read'
    exact step far
  · rw [read, Option.some.injEq] at read'
    exact read' ▸ ⟨UInt64.le_refl _, .inr rfl⟩

/-- From Electra, the registry updates keep the withdrawable epochs of assigned exits.

Reader: EffectiveRise. -/
theorem withdrawableKept_processRegistryUpdates {f : Fork} {s t : BeaconState preset f}
    (electra : .pectra ≤ f) (ok : processRegistryUpdates config s = .ok t) :
    WithdrawableKept s t := by
  unfold processRegistryUpdates at ok
  simp only [electra, ↓reduceIte] at ok
  obtain ⟨_, _, folded⟩ := bind_ok_iff.mp ok
  refine (foldlM_ok_invariant (fun u => RegistryLifecycle s u ∧ WithdrawableKept s u)
    (fun u _ w prior ok => ?_) ⟨RegistryLifecycle.refl s, .of_data rfl⟩ folded).2
  have frame := frame_updateRegistryEntryElectra ok
  have entry : RegistryLifecycle u w ∧ WithdrawableKept u w := by
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨v, found, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, written⟩ := ok
      exact ⟨.setValidatorAt found written ⟨fun _ => rfl, fun _ => rfl⟩,
        .setAt found written fun _ => ⟨UInt64.le_refl _, .inr rfl⟩⟩
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, exited⟩ := ok
      exact ⟨registryLifecycle_initiateValidatorExit exited,
        (lives_initiateValidatorExit exited).withdrawableKept⟩
    split at ok
    · rename_i eligible
      have far := activationEpoch_of_isEligibleForActivation eligible
      have written := liftAccessor_ok.mp ok
      exact ⟨.setValidatorAt found written ⟨fun set => absurd far set, fun _ => rfl⟩,
        .setAt found written fun _ => ⟨UInt64.le_refl _, .inr rfl⟩⟩
    · cases ok; exact ⟨RegistryLifecycle.refl _, .of_data rfl⟩
  exact ⟨prior.1.trans entry.1, prior.2.trans entry.2 prior.1 (.of_frame frame.toFrame)⟩

end EthLib.Consensus
