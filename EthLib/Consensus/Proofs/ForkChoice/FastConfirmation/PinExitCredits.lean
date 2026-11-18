module

public import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
public import EthLib.Consensus.Proofs.Transition.BranchLedger
import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
import EthLib.Consensus.Proofs.Transition.Operations
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.ValidatorCaps

/-!
# Credits to keys that exit, along a run

A key that has exited and is not yet withdrawable earns no deposit credit.

Its pending deposits are postponed until it is withdrawable.

A block deposit from Electra only queues the deposit, so it leaves every balance alone.

An epoch's pending deposits leave its balance alone (`processPendingDeposits_exited_balance`).

Along a run the key keeps its exit, and its withdrawable epoch does not fall.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network.PinSplit

open Base Uint64 Models DirectSafety

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- The credit of key `i` in one replayed event. -/
def keyCredit (i : ℕ) (e : BalanceEvent preset) : ℕ :=
  actualBalanceAt e.after i - actualBalanceAt e.before i

/-! ## Deposits leave the balance of an exiting key alone -/

/-- The statement of PinDriftBound's private `processPendingDeposits_exited_balance`.

From Electra, the pending deposits of an epoch leave a key's balance alone.

This holds while the key exits and is not yet withdrawable. -/
def PendingDepositsKeepExited (config : Config) (checks : SignatureChecks) : Prop :=
  ∀ {fork : Fork} {state after : BeaconState preset fork} {electra : .pectra ≤ fork},
    processPendingDeposits config checks state electra = .ok after →
    ∀ {i : ℕ} {v : Validator}, state.validators.data[i]? = some v →
      v.exitEpoch.toNat < 2 ^ 64 - 1 →
      (getCurrentEpoch state).toNat < v.withdrawableEpoch.toNat →
      after.balances.data[i]? = state.balances.data[i]?

/-- Every exiting key of the first state keeps its balance in the second state. -/
private def KeepsExiting {f g : Fork} (s : BeaconState preset f) (t : BeaconState preset g) :
    Prop :=
  ∀ (i : ℕ) (v : Validator), s.validators.data[i]? = some v → v.exitEpoch.toNat < 2 ^ 64 - 1 →
    (getCurrentEpoch s).toNat < v.withdrawableEpoch.toNat →
    t.balances.data[i]? = s.balances.data[i]?

/-- Every deposit event of the list leaves the balance of an exiting key alone. -/
private def Quiet (events : List (BalanceEvent preset)) : Prop :=
  ∀ e ∈ events, e.source = .deposits → KeepsExiting e.before.state e.after.state

/-- The event raises no balance of the registry. -/
private def Unconditional (e : BalanceEvent preset) : Prop :=
  ∀ i, actualBalanceAt e.after i ≤ actualBalanceAt e.before i

private theorem quiet_nil : Quiet ([] : List (BalanceEvent preset)) := fun _ mem => by
  simp at mem

private theorem quiet_carry {f : Fork}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    {pre post : BalanceReplay preset f} (initial : Quiet pre.2)
    (ok : carryBalance action pre = .ok post) : Quiet post.2 := by
  simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  exact initial

private theorem quiet_record {f : Fork} {source : BalanceSource}
    {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    {pre post : BalanceReplay preset f} (initial : Quiet pre.2)
    (keeps : source = .deposits → ∀ t, action pre.1 = .ok t → KeepsExiting pre.1 t)
    (ok : recordBalance source limits action pre = .ok post) : Quiet post.2 := by
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨⟨credit, debit⟩, _, t, actionOk, rfl⟩ := ok
  intro e member sourceEq
  rcases List.mem_append.mp member with old | new
  · exact initial e old sourceEq
  · obtain rfl := List.mem_singleton.mp new
    exact keeps sourceEq t actionOk

/-- A new validator with no balance never raises a balance. -/
private theorem addValidatorToRegistry_zero_balance {f : Fork} {s t : BeaconState preset f}
    (altair : .altair ≤ f) {pubkey : Cryptography.Bls.BLSPubkey} {credentials : Bytes32}
    (ok : addValidatorToRegistry s pubkey credentials 0 = .ok t) (i : ℕ) :
    ((t.balances.data[i]?).map (·.toNat)).getD 0 ≤
      ((s.balances.data[i]?).map (·.toNat)).getD 0 := by
  unfold addValidatorToRegistry at ok
  simp only [altair, ↓reduceDIte, addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, balancesOk, _, _, _, _, _, _, rfl⟩ := ok
  show ((_ : Option Gwei).map (·.toNat)).getD 0 ≤ _
  rw [setOrAppendList_getElem? balancesOk]
  split <;> simp

/-- From Electra, a block deposit raises no balance. -/
private theorem processDeposit_balance_le {f : Fork} {s t : BeaconState preset f}
    (electra : .pectra ≤ f) {before : f < .hegota} {dep : Deposit}
    (ok : processDeposit config checks before s dep = .ok t) (i : ℕ) :
    actualBalanceAt ⟨f, t⟩ i ≤ actualBalanceAt ⟨f, s⟩ i := by
  obtain ⟨-, -, next, -, applied⟩ := processDeposit_ok ok
  rcases applyDeposit_cases applied with rfl | ⟨_, middle, pending, rfl | added, rfl⟩ |
      ⟨early, _⟩
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · exact addValidatorToRegistry_zero_balance (Nat.le_trans (by decide) electra) added i
  · exact absurd (Nat.lt_of_lt_of_le early electra) (Nat.lt_irrefl _)

/-- A property of the events of a block replay that each recorded event keeps.

Every operation of a block records an event of its own source.

The deposits of the block are the only events of the source `.deposits`.

No operation of a block records the source `.consolidations`. -/
private theorem blockReplay_invariant {f : Fork} (electra : .pectra ≤ f) (early : f < .glamsterdam)
    (P : List (BalanceEvent preset) → Prop) (nil : P [])
    (ordinary : ∀ (l : List (BalanceEvent preset)) (e : BalanceEvent preset),
      e.source ≠ .deposits → e.source ≠ .consolidations → P l → P (l ++ [e]))
    (deposit : ∀ (l : List (BalanceEvent preset)) (s t : BeaconState preset f)
      (before : f < .hegota) (dep : Deposit) (credit debit : ℕ), P l →
      processDeposit config checks before s dep = .ok t →
      P (l ++ [⟨.deposits, ⟨f, s⟩, ⟨f, t⟩, credit, debit⟩]))
    (engine : ExecutionEngine preset f) (s : BeaconState preset f)
    (block : BeaconBlock preset f) {post : BalanceReplay preset f}
    (ok : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok post) : P post.2 := by
  have carry {pre post : BalanceReplay preset f}
      {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
      (initial : P pre.2) (ok : carryBalance action pre = .ok post) : P post.2 := by
    simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, rfl⟩ := ok
    exact initial
  have record {pre post : BalanceReplay preset f} {source : BalanceSource}
      {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
      {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
      (notDeposit : source ≠ .deposits) (notConsolidation : source ≠ .consolidations)
      (initial : P pre.2) (ok : recordBalance source limits action pre = .ok post) :
      P post.2 := by
    simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨⟨credit, debit⟩, _, t, _, rfl⟩ := ok
    exact ordinary _ _ notDeposit notConsolidation initial
  have altair : .altair ≤ f := Nat.le_trans (by decide) electra
  have bellatrix : .bellatrix ≤ f := Nat.le_trans (by decide) electra
  unfold blockBalanceReplay at ok
  obtain ⟨headed, headedOk, rest⟩ := bind_ok_iff.mp ok
  have headedQuiet := carry nil headedOk
  simp only [bellatrix, ↓reduceDIte] at rest
  obtain ⟨executed, executedOk, rest⟩ := bind_ok_iff.mp rest
  have executedQuiet := record (by decide : BalanceSource.withdrawals ≠ .deposits)
    (by decide) headedQuiet executedOk
  simp only [bind_ok_iff] at rest
  obtain ⟨randao, randaoOk, voted, votedOk, expected, _, _, _,
    proposed, proposedOk, attested, attestedOk, rewarded, rewardedOk, deposited, depositOk,
    exited, exitOk, changed, changedOk, rest⟩ := rest
  have randaoQuiet := carry executedQuiet randaoOk
  have votedQuiet := carry randaoQuiet votedOk
  have proposedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun _ _ _ h ok => record (by decide : BalanceSource.slashings ≠ .deposits) (by decide) h ok)
    votedQuiet proposedOk
  have attestedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun _ _ _ h ok => record (by decide : BalanceSource.slashings ≠ .deposits) (by decide) h ok)
    proposedQuiet attestedOk
  have rewardedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun _ _ _ h ok => record (by decide : BalanceSource.rewards ≠ .deposits) (by decide) h ok)
    attestedQuiet rewardedOk
  have depositedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun pre dep post h ok => by
      simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨⟨credit, debit⟩, _, t, actionOk, rfl⟩ := ok
      exact deposit _ _ _ _ _ _ _ h actionOk)
    rewardedQuiet depositOk
  have exitedQuiet := carry depositedQuiet exitOk
  have changedQuiet := carry exitedQuiet changedOk
  simp only [electra, ↓reduceDIte, bind_ok_iff] at rest
  obtain ⟨deposits, depositRequestOk, withdrawals, withdrawalOk,
    requested, consolidations, rest⟩ := rest
  have depositsQuiet := carry changedQuiet depositRequestOk
  have withdrawalsQuiet := carry depositsQuiet withdrawalOk
  have requestedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun _ _ _ h ok => record (by decide : BalanceSource.excess ≠ .deposits) (by decide) h ok)
    withdrawalsQuiet consolidations
  simp only [altair, ↓reduceDIte] at rest
  exact record (by decide : BalanceSource.sync ≠ .deposits) (by decide) requestedQuiet rest

/-- From Electra, the deposit events of a block replay raise no balance. -/
private theorem blockReplay_unconditional {f : Fork} (electra : .pectra ≤ f)
    (early : f < .glamsterdam)
    (engine : ExecutionEngine preset f) (s : BeaconState preset f)
    (block : BeaconBlock preset f) {post : BalanceReplay preset f}
    (ok : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok post) :
    ∀ e ∈ post.2, e.source = .deposits → Unconditional e :=
  blockReplay_invariant electra early (fun l => ∀ e ∈ l, e.source = .deposits → Unconditional e)
    (fun _ h => by simp at h)
    (fun l e notDeposit _ held e' member sourceEq => by
      rcases List.mem_append.mp member with old | new
      · exact held e' old sourceEq
      · exact absurd ((List.mem_singleton.mp new) ▸ sourceEq) notDeposit)
    (fun l s t _ dep credit debit held computed e' member sourceEq => by
      rcases List.mem_append.mp member with old | new
      · exact held e' old sourceEq
      · obtain rfl := List.mem_singleton.mp new
        exact fun i => processDeposit_balance_le electra computed i)
    engine s block ok

/-- No operation of a block records a consolidation event. -/
private theorem blockReplay_noConsolidations {f : Fork} (electra : .pectra ≤ f)
    (early : f < .glamsterdam) (engine : ExecutionEngine preset f) (s : BeaconState preset f)
    (block : BeaconBlock preset f) {post : BalanceReplay preset f}
    (ok : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok post) : ∀ e ∈ post.2, e.source ≠ .consolidations :=
  blockReplay_invariant electra early (fun l => ∀ e ∈ l, e.source ≠ .consolidations)
    (fun _ h => by simp at h)
    (fun l e _ notConsolidation held e' member => by
      rcases List.mem_append.mp member with old | new
      · exact held e' old
      · exact (List.mem_singleton.mp new) ▸ notConsolidation)
    (fun l s t _ dep credit debit held _ e' member => by
      rcases List.mem_append.mp member with old | new
      · exact held e' old
      · obtain rfl := List.mem_singleton.mp new
        exact fun eq => by cases eq)
    engine s block ok

/-- The deposit events of an epoch replay leave the balance of an exiting key alone.

The pending deposits of an epoch are the only deposit events of the replay. -/
private theorem epochReplay_quiet (exitedBalance : PendingDepositsKeepExited (preset := preset)
      config checks)
    {f : Fork} {s : BeaconState preset f} {post : BalanceReplay preset f}
    (ok : epochBalanceReplay (config := config) (checks := checks) s = .ok post) :
    Quiet post.2 := by
  refine (epochBalanceReplay_trace ok).transport
    (fun a b : BalanceReplay preset f => Quiet a.2 → Quiet b.2)
    (fun _ => id) (fun one two held => two (one held)) ?_ quiet_nil
  intro k member pre after step held
  cases k <;> simp only [epochReplayAction] at step
  case justification | registry => exact quiet_carry held step
  case inactivity | eth1Reset =>
    split at step
    · exact quiet_carry held step
    · cases step; exact held
  case rewards =>
    exact replayRewards_induction (fun pre => Quiet pre.2)
      (fun prior ok => quiet_record prior (fun eq => by cases eq) ok)
      (fun penalty prior ok => quiet_record prior
        (fun eq => by rcases penalty with rfl | rfl <;> cases eq) ok) held step
  case slashings => exact quiet_record held (fun eq => by cases eq) step
  case pendingDeposits =>
    split at step
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
      obtain ⟨deposited, depositedOk, rfl⟩ := step
      intro e member sourceEq
      rcases List.mem_append.mp member with old | new
      · exact held e old sourceEq
      · obtain rfl := List.mem_singleton.mp new
        intro i v found exited withdrawable
        exact exitedBalance depositedOk found exited withdrawable
    · cases step; exact held
  case pendingConsolidations =>
    split at step
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
      obtain ⟨consolidated, consolidatedOk, rfl⟩ := step
      intro e member sourceEq
      rcases List.mem_append.mp member with old | new
      · exact held e old sourceEq
      · obtain rfl := List.mem_singleton.mp new
        cases sourceEq
    · cases step; exact held
  all_goals simp [EpochStage.prefixStages] at member

/-- The deposit events of a slot step leave the balance of an exiting key alone. -/
private theorem slot_quiet (exitedBalance : PendingDepositsKeepExited (preset := preset)
      config checks)
    {x y : ForkedBeaconState preset} (ok : advanceSlotAcross config checks x = .ok y)
    (early : y.fork < .glamsterdam)
    {events : List (BalanceEvent preset)} (replayed : (Step.slot ok).balanceEvents = .ok events) :
    Quiet events := by
  obtain ⟨advanced, cached, crossings, -, -, -, crossingOk, split⟩ :=
    Step.balanceEvents_slot ok early replayed
  have crossed : Quiet crossings := fun e member sourceEq => by
    cases (upgradeBalanceReplay_crossing crossingOk e member).symm.trans sourceEq
  rcases split with ⟨-, rfl⟩ | ⟨middle, updated, recorded, recordOk, -, -, -, rfl, -⟩
  · exact crossed
  · intro e member sourceEq
    rcases List.mem_append.mp member with old | new
    · exact epochReplay_quiet exitedBalance recordOk e old sourceEq
    · exact crossed e new sourceEq

/-- A deposit event of a run raises no balance, or it is an epoch's deposit event of a slot step.

Then it leaves the balance of an exiting key alone. -/
private def Located {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (e : BalanceEvent preset) : Prop :=
  Unconditional e ∨ ∃ (u w : ForkedBeaconState preset)
    (ok : advanceSlotAcross config checks u = .ok w) (es : List (BalanceEvent preset)),
    tail.Contains (Step.slot ok) ∧ (Step.slot ok : Step config checks u w).balanceEvents = .ok es ∧
      e ∈ es ∧ KeepsExiting e.before.state e.after.state

/-- Locate each deposit event of a run. -/
private theorem run_located (exitedBalance : PendingDepositsKeepExited (preset := preset)
      config checks)
    {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    ∀ e ∈ events, e.source = .deposits → Located tail e := by
  induction tail generalizing events with
  | nil => cases replayed; intro e member; simp at member
  | @snoc middle last pre step ih =>
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    have priorLocated := ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early) priorOk
    have lift : ∀ e, Located pre e → Located (pre.snoc step) e := by
      rintro e (unconditional | ⟨u, w, ok, es, contains, replayedEs, member, keeps⟩)
      · exact .inl unconditional
      · exact .inr ⟨u, w, ok, es, .earlier contains step, replayedEs, member, keeps⟩
    by_cases selected : (getCurrentEpoch middle.state).toNat ≤ high + 1
    · simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at rest
      obtain ⟨added, addedOk, rfl⟩ := rest
      have inFork : .pectra ≤ middle.fork :=
        Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
      intro e member sourceEq
      rcases List.mem_append.mp member with old | new
      · exact lift e (priorLocated e old sourceEq)
      · cases step with
        | block engine signed due ok =>
          exact .inl (blockReplay_unconditional inFork early engine _ _
            (Step.balanceEvents_block early addedOk) e new sourceEq)
        | slot ok =>
          exact .inr ⟨_, _, ok, added, .last pre _, addedOk, new,
            slot_quiet exitedBalance ok early addedOk e new sourceEq⟩
    · simp only [selected, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      intro e member sourceEq
      exact lift e (priorLocated e member sourceEq)

/-! ## Consolidation credits of one pass -/

/-- The stake that a pending consolidation can move at a pass: the source's effective balance.

It counts only a source that is unslashed and can withdraw by the next epoch.

A pass reads the other sources without moving anything. -/
def sourceBound {f : Fork} (s : BeaconState preset f) (next : Epoch)
    (c : PendingConsolidation) : ℕ :=
  match s.validators.data[c.sourceIndex.toNat]? with
  | some v => if v.slashed = false ∧ v.withdrawableEpoch ≤ next then v.effectiveBalance.toNat else 0
  | none => 0

/-- The credits of the balances from one state to another, over the later balances. -/
private def credited {f : Fork} (s t : BeaconState preset f) : ℕ :=
  ∑ j ∈ Finset.range t.balances.data.size,
    (actualBalanceAt ⟨f, t⟩ j - actualBalanceAt ⟨f, s⟩ j)

private theorem credited_trans {f : Fork} {a b c : BeaconState preset f}
    (ab : b.balances.data.size = a.balances.data.size)
    (bc : c.balances.data.size = b.balances.data.size) :
    credited a c ≤ credited a b + credited b c := by
  unfold credited
  rw [bc, ab, ← ab, ← Finset.sum_add_distrib]
  rw [ab, bc] at *
  apply Finset.sum_le_sum
  intro j _
  omega

/-- One transfer of a pass credits at most the amount moved. -/
private theorem credited_transfer {f : Fork} {s lowered raised : BeaconState preset f}
    {source target : ValidatorIndex} {moved : Gwei}
    (lowerOk : decreaseBalance s source moved = .ok lowered)
    (raiseOk : increaseBalance lowered target moved = .ok raised) :
    credited s raised ≤ moved.toNat := by
  have sizes := (sameSizes_increaseBalance raiseOk).2.trans (sameSizes_decreaseBalance lowerOk).2
  unfold credited
  have pointwise : ∀ j, actualBalanceAt ⟨f, raised⟩ j - actualBalanceAt ⟨f, s⟩ j ≤
      if target.toNat = j then moved.toNat else 0 := by
    intro j
    by_cases inside : j < s.balances.data.size
    · obtain ⟨balance, found⟩ : ∃ balance, s.balances.data[j]? = some balance :=
        ⟨_, Array.getElem?_eq_getElem inside⟩
      obtain ⟨down, downFound, downEq⟩ := balance_decreaseBalance lowerOk found
      obtain ⟨up, upFound, upEq⟩ := balance_increaseBalance raiseOk downFound
      simp only [actualBalanceAt, found, upFound, Option.map_some, Option.getD_some]
      split at downEq <;> split at upEq <;> split <;> omega
    · have missing : s.balances.data[j]? = Option.none := Array.getElem?_eq_none (by omega)
      have outside : raised.balances.data[j]? = Option.none := Array.getElem?_eq_none (by omega)
      simp [actualBalanceAt, missing, outside]
  calc ∑ j ∈ Finset.range raised.balances.data.size,
        (actualBalanceAt ⟨f, raised⟩ j - actualBalanceAt ⟨f, s⟩ j)
      ≤ ∑ j ∈ Finset.range raised.balances.data.size, if target.toNat = j then moved.toNat else 0 :=
        Finset.sum_le_sum fun j _ => pointwise j
    _ ≤ moved.toNat := by
        rw [Finset.sum_ite_eq]
        split <;> omega

/-- A pass credits at most the effective balances of the unslashed due sources it reads.

It keeps the registry and the number of balances. -/
private theorem pass_credits_le {f : Fork} (next : Epoch) :
    ∀ (items : List PendingConsolidation) {s t : BeaconState preset f} {read : ℕ},
      passPendingConsolidations next s items = .ok (t, read) →
      t.validators = s.validators ∧ t.balances.data.size = s.balances.data.size ∧
        credited s t ≤ ((items.take read).map (sourceBound s next)).sum
  | [], s, t, read, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at computed
    obtain ⟨rfl, rfl⟩ := computed
    refine ⟨rfl, rfl, ?_⟩
    simp [credited, actualBalanceAt]
  | c :: rest, s, t, read, computed => by
    simp only [passPendingConsolidations, liftAccessor, bind_ok_iff, mapError_ok_iff] at computed
    obtain ⟨source, sourceRead, computed⟩ := computed
    have found := getValidator_eq_ok_iff.mp sourceRead
    have bound : sourceBound s next c = if source.slashed = false ∧ source.withdrawableEpoch ≤ next
        then source.effectiveBalance.toNat else 0 := by
      simp [sourceBound, found]
    by_cases slashed : source.slashed = true
    · simp only [slashed, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at computed
      obtain ⟨⟨state', read'⟩, passed, rfl, rfl⟩ := computed
      obtain ⟨validators, sizes, credits⟩ := pass_credits_le next rest passed
      refine ⟨validators, sizes, ?_⟩
      simpa [bound, slashed, List.take_succ_cons] using credits
    · replace slashed : source.slashed = false := by simpa using slashed
      by_cases early : next < source.withdrawableEpoch
      · simp only [slashed, early, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq] at computed
        obtain ⟨rfl, rfl⟩ := computed
        refine ⟨rfl, rfl, ?_⟩
        simp [credited, actualBalanceAt]
      · simp only [slashed, early, Bool.false_eq_true, ↓reduceIte, bind_ok_iff,
          mapError_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
        obtain ⟨balance, balanceOk, lowered, loweredOk, raised, raisedOk,
          ⟨state', read'⟩, passed, rfl, rfl⟩ := computed
        obtain ⟨validators, sizes, credits⟩ := pass_credits_le next rest passed
        have sameValidators := (increaseBalance_validators raisedOk).trans
          (decreaseBalance_validators loweredOk)
        have step := credited_transfer loweredOk raisedOk
        have sizeStep := (sameSizes_increaseBalance raisedOk).2.trans
          (sameSizes_decreaseBalance loweredOk).2
        have moved : (min balance source.effectiveBalance).toNat ≤
            source.effectiveBalance.toNat := by
          rw [Uint64.toNat_min]; exact Nat.min_le_right _ _
        have restBound : ((rest.take read').map (sourceBound raised next)) =
            ((rest.take read').map (sourceBound s next)) := by
          congr 1
          funext d
          simp only [sourceBound, sameValidators]
        refine ⟨validators.trans sameValidators, sizes.trans sizeStep, ?_⟩
        have total := credited_trans (a := s) (b := raised) (c := state') sizeStep sizes
        rw [restBound] at credits
        have isDue : sourceBound s next c = source.effectiveBalance.toNat := by
          rw [bound]; simp [slashed, UInt64.not_lt.mp early]
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons, isDue]
        omega

/-! ## The queue of pending consolidations over a block -/

/-- The queue only grows at its end inside a block.

Each new entry has a source whose exit is assigned after the current epoch. -/
private def Grows {f : Fork} (s t : BeaconState preset f) : Prop :=
  ∀ electra : .pectra ≤ f, ∃ added : List PendingConsolidation,
    (t.pendingConsolidations electra).data.toList =
      (s.pendingConsolidations electra).data.toList ++ added ∧
    ∀ c ∈ added, ∃ w, t.validators.data[c.sourceIndex.toNat]? = some w ∧
      getCurrentEpoch s < w.exitEpoch ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH

private theorem Grows.of_same {f : Fork} {s t : BeaconState preset f}
    (queue : .pectra ≤ f → SamePendingQueue s t) : Grows s t := by
  intro electra
  refine ⟨[], ?_, fun _ member => by simp at member⟩
  rw [show t.pendingConsolidations electra = s.pendingConsolidations electra from
    congrFun (queue electra) electra, List.append_nil]

private theorem Grows.trans {f : Fork} {s u t : BeaconState preset f}
    (one : Grows s u) (two : Grows u t) (life : RegistryLifecycle u t)
    (slot : u.slot = s.slot) : Grows s t := by
  intro electra
  obtain ⟨added, queue, new⟩ := one electra
  obtain ⟨added', queue', new'⟩ := two electra
  have epoch : getCurrentEpoch u = getCurrentEpoch s := by simp only [getCurrentEpoch, slot]
  refine ⟨added ++ added', by rw [queue', queue, List.append_assoc], fun c member => ?_⟩
  rcases List.mem_append.mp member with old | fresh
  · obtain ⟨w, read, later, assigned⟩ := new c old
    obtain ⟨w', read', kept⟩ := life.validators _ w read
    have exit := kept.exitEpoch assigned
    exact ⟨w', read', by rw [exit]; exact later, by rw [exit]; exact assigned⟩
  · obtain ⟨w, read, later, assigned⟩ := new' c fresh
    exact ⟨w, read, epoch ▸ later, assigned⟩

/-- A block step: master's frame and lifecycle, and the growth of the queue. -/
private def GrowStep {f : Fork} (s t : BeaconState preset f) : Prop :=
  Frame s t ∧ RegistryLifecycle s t ∧ Grows s t

private theorem GrowStep.of_same {f : Fork} {s t : BeaconState preset f} (frame : Frame s t)
    (life : RegistryLifecycle s t) (queue : .pectra ≤ f → SamePendingQueue s t) :
    GrowStep s t :=
  ⟨frame, life, Grows.of_same queue⟩

private theorem GrowStep.of_data {f : Fork} {s t : BeaconState preset f} (frame : Frame s t)
    (same : t.validators.data = s.validators.data)
    (queue : .pectra ≤ f → SamePendingQueue s t) : GrowStep s t :=
  GrowStep.of_same frame (RegistryLifecycle.of_data same) queue

private theorem GrowStep.refl {f : Fork} (s : BeaconState preset f) : GrowStep s s :=
  GrowStep.of_data (Frame.refl s) rfl fun _ => rfl

private theorem GrowStep.trans {f : Fork} {s u t : BeaconState preset f}
    (one : GrowStep s u) (two : GrowStep u t) : GrowStep s t :=
  ⟨one.1.trans two.1, one.2.1.trans two.2.1, one.2.2.trans two.2.2 two.2.1 one.1.slot⟩

private theorem GrowStep.fold {f : Fork} {s t : BeaconState preset f} {α ε : Type}
    {step : BeaconState preset f → α → Except ε (BeaconState preset f)} {xs : List α}
    (kept : ∀ a item b, step a item = .ok b → GrowStep a b)
    (ok : xs.foldlM step s = .ok t) : GrowStep s t :=
  foldlM_ok_invariant (GrowStep s)
    (fun _ _ _ prior computed => prior.trans (kept _ _ _ computed)) (GrowStep.refl s) ok

section GrowSteps

variable {f : Fork} {s t : BeaconState preset f}

private theorem growStep_processProposerSlashing {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processProposerSlashing ok).toFrame
    (registryLifecycle_processProposerSlashing ok) (fun _ => SamePendingQueue.proposer ok)

private theorem growStep_processAttesterSlashing {slashing : AttesterSlashing preset f}
    (ok : processAttesterSlashing config checks s slashing = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processAttesterSlashing ok).toFrame
    (registryLifecycle_processAttesterSlashing ok) (fun _ => SamePendingQueue.attester ok)

private theorem growStep_processAttestation {attestation : Attestation preset f} {parent : Slot}
    (ok : processAttestation config checks s parent attestation = .ok t) : GrowStep s t :=
  GrowStep.of_data (frame_processAttestation ok)
    (congrArg (·.data) (processAttestation_registry ok).1)
    (fun electra => SamePendingQueue.attestation electra ok)

private theorem growStep_processDeposit {before : f < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processDeposit ok).toFrame (registryLifecycle_processDeposit ok)
    (fun electra => SamePendingQueue.deposit electra ok)

private theorem growStep_processVoluntaryExit {signed : SignedVoluntaryExit}
    (ok : processVoluntaryExit config checks s signed = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processVoluntaryExit ok).toFrame
    (registryLifecycle_processVoluntaryExit ok) (fun _ => SamePendingQueue.voluntary ok)

private theorem growStep_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processBlsToExecutionChange ok).toFrame
    (registryLifecycle_processBlsToExecutionChange ok) (fun _ => SamePendingQueue.bls ok)

private theorem growStep_processDepositRequest {electra : .pectra ≤ f} {request : DepositRequest}
    (ok : processDepositRequest s electra request = .ok t) : GrowStep s t :=
  GrowStep.of_data (frame_processDepositRequest ok).toFrame
    (congrArg (·.data) (processDepositRequest_ok ok).2.1)
    (fun _ => SamePendingQueue.depositRequest ok)

private theorem growStep_processWithdrawalRequest {electra : .pectra ≤ f}
    {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) : GrowStep s t :=
  GrowStep.of_same (frame_processWithdrawalRequest ok).toFrame
    (registryLifecycle_processWithdrawalRequest ok)
    (fun _ => SamePendingQueue.withdrawalRequest ok)

/-- A queued consolidation assigns its source an exit after the current epoch. -/
private theorem grows_queueConsolidation {electra : .pectra ≤ f}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    Grows s t := by
  obtain ⟨churned, written, epoch, withdrawal, -, assigned, later, -, set, validators, pushed⟩ :=
    queueConsolidation_queued delay ok
  intro electra'
  refine ⟨[⟨sourceIndex, targetIndex⟩], ?_, fun c member => ?_⟩
  · exact pushed
  · rw [List.mem_singleton] at member
    subst member
    rw [validators]
    exact ⟨_, getValidator_eq_ok_iff.mp (getValidator_setValidator_self set), later, assigned⟩

/-- A consolidation request switches credentials or queues a consolidation. -/
private theorem growStep_processConsolidationRequest {electra : .pectra ≤ f}
    {request : ConsolidationRequest}
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processConsolidationRequest config s electra request = .ok t) : GrowStep s t := by
  have frame := (frame_processConsolidationRequest ok).toFrame
  have life := registryLifecycle_processConsolidationRequest ok
  suffices new : Grows s t from ⟨frame, life, new⟩
  clear frame life
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals try first
    | (cases ok; done)
    | (cases ok; exact Grows.of_same fun _ => rfl)
    | exact Grows.of_same fun _ => SamePendingQueue.compounding (liftAccessor_ok.mp ok)
  exact grows_queueConsolidation delay ok

private theorem growStep_processExecutionRequests {body : BeaconBlockBody preset f}
    {electra : .pectra ≤ f ∧ f < .glamsterdam}
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processExecutionRequests config s body electra = .ok t) : GrowStep s t := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
  exact (GrowStep.fold (fun _ _ _ ok => growStep_processDepositRequest ok) deposits).trans <|
    (GrowStep.fold (fun _ _ _ ok => growStep_processWithdrawalRequest ok) withdrawals).trans
      (GrowStep.fold (fun _ _ _ ok => growStep_processConsolidationRequest delay ok)
        consolidations)

private theorem growStep_processOperations {body : BeaconBlockBody preset f} {parent : Slot}
    (early : f < .glamsterdam) (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processOperations config checks s body parent = .ok t) :
    GrowStep s t := by
  unfold processOperations at ok
  rw [dite_eq_right (show ¬ .glamsterdam ≤ f from Nat.not_le_of_lt early)] at ok
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, _, _, _, _, proposers, _, attesters, _, attested, _, deposits, exited,
    exits, changed, changes, requests⟩ := ok
  have c : GrowStep exited changed := by
    unfold processBlsToExecutionChanges at changes
    split at changes
    · rw [← Array.foldlM_toList] at changes
      exact GrowStep.fold (fun _ _ _ ok => growStep_processBlsToExecutionChange ok) changes
    · cases changes; exact GrowStep.refl _
  have r : GrowStep changed t := by
    split at requests
    · exact growStep_processExecutionRequests delay requests
    · cases requests; exact GrowStep.refl _
  exact (GrowStep.fold (fun _ _ _ ok => growStep_processProposerSlashing ok) proposers).trans <|
    (GrowStep.fold (fun _ _ _ ok => growStep_processAttesterSlashing ok) attesters).trans <|
    (GrowStep.fold (fun _ _ _ ok => growStep_processAttestation ok) attested).trans <|
    (GrowStep.fold (fun _ _ _ ok => growStep_processDeposit ok) deposits).trans <|
    (GrowStep.fold (fun _ _ _ ok => growStep_processVoluntaryExit ok) exits).trans <|
    c.trans r

/-- A block from Altair and before Gloas keeps the frame and the lifecycle.

It also grows the queue. -/
private theorem growStep_processBlock {engine : ExecutionEngine preset f}
    {block : BeaconBlock preset f} (altair : .altair ≤ f) (early : f < .glamsterdam)
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : processBlock config checks engine s block = .ok t) : GrowStep s t := by
  unfold processBlock at ok
  simp only [altair, ↓reduceDIte] at ok
  unfold processBlockAltair at ok
  simp only [stateBeforeOperations, bind_assoc, bind_ok_iff] at ok
  obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
    votedOk, operated, operatedOk, synced⟩ := ok
  rw [dite_eq_right (show ¬ .glamsterdam ≤ f from Nat.not_le_of_lt early)] at paidOk
  cases paidOk
  have header : GrowStep s headed := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
    exact GrowStep.of_data (frame_processBlockHeader headedOk).toFrame rfl fun _ => rfl
  have e : GrowStep headed executed := by
    split at executedOk
    · exact GrowStep.of_data (frame_processBlockExecution executedOk).toFrame
        (congrArg (·.data) (processBlockExecution_validators executedOk))
        (fun _ => SamePendingQueue.blockExecution early executedOk)
    · cases executedOk; exact GrowStep.refl _
  have randao : GrowStep executed revealed := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealedOk
    exact GrowStep.of_data (frame_processRandao revealedOk).toFrame rfl fun _ => rfl
  have v : GrowStep revealed voted := by
    split at votedOk
    · obtain ⟨_, _, rest⟩ := processEth1Data_eq votedOk
      exact GrowStep.of_data (frame_processEth1Data votedOk).toFrame (by rw [← rest])
        (fun _ => by unfold SamePendingQueue; rw [← rest])
    · cases votedOk; exact GrowStep.refl _
  have sync : GrowStep operated t := by
    have frame := (frame_processSyncAggregate synced).toFrame
    obtain ⟨balances, rfl⟩ := processSyncAggregate_eq synced
    exact GrowStep.of_data frame rfl fun _ => rfl
  exact header.trans <| e.trans <| randao.trans <| v.trans <|
    (growStep_processOperations early delay operatedOk).trans sync

end GrowSteps

/-! ## The queue of a run from X, and the stake a pass can move -/

private theorem fundingSources_eq {f : Fork} (electra : .pectra ≤ f) (s : BeaconState preset f) :
    fundingSources s = (s.pendingConsolidations electra).data.toList := by
  simp [fundingSources, electra]

/-- The queue is the unread part of X's queue, then entries that are new since X.

Every new entry has a source whose exit was assigned after `e0`, the epoch of X. -/
private def Shape (L : List PendingConsolidation) (e0 : Epoch) (n : ℕ) {f : Fork}
    (z : BeaconState preset f) : Prop :=
  ∃ N : List PendingConsolidation, fundingSources z = L.drop n ++ N ∧
    ∀ c ∈ N, ∃ w, z.validators.data[c.sourceIndex.toNat]? = some w ∧
      e0 < w.exitEpoch ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH

/-- A state of any fork with the same queue and a later life of its validators has the shape. -/
private theorem Shape.carry {L : List PendingConsolidation} {e0 : Epoch} {n : ℕ} {f g : Fork}
    {a : BeaconState preset f} {b : BeaconState preset g} (shape : Shape L e0 n a)
    (queue : fundingSources b = fundingSources a) (life : RegistryLifecycle a b) :
    Shape L e0 n b := by
  obtain ⟨N, eq, new⟩ := shape
  refine ⟨N, queue.trans eq, fun c member => ?_⟩
  obtain ⟨w, read, later, assigned⟩ := new c member
  obtain ⟨w', read', kept⟩ := life.validators _ w read
  have exit := kept.exitEpoch assigned
  exact ⟨w', read', by rw [exit]; exact later, by rw [exit]; exact assigned⟩

/-- A block that grows the queue keeps the shape. -/
private theorem Shape.grow {L : List PendingConsolidation} {e0 : Epoch} {n : ℕ} {f : Fork}
    {a b : BeaconState preset f} (electra : .pectra ≤ f) (shape : Shape L e0 n a)
    (grows : Grows a b) (life : RegistryLifecycle a b) (started : e0 ≤ getCurrentEpoch a) :
    Shape L e0 n b := by
  obtain ⟨N, eq, new⟩ := shape
  obtain ⟨added, queue, fresh⟩ := grows electra
  refine ⟨N ++ added, by rw [fundingSources_eq electra, queue, ← fundingSources_eq electra, eq,
    List.append_assoc], fun c member => ?_⟩
  rcases List.mem_append.mp member with old | recent
  · obtain ⟨w, read, later, assigned⟩ := new c old
    obtain ⟨w', read', kept⟩ := life.validators _ w read
    have exit := kept.exitEpoch assigned
    exact ⟨w', read', by rw [exit]; exact later, by rw [exit]; exact assigned⟩
  · obtain ⟨w, read, later, assigned⟩ := fresh c recent
    exact ⟨w, read, UInt64.lt_of_le_of_lt started later, assigned⟩

/-- A pass that reads `r` entries moves the shape on by `r`. -/
private theorem Shape.pass {L : List PendingConsolidation} {e0 : Epoch} {n r : ℕ} {f : Fork}
    {a b : BeaconState preset f} (shape : Shape L e0 n a)
    (queue : fundingSources b = (fundingSources a).drop r) (life : RegistryLifecycle a b) :
    Shape L e0 (n + r) b := by
  obtain ⟨N, eq, new⟩ := shape
  refine ⟨N.drop (r - (L.length - n)), ?_, fun c member => ?_⟩
  · rw [queue, eq, List.drop_append, List.drop_drop]
    simp [List.length_drop]
  · obtain ⟨w, read, later, assigned⟩ := new c (List.mem_of_mem_drop member)
    obtain ⟨w', read', kept⟩ := life.validators _ w read
    have exit := kept.exitEpoch assigned
    exact ⟨w', read', by rw [exit]; exact later, by rw [exit]; exact assigned⟩

/-- The stake that X lets a pending consolidation move: the cap of its source at X.

It counts only a source that is unslashed at X and can withdraw by `high + 1`. -/
private def capBound (x : ForkedBeaconState preset) (high : ℕ) (c : PendingConsolidation) : ℕ :=
  match x.state.validators.data[c.sourceIndex.toNat]? with
  | some v =>
    if v.slashed = false ∧ v.withdrawableEpoch.toNat ≤ high + 1 then
      (withdrawalMaxEffectiveBalance preset x.fork v).toNat
    else 0
  | none => 0

/-- A key that cannot switch to compounding credentials has a cap that does not rise. -/
private theorem withdrawalMax_le {f g : Fork} (hf : .pectra ≤ f) (hg : .pectra ≤ g)
    (caps : CapOrder preset) {v w : Validator}
    (frozen : hasCompoundingWithdrawalCredential w = true →
      hasCompoundingWithdrawalCredential v = true) :
    withdrawalMaxEffectiveBalance preset f w ≤ withdrawalMaxEffectiveBalance preset g v := by
  simp only [withdrawalMaxEffectiveBalance, hf, hg, ↓reduceIte, getMaxEffectiveBalance]
  by_cases hw : hasCompoundingWithdrawalCredential w = true
  · simp [hw, frozen hw]
  · by_cases hv : hasCompoundingWithdrawalCredential v = true
    · simp only [hw, hv, Bool.false_eq_true, ↓reduceIte]
      exact caps.compounding
    · simp only [hw, hv, Bool.false_eq_true, ↓reduceIte]
      exact UInt64.le_refl _

/-- What a run from X, at a state `p` of the epoch pass, knows about the pending consolidations. -/
private structure PassFacts (x : ForkedBeaconState preset) (high : ℕ) {f : Fork}
    (p : BeaconState preset f) : Prop where
  electraX : .pectra ≤ x.fork
  electraP : .pectra ≤ f
  caps : CapOrder preset
  delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  within : high + 2 ≤ (getCurrentEpoch x.state).toNat +
    config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  life : RegistryLifecycle x.state p
  cap : Internal.CapStep config x.state p
  orderedX : PendingConsolidationsOrdered config (getCurrentEpoch x.state).toNat x.state
  invariantP : PendingConsolidationInvariant config p
  cappedX : ∀ v ∈ x.state.validators.data,
    v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset x.fork v
  next : (getCurrentEpoch p).toNat + 1 ≤ high + 1
  nextNat : (getCurrentEpoch p + 1).toNat = (getCurrentEpoch p).toNat + 1

/-- An entry of X's queue, still queued at the pass, moves at most its cap at X. -/
private theorem old_entry_bound {x : ForkedBeaconState preset} {high : ℕ} {f : Fork}
    {p : BeaconState preset f} (facts : PassFacts (config := config) x high p)
    {c : PendingConsolidation}
    (inX : c ∈ (x.state.pendingConsolidations facts.electraX).data.toList)
    (inP : c ∈ (p.pendingConsolidations facts.electraP).data.toList) :
    sourceBound p (getCurrentEpoch p + 1) c ≤ capBound x high c := by
  obtain ⟨v, foundX, -, -, assignedX⟩ := (facts.orderedX.1 facts.electraX).2 c inX
  obtain ⟨-, unslashedX, -⟩ := (facts.orderedX.2 facts.electraX).2 c inX v foundX
  obtain ⟨wP, foundP', -, exitDelayP, -⟩ := (facts.invariantP facts.electraP).2 c inP
  obtain ⟨w, foundP, lifecycle⟩ := facts.life.validators _ v foundX
  obtain rfl : w = wP := Option.some.inj (foundP.symm.trans foundP')
  simp only [sourceBound, capBound, foundP, foundX]
  split
  · rename_i due
    have exitEq := lifecycle.exitEpoch assignedX
    have slashedX : v.slashed = false := by
      cases flag : v.slashed
      · rfl
      · have := ((facts.cap.withdrawal _ v w foundX foundP).1 flag assignedX).1
        rw [due.1] at this
        cases this
    have dueNat := UInt64.le_iff_toNat_le.mp due.2
    have withdrawX := unslashedX slashedX
    rw [facts.nextNat] at dueNat
    have exitNat := congrArg UInt64.toNat exitEq
    have exitDelay : w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
        w.withdrawableEpoch.toNat := exitDelayP
    have dueX : v.slashed = false ∧ v.withdrawableEpoch.toNat ≤ high + 1 :=
      ⟨slashedX, by have := facts.next; omega⟩
    simp only [dueX, and_self, ↓reduceIte]
    have capped : w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f w :=
      facts.cap.capped facts.cappedX w (Array.mem_of_getElem? foundP)
    have bounded := withdrawalMax_le facts.electraP facts.electraX facts.caps
      ((facts.cap.frozen _ v w foundX foundP assignedX).2)
    exact UInt64.le_iff_toNat_le.mp (UInt64.le_trans capped bounded)
  · exact Nat.zero_le _

/-- An entry that is new since X moves nothing at the pass.

Its source exits after X, so it withdraws after the run. -/
private theorem new_entry_zero {x : ForkedBeaconState preset} {high : ℕ} {f : Fork}
    {p : BeaconState preset f} (facts : PassFacts (config := config) x high p)
    {c : PendingConsolidation}
    (inP : c ∈ (p.pendingConsolidations facts.electraP).data.toList) {w : Validator}
    (foundW : p.validators.data[c.sourceIndex.toNat]? = some w)
    (fresh : getCurrentEpoch x.state < w.exitEpoch) :
    sourceBound p (getCurrentEpoch p + 1) c = 0 := by
  obtain ⟨w', found', -, exitDelay, -⟩ := (facts.invariantP facts.electraP).2 c inP
  obtain rfl : w' = w := Option.some.inj (found'.symm.trans foundW)
  have later := UInt64.lt_iff_toNat_lt.mp fresh
  simp only [sourceBound, foundW]
  split
  · rename_i due
    have dueNat := UInt64.le_iff_toNat_le.mp due.2
    rw [facts.nextNat] at dueNat
    have := facts.next
    have := facts.within
    have := facts.delay
    omega
  · rfl

/-- A pass, from a state with the shape, credits at most the caps at X of the entries it reads. -/
private theorem pass_step {x : ForkedBeaconState preset} {high : ℕ} {f : Fork}
    {p t : BeaconState preset f} {n : ℕ} (facts : PassFacts (config := config) x high p)
    (shape : Shape (x.state.pendingConsolidations facts.electraX).data.toList
      (getCurrentEpoch x.state) n p)
    (computed : processPendingConsolidations p facts.electraP = .ok t) :
    ∃ r, Shape (x.state.pendingConsolidations facts.electraX).data.toList
        (getCurrentEpoch x.state) (n + r) t ∧ RegistryLifecycle p t ∧
      credited p t ≤
        ((((x.state.pendingConsolidations facts.electraX).data.toList.drop n).take r).map
          (capBound x high)).sum := by
  obtain ⟨result, passed, balancesEq, queueEq⟩ := processPendingConsolidations_pass computed
  obtain ⟨validators, sizes, credits⟩ :=
    pass_credits_le (getCurrentEpoch p + 1) _ passed
  have sameValidators := (processPendingConsolidations_kept computed).1
  have life : RegistryLifecycle p t := .of_data (congrArg (·.data) sameValidators)
  have queue : fundingSources t = (fundingSources p).drop result.2 := by
    rw [fundingSources_eq facts.electraP, fundingSources_eq facts.electraP]
    exact queueEq
  refine ⟨result.2, shape.pass queue life, life, ?_⟩
  have creditsEq : credited p t = credited p result.1 := by
    simp [credited, actualBalanceAt, balancesEq]
  rw [creditsEq]
  refine Nat.le_trans credits ?_
  obtain ⟨N, eq, new⟩ := shape
  rw [← fundingSources_eq facts.electraP, eq, List.take_append, List.map_append,
    List.sum_append]
  have oldPart : ((((x.state.pendingConsolidations facts.electraX).data.toList.drop n).take
      result.2).map (sourceBound p (getCurrentEpoch p + 1))).sum ≤
      ((((x.state.pendingConsolidations facts.electraX).data.toList.drop n).take result.2).map
        (capBound x high)).sum := by
    apply List.sum_le_sum
    intro c member
    have inDrop := List.mem_of_mem_take member
    refine old_entry_bound facts (List.mem_of_mem_drop inDrop) ?_
    rw [← fundingSources_eq facts.electraP, eq]
    exact List.mem_append_left _ inDrop
  have newPart : ((N.take (result.2 -
      ((x.state.pendingConsolidations facts.electraX).data.toList.drop n).length)).map
        (sourceBound p (getCurrentEpoch p + 1))).sum = 0 := by
    apply List.sum_eq_zero
    intro m member
    obtain ⟨c, inTake, rfl⟩ := List.mem_map.mp member
    have inN := List.mem_of_mem_take inTake
    obtain ⟨w, foundW, fresh, -⟩ := new c inN
    refine new_entry_zero facts ?_ foundW fresh
    rw [← fundingSources_eq facts.electraP, eq]
    exact List.mem_append_right _ inN
  omega

/-- The upgrades due at a slot keep the shape of the queue. -/
private theorem upgrade_shape {L : List PendingConsolidation} {e0 : Epoch} {n : ℕ}
    {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (electra : .pectra ≤ pre.fork) (shape : Shape L e0 n pre.state)
    (ok : upgradeNext config checks pre = .ok post) (early : post.val.fork < .glamsterdam) :
    .pectra ≤ post.val.fork ∧ Shape L e0 n post.val.state := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · exact absurd electra (Nat.not_le_of_lt (by decide : Fork.phase0 < Fork.pectra))
  · exact absurd electra (Nat.not_le_of_lt (by decide : Fork.altair < Fork.pectra))
  · exact absurd electra (Nat.not_le_of_lt (by decide : Fork.bellatrix < Fork.pectra))
  · exact absurd electra (Nat.not_le_of_lt (by decide : Fork.shapella < Fork.pectra))
  · exact absurd electra (Nat.not_le_of_lt (by decide : Fork.dencun < Fork.pectra))
  · obtain ⟨_, upgraded, rfl⟩ := ok
    refine ⟨(by decide : Fork.pectra ≤ Fork.fusaka),
      shape.carry ?_ (.of_data (upgradeToFulu_spec upgraded).1)⟩
    simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
    obtain ⟨_, -, rfl⟩ := upgraded
    simp [fundingSources, carryFields, carryList, carryRooted,
      show Fork.pectra ≤ Fork.fusaka from by decide]
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.lt_irrefl _ early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.not_le_of_lt early (show Fork.glamsterdam ≤ .hegota from by decide))

private theorem upgrades_shape {L : List PendingConsolidation} {e0 : Epoch} {n : ℕ}
    {advanced last : ForkedBeaconState preset} (electra : .pectra ≤ advanced.fork)
    (early : last.fork < .glamsterdam) (shape : Shape L e0 n advanced.state)
    (ok : processUpgrades config checks advanced = .ok last) : Shape L e0 n last.state := by
  have rest := processUpgrades_induction
    (property := fun z => z.fork < .glamsterdam → .pectra ≤ z.fork ∧ Shape L e0 n z.state)
    (fun {pre post} h ok early => by
      obtain ⟨electraPre, shapePre⟩ := h (Nat.lt_trans post.property early)
      exact upgrade_shape electraPre shapePre ok early)
    (fun _ => ⟨electra, shape⟩) ok
  exact (rest early).2

/-! ## The stages of an epoch -/

/-- The order of the pending consolidations of a state at its own epoch. -/
private abbrev OrderedAt {f : Fork} (config : Config) (s : BeaconState preset f) : Prop :=
  PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s

/-- A stage other than the pass keeps the slot, the queue and the order, and the lifecycle. -/
private theorem stage_rel {f : Fork} (electra : .pectra ≤ f) {k : EpochStage}
    (notPass : k ≠ .pendingConsolidations) {a b : BeaconState preset f}
    (edge : EpochStage.Edge config checks k a b) :
    RegistryLifecycle a b ∧ b.slot = a.slot ∧ fundingSources b = fundingSources a ∧
      (OrderedAt config a → OrderedAt config b) := by
  refine ⟨edge.registryLifecycle, edge.slot_eq, ?_, edge.pendingConsolidationsOrdered⟩
  rw [fundingSources_eq electra, fundingSources_eq electra,
    show b.pendingConsolidations = a.pendingConsolidations from edge.samePendingQueue notPass]

/-- The stages before the pass, from the cached state, keep what the pass reads. -/
private theorem prefix_rel {f : Fork} (electra : .pectra ≤ f) {stages : List EpochStage}
    (notPass : ∀ k ∈ stages, k ≠ .pendingConsolidations) {a b : BeaconState preset f}
    (trace : EpochTrace (EpochStage.action config checks) stages a b) :
    RegistryLifecycle a b ∧ b.slot = a.slot ∧ fundingSources b = fundingSources a ∧
      (OrderedAt config a → OrderedAt config b) := by
  apply trace.transport
    (fun a b : BeaconState preset f => RegistryLifecycle a b ∧ b.slot = a.slot ∧
      fundingSources b = fundingSources a ∧ (OrderedAt config a → OrderedAt config b))
    (fun _ => ⟨.refl _, rfl, rfl, id⟩)
    (fun one two => ⟨one.1.trans two.1, two.2.1.trans one.2.1, two.2.2.1.trans one.2.2.1,
      two.2.2.2 ∘ one.2.2.2⟩)
  intro k member s t computed
  exact stage_rel electra (notPass k member) (EpochStage.action_cases.mp computed)

/-- The events that the replay of the rewards records are rewards, penalties or inactivity. -/
private theorem rewards_noConsolidations {f : Fork} {pre post : BalanceReplay preset f}
    (initial : ∀ e ∈ pre.2, e.source ≠ .consolidations)
    (ok : replayRewards (config := config) pre = .ok post) :
    ∀ e ∈ post.2, e.source ≠ .consolidations := by
  have record {pre post : BalanceReplay preset f} {source : BalanceSource}
      {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
      {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
      (notConsolidation : source ≠ .consolidations)
      (initial : ∀ e ∈ pre.2, e.source ≠ .consolidations)
      (ok : recordBalance source limits action pre = .ok post) :
      ∀ e ∈ post.2, e.source ≠ .consolidations := by
    simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨⟨credit, debit⟩, _, t, _, rfl⟩ := ok
    intro e member
    rcases List.mem_append.mp member with old | new
    · exact initial e old
    · exact (List.mem_singleton.mp new) ▸ notConsolidation
  exact replayRewards_induction (fun pre => ∀ e ∈ pre.2, e.source ≠ .consolidations)
    (fun prior ok => record (by decide) prior ok)
    (fun penalty prior ok => record (by rcases penalty with rfl | rfl <;> decide) prior ok)
    initial ok

/-- The queue of X. -/
private abbrev queueX (x : ForkedBeaconState preset) (h : .pectra ≤ x.fork) :
    List PendingConsolidation :=
  (x.state.pendingConsolidations h).data.toList

/-- A slot step moves the shape of the queue on, and its consolidation credits are bounded. -/
private theorem slot_step {g x m last : ForkedBeaconState preset}
    (shared : Run config checks g x) (pre : Run config checks x m)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) (electra : .pectra ≤ x.fork)
    (high : ℕ) (within : high + 2 ≤ (getCurrentEpoch x.state).toNat +
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : advanceSlotAcross config checks m = .ok last) (early : last.fork < .glamsterdam)
    (endEpoch : (getCurrentEpoch last.state).toNat ≤ high + 1) {n : ℕ}
    (shape : Shape (queueX x electra) (getCurrentEpoch x.state) n m.state) :
    ∃ r, Shape (queueX x electra) (getCurrentEpoch x.state) (n + r) last.state ∧
      ∀ {events : List (BalanceEvent preset)},
        (Step.slot ok : Step config checks m last).balanceEvents = .ok events →
        ((events.filter (·.source = .consolidations)).map BalanceEvent.credits).sum ≤
          ((((queueX x electra).drop n).take r).map (capBound x high)).sum := by
  have beforeFork : m.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Step.slot ok).chainStep.fork_le early
  have mFork : .pectra ≤ m.fork := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
  obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
  obtain ⟨crossings, crossingOk, -⟩ := upgradeBalanceReplay_bounded upgrades
  have advanceCopy := slotOk
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at advanceCopy
  obtain ⟨next, nextOk, cached, cachedOk, epoched, epochOk, afterEq⟩ := advanceCopy
  have sum : next.toNat = m.state.slot.toNat + 1 :=
    (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp (liftAccessor_ok.mp nextOk))).2
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have shapeCached : Shape (queueX x electra) (getCurrentEpoch x.state) n cached := by
    rw [cachedEq]; exact shape
  by_cases boundary : next % preset.SLOTS_PER_EPOCH = 0
  · simp only [epochIfLast, boundary, ↓reduceIte] at epochOk
    obtain ⟨middle, updated, recorded, recordOk, updatedOk, validators, balances, cutOk⟩ :=
      epochBalanceReplay_result_before cached epoched beforeFork epochOk
    obtain ⟨justified, scored, rewarded, registered, slashed, reset, deposited, rewardEvents,
      limit, trace6, justifiedOk, scoredOk, rewardedOk, registeredOk, slashedOk, resetOk,
      depositedOk, consolidatedOk, rewardReplay, recordedEq⟩ := funding_epoch_site cutOk recordOk
    have trace7 : EpochTrace (EpochStage.action config checks)
        [.justification, .inactivity, .rewards, .registry, .slashings, .eth1Reset,
          .pendingDeposits] cached deposited :=
      EpochTrace.append_iff.mpr
        ⟨reset, trace6, .cons (EpochStage.action_cases.mpr depositedOk) .nil⟩
    simp only [EpochStage.Edge, mFork, ↓reduceDIte] at consolidatedOk
    simp only [mFork, ↓reduceDIte] at recordedEq
    -- The facts about the run before the step.
    have xEarly : x.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps pre.chainSteps) beforeFork
    have lifeXM : RegistryLifecycle x.state m.state := pre.registryLifecycle
    have capXM := (Internal.CapStep.run pre caps.activation caps.compounding beforeFork).1
    have orderedM : OrderedAt config m.state :=
      (shared.append pre).pendingConsolidationsOrdered genesis beforeFork delay
    have orderedX := shared.pendingConsolidationsOrdered genesis xEarly delay
    have cappedX := shared.effectiveBalance_capped genesis caps.activation caps.compounding xEarly
    -- The cached state is the state of the step, up to its roots.
    have lifeMC : RegistryLifecycle m.state cached := .of_data (by rw [cachedEq])
    have slotMC : cached.slot = m.state.slot := by rw [cachedEq]
    have queueMC : fundingSources cached = fundingSources m.state := by rw [cachedEq]; rfl
    have orderedC : OrderedAt config cached := by rw [cachedEq]; exact orderedM
    have capMC : Internal.CapStep config m.state cached := by
      rw [cachedEq]; exact Internal.CapStep.data
    -- The stages up to the pass.
    obtain ⟨lifeCD, slotCD, queueCD, orderedCD⟩ := prefix_rel mFork (by
      intro k member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact fun h => by cases h)
      trace7
    have capCD := Internal.CapStep.epochTrace trace7
    have epochD : getCurrentEpoch deposited = getCurrentEpoch m.state := by
      simp only [getCurrentEpoch, slotCD, slotMC]
    -- The epoch of the next state.
    have divides : preset.SLOTS_PER_EPOCH.toNat ∣ m.state.slot.toNat + 1 := by
      rw [← sum]
      exact Nat.dvd_of_mod_eq_zero (by simpa using congrArg UInt64.toNat boundary)
    have epochLast : (getCurrentEpoch last.state).toNat = (getCurrentEpoch m.state).toNat + 1 := by
      have advancedEpoch : getCurrentEpoch last.state = getCurrentEpoch
          ({ epoched with slot := next } : BeaconState preset m.fork) := by
        rw [afterEq]
        exact congrArg (computeEpochAtSlot preset) (processUpgrades_slot upgrades)
      rw [advancedEpoch]
      have nextEpoch :=
        getCurrentEpoch_toNat ({ epoched with slot := next } : BeaconState preset m.fork)
      simp only at nextEpoch
      rw [nextEpoch, sum, Nat.succ_div_of_dvd divides, getCurrentEpoch_toNat m.state]
    have nextBound : (getCurrentEpoch deposited).toNat + 1 ≤ high + 1 := by
      rw [epochD]; omega
    have nextNat :
        (getCurrentEpoch deposited + 1).toNat = (getCurrentEpoch deposited).toNat + 1 := by
      have fits := (getCurrentEpoch last.state).toNat_lt
      rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt]
      rw [epochD]; omega
    have facts : PassFacts (config := config) x high deposited :=
      { electraX := electra, electraP := mFork, caps := caps, delay := delay, within := within,
        life := lifeXM.trans (lifeMC.trans lifeCD), cap := capXM.trans (capMC.trans capCD),
        orderedX := orderedX, invariantP := (orderedCD orderedC).1, cappedX := cappedX,
        next := nextBound, nextNat := nextNat }
    have shapeD : Shape (queueX x electra) (getCurrentEpoch x.state) n deposited :=
      shapeCached.carry queueCD lifeCD
    obtain ⟨r, shapeMiddle, lifePM, credits⟩ := pass_step facts shapeD consolidatedOk
    refine ⟨r, ?_, fun {events} replayed => ?_⟩
    · have trace := processEpoch_trace epochOk
      change EpochTrace _ (EpochStage.prefixStages ++ [.payments, .effectiveBalances,
        .slashingsReset, .randaoReset, .history, .participation, .syncCommittees,
        .proposerLookahead, .ptcWindow]) _ _ at trace
      obtain ⟨middle', head, tailTrace⟩ := EpochTrace.append_iff.mp trace
      have midEq : middle' = middle := by
        have h1 : epochBeforePayments config checks cached = .ok middle' :=
          (epochBeforePayments_eq_run config checks cached).trans
            (EpochTrace.run_ok_iff.mpr head)
        rw [h1] at cutOk
        exact Except.ok.inj cutOk
      subst midEq
      obtain ⟨lifeTail, -, queueTail, -⟩ := prefix_rel mFork (by
        intro k member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact fun h => by cases h) tailTrace
      have shapeEpoched := shapeMiddle.carry queueTail lifeTail
      have shapeAdvanced : Shape (queueX x electra) (getCurrentEpoch x.state) (n + r)
          advanced := by
        rw [← afterEq]
        exact shapeEpoched.carry rfl (.of_data rfl)
      exact upgrades_shape (advanced := ⟨m.fork, advanced⟩) mFork early shapeAdvanced upgrades
    · have eventsEq : events = recorded ++ crossings :=
        Except.ok.inj (replayed.symm.trans (Step.balanceEvents_epoch_slot ok cachedOk nextOk
          boundary recordOk slotOk crossingOk))
      have rewardsNo := rewards_noConsolidations (pre := (scored, [])) (by simp) rewardReplay
      have f1 : rewardEvents.filter (fun e => decide (e.source = .consolidations)) = [] :=
        List.filter_eq_nil_iff.mpr fun e member => by simpa using rewardsNo e member
      have f2 : crossings.filter (fun e => decide (e.source = .consolidations)) = [] :=
        List.filter_eq_nil_iff.mpr fun e member => by
          simp [upgradeBalanceReplay_crossing crossingOk e member]
      rw [eventsEq, recordedEq]
      simp only [List.append_assoc, List.filter_append, f1, f2]
      simpa [List.filter_cons, credited, BalanceEvent.credits, actualBalanceAt] using credits
  · simp only [epochIfLast, boundary, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochOk
    subst epochOk
    refine ⟨0, ?_, fun {events} replayed => ?_⟩
    · have shapeAdvanced : Shape (queueX x electra) (getCurrentEpoch x.state) (n + 0)
          advanced := by
        rw [← afterEq]
        exact shapeCached.carry rfl (.of_data rfl)
      exact upgrades_shape (advanced := ⟨m.fork, advanced⟩) mFork early shapeAdvanced upgrades
    · have eventsEq : events = crossings := by
        simpa [Step.balanceEvents, cachedOk, nextOk, boundary, slotOk, crossingOk, pure,
          Except.pure,
          bind, Except.bind] using replayed.symm
      subst eventsEq
      have none : (events.filter (·.source = .consolidations)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro e member
        simp [upgradeBalanceReplay_crossing crossingOk e member]
      simp [none]

/-- A block keeps the shape of the queue: it only appends entries that are new since X. -/
private theorem block_step {f : Fork} {e0 : Epoch} {L : List PendingConsolidation} {n : ℕ}
    (electra : .pectra ≤ f) (early : f < .glamsterdam)
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {engine : ExecutionEngine preset f} {signed : SignedBeaconBlock preset f}
    {s t : BeaconState preset f}
    (ok : applySignedBlock config checks engine s signed true = .ok t)
    (started : e0 ≤ getCurrentEpoch s) (shape : Shape L e0 n s) : Shape L e0 n t := by
  have grown := growStep_processBlock (Nat.le_trans (by decide) electra) early delay
    (applySignedBlock_ok ok).2.1
  exact shape.grow electra grown.2.2 grown.2.1 started

/-- The consolidation credits of a run from X are within the caps of the entries it reads. -/
private theorem run_credits {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (electra : .pectra ≤ x.fork) (high : ℕ)
    (within : high + 2 ≤ (getCurrentEpoch x.state).toNat +
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    ∃ n, Shape (queueX x electra) (getCurrentEpoch x.state) n y.state ∧
      ((events.filter (·.source = .consolidations)).map BalanceEvent.credits).sum ≤
        (((queueX x electra).take n).map (capBound x high)).sum := by
  induction tail generalizing events with
  | nil =>
    cases replayed
    refine ⟨0, ⟨[], ?_, fun c member => by simp at member⟩, by simp⟩
    rw [fundingSources_eq electra]
    simp [queueX]
  | @snoc middle last pre step ih =>
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    have epochStep := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
    obtain ⟨n, shape, bound⟩ := ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early)
      (by omega) priorOk
    have inFork : .pectra ≤ middle.fork :=
      Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
    have started : getCurrentEpoch x.state ≤ getCurrentEpoch middle.state :=
      currentEpoch_le_of_chainSteps pre.chainSteps
    have beforeFork : middle.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have growth : ∀ {r : ℕ}, (((queueX x electra).take n).map (capBound x high)).sum +
        ((((queueX x electra).drop n).take r).map (capBound x high)).sum =
        (((queueX x electra).take (n + r)).map (capBound x high)).sum := by
      intro r
      rw [List.take_add, List.map_append, List.sum_append]
    have stepResult : ∃ r, Shape (queueX x electra) (getCurrentEpoch x.state) (n + r) last.state ∧
        ∀ {added : List (BalanceEvent preset)}, step.balanceEvents = .ok added →
          ((added.filter (·.source = .consolidations)).map BalanceEvent.credits).sum ≤
            ((((queueX x electra).drop n).take r).map (capBound x high)).sum := by
      cases step with
      | block engine signed due ok =>
        refine ⟨0, block_step inFork early (by omega) ok started shape, fun {added} addedOk => ?_⟩
        have none : (added.filter (·.source = .consolidations)) = [] :=
          List.filter_eq_nil_iff.mpr fun e member => by
            simpa using blockReplay_noConsolidations inFork early engine _ _
              (Step.balanceEvents_block early addedOk) e member
        simp [none]
      | slot ok =>
        obtain ⟨r, shapeLast, credits⟩ := slot_step shared pre genesis caps delay electra high
          within ok early endEpoch shape
        exact ⟨r, shapeLast, fun {added} addedOk => credits addedOk⟩
    obtain ⟨r, shapeLast, credits⟩ := stepResult
    refine ⟨n + r, shapeLast, ?_⟩
    by_cases selected : (getCurrentEpoch middle.state).toNat ≤ high + 1
    · simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
      obtain ⟨added, addedOk, rfl⟩ := rest
      have := credits addedOk
      rw [List.filter_append, List.map_append, List.sum_append, ← growth]
      omega
    · simp only [selected, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      rw [← growth]
      omega

/-- The caps of the entries of a queue, as the caps of their sources that X lets move. -/
private theorem capBound_sum (x : ForkedBeaconState preset) (high : ℕ)
    (queue : List PendingConsolidation) :
    (queue.map (capBound x high)).sum =
      ((((queue.filterMap fun c => x.state.validators.data[c.sourceIndex.toNat]?).filter
        fun v => !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)).map
          fun v => (withdrawalMaxEffectiveBalance preset x.fork v).toNat).sum) := by
  induction queue with
  | nil => simp
  | cons c rest ih =>
    cases lookup : x.state.validators.data[c.sourceIndex.toNat]? with
    | none => simpa [capBound, lookup] using ih
    | some v =>
      by_cases due : v.slashed = false ∧ v.withdrawableEpoch.toNat ≤ high + 1
      · simp [capBound, lookup, due, ih]
      · have : ¬ (!v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)) = true := by
          simpa [Bool.not_eq_true'] using due
        simp [capBound, lookup, due, this, ih]

/-! ## Group A: credits to exiting keys -/

/-- A1 (item 14, run lift).

Along C's run, no deposit credits a key that exits at the run's start.

The key stays not withdrawable through the run's end.

`exitedBalance` is PinDriftBound's private `processPendingDeposits_exited_balance`.

`kept` is the withdrawable-kept fact at the state before each deposit event of a slot step.

A block deposit needs none: from Electra it raises no balance.

It says that an assigned exit stays (`RegistryLifecycle`).

It says that once the exit is set, the withdrawable epoch only rises (`WithdrawableKept`).

The private sources of these facts are `WithdrawalKept` in PendingConsolidations.

The other private source is `Lives` in BranchLedger.

It also says that the epoch of each event's state is at most the run's last epoch. -/
theorem Run.exiting_deposit_credit_zero {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (high : ℕ) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (exitedBalance : PendingDepositsKeepExited (preset := preset) config checks)
    (kept : ∀ {u w : ForkedBeaconState preset} (ok : advanceSlotAcross config checks u = .ok w),
      tail.Contains (Step.slot ok) → ∀ {es : List (BalanceEvent preset)},
        (Step.slot ok : Step config checks u w).balanceEvents = .ok es →
        ∀ e ∈ es, e.source = .deposits →
          RegistryLifecycle x.state e.before.state ∧ WithdrawableKept x.state e.before.state ∧
          getCurrentEpoch e.before.state ≤ getCurrentEpoch y.state)
    (i : ℕ) (v : Validator) (found : x.state.validators.data[i]? = some v)
    (exited : v.exitEpoch.toNat < 2 ^ 64 - 1)
    (held : (getCurrentEpoch y.state).toNat < v.withdrawableEpoch.toNat) :
    ((events.filter (·.source = .deposits)).map (keyCredit i)).sum = 0 := by
  have located := run_located exitedBalance tail electra early high replayed
  apply List.sum_eq_zero
  intro n member
  obtain ⟨e, filtered, rfl⟩ := List.mem_map.mp member
  obtain ⟨inEvents, sourceEq⟩ := List.mem_filter.mp filtered
  simp only [decide_eq_true_eq] at sourceEq
  rcases located e inEvents sourceEq with unconditional | ⟨u, w, ok, es, contains, replayedEs,
      inStep, keeps⟩
  · have := unconditional i
    simp only [keyCredit]
    omega
  · obtain ⟨life, withdrawal, epoch⟩ := kept ok contains replayedEs e inStep sourceEq
    obtain ⟨w, read, lifecycle⟩ := life.validators i v found
    have assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
      rw [far] at exited
      exact absurd exited (Nat.lt_irrefl _)
    have sameExit := lifecycle.exitEpoch assigned
    have later := UInt64.le_iff_toNat_le.mp (withdrawal i v w found read assigned).1
    have now := UInt64.le_iff_toNat_le.mp epoch
    have same := keeps i w read (by rw [sameExit]; exact exited) (by omega)
    simp [keyCredit, actualBalanceAt, same]

/-- A2'' (rev 2.5.1).

Take a run from X whose last epoch is within the withdrawal delay of X's.

The consolidation credits to all keys along it are at most a sum of caps.

The sum is over the sources of X's pending consolidations.

They are unslashed at X and withdrawable by `high + 1`.

Each source counts at its cap at X.

An entry requested after X is due only past the run, so every applied entry is in X's queue.

It moves at most the source's effective balance, which is at most its cap.

An exited key cannot switch to compounding, so its cap does not rise after X. -/
theorem Run.consolidation_credits_le_X {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset)
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (high : ℕ) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (withinDelay : high + 2 ≤
      (getCurrentEpoch x.state).toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    ((events.filter (·.source = .consolidations)).map BalanceEvent.credits).sum ≤
      ((((x.state.pendingConsolidations electra).data.toList.filterMap fun c =>
        x.state.validators.data[c.sourceIndex.toNat]?).filter fun v =>
          !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)).map fun v =>
            (withdrawalMaxEffectiveBalance preset x.fork v).toNat).sum := by
  obtain ⟨n, -, bound⟩ := run_credits shared genesis caps delay electra high withinDelay tail
    early endEpoch replayed
  rw [← capBound_sum]
  refine Nat.le_trans bound ?_
  have split := List.take_append_drop n (x.state.pendingConsolidations electra).data.toList
  conv_rhs => rw [← split, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

end EthLib.Consensus.Models.Network.PinSplit
