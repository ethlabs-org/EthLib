module

public import EthLib.Consensus.Proofs.Transition.BalanceSources
public import EthLib.Consensus.Proofs.DirectSafety.ChurnBounds
public import EthLib.Consensus.Proofs.Transition.RewardDeltas

/-!
# Source bounds over a selected execution interval

The replay below executes the concrete transition passes and records their inputs and results.

It records positive changes per validator, so transfers cannot cancel losses or gains elsewhere.

No caller supplies the amount of a source or an accounting cap.

The source bounds retain the initial queues, scores and balances needed by arbitrary intervals.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Classical

noncomputable section

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

inductive BalanceSource where
  | rewards | penalties | inactivity | slashings | deposits | consolidations
  | withdrawals | sync | excess | crossing
  deriving DecidableEq

structure BalanceEvent (preset : Preset) where
  source : BalanceSource
  before : ForkedBeaconState preset
  after : ForkedBeaconState preset
  creditLimit : Nat
  debitLimit : Nat

def BalanceEvent.credits (event : BalanceEvent preset) : Nat :=
  ∑ i ∈ Finset.range event.after.state.balances.data.size,
    (actualBalanceAt event.after i - actualBalanceAt event.before i)

def BalanceEvent.debits (event : BalanceEvent preset) : Nat :=
  ∑ i ∈ Finset.range event.before.state.balances.data.size,
    (actualBalanceAt event.before i - actualBalanceAt event.after i)

abbrev BalanceReplay (preset : Preset) (fork : Fork) :=
  BeaconState preset fork × List (BalanceEvent preset)

/-- Replay a pass and charge its protocol-computed limits, not its observed balance difference. -/
def recordBalance {fork : Fork} (source : BalanceSource)
    (limits : BeaconState preset fork → Except TransitionError (Nat × Nat))
    (action : BeaconState preset fork → Except TransitionError (BeaconState preset fork))
    (pre : BalanceReplay preset fork) : Except TransitionError (BalanceReplay preset fork) := do
  let (credit, debit) ← limits pre.1
  let post ← action pre.1
  return (post, pre.2 ++ [⟨source, ⟨fork, pre.1⟩, ⟨fork, post⟩, credit, debit⟩])

def carryBalance {fork : Fork}
    (action : BeaconState preset fork → Except TransitionError (BeaconState preset fork))
    (pre : BalanceReplay preset fork) : Except TransitionError (BalanceReplay preset fork) := do
  return (← action pre.1, pre.2)

/-- Separate the reward and penalty updates even when the concrete pass interleaves them. -/
def replayDeltas {fork : Fork} (penaltySource : BalanceSource)
    (deltas : Array Gwei × Array Gwei) (pre : BalanceReplay preset fork) :
    Except TransitionError (BalanceReplay preset fork) :=
  (List.range pre.1.validators.data.size).foldlM (fun pre i => do
    let index ← liftAccessor (liftArith (Uint64.ofNatChecked i))
    let reward := deltas.1.getD i 0
    let penalty := deltas.2.getD i 0
    let pre ← recordBalance .rewards (fun _ => pure (reward.toNat, 0))
      (fun s => liftAccessor (increaseBalance s index reward)) pre
    recordBalance penaltySource (fun _ => pure (0, penalty.toNat))
      (fun s => liftAccessor (decreaseBalance s index penalty)) pre) pre

def replayRewards {fork : Fork} (pre : BalanceReplay preset fork) :
    Except TransitionError (BalanceReplay preset fork) := do
  if getCurrentEpoch pre.1 = GENESIS_EPOCH then return pre
  let ordinary ← rewardPasses pre.1
  let inactivity ← getInactivityPenaltyDeltas config pre.1
  if .altair ≤ fork then
    let pre ← ordinary.foldlM (fun pre deltas => replayDeltas .penalties deltas pre) pre
    replayDeltas .inactivity inactivity pre
  else
    -- Phase 0 combines arrays first; splitting their saturating debits has the same endpoint.
    let rewards ← (List.range pre.1.validators.data.size).mapM fun i =>
      liftAccessor (liftArith (Uint64.ofNatChecked
        ((ordinary.map fun p => (p.1.getD i 0).toNat).sum)))
    let pre ← replayDeltas .penalties (rewards.toArray, #[]) pre
    let pre ← ordinary.foldlM (fun pre p => replayDeltas .penalties (#[], p.2) pre) pre
    replayDeltas .inactivity (#[], inactivity.2) pre

/-- The replay ends after the last balance-changing epoch pass, before effective-balance updates. -/
def epochBalanceReplay {fork : Fork} (s : BeaconState preset fork) :
    Except TransitionError (BalanceReplay preset fork) := do
  let pre ← carryBalance processJustificationAndFinalization (s, [])
  let pre ← if altair : .altair ≤ fork then
      carryBalance (processInactivityUpdates config · altair) pre else pure pre
  let pre ← replayRewards (config := config) pre
  let pre ← carryBalance (processRegistryUpdates config) pre
  let pre ← recordBalance .slashings
    (fun s => return (0, ← delayedSlashingLimit s))
    processSlashings pre
  let pre ← if before : fork < .hegota then
      carryBalance (processEth1DataReset before) pre else pure pre
  if electra : .pectra ≤ fork then
    let deposited ← processPendingDeposits config checks pre.1 electra
    let events := pre.2 ++ [⟨.deposits, ⟨fork, pre.1⟩, ⟨fork, deposited⟩,
      consumedDeposits pre.1 deposited electra, 0⟩]
    let consolidated ← processPendingConsolidations deposited electra
    let moved := consumedConsolidations deposited consolidated electra
    return (consolidated, events ++
      [⟨.consolidations, ⟨fork, deposited⟩, ⟨fork, consolidated⟩, moved, moved⟩])
  else pure pre

def slashingLimits {fork : Fork} (indices : List ValidatorIndex) (s : BeaconState preset fork) :
    Except TransitionError (Nat × Nat) := do
  let validators ← liftAccessor (indices.mapM (getValidator s))
  let p := EthLib.Consensus.parameters preset fork
  return ((validators.map fun v => v.effectiveBalance.toNat /
      p.WHISTLEBLOWER_REWARD_QUOTIENT.toNat).sum,
    (validators.map fun v => v.effectiveBalance.toNat / p.MIN_SLASHING_PENALTY_QUOTIENT.toNat).sum)

/-- Pre-Gloas block replay, with limits read at the actual site of each operation. -/
def blockBalanceReplay {fork : Fork} (early : fork < .glamsterdam)
    (engine : ExecutionEngine preset fork) (s : BeaconState preset fork)
    (block : BeaconBlock preset fork) : Except TransitionError (BalanceReplay preset fork) := do
  let before := Nat.lt_trans early (by decide : Fork.glamsterdam < .hegota)
  let pre ← carryBalance (processBlockHeader · block) (s, [])
  let pre ← if bellatrix : .bellatrix ≤ fork then
      recordBalance .withdrawals (fun s => do
        if capella : .shapella ≤ fork then
          return (0, ((← getExpectedWithdrawals s capella).withdrawals.toList.map
            fun w => w.amount.toNat).sum)
        else return (0, 0))
        (processBlockExecution config checks engine · block.body bellatrix) pre
    else pure pre
  let pre ← carryBalance (processRandao config checks · block.body) pre
  let pre ← carryBalance (processEth1Data before · block.body) pre
  let expected ← expectedDepositCount pre.1 before
  let deposits := (block.body.deposits before).data
  ensure (deposits.size = expected) (.wrongDepositCount deposits.size expected)
  let pre ← block.body.proposerSlashings.data.toList.foldlM (fun pre sl =>
    recordBalance .slashings (slashingLimits [sl.signedHeader1.message.proposerIndex])
      (processProposerSlashing config checks · sl) pre) pre
  let pre ← block.body.attesterSlashings.data.toList.foldlM (fun pre sl =>
    recordBalance .slashings (slashingLimits (slashingIndices sl))
      (processAttesterSlashing config checks · sl) pre) pre
  let pre ← block.body.attestations.data.toList.foldlM (fun pre att =>
    recordBalance .rewards (fun site => do
      return (← attestationCredit site att s.latestBlockHeader.slot, 0))
      (processAttestation config checks · s.latestBlockHeader.slot att) pre) pre
  let pre ← (block.body.deposits before).data.toList.foldlM (fun pre dep =>
    recordBalance .deposits (fun _ => pure (if fork < .pectra then dep.data.amount.toNat else 0, 0))
      (processDeposit config checks before · dep) pre) pre
  let pre ← carryBalance (fun s => block.body.voluntaryExits.data.foldlM
    (processVoluntaryExit config checks) s) pre
  let pre ← carryBalance (processBlsToExecutionChanges config checks · block.body) pre
  let pre ← if electra : .pectra ≤ fork then do
      let requests := block.body.executionRequests ⟨electra, early⟩
      let pre ← carryBalance (fun s => requests.deposits.data.foldlM
        (processDepositRequest · electra ·) s) pre
      let pre ← carryBalance (fun s => requests.withdrawals.data.foldlM
        (processWithdrawalRequest config · electra ·) s) pre
      requests.consolidations.data.toList.foldlM (fun pre request =>
        recordBalance .excess (fun s => pure (0,
          match findValidatorByPubkey s request.sourcePubkey with
          | none => 0
          | some i => actualBalanceAt ⟨fork, s⟩ i.val - preset.MIN_ACTIVATION_BALANCE.toNat))
          (processConsolidationRequest config · electra request) pre) pre
    else pure pre
  if altair : .altair ≤ fork then
    recordBalance .sync (fun s => do
      let reward ← syncParticipantReward s
      let proposer ← liftAccessor (liftArith do
        Uint64.divChecked (← Uint64.mulChecked reward PROPOSER_WEIGHT)
          (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT))
      return (preset.SYNC_COMMITTEE_SIZE.toNat * (reward.toNat + proposer.toNat),
        preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat))
      (processSyncAggregate config checks · altair (block.body.syncAggregate altair)) pre
  else pure pre

private theorem replay_fold_result {α : Type} {fork : Fork}
    (action : BeaconState preset fork → α → Except TransitionError (BeaconState preset fork))
    (replay : BalanceReplay preset fork → α → Except TransitionError (BalanceReplay preset fork))
    (step : ∀ s x t, action s x = .ok t → ∀ events,
      ∃ recorded, replay (s, events) x = .ok (t, recorded))
    (items : List α) (s t : BeaconState preset fork)
    (ok : items.foldlM action s = .ok t) (events : List (BalanceEvent preset)) :
    ∃ recorded, items.foldlM replay (s, events) = .ok (t, recorded) := by
  induction items generalizing s events with
  | nil =>
    cases ok
    exact ⟨events, rfl⟩
  | cons x xs ih =>
    simp only [List.foldlM_cons, bind_ok_iff] at ok ⊢
    obtain ⟨middle, first, rest⟩ := ok
    obtain ⟨recorded, replayed⟩ := step s x middle first events
    obtain ⟨final, replayedRest⟩ := ih middle rest recorded
    exact ⟨final, (middle, recorded), replayed, replayedRest⟩

private theorem replayDeltas_result {fork : Fork} (s t : BeaconState preset fork)
    (source : BalanceSource) (deltas : Array Gwei × Array Gwei)
    (ok : applyAllDeltas s deltas = .ok t) (events : List (BalanceEvent preset)) :
    ∃ recorded, replayDeltas source deltas (s, events) = .ok (t, recorded) := by
  unfold replayDeltas applyAllDeltas at *
  apply replay_fold_result _ _ ?_ _ s t ok events
  intro state i after step previous
  simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at step
  obtain ⟨index, indexOk, raised, raisedOk, loweredOk⟩ := step
  have indexLift := liftAccessor_ok.mpr indexOk
  have raisedLift := liftAccessor_ok.mpr raisedOk
  have loweredLift := liftAccessor_ok.mpr loweredOk
  simp only [recordBalance, indexLift, raisedLift, loweredLift,
    bind, Except.bind, pure, Except.pure]
  exact ⟨_, rfl⟩

private theorem replayRewards_altair {fork : Fork} (altair : .altair ≤ fork)
    (s t : BeaconState preset fork) (events : List (BalanceEvent preset))
    (ok : processRewardsAndPenalties config s = .ok t) :
    ∃ recorded, replayRewards (config := config) (s, events) = .ok (t, recorded) := by
  by_cases genesis : getCurrentEpoch s = GENESIS_EPOCH
  · simp only [processRewardsAndPenalties, genesis, ↓reduceIte, pure,
      Except.pure, Except.ok.injEq] at ok
    subst t
    exact ⟨events, by simp only [replayRewards, genesis, ↓reduceIte]; rfl⟩
  · simp only [processRewardsAndPenalties, genesis, altair, ↓reduceIte, ↓reduceDIte,
      bind_ok_iff, List.foldlM_append, List.foldlM_cons, List.foldlM_nil,
      bind_pure] at ok
    obtain ⟨ordinary, ordinaryOk, inactivity, inactivityOk, middle, ordinaryApplied,
      inactivityApplied⟩ := ok
    obtain ⟨recorded, ordinaryReplay⟩ := replay_fold_result applyAllDeltas
      (fun pre deltas => replayDeltas .penalties deltas pre)
      (fun s deltas t ok events => replayDeltas_result s t .penalties deltas ok events)
      ordinary s middle ordinaryApplied events
    obtain ⟨final, inactivityReplay⟩ :=
      replayDeltas_result middle t .inactivity inactivity inactivityApplied recorded
    refine ⟨final, ?_⟩
    simp only [replayRewards, rewardPasses, genesis, altair, ↓reduceIte, ↓reduceDIte,
      ordinaryOk, inactivityOk, ordinaryReplay, inactivityReplay,
      bind, Except.bind]

private theorem replay_distinct_exists {α σ ε : Type} {step : σ → α → Except ε σ}
    (key : α → Nat) (Ready : σ → α → Prop)
    (advance : ∀ last x, Ready last x → ∃ next, step last x = .ok next ∧
      ∀ y, key y ≠ key x → Ready last y → Ready next y) :
    ∀ (xs : List α) (start : σ), (xs.map key).Nodup → (∀ x ∈ xs, Ready start x) →
      ∃ out, xs.foldlM step start = .ok out
  | [], start, _, _ => ⟨start, rfl⟩
  | x :: rest, start, distinct, ready => by
    rw [List.map_cons, List.nodup_cons] at distinct
    obtain ⟨next, stepped, keeps⟩ := advance start x (ready x List.mem_cons_self)
    obtain ⟨out, folded⟩ := replay_distinct_exists key Ready advance rest next distinct.2
      fun y member => keeps y (fun same => distinct.1 (same ▸ List.mem_map_of_mem member))
        (ready y (List.mem_cons_of_mem _ member))
    exact ⟨out, by rw [List.foldlM_cons, stepped]; exact folded⟩

private theorem replay_apply_exists {fork : Fork} (s : BeaconState preset fork)
    (rewards penalties : Array Gwei)
    (ready : ∀ i, i < s.validators.data.size → i < 2 ^ 64 ∧
      ∃ balance, s.balances.data[i]? = some balance ∧
        balance.toNat + (rewards.getD i 0).toNat < 2 ^ 64) :
    ∃ t, applyAllDeltas s (rewards, penalties) = .ok t := by
  unfold applyAllDeltas
  refine replay_distinct_exists id (fun (last : BeaconState preset fork) i =>
      ∃ inside : i < last.balances.data.size, i < 2 ^ 64 ∧
        last.balances.data[i].toNat + (rewards.getD i 0).toNat < 2 ^ 64)
    (fun last i ⟨inside, lt, fit⟩ => ?_) _ s (by simpa using List.nodup_range) ?_
  · intro i member
    obtain ⟨small, balance, found, fits⟩ := ready i (List.mem_range.mp member)
    obtain ⟨inside, same⟩ := Array.getElem?_eq_some_iff.mp found
    exact ⟨inside, small, by simpa [same] using fits⟩
  · refine ⟨_, applyDeltas_eq_ok_iff.mpr ⟨lt, inside, fit, rfl⟩,
      fun j other ⟨insideJ, ltJ, fitJ⟩ => ?_⟩
    have ne : i ≠ j := fun same => other same.symm
    exact ⟨by simpa [BeaconState.putBalance] using insideJ, ltJ,
      by simpa [BeaconState.putBalance, Array.getElem_set, ne] using fitJ⟩

private theorem replay_indices_small {fork : Fork} {s t : BeaconState preset fork}
    {deltas : Array Gwei × Array Gwei} (ok : applyAllDeltas s deltas = .ok t)
    {i : Nat} (inside : i < s.validators.data.size) : i < 2 ^ 64 := by
  have all := foldlM_forall_of_ok (P := fun j => j < 2 ^ 64)
    (fun _ _ _ step => (applyDeltas_eq_ok_iff.mp step).1) _ _ _ ok
  exact all i (List.mem_range.mpr inside)

private theorem replay_penalties_exists {fork : Fork} (s : BeaconState preset fork)
    (penalties : List (Array Gwei))
    (ready : ∀ i, i < s.validators.data.size → i < 2 ^ 64 ∧
      ∃ balance, s.balances.data[i]? = some balance) :
    ∃ t, (penalties.map fun p => (#[], p)).foldlM applyAllDeltas s = .ok t := by
  induction penalties generalizing s with
  | nil => exact ⟨s, rfl⟩
  | cons p ps ih =>
    obtain ⟨middle, applied⟩ := replay_apply_exists s #[] p (fun i inside => by
      obtain ⟨small, balance, found⟩ := ready i inside
      exact ⟨small, balance, found, by simpa using balance.toNat_lt_size⟩)
    have sizes := sameSizes_applyAllDeltas applied
    obtain ⟨t, rest⟩ := ih middle (fun i inside => by
      rw [sizes.1] at inside
      obtain ⟨balance, _, _, found⟩ := (applyAllDeltas_balances applied i).1 inside
      exact ⟨(ready i inside).1, _, found⟩)
    exact ⟨t, by simpa only [List.map_cons, List.foldlM_cons, applied, bind, Except.bind]
      using rest⟩

/-- The instrumented reward pass has the same endpoint as the real reward pass. -/
theorem replayRewards_result {fork : Fork} (s t : BeaconState preset fork)
    (events : List (BalanceEvent preset))
    (ok : processRewardsAndPenalties config s = .ok t) :
    ∃ recorded, replayRewards (config := config) (s, events) = .ok (t, recorded) := by
  by_cases altair : .altair ≤ fork
  · exact replayRewards_altair altair s t events ok
  by_cases genesis : getCurrentEpoch s = GENESIS_EPOCH
  · simp only [processRewardsAndPenalties, genesis, ↓reduceIte, pure,
      Except.pure, Except.ok.injEq] at ok
    subst t
    exact ⟨events, by simp only [replayRewards, genesis, ↓reduceIte]; rfl⟩
  simp only [processRewardsAndPenalties, genesis, altair, ↓reduceIte, ↓reduceDIte,
    bind_ok_iff] at ok
  obtain ⟨⟨rewards, penalties⟩, computed, applied⟩ := ok
  obtain ⟨source, target, head, inclusion, inactivity, sourceOk, targetOk, headOk,
    inclusionOk, inactivityOk, sums⟩ := getAttestationDeltas_getD _ computed
  let ordinary := [source, target, head, inclusion]
  let amounts := (List.range s.validators.data.size).map fun i => rewards.getD i 0
  have amountsOk : (List.range s.validators.data.size).mapM (fun i =>
      liftAccessor (liftArith (Uint64.ofNatChecked
        ((ordinary.map fun p => (p.1.getD i 0).toNat).sum)))) = .ok amounts := by
    apply mapM_eq_ok_iff.mpr
    refine ⟨by simp [amounts], fun i inside => ?_⟩
    simp only [List.length_range] at inside
    have sum := (sums i inside).1
    have value : ((ordinary.map fun p => (p.1.getD i 0).toNat).sum) =
        (rewards.getD i 0).toNat := by simpa [ordinary, Nat.add_assoc] using sum.symm
    simp only [amounts, List.getElem_map, List.getElem_range, value]
    rw [Uint64.ofNatChecked_ok_iff.mpr ⟨(rewards.getD i 0).toNat_lt_size, rfl⟩]
    rfl
  have amountAt (i : Nat) (inside : i < s.validators.data.size) :
      amounts.toArray.getD i 0 = rewards.getD i 0 := by
    simp [amounts, Array.getD, inside]
  obtain ⟨raised, raisedOk⟩ := replay_apply_exists s amounts.toArray #[] (fun i inside => by
    obtain ⟨balance, found, fits, _⟩ := (applyAllDeltas_balances applied i).1 inside
    exact ⟨replay_indices_small applied inside, balance, found, by rwa [amountAt i inside]⟩)
  let ps := [source.2, target.2, head.2, inclusion.2, inactivity.2]
  obtain ⟨final, loweredOk⟩ := replay_penalties_exists raised ps (fun i inside => by
    have original : i < s.validators.data.size :=
      (sameSizes_applyAllDeltas raisedOk).1 ▸ inside
    obtain ⟨balance, _, _, found⟩ := (applyAllDeltas_balances raisedOk i).1 original
    exact ⟨replay_indices_small applied original, _, found⟩)
  have inclusionZero (i : Nat) : inclusion.2.getD i 0 = 0 := by
    unfold getInclusionDelayDeltas at inclusionOk
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at inclusionOk
    obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := inclusionOk
    exact replicate_getD_zero _ _
  have endpoint : final = t := by
    have finalFrame : final = {s with balances := final.balances} := by
      have kept := foldlM_ok_invariant
        (fun next : BeaconState preset fork => next = {s with balances := next.balances})
        (fun _ _ _ previous step => by rw [applyAllDeltas_frame step, previous])
        (applyAllDeltas_frame raisedOk) loweredOk
      exact kept
    have balances : final.balances = t.balances := by
      suffices data : final.balances.data = t.balances.data by
        have ext (a b : Balances preset fork) (h : a.data = b.data) : a = b := by
          cases a
          cases b
          cases h
          rfl
        exact ext _ _ data
      apply Array.ext_getElem?
      intro i
      by_cases inside : i < s.validators.data.size
      · obtain ⟨balance, found, fits, result⟩ := (applyAllDeltas_balances applied i).1 inside
        obtain ⟨balance', found', fits', result'⟩ :=
          (applyAllDeltas_balances raisedOk i).1 inside
        have same : balance' = balance := Option.some.inj (found'.symm.trans found)
        subst balance'
        have lowered := (foldlM_applyAllDeltas_balances loweredOk i).1
          (by rwa [(sameSizes_applyAllDeltas raisedOk).1])
        rw [lowered, result', result]
        simp only [Option.map_some, Option.some.injEq]
        apply UInt64.toNat_inj.mp
        have empty : (#[] : Array Gwei).getD i 0 = 0 := by simp
        simp only [ps, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
          empty, UInt64.add_zero, Uint64.toNat_saturatingSub, UInt64.toNat_zero,
          Nat.sub_zero, amountAt i inside, inclusionZero]
        rw [← Nat.sub_add_eq, ← Nat.sub_add_eq, ← Nat.sub_add_eq]
        rw [(sums i inside).2]
        simp only [Nat.add_assoc]
      · rw [(applyAllDeltas_balances applied i).2 (by omega)]
        rw [(foldlM_applyAllDeltas_balances loweredOk i).2.2
          (by rw [(sameSizes_applyAllDeltas raisedOk).1]; omega)]
        exact (applyAllDeltas_balances raisedOk i).2 (by omega)
    rw [finalFrame, applyAllDeltas_frame applied, balances]
  subst final
  have folded : ((amounts.toArray, #[]) :: ps.map (fun p => (#[], p))).foldlM
      applyAllDeltas s = .ok t := by
    simpa only [List.foldlM_cons, raisedOk, bind, Except.bind] using loweredOk
  -- The final inactivity pass has the same state action, but a different event label.
  simp only [ps, List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil,
    bind_pure, bind_ok_iff] at folded
  obtain ⟨r, rOk, a, aOk, b, bOk, c, cOk, d, dOk, lastOk⟩ := folded
  obtain ⟨er, erOk⟩ := replayDeltas_result s r .penalties _ rOk events
  obtain ⟨ea, eaOk⟩ := replayDeltas_result r a .penalties _ aOk er
  obtain ⟨eb, ebOk⟩ := replayDeltas_result a b .penalties _ bOk ea
  obtain ⟨ec, ecOk⟩ := replayDeltas_result b c .penalties _ cOk eb
  obtain ⟨ed, edOk⟩ := replayDeltas_result c d .penalties _ dOk ec
  obtain ⟨et, etOk⟩ := replayDeltas_result d t .inactivity _ lastOk ed
  refine ⟨et, ?_⟩
  simp only [replayRewards, rewardPasses, genesis, altair, ↓reduceIte, ↓reduceDIte,
    sourceOk, targetOk, headOk, inclusionOk, inactivityOk, bind, Except.bind, pure, Except.pure]
  change (do
    let rs ← (List.range s.validators.data.size).mapM (fun i =>
      liftAccessor (liftArith (Uint64.ofNatChecked
        ((ordinary.map fun (p : Array Gwei × Array Gwei) => (p.1.getD i 0).toNat).sum))))
    let pre ← replayDeltas .penalties (rs.toArray, #[]) (s, events)
    let pre ← ordinary.foldlM
      (fun pre (p : Array Gwei × Array Gwei) => replayDeltas .penalties (#[], p.2) pre) pre
    replayDeltas .inactivity (#[], inactivity.2) pre) = .ok (t, et)
  simp only [amountsOk, erOk, ordinary, List.foldlM_cons, List.foldlM_nil,
    eaOk, ebOk, ecOk, edOk, etOk, bind, Except.bind, pure, Except.pure]

private theorem carryBalance_result {fork : Fork} {s t : BeaconState preset fork}
    {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
    (ok : action s = .ok t) (events : List (BalanceEvent preset)) :
    carryBalance action (s, events) = .ok (t, events) := by
  simp [carryBalance, ok]

private theorem recordBalance_result {fork : Fork} {s t : BeaconState preset fork}
    {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
    {limits : BeaconState preset fork → Except TransitionError (Nat × Nat)}
    (ok : action s = .ok t) (bounded : ∃ limit, limits s = .ok limit)
    (source : BalanceSource) (events : List (BalanceEvent preset)) :
    ∃ recorded, recordBalance source limits action (s, events) = .ok (t, recorded) := by
  obtain ⟨⟨credit, debit⟩, computed⟩ := bounded
  refine ⟨events ++ [⟨source, ⟨fork, s⟩, ⟨fork, t⟩, credit, debit⟩], ?_⟩
  simp only [recordBalance, computed, ok, bind, Except.bind, pure, Except.pure]

private theorem delayedSlashingLimit_result {fork : Fork} {s t : BeaconState preset fork}
    (ok : processSlashings s = .ok t) : ∃ limit, delayedSlashingLimit s = .ok limit := by
  simp only [processSlashings, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨total, totalOk, sum, sumOk, scaled, scaledOk, _⟩ := ok
  simp only [delayedSlashingLimit, bind_ok_iff, liftAccessor_ok, totalOk, sumOk,
    Except.ok.injEq, pure, Except.pure]
  exact ⟨_, total, rfl, sum, rfl, rfl⟩

private theorem epochBalanceReplay_before {fork : Fork} {s t : BeaconState preset fork}
    (ok : epochBeforePayments config checks s = .ok t) :
    ∃ events, epochBalanceReplay (config := config) (checks := checks) s = .ok (t, events) := by
  simp only [epochBeforePayments, bind_ok_iff] at ok
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pendingOk⟩ := ok
  obtain ⟨rewardEvents, rewardReplay⟩ := replayRewards_result scored rewarded [] rewardedOk
  have limitOk : ∃ limit, (do return (0, ← delayedSlashingLimit registered)) =
      (Except.ok limit : Except TransitionError (Nat × Nat)) := by
    obtain ⟨limit, computed⟩ := delayedSlashingLimit_result slashedOk
    exact ⟨(0, limit), by rw [computed]; rfl⟩
  obtain ⟨slashEvents, slashReplay⟩ := recordBalance_result
    (limits := fun s => do return (0, ← delayedSlashingLimit s)) slashedOk
    limitOk .slashings rewardEvents
  have scoredReplay : (if altair : .altair ≤ fork then
      carryBalance (processInactivityUpdates config · altair) (justified, [])
      else pure (justified, [])) =
        (Except.ok (scored, []) : Except TransitionError (BalanceReplay preset fork)) := by
    split at scoredOk <;> rename_i h
    · simpa only [h, ↓reduceDIte] using carryBalance_result scoredOk []
    · simp only [pure, Except.pure, Except.ok.injEq] at scoredOk
      simp only [h, ↓reduceDIte, ← scoredOk]; rfl
  have resetReplay : (if before : fork < .hegota then
      carryBalance (processEth1DataReset before) (slashed, slashEvents)
      else pure (slashed, slashEvents)) =
        (Except.ok (reset, slashEvents) : Except TransitionError (BalanceReplay preset fork)) := by
    split at resetOk <;> rename_i h
    · simpa only [h, ↓reduceDIte] using carryBalance_result resetOk slashEvents
    · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
      simp only [h, ↓reduceDIte, ← resetOk]; rfl
  by_cases altair : .altair ≤ fork <;> by_cases before : fork < .hegota
  all_goals
    simp only [altair, before, ↓reduceDIte] at scoredReplay resetReplay
    simp only [bind, Except.bind, pure, Except.pure] at slashReplay scoredReplay resetReplay
    simp only [epochBalanceReplay, altair, before, ↓reduceDIte,
      carryBalance_result justifiedOk [], scoredReplay, rewardReplay,
      carryBalance_result registeredOk rewardEvents, slashReplay, resetReplay,
      bind, Except.bind, pure, Except.pure]
    unfold processPendingBalances at pendingOk
    split at pendingOk <;> rename_i h
    · simp only [bind_ok_iff] at pendingOk
      obtain ⟨deposited, depositedOk, consolidatedOk⟩ := pendingOk
      simp only [h, ↓reduceDIte, depositedOk, consolidatedOk]
      exact ⟨_, rfl⟩
    · simp only [pure, Except.pure, Except.ok.injEq] at pendingOk
      simp only [h, ↓reduceDIte, pendingOk]
      exact ⟨_, rfl⟩

private theorem effectiveUpdates_balances {fork : Fork} {s t : BeaconState preset fork}
    (ok : processEffectiveBalanceUpdates s = .ok t) : t.balances = s.balances := by
  unfold processEffectiveBalanceUpdates at ok
  apply foldlM_ok_invariant (fun current : BeaconState preset fork =>
    current.balances = s.balances) ?_ rfl ok
  intro current index next kept step
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at step
  obtain ⟨v, _, balance, _, effective, _, updated⟩ := step
  unfold BeaconState.setValidatorAt at updated
  split at updated
  · cases updated
    exact kept
  · simp only [bind_ok_iff] at updated
    obtain ⟨_, _, impossible⟩ := updated
    cases impossible

private theorem epochTail_kept {fork : Fork} {s t : BeaconState preset fork}
    (ok : (do
      let state ← processSlashingsReset s
      let state ← processRandaoMixesReset state
      let state ← if capella : Fork.shapella ≤ fork then
          processHistoricalSummariesUpdate state capella else processHistoricalRootsUpdate state
      if altair : Fork.altair ≤ fork then do
        let state := processParticipationFlagUpdates state altair
        let state ← processSyncCommitteeUpdates state altair
        if fulu : Fork.fusaka ≤ fork then liftAccessor (processProposerLookahead state fulu)
        else pure state
      else processParticipationRecordUpdates state) = .ok t) :
    t.validators = s.validators ∧ t.balances = s.balances := by
  simp only [bind_ok_iff] at ok
  obtain ⟨cleared, clearedOk, mixed, mixedOk, ok⟩ := ok
  obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
  obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
  simp only [processHistoricalSummariesUpdate, processHistoricalRootsUpdate,
    processSyncCommitteeUpdates, processParticipationRecordUpdates,
    processProposerLookahead, liftAccessor, Except.mapError,
    bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at * <;> try contradiction)
  all_goals
    simp_all only [Except.ok.injEq]
    subst_vars
    exact ⟨rfl, rfl⟩

/-- The remaining epoch passes keep balances; the replay endpoint is the effective-update input. -/
theorem epochBalanceReplay_result {fork : Fork} (s t : BeaconState preset fork)
    (early : fork < .glamsterdam) (ok : processEpoch config checks s = .ok t) :
    ∃ middle updated events,
      epochBalanceReplay (config := config) (checks := checks) s = .ok (middle, events) ∧
      processEffectiveBalanceUpdates middle = .ok updated ∧
      updated.validators = t.validators ∧ middle.balances = t.balances := by
  have gloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  have before : fork < .hegota := Nat.lt_trans early (by decide)
  have factor : processEpoch config checks s = (do
      let middle ← epochBeforePayments config checks s
      let updated ← processEffectiveBalanceUpdates middle
      let state ← processSlashingsReset updated
      let state ← processRandaoMixesReset state
      let state ← if capella : Fork.shapella ≤ fork then
          processHistoricalSummariesUpdate state capella else processHistoricalRootsUpdate state
      if altair : Fork.altair ≤ fork then do
        let state := processParticipationFlagUpdates state altair
        let state ← processSyncCommitteeUpdates state altair
        if fulu : Fork.fusaka ≤ fork then liftAccessor (processProposerLookahead state fulu)
        else pure state
      else processParticipationRecordUpdates state) := by
    by_cases altair : .altair ≤ fork
    · simp only [processEpoch, altair, ↓reduceDIte,
        processEpochAltair_eq_epochBeforePayments_bind, gloas, ↓reduceDIte, pure_bind]
      congr 1; funext middle
      split <;> simp
    · have capella : ¬ .shapella ≤ fork := fun h =>
        altair (Nat.le_trans (by decide) h)
      have electra : ¬ .pectra ≤ fork := fun h =>
        altair (Nat.le_trans (by decide) h)
      simp only [processEpoch, epochBeforePayments, processPendingBalances,
        altair, before, capella, electra, ↓reduceDIte, pure_bind,
        bind_assoc]
  rw [factor] at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨middle, middleOk, updated, updatedOk, tail⟩ := ok
  obtain ⟨events, replay⟩ := epochBalanceReplay_before middleOk
  have kept := epochTail_kept (by simpa only [bind_ok_iff] using tail)
  exact ⟨middle, updated, events, replay, updatedOk, kept.1.symm,
    ((kept.2).trans (effectiveUpdates_balances updatedOk)).symm⟩

private theorem slashingLimits_result {fork : Fork} (s : BeaconState preset fork)
    (indices : List ValidatorIndex)
    (found : ∀ i ∈ indices, ∃ v, getValidator s i = .ok v) :
    ∃ limit, slashingLimits indices s = .ok limit := by
  obtain ⟨validators, computed⟩ := mapM_exists_ok found
  simp only [slashingLimits, bind_ok_iff, liftAccessor_ok]
  exact ⟨_, validators, computed, rfl⟩

private theorem proposerLimits_result {fork : Fork} {s t : BeaconState preset fork}
    {sl : ProposerSlashing} (ok : processProposerSlashing config checks s sl = .ok t) :
    ∃ limit, slashingLimits [sl.signedHeader1.message.proposerIndex] s = .ok limit := by
  simp only [processProposerSlashing, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, proposer, found, _⟩ := ok
  apply slashingLimits_result
  intro i member
  simp only [List.mem_singleton] at member
  exact member ▸ ⟨proposer, found⟩

private theorem attesterLimits_result {fork : Fork} {s t : BeaconState preset fork}
    {sl : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks s sl = .ok t) :
    ∃ limit, slashingLimits (slashingIndices sl) s = .ok limit := by
  obtain ⟨_, first, _⟩ := processAttesterSlashing_checks ok
  obtain ⟨_, _, _, pubkeys, _⟩ := isValidIndexedAttestation_signature first
  apply slashingLimits_result
  intro i member
  rw [slashingIndices, mem_sortedSet, List.mem_filter, decide_eq_true_iff] at member
  rw [Array.mapM_eq_mapM_toList] at pubkeys
  change (do
    let keys ← sl.attestation1.attestingIndices.data.toList.mapM
      (fun index => do return packBytes (← liftAccessor (getValidator s index)).pubkey)
    pure keys.toArray) = .ok _ at pubkeys
  rw [bind_ok_iff] at pubkeys
  obtain ⟨keys, mapped, _⟩ := pubkeys
  obtain ⟨key, computed⟩ := mapM_ok_of_mem mapped i (by simpa using member.1)
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨v, found, _⟩ := computed
  exact ⟨v, found⟩

private theorem attestationCredit_result {fork : Fork} {s t : BeaconState preset fork}
    {att : Attestation preset fork} {parent : Slot}
    (ok : processAttestation config checks s parent att = .ok t) :
    ∃ credit, attestationCredit s att parent = .ok credit := by
  unfold processAttestation at ok
  split at ok <;> rename_i altair
  · simp only [processAttestationAltair, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, earned, earnedOk,
      _, _, _, _, _, _, total, totalOk, attesters, attestersOk, result, resultOk, _⟩ := ok
    simp only [attestationCredit, altair, ↓reduceDIte, bind_ok_iff, liftAccessor_ok]
    exact ⟨_, earned, earnedOk, total, totalOk, attesters, attestersOk,
      result, resultOk, rfl⟩
  · simp only [attestationCredit, altair, ↓reduceDIte]
    exact ⟨0, rfl⟩

private theorem syncLimits_result {fork : Fork} {s t : BeaconState preset fork}
    {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (ok : processSyncAggregate config checks s altair aggregate = .ok t) :
    ∃ reward proposer,
      syncParticipantReward s = .ok reward ∧
      liftAccessor (liftArith (do
        Uint64.divChecked (← Uint64.mulChecked reward PROPOSER_WEIGHT)
          (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT))) =
        (Except.ok proposer : Except TransitionError Gwei) := by
  simp only [processSyncAggregate, bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, reward, rewardOk, proposer, proposerOk, _⟩ := ok
  exact ⟨reward, proposer, rewardOk, proposerOk⟩

private theorem executionLimits_result {fork : Fork} {s t : BeaconState preset fork}
    {bellatrix : .bellatrix ≤ fork} {engine : ExecutionEngine preset fork}
    {body : BeaconBlockBody preset fork} (early : fork < .glamsterdam)
    (ok : processBlockExecution config checks engine s body bellatrix = .ok t) :
    ∃ limit, (do
      if capella : Fork.shapella ≤ fork then
        return (0, ((← getExpectedWithdrawals s capella).withdrawals.toList.map
          fun w => w.amount.toNat).sum)
      else return (0, 0)) = (Except.ok limit : Except TransitionError (Nat × Nat)) := by
  have gloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [processBlockExecution, gloas, ↓reduceDIte] at ok
  split at ok <;> rename_i capella
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, _⟩ := ok
    simp only [processWithdrawals, gloas, ↓reduceDIte, bind_ok_iff] at withdrawn
    obtain ⟨expected, expectedOk, _⟩ := withdrawn
    simp only [capella, ↓reduceDIte, expectedOk, bind, Except.bind, pure, Except.pure]
    exact ⟨_, rfl⟩
  · simp only [capella, ↓reduceDIte]
    exact ⟨(0, 0), rfl⟩

/-- Every real pre-Gloas block has the exact endpoint of the instrumented passes. -/
theorem blockBalanceReplay_result {fork : Fork} (s t : BeaconState preset fork)
    (early : fork < .glamsterdam) (engine : ExecutionEngine preset fork)
    (block : BeaconBlock preset fork)
    (ok : processBlock config checks engine s block = .ok t) :
    ∃ events, blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok (t, events) := by
  have gloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  have before : fork < .hegota := Nat.lt_trans early (by decide)
  have factor : ∃ headed executed revealed voted operated,
      processBlockHeader s block = .ok headed ∧
      (if bellatrix : Fork.bellatrix ≤ fork then
        processBlockExecution config checks engine headed block.body bellatrix
        else pure headed) = (Except.ok executed : Except TransitionError _) ∧
      processRandao config checks executed block.body = .ok revealed ∧
      processEth1Data before revealed block.body = .ok voted ∧
      processOperations config checks voted block.body s.latestBlockHeader.slot = .ok operated ∧
      (if altair : Fork.altair ≤ fork then
        processSyncAggregate config checks operated altair (block.body.syncAggregate altair)
        else pure operated) = (Except.ok t : Except TransitionError _) := by
    unfold processBlock at ok
    split at ok <;> rename_i altair
    · simp only [processBlockAltair, gloas, before, ↓reduceDIte,
        pure_bind, bind_ok_iff] at ok
      obtain ⟨a, ha, b, hb, c, hc, d, hd, e, he, last⟩ := ok
      exact ⟨a, b, c, d, e, ha, hb, hc, hd, he,
        by simpa only [altair, ↓reduceDIte] using last⟩
    · have bellatrix : ¬ .bellatrix ≤ fork := fun h => altair (Nat.le_trans (by decide) h)
      simp only [bind_ok_iff] at ok
      obtain ⟨headed, headerOk, revealed, randaoOk, voted, voteOk, operationsOk⟩ := ok
      exact ⟨headed, headed, revealed, voted, t, headerOk,
        by simp only [bellatrix, ↓reduceDIte]; rfl,
        randaoOk, voteOk, operationsOk, by simp only [altair, ↓reduceDIte]; rfl⟩
  obtain ⟨headed, executed, revealed, voted, operated, headerOk, executionOk,
    randaoOk, eth1Ok, operationsOk, syncOk⟩ := factor
  have executedReplay : ∃ events,
      (if bellatrix : Fork.bellatrix ≤ fork then
        recordBalance .withdrawals (fun site => do
          if capella : Fork.shapella ≤ fork then
            return (0, ((← getExpectedWithdrawals site capella).withdrawals.toList.map
              fun w => w.amount.toNat).sum)
          else return (0, 0))
          (processBlockExecution config checks engine · block.body bellatrix) (headed, [])
        else pure (headed, [])) = (Except.ok (executed, events) : Except TransitionError _) := by
    split at executionOk <;> rename_i h
    · simp only [h, ↓reduceDIte]
      exact recordBalance_result executionOk (executionLimits_result early executionOk) _ []
    · simp only [pure, Except.pure, Except.ok.injEq] at executionOk
      exact ⟨[], by simp only [h, ↓reduceDIte, ← executionOk]; rfl⟩
  obtain ⟨executionEvents, executionReplay⟩ := executedReplay
  simp only [processOperations, gloas, ↓reduceDIte, bind_ok_iff,
    ← Array.foldlM_toList] at operationsOk
  obtain ⟨expected, expectedOk, _, countOk, proposed, proposedOk, attestedSlashes,
    attestedSlashesOk, attested, attestedOk, deposited, depositedOk,
    exited, exitedOk, changed, changedOk, requestsOk⟩ := operationsOk
  obtain ⟨proposedEvents, proposedReplay⟩ := replay_fold_result
    (processProposerSlashing config checks)
    (fun pre sl => recordBalance .slashings
      (slashingLimits [sl.signedHeader1.message.proposerIndex])
      (processProposerSlashing config checks · sl) pre)
    (fun _ _ _ step events => recordBalance_result step (proposerLimits_result step) _ events)
    _ voted proposed proposedOk executionEvents
  obtain ⟨slashedEvents, slashedReplay⟩ := replay_fold_result
    (processAttesterSlashing config checks)
    (fun pre sl => recordBalance .slashings (slashingLimits (slashingIndices sl))
      (processAttesterSlashing config checks · sl) pre)
    (fun _ _ _ step events => recordBalance_result step (attesterLimits_result step) _ events)
    _ proposed attestedSlashes attestedSlashesOk proposedEvents
  obtain ⟨attestedEvents, attestedReplay⟩ := replay_fold_result
    (processAttestation config checks · s.latestBlockHeader.slot ·)
    (fun pre att => recordBalance .rewards (fun site => do
      return (← attestationCredit site att s.latestBlockHeader.slot, 0))
      (processAttestation config checks · s.latestBlockHeader.slot att) pre)
    (fun site att result step events => recordBalance_result step (by
      obtain ⟨credit, computed⟩ := attestationCredit_result step
      exact ⟨(credit, 0), by rw [computed]; rfl⟩) _ events)
    _ attestedSlashes attested attestedOk slashedEvents
  obtain ⟨depositEvents, depositReplay⟩ := replay_fold_result
    (processDeposit config checks before)
    (fun pre dep => recordBalance .deposits
      (fun _ => pure (if fork < .pectra then dep.data.amount.toNat else 0, 0))
      (processDeposit config checks before · dep) pre)
    (fun _ _ _ step events => recordBalance_result step ⟨_, rfl⟩ _ events)
    _ attested deposited depositedOk attestedEvents
  have requestReplay : ∃ events, (if electra : Fork.pectra ≤ fork then do
      let requests := block.body.executionRequests ⟨electra, early⟩
      let pre ← carryBalance (fun site => requests.deposits.data.foldlM
        (processDepositRequest · electra ·) site) (changed, depositEvents)
      let pre ← carryBalance (fun site => requests.withdrawals.data.foldlM
        (processWithdrawalRequest config · electra ·) site) pre
      requests.consolidations.data.toList.foldlM (fun pre request =>
        recordBalance .excess (fun site => pure (0,
          match findValidatorByPubkey site request.sourcePubkey with
          | none => 0
          | some i => actualBalanceAt ⟨fork, site⟩ i.val - preset.MIN_ACTIVATION_BALANCE.toNat))
          (processConsolidationRequest config · electra request) pre) pre
      else pure (changed, depositEvents)) =
        (Except.ok (operated, events) : Except TransitionError _) := by
    split at requestsOk <;> rename_i h
    · simp only [processExecutionRequests, bind_ok_iff] at requestsOk
      obtain ⟨deposits, depositsOk, withdrawals, withdrawalsOk, consolidationsOk⟩ := requestsOk
      obtain ⟨events, replay⟩ := replay_fold_result
        (processConsolidationRequest config · h ·)
        (fun pre request => recordBalance .excess (fun site => pure (0,
          match findValidatorByPubkey site request.sourcePubkey with
          | none => 0
          | some i => actualBalanceAt ⟨fork, site⟩ i.val - preset.MIN_ACTIVATION_BALANCE.toNat))
          (processConsolidationRequest config · h request) pre)
        (fun _ _ _ step events => recordBalance_result step ⟨_, rfl⟩ _ events)
        _ withdrawals operated (by simpa only [← Array.foldlM_toList] using consolidationsOk)
        depositEvents
      refine ⟨events, ?_⟩
      have depositsReplay := carryBalance_result (action := fun site =>
        (block.body.executionRequests ⟨h, early⟩).deposits.data.foldlM
          (processDepositRequest · h ·) site) depositsOk depositEvents
      have withdrawalsReplay := carryBalance_result (action := fun site =>
        (block.body.executionRequests ⟨h, early⟩).withdrawals.data.foldlM
          (processWithdrawalRequest config · h ·) site) withdrawalsOk depositEvents
      simp only [h, ↓reduceDIte, depositsReplay, withdrawalsReplay, replay, bind, Except.bind]
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact ⟨depositEvents, by simp only [h, ↓reduceDIte, requestsOk]; rfl⟩
  obtain ⟨requestEvents, requestsReplay⟩ := requestReplay
  have syncedReplay : ∃ events, (if altair : Fork.altair ≤ fork then
      recordBalance .sync (fun site => do
        let reward ← syncParticipantReward site
        let proposer ← liftAccessor (liftArith do
          Uint64.divChecked (← Uint64.mulChecked reward PROPOSER_WEIGHT)
            (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT))
        return (preset.SYNC_COMMITTEE_SIZE.toNat * (reward.toNat + proposer.toNat),
          preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat))
        (processSyncAggregate config checks · altair (block.body.syncAggregate altair))
        (operated, requestEvents)
      else pure (operated, requestEvents)) =
        (Except.ok (t, events) : Except TransitionError _) := by
    split at syncOk <;> rename_i h
    · simp only [h, ↓reduceDIte]
      apply recordBalance_result syncOk
      obtain ⟨reward, proposer, rewardOk, proposerOk⟩ := syncLimits_result syncOk
      simp only [bind, Except.bind] at proposerOk
      simp only [rewardOk, proposerOk, bind, Except.bind, pure, Except.pure]
      exact ⟨_, rfl⟩
    · simp only [pure, Except.pure, Except.ok.injEq] at syncOk
      exact ⟨requestEvents, by simp only [h, ↓reduceDIte, syncOk]; rfl⟩
  obtain ⟨events, synced⟩ := syncedReplay
  have headerReplay := carryBalance_result (action := (processBlockHeader · block)) headerOk []
  have randaoReplay := carryBalance_result
    (action := (processRandao config checks · block.body)) randaoOk executionEvents
  have eth1Replay := carryBalance_result (action := (processEth1Data before · block.body))
    eth1Ok executionEvents
  have exitReplay := carryBalance_result
    (action := fun site => block.body.voluntaryExits.data.foldlM
      (processVoluntaryExit config checks) site)
    (by simpa only [← Array.foldlM_toList] using exitedOk) depositEvents
  have changeReplay := carryBalance_result
    (action := (processBlsToExecutionChanges config checks · block.body)) changedOk depositEvents
  refine ⟨events, ?_⟩
  by_cases altair : Fork.altair ≤ fork <;> by_cases bellatrix : Fork.bellatrix ≤ fork <;>
    by_cases electra : Fork.pectra ≤ fork
  all_goals
    simp only [altair, bellatrix, electra, ↓reduceDIte, bind, Except.bind,
      pure, Except.pure] at executionReplay requestsReplay synced attestedReplay depositReplay
    simp only [blockBalanceReplay, altair, bellatrix, electra, ↓reduceDIte,
      headerReplay, executionReplay, randaoReplay, eth1Replay,
      expectedOk, countOk, proposedReplay, slashedReplay, attestedReplay, depositReplay,
      exitReplay, changeReplay, requestsReplay, synced,
      bind, Except.bind, pure, Except.pure]
    repeat' (split at requestsReplay <;> simp_all)

def upgradeBalanceReplay (s : ForkedBeaconState preset) :
    Except TransitionError (List (BalanceEvent preset)) := do
  if upgradeDue config s then
    let next ← upgradeNext config checks s
    let rest ← upgradeBalanceReplay next.val
    if s.fork = .dencun then
      if electra : .pectra ≤ next.val.fork then
        let queued := ((next.val.state.pendingDeposits electra).data.toList.map
          fun d => d.amount.toNat).sum
        return ⟨.crossing, s, next.val, 0, queued⟩ :: rest
      else return rest
    else return rest
  else return []
termination_by Fork.hegota.ctorIdx + 1 - s.fork.ctorIdx
decreasing_by
  have later : s.fork.ctorIdx < next.val.fork.ctorIdx := next.property
  have last : next.val.fork.ctorIdx ≤ Fork.hegota.ctorIdx := by cases next.val.fork <;> decide
  omega

def _root_.EthLib.Consensus.Step.balanceEvents {x y : ForkedBeaconState preset}
    (step : Step config checks x y) :
    Except TransitionError (List (BalanceEvent preset)) :=
  match step with
  | .block engine signed _ _ => do
    if early : x.fork < .glamsterdam then
      return (← blockBalanceReplay (config := config) (checks := checks)
        early engine x.state signed.message).2
    else throw (.accessor (.forkNotYetSpecified x.fork))
  | .slot _ => do
    let cached ← processSlot x.state
    let next ← liftAccessor (liftArith (Uint64.addChecked x.state.slot 1))
    let events ← if next % preset.SLOTS_PER_EPOCH = 0 then do
        pure (← epochBalanceReplay (config := config) (checks := checks) cached).2
      else pure []
    let advanced ← advanceSlot config checks x.state
    return events ++
      (← upgradeBalanceReplay (config := config) (checks := checks) ⟨x.fork, advanced⟩)

/-- An epoch-boundary slot records its epoch passes and the subsequent fork-upgrade passes. -/
theorem _root_.EthLib.Consensus.Step.balanceEvents_epoch_slot
    {x y : ForkedBeaconState preset} (ok : advanceSlotAcross config checks x = .ok y)
    {cached middle advanced : BeaconState preset x.fork} {next : Slot}
    {events crossings : List (BalanceEvent preset)}
    (cachedOk : processSlot x.state = .ok cached)
    (nextOk : liftAccessor (liftArith (Uint64.addChecked x.state.slot 1)) =
      (Except.ok next : Except TransitionError Slot))
    (last : next % preset.SLOTS_PER_EPOCH = 0)
    (replayed : epochBalanceReplay (config := config) (checks := checks) cached =
      .ok (middle, events))
    (advancedOk : advanceSlot config checks x.state = .ok advanced)
    (crossed : upgradeBalanceReplay (config := config) (checks := checks)
      ⟨x.fork, advanced⟩ = .ok crossings) :
    (Step.slot ok).balanceEvents = .ok (events ++ crossings) := by
  simp [Step.balanceEvents, cachedOk, nextOk, last, replayed, advancedOk, crossed,
    pure, Except.pure, bind, Except.bind]

/-- Start at this run's first state and include tests with target epoch at most `high`. -/
def _root_.EthLib.Consensus.Run.balanceEvents {x : ForkedBeaconState preset} (high : Nat) :
    {y : ForkedBeaconState preset} → Run config checks x y →
      Except TransitionError (List (BalanceEvent preset))
  | _, .nil => pure []
  | _, .snoc (middle := m) pre step => do
    let prior ← pre.balanceEvents high
    if (getCurrentEpoch m.state).toNat ≤ high + 1 then
      return prior ++ (← step.balanceEvents)
    else return prior

/-- Filtering by the same horizon preserves the selected prefix's events. -/
theorem _root_.EthLib.Consensus.Run.balanceEvents_prefix {x m y : ForkedBeaconState preset}
    (pre : Run config checks x m) (tail : Run config checks m y) (high : Nat)
    (events : List (BalanceEvent preset))
    (ok : (pre.append tail).balanceEvents high = .ok events) :
    ∃ before, pre.balanceEvents high = .ok before ∧ before <+: events := by
  induction tail generalizing events with
  | nil => exact ⟨events, ok, List.prefix_refl _⟩
  | snoc tail step ih =>
    simp only [Run.append, Run.balanceEvents, bind_ok_iff] at ok
    obtain ⟨prior, priorOk, remaining⟩ := ok
    obtain ⟨before, beforeOk, initial⟩ := ih prior priorOk
    refine ⟨before, beforeOk, ?_⟩
    split at remaining
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at remaining
      obtain ⟨added, _, rfl⟩ := remaining
      exact initial.trans (List.prefix_append _ _)
    · cases remaining
      exact initial

def sourceTotal (events : List (BalanceEvent preset)) (source : BalanceSource)
    (amount : BalanceEvent preset → Nat) : Nat :=
  ((events.filter fun e => e.source == source).map amount).sum

private def EventsBounded (events : List (BalanceEvent preset)) : Prop :=
  ∀ event ∈ events, event.credits ≤ event.creditLimit ∧ event.debits ≤ event.debitLimit

private theorem eventsBounded_append {left right : List (BalanceEvent preset)}
    (first : EventsBounded left) (last : EventsBounded right) :
    EventsBounded (left ++ right) := by
  intro event member
  rcases List.mem_append.mp member with member | member
  · exact first event member
  · exact last event member

private theorem recordBalance_bounded {fork : Fork} (source : BalanceSource)
    (limits : BeaconState preset fork → Except TransitionError (Nat × Nat))
    (action : BeaconState preset fork → Except TransitionError (BeaconState preset fork))
    (bound : ∀ s t credit debit, limits s = .ok (credit, debit) → action s = .ok t →
      balanceCredits s t ≤ credit ∧ balanceDebits s t ≤ debit)
    {pre post : BalanceReplay preset fork} (initial : EventsBounded pre.2)
    (ok : recordBalance source limits action pre = .ok post) : EventsBounded post.2 := by
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨⟨credit, debit⟩, limitOk, after, actionOk, rfl⟩ := ok
  apply eventsBounded_append initial
  intro event member
  simp only [List.mem_singleton] at member
  subst event
  exact bound pre.1 after credit debit limitOk actionOk

private theorem increase_bounds {fork : Fork} {s t : BeaconState preset fork}
    {i : ValidatorIndex} {amount : Gwei} (ok : increaseBalance s i amount = .ok t) :
    balanceCredits s t ≤ amount.toNat ∧ balanceDebits s t ≤ 0 := by
  obtain ⟨inside, fits, rfl⟩ := increaseBalance_eq_ok_iff.mp ok
  have point (j : Nat) :
      actualBalanceAt ⟨fork, s.putBalance i.toNat inside (s.balances.data[i.toNat] + amount)⟩ j =
        actualBalanceAt ⟨fork, s⟩ j + if j = i.toNat then amount.toNat else 0 := by
    by_cases same : j = i.toNat
    · subst j
      simp [actualBalanceAt, BeaconState.putBalance, inside, Uint64.toNat_add_of_lt fits]
    · simp [actualBalanceAt, BeaconState.putBalance, same, Ne.symm same]
  have size := (sameSizes_increaseBalance ok).2
  simp [balanceCredits, balanceDebits, size, point, Finset.sum_ite_eq', inside]

private theorem decrease_bounds {fork : Fork} {s t : BeaconState preset fork}
    {i : ValidatorIndex} {amount : Gwei} (ok : decreaseBalance s i amount = .ok t) :
    balanceCredits s t ≤ 0 ∧ balanceDebits s t ≤ amount.toNat := by
  obtain ⟨inside, rfl⟩ := decreaseBalance_eq_ok_iff.mp ok
  have point (j : Nat) :
      actualBalanceAt ⟨fork, s.putBalance i.toNat inside
        (Uint64.saturatingSub s.balances.data[i.toNat] amount)⟩ j =
        actualBalanceAt ⟨fork, s⟩ j - if j = i.toNat then amount.toNat else 0 := by
    by_cases same : j = i.toNat
    · subst j
      simp [actualBalanceAt, BeaconState.putBalance, inside, Uint64.toNat_saturatingSub]
    · simp [actualBalanceAt, BeaconState.putBalance, same, Ne.symm same]
  constructor
  · simp [balanceCredits, point]
  · unfold balanceDebits
    simp only [point]
    calc
      _ ≤ ∑ j ∈ Finset.range s.balances.data.size,
          if j = i.toNat then amount.toNat else 0 := by
        apply Finset.sum_le_sum
        intro j _
        omega
      _ = amount.toNat := by simp [Finset.sum_ite_eq', inside]

private theorem replayDeltas_bounded {fork : Fork} (source : BalanceSource)
    (deltas : Array Gwei × Array Gwei) {pre post : BalanceReplay preset fork}
    (initial : EventsBounded pre.2) (ok : replayDeltas source deltas pre = .ok post) :
    EventsBounded post.2 := by
  apply foldlM_ok_invariant (fun pre => EventsBounded pre.2) _ initial ok
  intro pre i post initial ok
  simp only [bind_ok_iff] at ok
  obtain ⟨index, _, rewarded, rewardedOk, penalizedOk⟩ := ok
  have rewardedBound := recordBalance_bounded .rewards _ _
    (fun s t credit debit limits action => by
      cases limits
      exact increase_bounds (liftAccessor_ok.mp action)) initial rewardedOk
  exact recordBalance_bounded source _ _
    (fun s t credit debit limits action => by
      cases limits
      exact decrease_bounds (liftAccessor_ok.mp action)) rewardedBound penalizedOk

private theorem replayRewards_bounded {fork : Fork} {pre post : BalanceReplay preset fork}
    (initial : EventsBounded pre.2)
    (ok : replayRewards (config := config) pre = .ok post) : EventsBounded post.2 := by
  simp only [replayRewards] at ok
  split at ok
  · cases ok
    exact initial
  · simp only [bind_ok_iff] at ok
    obtain ⟨ordinary, _, inactivity, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨middle, folded, last⟩ := ok
      exact replayDeltas_bounded _ _
        (foldlM_ok_invariant (fun pre => EventsBounded pre.2)
          (fun _ _ _ h ok => replayDeltas_bounded _ _ h ok) initial folded) last
    · simp only [bind_ok_iff] at ok
      obtain ⟨rewards, _, rewarded, rewardOk, middle, folded, last⟩ := ok
      exact replayDeltas_bounded _ _
        (foldlM_ok_invariant (fun pre => EventsBounded pre.2)
          (fun _ _ _ h ok => replayDeltas_bounded _ _ h ok)
          (replayDeltas_bounded _ _ initial rewardOk) folded) last

private theorem replayDeltas_matches {fork : Fork} (source : BalanceSource)
    (deltas : Array Gwei × Array Gwei) {pre post : BalanceReplay preset fork}
    (initial : BalancesMatch pre.1) (ok : replayDeltas source deltas pre = .ok post) :
    BalancesMatch post.1 := by
  apply foldlM_ok_invariant (fun pre => BalancesMatch pre.1) _ initial ok
  intro pre i post initial ok
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
    exists_eq_left', liftAccessor_ok] at ok
  obtain ⟨index, _, rewarded, rewardedOk, after, afterOk, rfl⟩ := ok
  obtain ⟨middle, rewardedOk, rfl⟩ := rewardedOk
  exact balancesMatch_of_sameSizes (sameSizes_decreaseBalance afterOk)
    (balancesMatch_of_sameSizes (sameSizes_increaseBalance rewardedOk) initial)

private theorem replayRewards_matches {fork : Fork} {pre post : BalanceReplay preset fork}
    (initial : BalancesMatch pre.1)
    (ok : replayRewards (config := config) pre = .ok post) : BalancesMatch post.1 := by
  simp only [replayRewards] at ok
  split at ok
  · cases ok
    exact initial
  · simp only [bind_ok_iff] at ok
    obtain ⟨ordinary, _, inactivity, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨middle, folded, last⟩ := ok
      exact replayDeltas_matches _ _
        (foldlM_ok_invariant (fun pre => BalancesMatch pre.1)
          (fun _ _ _ h ok => replayDeltas_matches _ _ h ok) initial folded) last
    · simp only [bind_ok_iff] at ok
      obtain ⟨rewards, _, rewarded, rewardOk, middle, folded, last⟩ := ok
      exact replayDeltas_matches _ _
        (foldlM_ok_invariant (fun pre => BalancesMatch pre.1)
          (fun _ _ _ h ok => replayDeltas_matches _ _ h ok)
          (replayDeltas_matches _ _ initial rewardOk) folded) last

private theorem epochBalanceReplay_bounded {fork : Fork} {s : BeaconState preset fork}
    {post : BalanceReplay preset fork} (initial : BalancesMatch s)
    (early : fork < .glamsterdam)
    (ok : epochBalanceReplay (config := config) (checks := checks) s = .ok post) :
    EventsBounded post.2 := by
  have before : fork < .hegota := Nat.lt_trans early (by decide)
  unfold epochBalanceReplay at ok
  obtain ⟨justified, justifiedOk, ok⟩ := bind_ok_iff.mp ok
  simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at justifiedOk
  obtain ⟨justified, justifiedOk, rfl⟩ := justifiedOk
  have matched := balancesMatch_of_sameSizes
    (sameSizes_processJustificationAndFinalization justifiedOk) initial
  by_cases altair : .altair ≤ fork
  case' pos =>
    simp only [altair, ↓reduceDIte] at ok
    obtain ⟨inactive, inactiveOk, ok⟩ := bind_ok_iff.mp ok
    simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at inactiveOk
    obtain ⟨inactive, inactiveOk, rfl⟩ := inactiveOk
    have inactiveMatch := (frame_processInactivityUpdates inactiveOk).balancesMatch matched
    clear matched
    simp only [bind_ok_iff] at ok
    obtain ⟨rewarded, rewardOk, rest⟩ := ok
    have rewardedMatch := replayRewards_matches inactiveMatch rewardOk
    have rewardedBound := replayRewards_bounded (by simp [EventsBounded]) rewardOk
  case' neg =>
    simp only [altair, ↓reduceDIte, pure, Except.pure, bind_ok_iff,
      Except.ok.injEq, exists_eq_left'] at ok
    obtain ⟨rewarded, rewardOk, rest⟩ := ok
    have rewardedMatch := replayRewards_matches matched rewardOk
    have rewardedBound := replayRewards_bounded (by simp [EventsBounded]) rewardOk
  all_goals
    simp only [before, ↓reduceDIte, carryBalance, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at rest
    obtain ⟨registered, registeredOk, slashed, slashedOk, reset, resetOk, last⟩ := rest
    obtain ⟨registered, registeredOk, rfl⟩ := registeredOk
    have registeredMatch := (frame_processRegistryUpdates registeredOk).balancesMatch rewardedMatch
    have slashedFacts : BalancesMatch slashed.1 ∧ EventsBounded slashed.2 := by
      simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at slashedOk
      obtain ⟨⟨credit, debit⟩, limitOk, after, afterOk, rfl⟩ := slashedOk
      simp only [Prod.mk.injEq] at limitOk
      obtain ⟨limit, limitOk, rfl, rfl⟩ := limitOk
      obtain ⟨limit', limitOk', credits, debits⟩ :=
        delayed_slashing_bounds registered after
          (registered.validators.bound early) afterOk
      have same := Except.ok.inj (limitOk.symm.trans limitOk')
      subst limit'
      refine ⟨(frame_processSlashings afterOk).balancesMatch registeredMatch,
        eventsBounded_append rewardedBound ?_⟩
      intro event member
      simp only [List.mem_singleton] at member
      subst event
      exact ⟨credits.le, debits⟩
    obtain ⟨reset, resetOk, rfl⟩ := resetOk
    have resetMatch := (frame_processEth1DataReset resetOk).balancesMatch slashedFacts.1
    split at last
    · rename_i electra
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at last
      obtain ⟨deposited, depositOk, consolidated, consolidationOk, rfl⟩ := last
      have deposits := pending_deposit_bound reset deposited resetMatch electra depositOk
      have consolidations :=
        consolidation_transfer_bound deposited consolidated electra consolidationOk
      apply eventsBounded_append (eventsBounded_append slashedFacts.2 ?_) ?_
      · intro event member
        simp only [List.mem_singleton] at member
        subst event
        exact ⟨deposits.2, deposits.1.le⟩
      · intro event member
        simp only [List.mem_singleton] at member
        subst event
        exact consolidations.2
    · cases last
      exact slashedFacts.2

private theorem deposit_bounds {fork : Fork} {s t : BeaconState preset fork}
    (matched : BalancesMatch s) (before : fork < .hegota) (deposit : Deposit)
    (ok : processDeposit config checks before s deposit = .ok t) :
    balanceCredits s t ≤ (if fork < .pectra then deposit.data.amount.toNat else 0) ∧
      balanceDebits s t ≤ 0 := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok ok
  let site := { s with eth1DepositIndex := fun _ => next }
  have matchedSite : BalancesMatch site := matched
  change applyDeposit config checks site _ _ _ _ = .ok t at applied
  unfold applyDeposit at applied
  split at applied
  · rename_i electra
    have notEarly : ¬ fork < .pectra := Nat.not_lt.mpr electra
    simp only [notEarly, ↓reduceIte]
    have added {u : BeaconState preset fork}
        (ok : addValidatorToRegistry site deposit.data.pubkey
          deposit.data.withdrawalCredentials 0 = .ok u) :
        balanceCredits s u = 0 ∧ balanceDebits s u = 0 := by
      have balances := (addValidatorToRegistry_push ok matchedSite).2
      have point (j : Nat) : actualBalanceAt ⟨fork, u⟩ j = actualBalanceAt ⟨fork, s⟩ j := by
        simp only [actualBalanceAt, balances, site, Array.getElem?_push]
        split <;> simp_all
      simp [balanceCredits, balanceDebits, point]
    unfold applyDepositElectra at applied
    split at applied
    · simp only [bind_ok_iff] at applied
      obtain ⟨valid, _, applied⟩ := applied
      split at applied
      · simp only [bind_ok_iff, liftAccessor_ok] at applied
        obtain ⟨u, add, pending⟩ := applied
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq pending
        exact ⟨(added add).1.le, (added add).2.le⟩
      · have same : site = t := Except.ok.inj applied
        rw [← same]
        simp [balanceCredits, balanceDebits, actualBalanceAt, site]
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp applied)
      simp [balanceCredits, balanceDebits, actualBalanceAt, site]
  · rename_i notElectra
    have early : fork < .pectra := Nat.lt_of_not_le notElectra
    have bounds := deposit_credit_bound site t matchedSite _ applied
    simpa only [early, ↓reduceIte, balanceCredits, balanceDebits, actualBalanceAt, site]
      using And.intro bounds.2 bounds.1.le

private theorem execution_bounds {fork : Fork} {s t : BeaconState preset fork}
    (early : fork < .glamsterdam) (engine : ExecutionEngine preset fork)
    (body : BeaconBlockBody preset fork) (bellatrix : .bellatrix ≤ fork)
    (ok : processBlockExecution config checks engine s body bellatrix = .ok t) :
    ∃ debit, (if capella : .shapella ≤ fork then do
        return (0, ((← getExpectedWithdrawals s capella).withdrawals.toList.map
          fun w => w.amount.toNat).sum)
      else pure (0, 0)) = Except.ok (0, debit) ∧
      balanceCredits s t ≤ 0 ∧ balanceDebits s t ≤ debit := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le.mpr early
  simp only [processBlockExecution, notGloas, ↓reduceDIte] at ok
  split at ok
  · rename_i capella
    obtain ⟨u, withdrawals, payload⟩ := bind_ok_iff.mp ok
    obtain ⟨_, header, _, rfl⟩ := processExecutionPayload_ok payload
    obtain ⟨expected, expectedOk, _, applied⟩ := processWithdrawals_expected early withdrawals
    obtain ⟨v, applied, balances, _⟩ := applyExpectedWithdrawals_balances applied
    have bounds := withdrawal_debit_bound s v expected.withdrawals applied
    refine ⟨(expected.withdrawals.toList.map fun w => w.amount.toNat).sum, ?_, ?_, ?_⟩
    · simp [capella, expectedOk, bind, Except.bind, pure, Except.pure]
    · simpa only [balanceCredits, actualBalanceAt, balances] using bounds.1.le
    · simpa only [balanceDebits, actualBalanceAt, balances] using bounds.2
  · rename_i notCapella
    refine ⟨0, by simp [notCapella, pure, Except.pure], ?_⟩
    split at ok
    · obtain ⟨_, header, _, rfl⟩ := processExecutionPayload_ok ok
      simp [balanceCredits, balanceDebits, actualBalanceAt]
    · cases ok
      simp [balanceCredits, balanceDebits]

private theorem balance_triangle {fork : Fork} (s u t : BeaconState preset fork)
    (first : s.balances.data.size = u.balances.data.size)
    (last : t.balances.data.size = u.balances.data.size) :
    balanceCredits s t ≤ balanceCredits s u + balanceCredits u t ∧
      balanceDebits s t ≤ balanceDebits s u + balanceDebits u t := by
  constructor
  · unfold balanceCredits
    rw [last, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    omega
  · unfold balanceDebits
    rw [first, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    omega

private theorem sync_bounds {fork : Fork} {s t : BeaconState preset fork}
    (altair : .altair ≤ fork) (aggregate : SyncAggregate preset)
    (ok : processSyncAggregate config checks s altair aggregate = .ok t) :
    ∃ reward proposer,
      syncParticipantReward s = .ok reward ∧
      liftAccessor (liftArith (do
        Uint64.divChecked (← Uint64.mulChecked reward PROPOSER_WEIGHT)
          (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT))) = Except.ok proposer ∧
      balanceCredits s t ≤
        preset.SYNC_COMMITTEE_SIZE.toNat * (reward.toNat + proposer.toNat) ∧
      balanceDebits s t ≤ preset.SYNC_COMMITTEE_SIZE.toNat * reward.toNat := by
  simp only [processSyncAggregate, bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, reward, rewardOk, proposer, proposerOk,
    members, membersOk, folded⟩ := ok
  refine ⟨reward, proposer, rewardOk, proposerOk, ?_⟩
  have fold (xs : List (ValidatorIndex × Bool)) (s t : BeaconState preset fork)
      (proposerIndex : Except AccessorError ValidatorIndex)
      (ok : xs.foldlM (applySyncReward reward proposer proposerIndex) s = .ok t) :
      t.balances.data.size = s.balances.data.size ∧
      balanceCredits s t ≤ xs.length * (reward.toNat + proposer.toNat) ∧
      balanceDebits s t ≤ xs.length * reward.toNat := by
    induction xs generalizing s with
    | nil => cases ok; simp [balanceCredits, balanceDebits]
    | cons x xs ih =>
      obtain ⟨u, one, rest⟩ := bind_ok_iff.mp ok
      have bounds := sync_reward_bounds s u reward proposer proposerIndex x one
      have sizes : u.balances.data.size = s.balances.data.size := by
        unfold applySyncReward at one
        split at one
        · simp only [bind_ok_iff, liftAccessor_ok] at one
          obtain ⟨v, first, _, _, last⟩ := one
          exact (sameSizes_increaseBalance last).2.trans (sameSizes_increaseBalance first).2
        · exact (sameSizes_decreaseBalance (liftAccessor_ok.mp one)).2
      have tail := ih u rest
      have triangle := balance_triangle s u t sizes.symm tail.1
      refine ⟨tail.1.trans sizes, ?_, ?_⟩ <;>
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul] <;>
        split_ifs at bounds <;> omega
  have bounds := fold _ s t _ (by simpa only [← Array.foldlM_toList] using folded)
  have length : (members.zip aggregate.syncCommitteeBits.bits.toArray).toList.length ≤
      preset.SYNC_COMMITTEE_SIZE.toNat := by
    simp only [Array.length_toList, Array.size_zip]
    exact (Nat.min_le_right _ _).trans (by simp)
  exact ⟨bounds.2.1.trans (Nat.mul_le_mul_right _ length),
    bounds.2.2.trans (Nat.mul_le_mul_right _ length)⟩

private theorem proposer_slashing_bounds {fork : Fork} {s t : BeaconState preset fork}
    (sl : ProposerSlashing) (ok : processProposerSlashing config checks s sl = .ok t) :
    ∃ credit debit,
      slashingLimits [sl.signedHeader1.message.proposerIndex] s = .ok (credit, debit) ∧
      balanceCredits s t ≤ credit ∧ balanceDebits s t ≤ debit := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, v, found, _, _, _, _, _, _, slashed⟩ := ok
  have bounds := initial_slashing_bounds s t _ none v found slashed
  refine ⟨_, _, ?_, bounds.2, bounds.1⟩
  simp [slashingLimits, found, List.mapM_cons, List.mapM_nil, liftAccessor,
    Except.mapError, bind, Except.bind, pure, Except.pure]

private theorem slash_effective {fork : Fork} {s t : BeaconState preset fork}
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config s index whistleblower = .ok t) :
    ∀ j, (getValidator t j).map Validator.effectiveBalance =
      (getValidator s j).map Validator.effectiveBalance := by
  have set {s t : BeaconState preset fork} {i : ValidatorIndex} {v w : Validator}
      (read : getValidator s i = .ok v) (ok : s.setValidator i w = .ok t)
      (same : w.effectiveBalance = v.effectiveBalance) (j : ValidatorIndex) :
      (getValidator t j).map Validator.effectiveBalance =
        (getValidator s j).map Validator.effectiveBalance := by
    by_cases h : j = i
    · subst j
      rw [getValidator_setValidator_self ok, read]
      exact congrArg Except.ok same
    · rw [getValidator_setValidator_of_ne ok h]
  have exit {s t : BeaconState preset fork}
      (ok : initiateValidatorExit config s index = .ok t) (j : ValidatorIndex) :
      (getValidator t j).map Validator.effectiveBalance =
        (getValidator s j).map Validator.effectiveBalance := by
    obtain ⟨v, read, unchanged | ⟨_, queued, epoch, withdrawal, queue, _, changed⟩⟩ :=
      initiateValidatorExit_ok ok
    · rw [unchanged.2]
    · have same := (exitQueue_validators queue).1
      rw [set (v := v) (by rw [getValidator_of_validators_eq same]; exact read) changed rfl,
        getValidator_of_validators_eq same]
  obtain ⟨_, _, _, marked, _, _, slashings, _, _, _, _, last, exited, found, _, changed,
    _, _, _, lowered, _, _, raised, paid, rfl⟩ := slashValidator_ok ok
  intro j
  have middle := set found changed rfl
  have endpoint : ∀ j, (getValidator last j).map Validator.effectiveBalance =
      (getValidator s j).map Validator.effectiveBalance := by
    intro j
    rw [getValidator_of_validators_eq (increaseBalance_validators paid),
      getValidator_of_validators_eq (increaseBalance_validators raised),
      getValidator_of_validators_eq (decreaseBalance_validators lowered)]
    change (getValidator marked j).map Validator.effectiveBalance = _
    rw [middle j, exit exited j]
  split <;> exact endpoint j

private theorem attester_slashing_bounds {fork : Fork} {s t : BeaconState preset fork}
    (sl : AttesterSlashing preset fork)
    (ok : processAttesterSlashing config checks s sl = .ok t) :
    ∃ credit debit, slashingLimits (slashingIndices sl) s = .ok (credit, debit) ∧
      balanceCredits s t ≤ credit ∧ balanceDebits s t ≤ debit := by
  have fold (indices : List ValidatorIndex) (s t : BeaconState preset fork) (flag last : Bool)
      (ok : indices.foldlM (slashIfSlashable config) (s, flag) = .ok (t, last)) :
      ∃ credit debit, slashingLimits indices s = .ok (credit, debit) ∧
        balanceCredits s t ≤ credit ∧ balanceDebits s t ≤ debit ∧
        t.balances.data.size = s.balances.data.size := by
    induction indices generalizing s flag with
    | nil =>
      cases ok
      exact ⟨0, 0, by simp [slashingLimits, liftAccessor, Except.mapError, pure,
        Except.pure, bind, Except.bind], by simp [balanceCredits],
        by simp [balanceDebits], rfl⟩
    | cons i indices ih =>
      obtain ⟨⟨u, flag'⟩, one, rest⟩ := bind_ok_iff.mp ok
      simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at one
      obtain ⟨v, read, one⟩ := one
      have oneFacts :
          balanceCredits s u ≤ v.effectiveBalance.toNat /
            (EthLib.Consensus.parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ∧
          balanceDebits s u ≤ v.effectiveBalance.toNat /
            (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
          u.balances.data.size = s.balances.data.size ∧
          ∀ j, (getValidator u j).map Validator.effectiveBalance =
            (getValidator s j).map Validator.effectiveBalance := by
        split at one
        · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at one
          obtain ⟨u', slashed, rfl, rfl⟩ := one
          have bounds := initial_slashing_bounds s u' i none v read slashed
          exact ⟨bounds.2, bounds.1, (sameSizes_slashValidator slashed).2,
            slash_effective slashed⟩
        · cases one
          exact ⟨by simp [balanceCredits], by simp [balanceDebits], rfl, fun _ => rfl⟩
      obtain ⟨credit, debit, limits, credits, debits, sizes⟩ := ih u flag' rest
      have triangle := balance_triangle s u t oneFacts.2.2.1.symm sizes
      refine ⟨v.effectiveBalance.toNat /
          (EthLib.Consensus.parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat + credit,
        v.effectiveBalance.toNat /
          (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat + debit,
        ?_, by omega, by omega, sizes.trans oneFacts.2.2.1⟩
      simp only [slashingLimits, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
        Except.ok.injEq] at limits ⊢
      obtain ⟨validators, found, limits⟩ := limits
      have original : ∃ validators', indices.mapM (getValidator s) = .ok validators' ∧
          (validators'.map fun v => v.effectiveBalance) =
            (validators.map fun v => v.effectiveBalance) := by
        clear limits credits debits triangle sizes rest ih ok
        induction indices generalizing validators with
        | nil => cases found; exact ⟨[], rfl, rfl⟩
        | cons j js ih =>
          simp only [List.mapM_cons, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at found
          obtain ⟨v', read', vs, rest, rfl⟩ := found
          have eq := oneFacts.2.2.2 j
          rw [read'] at eq
          cases originalRead : getValidator s j with
          | error e => simp [originalRead, Except.map] at eq
          | ok w =>
            simp only [originalRead, Except.map, Except.ok.injEq] at eq
            obtain ⟨ws, wsOk, same⟩ := ih vs rest
            refine ⟨w :: ws, ?_, ?_⟩
            · simp [List.mapM_cons, originalRead, wsOk, bind, Except.bind, pure, Except.pure]
            · simp only [List.map_cons, same, eq]
      obtain ⟨validators', found', same⟩ := original
      refine ⟨v :: validators', ?_, ?_⟩
      · simp [List.mapM_cons, read, found', bind, Except.bind, pure, Except.pure]
      · have creditsEq := congrArg (fun vs => (vs.map fun b => b.toNat /
            (EthLib.Consensus.parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat).sum)
          same
        have debitsEq := congrArg (fun vs => (vs.map fun b => b.toNat /
            (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat).sum)
          same
        simp only [List.map_map, Function.comp_def] at creditsEq debitsEq
        cases limits
        simp only [List.map_cons, List.sum_cons, creditsEq, debitsEq]
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨u, flag⟩, folded, _, _, rfl⟩ := ok
  obtain ⟨credit, debit, limits, credits, debits, _⟩ := fold _ s u false flag folded
  exact ⟨credit, debit, limits, credits, debits⟩

set_option maxHeartbeats 800000 in
private theorem consolidation_request_bounds {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (request : ConsolidationRequest)
    (ok : processConsolidationRequest config s electra request = .ok t) :
    balanceCredits s t ≤ 0 ∧ balanceDebits s t ≤
      (match findValidatorByPubkey s request.sourcePubkey with
      | none => 0
      | some i => actualBalanceAt ⟨fork, s⟩ i.val - preset.MIN_ACTIVATION_BALANCE.toNat) := by
  have unchanged (same : t.balances = s.balances) : balanceCredits s t ≤ 0 ∧
      balanceDebits s t ≤ (match findValidatorByPubkey s request.sourcePubkey with
        | none => 0
        | some i => actualBalanceAt ⟨fork, s⟩ i.val - preset.MIN_ACTIVATION_BALANCE.toNat) := by
    simp [balanceCredits, balanceDebits, actualBalanceAt, same]
  have switched (i : Fin s.validators.data.size) (index : ValidatorIndex)
      (found : findValidatorByPubkey s request.sourcePubkey = some i)
      (indexOk : Uint64.ofNatChecked i.val = .ok index)
      (ok : switchToCompoundingValidator s electra index = .ok t) :
      balanceCredits s t ≤ 0 ∧ balanceDebits s t ≤
        (match findValidatorByPubkey s request.sourcePubkey with
        | none => 0
        | some i => actualBalanceAt ⟨fork, s⟩ i.val - preset.MIN_ACTIVATION_BALANCE.toNat) := by
    simp only [switchToCompoundingValidator, bind_ok_iff] at ok
    obtain ⟨v, _, u, set, queued⟩ := ok
    have queuedCopy := queued
    simp only [queueExcessActiveBalance, bind_ok_iff] at queuedCopy
    obtain ⟨balance, read, _⟩ := queuedCopy
    have bounds := excess_queue_debit u t electra index balance read queued
    obtain ⟨_, rfl⟩ := setValidator_ok set
    have actual : actualBalanceAt ⟨fork, s⟩ i.val = balance.toNat := by
      have read := getBalance_eq_ok_iff.mp read
      simp only [BeaconState.putValidator] at read
      rw [(Uint64.ofNatChecked_ok_iff.mp indexOk).2] at read
      simp [actualBalanceAt, read]
    rw [found]
    dsimp only
    rw [actual]
    simpa only [balanceCredits, balanceDebits, actualBalanceAt,
      BeaconState.putValidator] using And.intro bounds.1.le bounds.2
  have queued (source : Validator) (sourceIndex targetIndex : ValidatorIndex)
      (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
      t.balances = s.balances := by
    simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at ok
    obtain ⟨⟨u, epoch⟩, churned, _, _, v, set, _, _, rfl⟩ := ok
    obtain ⟨_, _, balances⟩ := computeConsolidationEpochAndUpdateChurn_earliest churned
    obtain ⟨_, rfl⟩ := setValidator_ok set
    exact balances
  unfold processConsolidationRequest at ok
  split at ok
  · split at ok
    · rename_i position found
      obtain ⟨index, indexOk, ok⟩ := bind_ok_iff.mp ok
      split at ok
      · exact switched position index found
          (by cases h : Uint64.ofNatChecked position.val <;>
                simp [liftAccessor, liftArith, Except.mapError, h] at indexOk ⊢; exact indexOk)
          (liftAccessor_ok.mp ok)
      · cases ok
        exact unchanged rfl
    · cases ok
      exact unchanged rfl
  · simp only [bind, Except.bind, pure, Except.pure] at ok
    repeat' split at ok
    all_goals first
      | (cases ok; done)
      | (cases ok; exact unchanged rfl)
      | exact unchanged (queued _ _ _ ok)

private def ReplayBounded {fork : Fork} (pre : BalanceReplay preset fork) : Prop :=
  BalancesMatch pre.1 ∧ EventsBounded pre.2

private theorem carryBalance_bounded {fork : Fork}
    (action : BeaconState preset fork → Except TransitionError (BeaconState preset fork))
    (preserves : ∀ s t, action s = .ok t → BalancesMatch s → BalancesMatch t)
    {pre post : BalanceReplay preset fork} (initial : ReplayBounded pre)
    (ok : carryBalance action pre = .ok post) : ReplayBounded post := by
  simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨after, afterOk, rfl⟩ := ok
  exact ⟨preserves pre.1 after afterOk initial.1, initial.2⟩

private theorem recordBalance_matched {fork : Fork} (source : BalanceSource)
    (limits : BeaconState preset fork → Except TransitionError (Nat × Nat))
    (action : BeaconState preset fork → Except TransitionError (BeaconState preset fork))
    (preserves : ∀ s t, action s = .ok t → BalancesMatch s → BalancesMatch t)
    (bound : ∀ s t credit debit, BalancesMatch s →
      limits s = .ok (credit, debit) → action s = .ok t →
      balanceCredits s t ≤ credit ∧ balanceDebits s t ≤ debit)
    {pre post : BalanceReplay preset fork} (initial : ReplayBounded pre)
    (ok : recordBalance source limits action pre = .ok post) : ReplayBounded post := by
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨⟨credit, debit⟩, limitOk, after, actionOk, rfl⟩ := ok
  refine ⟨preserves pre.1 after actionOk initial.1, eventsBounded_append initial.2 ?_⟩
  intro event member
  simp only [List.mem_singleton] at member
  subst event
  exact bound pre.1 after credit debit initial.1 limitOk actionOk

set_option maxHeartbeats 800000 in
private theorem blockBalanceReplay_bounded {fork : Fork} {s : BeaconState preset fork}
    (early : fork < .glamsterdam) (engine : ExecutionEngine preset fork)
    (block : BeaconBlock preset fork) {post : BalanceReplay preset fork}
    (matched : BalancesMatch s)
    (ok : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok post) : EventsBounded post.2 := by
  have before : fork < .hegota := Nat.lt_trans early (by decide)
  have record {pre post : BalanceReplay preset fork} {source : BalanceSource}
      {limits : BeaconState preset fork → Except TransitionError (Nat × Nat)}
      {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
      (preserves : ∀ s t, action s = .ok t → BalancesMatch s → BalancesMatch t)
      (bound : ∀ s t credit debit, BalancesMatch s →
        limits s = .ok (credit, debit) → action s = .ok t →
        balanceCredits s t ≤ credit ∧ balanceDebits s t ≤ debit)
      (initial : ReplayBounded pre) (ok : recordBalance source limits action pre = .ok post) :
      ReplayBounded post := recordBalance_matched _ _ _ preserves bound initial ok
  have proposer {pre post : BalanceReplay preset fork} (sl : ProposerSlashing)
      (initial : ReplayBounded pre)
      (ok : recordBalance .slashings (slashingLimits [sl.signedHeader1.message.proposerIndex])
        (processProposerSlashing config checks · sl) pre = .ok post) : ReplayBounded post := by
    apply record (fun _ _ ok => (frame_processProposerSlashing ok).balancesMatch) _ initial ok
    intro s t credit debit _ limits action
    obtain ⟨credit', debit', limits', bounds⟩ := proposer_slashing_bounds sl action
    cases Except.ok.inj (limits.symm.trans limits')
    exact bounds
  have attester {pre post : BalanceReplay preset fork} (sl : AttesterSlashing preset fork)
      (initial : ReplayBounded pre)
      (ok : recordBalance .slashings (slashingLimits (slashingIndices sl))
        (processAttesterSlashing config checks · sl) pre = .ok post) : ReplayBounded post := by
    apply record (fun _ _ ok => (frame_processAttesterSlashing ok).balancesMatch) _ initial ok
    intro s t credit debit _ limits action
    obtain ⟨credit', debit', limits', bounds⟩ := attester_slashing_bounds sl action
    cases Except.ok.inj (limits.symm.trans limits')
    exact bounds
  have attestation {pre post : BalanceReplay preset fork} (att : Attestation preset fork)
      (initial : ReplayBounded pre)
      (ok : recordBalance .rewards (fun site => do
          return (← attestationCredit site att s.latestBlockHeader.slot, 0))
        (processAttestation config checks · s.latestBlockHeader.slot att) pre = .ok post) :
      ReplayBounded post := by
    apply record (fun _ _ ok => (frame_processAttestation ok).balancesMatch) _ initial ok
    intro site t credit debit _ limits action
    obtain ⟨credit', limits', debits, credits⟩ :=
      attestation_proposer_bound site t att s.latestBlockHeader.slot early action
    simp only [limits', bind, Except.bind, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at limits
    rcases limits with ⟨rfl, rfl⟩
    exact ⟨credits, debits.le⟩
  have deposit {pre post : BalanceReplay preset fork} (dep : Deposit)
      (initial : ReplayBounded pre)
      (ok : recordBalance .deposits
        (fun _ => pure (if fork < .pectra then dep.data.amount.toNat else 0, 0))
        (processDeposit config checks before · dep) pre = .ok post) : ReplayBounded post := by
    apply record (fun _ _ ok => balancesMatch_processDeposit ok) _ initial ok
    intro site t credit debit matched limits action
    cases limits
    exact deposit_bounds matched before dep action
  have excess {pre post : BalanceReplay preset fork} (electra : .pectra ≤ fork)
      (request : ConsolidationRequest) (initial : ReplayBounded pre)
      (ok : recordBalance .excess (fun site => pure (0,
          match findValidatorByPubkey site request.sourcePubkey with
          | none => 0
          | some i => actualBalanceAt ⟨fork, site⟩ i.val - preset.MIN_ACTIVATION_BALANCE.toNat))
        (processConsolidationRequest config · electra request) pre = .ok post) :
      ReplayBounded post := by
    apply record (fun _ _ ok =>
      balancesMatch_of_sameSizes (sameSizes_processConsolidationRequest ok)) _ initial ok
    intro site t credit debit _ limits action
    cases limits
    exact consolidation_request_bounds electra request action
  unfold blockBalanceReplay at ok
  obtain ⟨headed, headerOk, ok⟩ := bind_ok_iff.mp ok
  have headedBound := carryBalance_bounded _
    (fun _ _ ok => (frame_processBlockHeader ok).balancesMatch)
    ⟨matched, by simp [EventsBounded]⟩ headerOk
  by_cases bellatrix : .bellatrix ≤ fork
  case' pos =>
    simp only [bellatrix, ↓reduceDIte] at ok
    obtain ⟨executed, executionOk, rest⟩ := bind_ok_iff.mp ok
    have executedBound : ReplayBounded executed := by
      apply record (fun _ _ ok => (frame_processBlockExecution ok).balancesMatch) _
        headedBound executionOk
      intro site t credit debit _ limits action
      obtain ⟨debit', limits', credits, debits⟩ := execution_bounds early engine block.body
        bellatrix action
      cases Except.ok.inj (limits.symm.trans limits')
      exact ⟨credits, debits⟩
  case' neg =>
    simp only [bellatrix, ↓reduceDIte, pure, Except.pure, bind_ok_iff,
      Except.ok.injEq, exists_eq_left'] at ok
    have rest := ok
    have executedBound := headedBound
  all_goals
    try simp only [bind_ok_iff] at rest
    obtain ⟨randao, randaoOk, voted, votedOk, expected, _, _, _,
      proposed, proposedOk, attested, attestedOk, rewarded, rewardedOk, deposited, depositOk,
      exited, exitOk, changed, changedOk, rest⟩ := rest
    have randaoBound := carryBalance_bounded _
      (fun _ _ ok => (frame_processRandao ok).balancesMatch) executedBound randaoOk
    have votedBound := carryBalance_bounded _
      (fun _ _ ok => (frame_processEth1Data ok).balancesMatch) randaoBound votedOk
    have proposedBound := foldlM_ok_invariant ReplayBounded
      (fun _ sl _ h ok => proposer sl h ok) votedBound proposedOk
    have attestedBound := foldlM_ok_invariant ReplayBounded
      (fun _ sl _ h ok => attester sl h ok) proposedBound attestedOk
    have rewardedBound := foldlM_ok_invariant ReplayBounded
      (fun _ att _ h ok => attestation att h ok) attestedBound rewardedOk
    have depositedBound := foldlM_ok_invariant ReplayBounded
      (fun _ dep _ h ok => deposit dep h ok) rewardedBound depositOk
    have exitedBound := carryBalance_bounded _ (fun _ _ ok h =>
      foldlM_ok_invariant BalancesMatch
        (fun _ _ _ h ok => (frame_processVoluntaryExit ok).balancesMatch h) h
        (by simpa only [← Array.foldlM_toList] using ok)) depositedBound exitOk
    have changedBound := carryBalance_bounded _ (fun _ _ ok h => by
      unfold processBlsToExecutionChanges at ok
      split at ok
      · exact foldlM_ok_invariant BalancesMatch
          (fun _ _ _ h ok => (frame_processBlsToExecutionChange ok).balancesMatch h) h
          (by simpa only [← Array.foldlM_toList] using ok)
      · cases ok; exact h) exitedBound changedOk
    by_cases electra : .pectra ≤ fork
    case' pos =>
      simp only [electra, ↓reduceDIte, bind_ok_iff] at rest
      obtain ⟨deposits, depositRequestOk, withdrawals, withdrawalOk,
        requested, consolidations, rest⟩ := rest
      have requestedBound : ReplayBounded requested := by
        have depositsBound := carryBalance_bounded _ (fun _ _ ok h =>
          foldlM_ok_invariant BalancesMatch
            (fun _ _ _ h ok => (frame_processDepositRequest ok).balancesMatch h) h
            (by simpa only [← Array.foldlM_toList] using ok)) changedBound depositRequestOk
        have withdrawalsBound := carryBalance_bounded _ (fun _ _ ok h =>
          foldlM_ok_invariant BalancesMatch
            (fun _ _ _ h ok => (frame_processWithdrawalRequest ok).balancesMatch h) h
            (by simpa only [← Array.foldlM_toList] using ok)) depositsBound withdrawalOk
        exact foldlM_ok_invariant ReplayBounded
          (fun _ request _ h ok => excess electra request h ok) withdrawalsBound consolidations
    case' neg =>
      simp only [electra, ↓reduceDIte, pure, Except.pure, bind_ok_iff,
        Except.ok.injEq, exists_eq_left'] at rest
      have requestedBound := changedBound
    all_goals
      split at rest
      · have final : ReplayBounded post := by
          apply record (fun _ _ ok => (frame_processSyncAggregate ok).balancesMatch) _
            requestedBound rest
          intro site t credit debit _ limits action
          obtain ⟨reward, proposer, rewardOk, proposerOk, bounds⟩ := sync_bounds _ _ action
          rw [rewardOk] at limits
          dsimp only [bind, Except.bind] at limits
          simp only [bind, Except.bind] at proposerOk
          rw [proposerOk] at limits
          simp only [bind, Except.bind, pure, Except.pure,
            Except.ok.injEq] at limits
          cases limits
          exact bounds
        exact final.2
      · cases rest
        exact requestedBound.2

private theorem upgradeBalanceReplay_bounded {s t : ForkedBeaconState preset}
    (ok : processUpgrades config checks s = .ok t) :
    ∃ events, upgradeBalanceReplay (config := config) (checks := checks) s = .ok events ∧
      EventsBounded events := by
  fun_induction processUpgrades config checks s generalizing t with
  | case1 s due ih =>
    obtain ⟨next, nextOk, restOk⟩ := bind_ok_iff.mp ok
    obtain ⟨rest, replay, bounded⟩ := ih next restOk
    rw [upgradeBalanceReplay]
    simp only [due, ↓reduceIte, nextOk, bind, Except.bind, replay]
    by_cases crossing : s.fork = .dencun
    · obtain ⟨fork, state⟩ := s
      dsimp only at crossing
      subst fork
      simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at nextOk
      obtain ⟨after, upgraded, rfl⟩ := nextOk
      simp only [↓reduceIte, show Fork.pectra ≤ .pectra from Nat.le_refl _, ↓reduceDIte,
        pure, Except.pure, Except.ok.injEq, exists_eq_left']
      intro event member
      rcases List.mem_cons.mp member with rfl | member
      · have bound := electra_upgrade_debit state after upgraded
        exact ⟨bound.1.le, bound.2⟩
      · exact bounded event member
    · simpa only [crossing, ↓reduceIte, pure, Except.pure, Except.ok.injEq,
        exists_eq_left'] using bounded
  | case2 s due =>
    refine ⟨[], ?_, by simp [EventsBounded]⟩
    rw [upgradeBalanceReplay]
    simp [due, pure, Except.pure]

private theorem stepBalanceEvents_bounded {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (matched : BalancesMatch x.state)
    (early : y.fork < .glamsterdam) :
    ∃ events, step.balanceEvents = .ok events ∧ EventsBounded events := by
  have before : x.fork < .glamsterdam := Nat.lt_of_le_of_lt step.chainStep.fork_le early
  cases step with
  | block engine signed due ok =>
    obtain ⟨events, replay⟩ := blockBalanceReplay_result _ _ before engine signed.message
      (applySignedBlock_ok ok).2.1
    refine ⟨events, ?_, blockBalanceReplay_bounded before engine signed.message matched replay⟩
    simp [Step.balanceEvents, before, replay, pure, Except.pure, bind, Except.bind]
  | slot ok =>
    obtain ⟨advanced, advanceOk, upgrades⟩ := bind_ok_iff.mp ok
    obtain ⟨crossings, crossingOk, crossingBound⟩ := upgradeBalanceReplay_bounded upgrades
    have advanceCopy := advanceOk
    simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at advanceCopy
    obtain ⟨next, nextOk, cached, cachedOk, epoched, epochOk, _⟩ := advanceCopy
    have cachedMatch := (frame_processSlot cachedOk).balancesMatch matched
    by_cases last : next % preset.SLOTS_PER_EPOCH = 0
    · simp only [epochIfLast, last, ↓reduceIte] at epochOk
      obtain ⟨middle, updated, events, replay, _⟩ :=
        epochBalanceReplay_result cached epoched before epochOk
      refine ⟨events ++ crossings, ?_,
        eventsBounded_append (epochBalanceReplay_bounded cachedMatch before replay) crossingBound⟩
      simp [Step.balanceEvents, cachedOk, nextOk, last, replay, advanceOk, crossingOk,
        pure, Except.pure, bind, Except.bind]
    · refine ⟨crossings, ?_, crossingBound⟩
      simp [Step.balanceEvents, cachedOk, nextOk, last, advanceOk, crossingOk,
        pure, Except.pure, bind, Except.bind]

/-- Every source is bounded separately, with no freely supplied credit or debit cap. -/
theorem source_bounds_over_interval {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (alignedCaps : MaxEffectiveBalancesAligned preset)
    (early : y.fork < .glamsterdam) (high : Nat) :
    ∃ events, tail.balanceEvents high = .ok events ∧
      ∀ source : BalanceSource,
        sourceTotal events source BalanceEvent.credits ≤ sourceTotal events source (·.creditLimit) ∧
        sourceTotal events source BalanceEvent.debits ≤
          sourceTotal events source (·.debitLimit) := by
  have invariant {z : ForkedBeaconState preset} (run : Run config checks g z) :
      Invariant z.state := by
    induction run with
    | nil =>
      obtain ⟨_, _, _, ok⟩ := genesis
      exact (initializeBeaconStateFromEth1_invariant ok).2
    | snoc pre step ih =>
      cases step with
      | slot ok => exact (advanceSlotAcross_invariant ih ok).1
      | block engine signed due ok =>
        exact (frame_processBlock (applySignedBlock_ok ok).2.1).invariant ih
  have replay : ∃ events, tail.balanceEvents high = .ok events ∧ EventsBounded events := by
    induction tail with
    | nil => exact ⟨[], rfl, by simp [EventsBounded]⟩
    | @snoc middle last pre step ih =>
      obtain ⟨prior, priorOk, priorBound⟩ :=
        ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early)
      by_cases selected : (getCurrentEpoch middle.state).toNat ≤ high + 1
      · obtain ⟨added, addedOk, addedBound⟩ := stepBalanceEvents_bounded step
          (invariant (shared.append pre)).balancesMatch early
        refine ⟨prior ++ added, ?_, eventsBounded_append priorBound addedBound⟩
        simp [Run.balanceEvents, priorOk, selected, addedOk, pure, Except.pure, bind, Except.bind]
      · refine ⟨prior, ?_, priorBound⟩
        simp [Run.balanceEvents, priorOk, selected, pure, Except.pure, bind, Except.bind]
  obtain ⟨events, replay, bounded⟩ := replay
  refine ⟨events, replay, fun source => ?_⟩
  have bound : ∀ event ∈ events.filter (fun e => e.source == source),
      event.credits ≤ event.creditLimit ∧ event.debits ≤ event.debitLimit :=
    fun event member => bounded event (List.mem_filter.mp member).1
  unfold sourceTotal
  constructor
  · exact List.sum_le_sum (fun event member => (bound event member).1)
  · exact List.sum_le_sum (fun event member => (bound event member).2)

private def coverageDelta (debit : Bool) (x y : ForkedBeaconState preset) (i : Nat) : Nat :=
  if debit then actualBalanceAt x i - actualBalanceAt y i
  else actualBalanceAt y i - actualBalanceAt x i

private def Coverage (x y : ForkedBeaconState preset)
    (events : List (BalanceEvent preset)) : Prop :=
  ∀ debit i, coverageDelta debit x y i ≤
    (events.map fun e => coverageDelta debit e.before e.after i).sum

private theorem coverage_refl (x : ForkedBeaconState preset) : Coverage x x [] := by
  intro debit i
  cases debit <;> simp [coverageDelta]

private theorem coverage_event (event : BalanceEvent preset) :
    Coverage event.before event.after [event] := by
  intro debit i
  simp

private theorem coverage_trans {x y z : ForkedBeaconState preset}
    {left right : List (BalanceEvent preset)} (first : Coverage x y left)
    (last : Coverage y z right) : Coverage x z (left ++ right) := by
  intro debit i
  have a := first debit i
  have b := last debit i
  simp only [List.map_append, List.sum_append]
  cases debit <;> simp only [coverageDelta, Bool.false_eq_true, ↓reduceIte] at * <;> omega

private theorem coverage_same {fork : Fork} {s t : BeaconState preset fork}
    (same : t.balances = s.balances) : Coverage ⟨fork, s⟩ ⟨fork, t⟩ [] := by
  intro debit i
  cases debit <;> simp [coverageDelta, actualBalanceAt, same]

private abbrev ReplayCoverage {fork : Fork} (start : BeaconState preset fork)
    (pre : BalanceReplay preset fork) : Prop := Coverage ⟨fork, start⟩ ⟨fork, pre.1⟩ pre.2

private theorem coverage_record {fork : Fork} {start : BeaconState preset fork}
    {source : BalanceSource}
    {limits : BeaconState preset fork → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
    {pre post : BalanceReplay preset fork} (initial : ReplayCoverage start pre)
    (ok : recordBalance source limits action pre = .ok post) : ReplayCoverage start post := by
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨⟨credit, debit⟩, _, after, _, rfl⟩ := ok
  exact coverage_trans initial (by intro debit i; simp)

private theorem coverage_carry {fork : Fork} {start : BeaconState preset fork}
    {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
    (keeps : ∀ s t, action s = .ok t → t.balances = s.balances)
    {pre post : BalanceReplay preset fork} (initial : ReplayCoverage start pre)
    (ok : carryBalance action pre = .ok post) : ReplayCoverage start post := by
  simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨after, actionOk, rfl⟩ := ok
  simpa only [List.append_nil] using coverage_trans initial (coverage_same (keeps _ _ actionOk))

private theorem coverage_deltas {fork : Fork} {start : BeaconState preset fork}
    (source : BalanceSource) (deltas : Array Gwei × Array Gwei)
    {pre post : BalanceReplay preset fork} (initial : ReplayCoverage start pre)
    (ok : replayDeltas source deltas pre = .ok post) : ReplayCoverage start post := by
  apply foldlM_ok_invariant (ReplayCoverage start) _ initial ok
  intro pre i post initial ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, rewarded, rewardOk, penaltyOk⟩ := ok
  exact coverage_record (coverage_record initial rewardOk) penaltyOk

private theorem coverage_rewards {fork : Fork} {start : BeaconState preset fork}
    {pre post : BalanceReplay preset fork} (initial : ReplayCoverage start pre)
    (ok : replayRewards (config := config) pre = .ok post) : ReplayCoverage start post := by
  unfold replayRewards at ok
  split at ok
  · cases ok; exact initial
  · simp only [bind_ok_iff] at ok
    obtain ⟨ordinary, _, inactivity, _, ok⟩ := ok
    split at ok
    · obtain ⟨middle, folded, last⟩ := bind_ok_iff.mp ok
      exact coverage_deltas _ _ (foldlM_ok_invariant (ReplayCoverage start)
        (fun _ _ _ h ok => coverage_deltas _ _ h ok) initial folded) last
    · simp only [bind_ok_iff] at ok
      obtain ⟨rewards, _, rewarded, rewardOk, middle, folded, last⟩ := ok
      exact coverage_deltas _ _ (foldlM_ok_invariant (ReplayCoverage start)
        (fun _ _ _ h ok => coverage_deltas _ _ h ok)
        (coverage_deltas _ _ initial rewardOk) folded) last

private theorem coverage_setAt {fork : Fork} {s t : BeaconState preset fork}
    {i : Nat} {v : Validator} (ok : s.setValidatorAt i v = .ok t) :
    t.balances = s.balances := by
  unfold BeaconState.setValidatorAt at ok
  split at ok
  · cases ok; rfl
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, impossible⟩ := ok
    cases impossible

private theorem coverage_exit {fork : Fork} {s t : BeaconState preset fork}
    {i : ValidatorIndex} (ok : initiateValidatorExit config s i = .ok t) :
    t.balances = s.balances := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok ok
  · rfl
  · obtain ⟨_, rfl⟩ := setValidator_ok set
    exact (exitQueue_validators queue).2

private theorem coverage_fold_keeps {fork : Fork} {α ε : Type}
    {action : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (keeps : ∀ s a t, action s a = .ok t → t.balances = s.balances)
    {s t : BeaconState preset fork} {xs : List α} (ok : xs.foldlM action s = .ok t) :
    t.balances = s.balances :=
  foldlM_ok_invariant (fun t => t.balances = s.balances)
    (fun a b c previous step => (keeps a b c step).trans previous) rfl ok

private theorem coverage_registry {fork : Fork} {s t : BeaconState preset fork}
    (ok : processRegistryUpdates config s = .ok t) : t.balances = s.balances := by
  have electra (epoch : Epoch) (s t : BeaconState preset fork) (i : Nat)
      (ok : updateRegistryEntryElectra config epoch s i = .ok t) :
      t.balances = s.balances := by
    simp only [updateRegistryEntryElectra, bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · obtain ⟨_, _, set⟩ := bind_ok_iff.mp ok
      exact coverage_setAt (liftAccessor_ok.mp set)
    · split at ok
      · obtain ⟨_, _, exited⟩ := bind_ok_iff.mp ok
        exact coverage_exit (liftAccessor_ok.mp exited)
      · split at ok
        · exact coverage_setAt (liftAccessor_ok.mp ok)
        · cases ok; rfl
  have ordinary (s t : BeaconState preset fork) (i : Nat)
      (ok : updateRegistryEntry config s i = .ok t) : t.balances = s.balances := by
    simp only [updateRegistryEntry, bind_ok_iff] at ok
    obtain ⟨_, _, _, _, u, set, rest⟩ := ok
    have same := coverage_setAt (liftAccessor_ok.mp set)
    split at rest
    · obtain ⟨_, _, exited⟩ := bind_ok_iff.mp rest
      exact (coverage_exit (liftAccessor_ok.mp exited)).trans same
    · cases rest; exact same
  have activate (s t : BeaconState preset fork) (i : ValidatorIndex)
      (ok : activateValidator s i = .ok t) : t.balances = s.balances := by
    simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, set⟩ := ok
    obtain ⟨_, rfl⟩ := setValidator_ok set
    rfl
  unfold processRegistryUpdates at ok
  split at ok
  · obtain ⟨epoch, _, folded⟩ := bind_ok_iff.mp ok
    exact coverage_fold_keeps (fun s i t => electra epoch s t i) folded
  · obtain ⟨u, first, last⟩ := bind_ok_iff.mp ok
    exact (coverage_fold_keeps (fun s i t => activate s t i) last).trans
      (coverage_fold_keeps (fun s i t => ordinary s t i) first)

private theorem coverage_justification {fork : Fork} {s t : BeaconState preset fork}
    (ok : processJustificationAndFinalization s = .ok t) : t.balances = s.balances := by
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok ok
  · exact congrArg BeaconState.balances same
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    rw [← rest]

private theorem coverage_inactivity {fork : Fork} {s t : BeaconState preset fork}
    {altair : .altair ≤ fork} (ok : processInactivityUpdates config s altair = .ok t) :
    t.balances = s.balances := by
  unfold processInactivityUpdates at ok
  split at ok
  · cases ok; rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    rfl

set_option maxHeartbeats 800000 in
private theorem coverage_epoch {fork : Fork} {s : BeaconState preset fork}
    {post : BalanceReplay preset fork}
    (early : fork < .glamsterdam)
    (ok : epochBalanceReplay (config := config) (checks := checks) s = .ok post) :
    ReplayCoverage s post := by
  have before : fork < .hegota := Nat.lt_trans early (by decide)
  unfold epochBalanceReplay at ok
  obtain ⟨justified, justifiedOk, ok⟩ := bind_ok_iff.mp ok
  have justifiedCover := coverage_carry (fun _ _ => coverage_justification)
    (coverage_refl ⟨fork, s⟩) justifiedOk
  by_cases altair : .altair ≤ fork
  case' pos =>
    simp only [altair, ↓reduceDIte] at ok
    obtain ⟨inactive, inactiveOk, ok⟩ := bind_ok_iff.mp ok
    have inactiveCover := coverage_carry (fun _ _ => coverage_inactivity) justifiedCover inactiveOk
    obtain ⟨rewarded, rewardOk, rest⟩ := bind_ok_iff.mp ok
    have rewardedCover := coverage_rewards inactiveCover rewardOk
  case' neg =>
    simp only [altair, ↓reduceDIte, pure, Except.pure, bind_ok_iff,
      Except.ok.injEq, exists_eq_left'] at ok
    obtain ⟨rewarded, rewardOk, rest⟩ := ok
    have rewardedCover := coverage_rewards justifiedCover rewardOk
  all_goals
    simp only [before, ↓reduceDIte, bind_ok_iff] at rest
    obtain ⟨registered, registeredOk, slashed, slashedOk, reset, resetOk, last⟩ := rest
    have registeredCover := coverage_carry (fun _ _ => coverage_registry) rewardedCover registeredOk
    have slashedCover := coverage_record registeredCover slashedOk
    have resetCover := coverage_carry (fun a b action => by
      simp only [processEth1DataReset, bind_ok_iff] at action
      obtain ⟨_, _, action⟩ := action
      split at action <;> cases action <;> rfl) slashedCover resetOk
    split at last
    · rename_i electra
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at last
      obtain ⟨deposited, _, consolidated, _, rfl⟩ := last
      have depositedCover := coverage_trans resetCover (coverage_event
        ⟨.deposits, ⟨fork, reset.1⟩, ⟨fork, deposited⟩,
          consumedDeposits reset.1 deposited electra, 0⟩)
      exact coverage_trans depositedCover (coverage_event
        ⟨.consolidations, ⟨fork, deposited⟩, ⟨fork, consolidated⟩,
          consumedConsolidations deposited consolidated electra,
          consumedConsolidations deposited consolidated electra⟩)
    · cases last; exact resetCover

private theorem coverage_voluntary {fork : Fork} {s t : BeaconState preset fork}
    {signed : SignedVoluntaryExit} (ok : processVoluntaryExit config checks s signed = .ok t) :
    t.balances = s.balances := by
  simp only [processVoluntaryExit, bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
  exact coverage_exit (liftAccessor_ok.mp exited)

private theorem coverage_bls {fork : Fork} {s t : BeaconState preset fork}
    {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) :
    t.balances = s.balances := by
  simp only [processBlsToExecutionChange, bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, set⟩ := ok
  obtain ⟨_, rfl⟩ := setValidator_ok (liftAccessor_ok.mp set)
  rfl

private theorem coverage_withdrawal_request {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) :
    t.balances = s.balances := by
  have partialRequest (s t : BeaconState preset fork) (index : ValidatorIndex) (v : Validator)
      (amount owed : Gwei)
      (ok : requestPartialWithdrawal config s electra index v amount owed = .ok t) :
      t.balances = s.balances := by
    simp only [requestPartialWithdrawal, bind_ok_iff] at ok
    obtain ⟨_, _, _, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨⟨u, epoch⟩, churned, _, _, _, _, rfl⟩ := ok
      exact (computeExitEpochAndUpdateChurn_earliest (liftAccessor_ok.mp churned)).2.2
    · cases ok; rfl
  simp only [processWithdrawalRequest] at ok
  repeat' first
    | (exact partialRequest _ _ _ _ _ _ ok)
    | (exact coverage_exit (liftAccessor_ok.mp ok))
    | (cases ok; rfl)
    | (split at ok)
    | (rcases bind_ok_iff.mp ok with ⟨_, _, ok⟩)

set_option maxHeartbeats 800000 in
private theorem coverage_block {fork : Fork} {s : BeaconState preset fork}
    (early : fork < .glamsterdam) (engine : ExecutionEngine preset fork)
    (block : BeaconBlock preset fork) {post : BalanceReplay preset fork}
    (ok : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok post) : ReplayCoverage s post := by
  unfold blockBalanceReplay at ok
  obtain ⟨headed, headerOk, ok⟩ := bind_ok_iff.mp ok
  have headedCover := coverage_carry (fun a b action => by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq action
    rfl) (coverage_refl ⟨fork, s⟩) headerOk
  by_cases bellatrix : .bellatrix ≤ fork
  case' pos =>
    simp only [bellatrix, ↓reduceDIte] at ok
    obtain ⟨executed, executionOk, rest⟩ := bind_ok_iff.mp ok
    have executedCover := coverage_record headedCover executionOk
  case' neg =>
    simp only [bellatrix, ↓reduceDIte, pure, Except.pure, bind_ok_iff,
      Except.ok.injEq, exists_eq_left'] at ok
    have rest := ok
    have executedCover := headedCover
  all_goals
    try simp only [bind_ok_iff] at rest
    obtain ⟨randao, randaoOk, voted, votedOk, expected, _, _, _,
      proposed, proposedOk, attested, attestedOk, rewarded, rewardedOk, deposited, depositOk,
      exited, exitOk, changed, changedOk, rest⟩ := rest
    have randaoCover := coverage_carry (fun a b action => by
      simp only [processRandao, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at action
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := action
      rfl) executedCover randaoOk
    have votedCover := coverage_carry (fun a b action => by
      simp only [processEth1Data] at action
      split at action
      · obtain ⟨_, _, action⟩ := bind_ok_iff.mp action
        split at action <;> cases action <;> rfl
      · cases action) randaoCover votedOk
    have proposedCover := foldlM_ok_invariant (ReplayCoverage s)
      (fun _ _ _ h ok => coverage_record h ok) votedCover proposedOk
    have attestedCover := foldlM_ok_invariant (ReplayCoverage s)
      (fun _ _ _ h ok => coverage_record h ok) proposedCover attestedOk
    have rewardedCover := foldlM_ok_invariant (ReplayCoverage s)
      (fun _ _ _ h ok => coverage_record h ok) attestedCover rewardedOk
    have depositedCover := foldlM_ok_invariant (ReplayCoverage s)
      (fun _ _ _ h ok => coverage_record h ok) rewardedCover depositOk
    have exitedCover := coverage_carry (fun _ _ ok =>
      coverage_fold_keeps (fun _ _ _ => coverage_voluntary)
        (by simpa only [← Array.foldlM_toList] using ok)) depositedCover exitOk
    have changedCover := coverage_carry (fun _ _ ok => by
      unfold processBlsToExecutionChanges at ok
      split at ok
      · exact coverage_fold_keeps (fun _ _ _ => coverage_bls)
          (by simpa only [← Array.foldlM_toList] using ok)
      · cases ok; rfl) exitedCover changedOk
    by_cases electra : .pectra ≤ fork
    case' pos =>
      simp only [electra, ↓reduceDIte, bind_ok_iff] at rest
      obtain ⟨deposits, depositRequestOk, withdrawals, withdrawalOk,
        requested, consolidations, rest⟩ := rest
      have depositsCover := coverage_carry (fun _ _ ok =>
        coverage_fold_keeps (action := fun a req => processDepositRequest a electra req)
          (fun a req b action => by
          simp only [processDepositRequest, liftAccessor_ok, addPendingDeposit,
            bind_ok_iff, pure, Except.pure, Except.ok.injEq] at action
          obtain ⟨_, _, rfl⟩ := action
          simp only [recordDepositRequestsStart]
          split <;> first | rfl | (split <;> rfl))
          (by simpa only [← Array.foldlM_toList] using ok)) changedCover depositRequestOk
      have withdrawalsCover := coverage_carry (fun _ _ ok =>
        coverage_fold_keeps (fun _ _ _ => coverage_withdrawal_request)
          (by simpa only [← Array.foldlM_toList] using ok)) depositsCover withdrawalOk
      have requestedCover := foldlM_ok_invariant (ReplayCoverage s)
        (fun _ _ _ h ok => coverage_record h ok) withdrawalsCover consolidations
    case' neg =>
      simp only [electra, ↓reduceDIte, pure, Except.pure, bind_ok_iff,
        Except.ok.injEq, exists_eq_left'] at rest
      have requestedCover := changedCover
    all_goals
      split at rest
      · exact coverage_record requestedCover rest
      · cases rest; exact requestedCover

private theorem coverage_upgrade_kept {s : ForkedBeaconState preset}
    {next : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (ok : upgradeNext config checks s = .ok next) (early : next.val.fork < .glamsterdam)
    (notElectra : s.fork ≠ .dencun) : Coverage s next.val [] := by
  have same (s t : ForkedBeaconState preset) (h : t.state.balances.data = s.state.balances.data) :
      Coverage s t [] := by
    intro debit i
    cases debit <;> simp [coverageDelta, actualBalanceAt, h]
  obtain ⟨fork, state⟩ := s
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact same _ _ (upgradeToAltair_spec upgraded).2.1
  · subst ok; exact same _ _ rfl
  · subst ok; exact same _ _ rfl
  · subst ok; exact same _ _ rfl
  · exact False.elim (notElectra rfl)
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact same _ _ (upgradeToFulu_spec upgraded).2.1
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.lt_irrefl _ early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim ((by decide : ¬Fork.hegota < Fork.glamsterdam) early)

private theorem coverage_upgrades {s t : ForkedBeaconState preset}
    (ok : processUpgrades config checks s = .ok t) (early : t.fork < .glamsterdam)
    {events : List (BalanceEvent preset)}
    (replayed : upgradeBalanceReplay (config := config) (checks := checks) s = .ok events) :
    Coverage s t events := by
  fun_induction processUpgrades config checks s generalizing t events with
  | case1 s due ih =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
    rw [upgradeBalanceReplay] at replayed
    simp only [due, ↓reduceIte, nextOk] at replayed
    dsimp only [bind, Except.bind] at replayed
    change (do
      let tail ← upgradeBalanceReplay (config := config) (checks := checks) next.val
      if s.fork = Fork.dencun then
        if electra : Fork.pectra ≤ next.val.fork then
          pure ((⟨.crossing, s, next.val, 0,
            ((next.val.state.pendingDeposits electra).data.toList.map
              fun (d : PendingDeposit) => d.amount.toNat).sum⟩ : BalanceEvent preset) :: tail)
        else pure tail
      else pure tail) = .ok events at replayed
    simp only [bind_ok_iff] at replayed
    obtain ⟨tail, tailOk, last⟩ := replayed
    have covered := ih next rest early tailOk
    by_cases crossing : s.fork = .dencun
    · obtain ⟨fork, state⟩ := s
      dsimp only at crossing
      subst fork
      simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at nextOk
      obtain ⟨after, upgraded, rfl⟩ := nextOk
      simp only [↓reduceIte, show Fork.pectra ≤ .pectra from Nat.le_refl _, ↓reduceDIte,
        pure, Except.pure, Except.ok.injEq] at last
      subst events
      exact coverage_trans (coverage_event
        ⟨.crossing, ⟨.dencun, state⟩, ⟨.pectra, after⟩, 0,
          ((after.pendingDeposits (by decide)).data.toList.map
            fun d => d.amount.toNat).sum⟩) covered
    · simp only [crossing, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at last
      subst events
      simpa only [List.nil_append] using coverage_trans
        (coverage_upgrade_kept nextOk
          (Nat.lt_of_le_of_lt (processUpgrades_fork_le rest) early) crossing) covered
  | case2 s due =>
    cases ok
    rw [upgradeBalanceReplay] at replayed
    simp [due, pure, Except.pure] at replayed
    subst events
    exact coverage_refl _

private def coveragePath (debit : Bool) (i : Nat) (path : List (ForkedBeaconState preset)) : Nat :=
  if debit then pathDebits i path else pathCredits i path

private theorem coverage_step {x y : ForkedBeaconState preset} (step : Step config checks x y)
    (early : y.fork < .glamsterdam) {events : List (BalanceEvent preset)}
    (replayed : step.balanceEvents = .ok events) :
    ∀ debit i, coveragePath debit i step.balancePath ≤
      (events.map fun e => coverageDelta debit e.before e.after i).sum := by
  have before : x.fork < .glamsterdam := Nat.lt_of_le_of_lt step.chainStep.fork_le early
  cases step with
  | block engine signed due ok =>
    obtain ⟨recorded, replay⟩ := blockBalanceReplay_result _ _ before engine signed.message
      (applySignedBlock_ok ok).2.1
    have cover := coverage_block before engine signed.message replay
    simp only [Step.balanceEvents, before, ↓reduceDIte, replay, bind, Except.bind,
      pure, Except.pure, Except.ok.injEq] at replayed
    subst events
    intro debit i
    simpa [coveragePath, coverageDelta, Step.balancePath, pathCredits, pathDebits]
      using cover debit i
  | slot ok =>
    obtain ⟨advanced, advanceOk, upgrades⟩ := bind_ok_iff.mp ok
    have advanceCopy := advanceOk
    simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at advanceCopy
    obtain ⟨next, nextOk, cached, cachedOk, epoched, epochOk, afterEq⟩ := advanceCopy
    obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
    have cachedCover : Coverage x ⟨x.fork, cached⟩ [] :=
      coverage_same (by rw [cachedEq])
    obtain ⟨crossings, crossingOk, _⟩ := upgradeBalanceReplay_bounded upgrades
    have crossingCover := coverage_upgrades upgrades early crossingOk
    have finish (epochEvents : List (BalanceEvent preset))
        (eventEq : events = epochEvents ++ crossings)
        (epochCover : Coverage x ⟨x.fork, advanced⟩ epochEvents) :
        ∀ debit i, coveragePath debit i (Step.slot ok).balancePath ≤
          (events.map fun e => coverageDelta debit e.before e.after i).sum := by
      intro debit i
      have first := epochCover debit i
      have second := crossingCover debit i
      rw [eventEq, List.map_append, List.sum_append]
      cases debit <;>
        simpa [coveragePath, Step.balancePath, advanceOk, Except.toOption,
          pathCredits, pathDebits, coverageDelta] using Nat.add_le_add first second
    by_cases last : next % preset.SLOTS_PER_EPOCH = 0
    · simp only [epochIfLast, last, ↓reduceIte] at epochOk
      obtain ⟨middle, updated, recorded, recordOk, _, _, balances⟩ :=
        epochBalanceReplay_result cached epoched before epochOk
      have total := coverage_trans cachedCover (coverage_epoch before recordOk)
      have final : Coverage ⟨x.fork, middle⟩ ⟨x.fork, advanced⟩ [] :=
        coverage_same (by rw [← afterEq]; exact balances.symm)
      have eventEq := Except.ok.inj (replayed.symm.trans
        (Step.balanceEvents_epoch_slot ok cachedOk nextOk last recordOk advanceOk crossingOk))
      apply finish recorded eventEq
      simpa only [List.nil_append, List.append_nil] using coverage_trans total final
    · simp only [epochIfLast, last, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochOk
      have eventEq : events = [] ++ crossings := by
        simpa [Step.balanceEvents, cachedOk, nextOk, last, advanceOk, crossingOk,
          pure, Except.pure, bind, Except.bind] using replayed.symm
      apply finish [] eventEq
      apply coverage_same
      rw [← afterEq, ← epochOk, cachedEq]

private theorem coverage_path_append (debit : Bool) (i : Nat)
    (a b : List (ForkedBeaconState preset)) (x : ForkedBeaconState preset) :
    coveragePath debit i (a ++ x :: b) =
      coveragePath debit i (a ++ [x]) + coveragePath debit i (x :: b) := by
  cases debit <;> simp only [coveragePath, ↓reduceIte]
  all_goals
    induction a with
    | nil => simp [pathCredits, pathDebits]
    | cons first rest ih =>
      cases rest with
      | nil => simp [pathCredits, pathDebits]
      | cons second rest => simpa [pathCredits, pathDebits, Nat.add_assoc] using ih

private theorem coverage_path_last {x y : ForkedBeaconState preset}
    (run : Run config checks x y) : ∃ pre, run.balancePath = pre ++ [y] := by
  cases run with
  | nil => exact ⟨[], rfl⟩
  | @snoc middle last pre step =>
    cases step with
    | @block fork before after engine signed due ok =>
      exact ⟨pre.balancePath ++ [⟨fork, before⟩], by
        simp [Run.balancePath, Step.balancePath, List.append_assoc]⟩
    | slot ok =>
      obtain ⟨advanced, advanceOk, _⟩ := bind_ok_iff.mp ok
      exact ⟨pre.balancePath ++ [middle, ⟨middle.fork, advanced⟩], by
        simp [Run.balancePath, Step.balancePath, advanceOk, Except.toOption, List.append_assoc]⟩

private theorem coverage_step_epoch {x y : ForkedBeaconState preset}
    (step : Step config checks x y) :
    (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch y.state).toNat := by
  have slots : x.state.slot.toNat ≤ y.state.slot.toNat := by
    cases step with
    | slot ok =>
      obtain ⟨advanced, advanceOk, upgradeOk⟩ := bind_ok_iff.mp ok
      rw [processUpgrades_slot upgradeOk]
      obtain ⟨_, _, _, next, _, _, rfl⟩ := advanceSlot_ok advanceOk
      dsimp only
      omega
    | block engine signed due ok =>
      rw [(frame_processBlock (applySignedBlock_ok ok).2.1).slot]
  rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
  exact Nat.div_le_div_right slots

private theorem coverage_run {x y : ForkedBeaconState preset} (run : Run config checks x y)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : run.balanceEvents high = .ok events) :
    ∀ debit i, coveragePath debit i run.balancePath ≤
      (events.map fun e => coverageDelta debit e.before e.after i).sum := by
  induction run generalizing events with
  | nil =>
    cases replayed
    intro debit i
    cases debit <;> simp [coveragePath, Run.balancePath, pathCredits, pathDebits]
  | @snoc middle last pre step ih =>
    have selected := (coverage_step_epoch step).trans endEpoch
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
    obtain ⟨added, addedOk, rfl⟩ := rest
    have priorCover := ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early) selected priorOk
    have addedCover := coverage_step step early addedOk
    obtain ⟨initialPath, prefixEq⟩ := coverage_path_last pre
    have stepStarts : ∃ rest, step.balancePath = middle :: rest := by
      cases step with
      | block => exact ⟨_, rfl⟩
      | slot ok =>
        obtain ⟨advanced, advanceOk, _⟩ := bind_ok_iff.mp ok
        exact ⟨[⟨middle.fork, advanced⟩, last], by
          simp [Step.balancePath, advanceOk, Except.toOption]⟩
    obtain ⟨suffix, suffixEq⟩ := stepStarts
    intro debit i
    have splitPath : coveragePath debit i (pre.snoc step).balancePath =
        coveragePath debit i pre.balancePath + coveragePath debit i step.balancePath := by
      rw [Run.balancePath, suffixEq, coverage_path_append]
      congr 1
      rw [prefixEq]
      rw [List.append_assoc]
      change coveragePath debit i (initialPath ++ middle :: [middle]) = _
      rw [coverage_path_append]
      cases debit <;> simp [coveragePath, pathCredits, pathDebits]
    rw [splitPath, List.map_append, List.sum_append]
    exact Nat.add_le_add (priorCover debit i) (addedCover debit i)

private theorem coverage_event_sum (event : BalanceEvent preset) (n : Nat) (debit : Bool) :
    (∑ i ∈ Finset.range n, coverageDelta debit event.before event.after i) ≤
      if debit then event.debits else event.credits := by
  have bound (a b : ForkedBeaconState preset) :
      (∑ i ∈ Finset.range n, (actualBalanceAt a i - actualBalanceAt b i)) ≤
        ∑ i ∈ Finset.range a.state.balances.data.size,
          (actualBalanceAt a i - actualBalanceAt b i) := by
    by_cases small : n ≤ a.state.balances.data.size
    · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono small) (by intros; omega)
    · have le : a.state.balances.data.size ≤ n := by omega
      apply le_of_eq
      symm
      apply Finset.sum_subset (Finset.range_mono le)
      intro i _ outside
      have ge : a.state.balances.data.size ≤ i := by simpa using outside
      simp [actualBalanceAt, Array.getElem?_eq_none (by omega)]
  cases debit <;> exact bound _ _

private theorem coverage_sum_events (events : List (BalanceEvent preset)) (n : Nat) (debit : Bool) :
    (∑ i ∈ Finset.range n,
      (events.map fun e => coverageDelta debit e.before e.after i).sum) ≤
      (events.map fun e => if debit then e.debits else e.credits).sum := by
  induction events with
  | nil => simp
  | cons event rest ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
    exact Nat.add_le_add (coverage_event_sum event n debit) ih

/-- The replay covers all positive balance changes of the selected steps, not just net issuance. -/
theorem balance_path_covered {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    (∑ i ∈ Finset.range y.state.validators.data.size, pathCredits i tail.balancePath) ≤
      (events.map (·.creditLimit)).sum ∧
    (∑ i ∈ Finset.range y.state.validators.data.size, pathDebits i tail.balancePath) ≤
      (events.map (·.debitLimit)).sum := by
  have invariant {z : ForkedBeaconState preset} (run : Run config checks g z) :
      Invariant z.state := by
    induction run with
    | nil =>
      obtain ⟨_, _, _, ok⟩ := genesis
      exact (initializeBeaconStateFromEth1_invariant ok).2
    | snoc pre step ih =>
      cases step with
      | slot ok => exact (advanceSlotAcross_invariant ih ok).1
      | block engine signed due ok =>
        exact (frame_processBlock (applySignedBlock_ok ok).2.1).invariant ih
  have bounded : EventsBounded events := by
    induction tail generalizing events with
    | nil => cases replayed; simp [EventsBounded]
    | @snoc middle last pre step ih =>
      have selected := (coverage_step_epoch step).trans endEpoch
      simp only [Run.balanceEvents, bind_ok_iff] at replayed
      obtain ⟨prior, priorOk, rest⟩ := replayed
      simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
      obtain ⟨added, addedOk, rfl⟩ := rest
      have previous := ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early) selected prior priorOk
      obtain ⟨actual, actualOk, bound⟩ := stepBalanceEvents_bounded step
        (invariant (shared.append pre)).balancesMatch early
      cases Except.ok.inj (actualOk.symm.trans addedOk)
      exact eventsBounded_append previous bound
  have result (debit : Bool) :
      (∑ i ∈ Finset.range y.state.validators.data.size, coveragePath debit i tail.balancePath) ≤
        (events.map fun e => if debit then e.debitLimit else e.creditLimit).sum := by
    apply (Finset.sum_le_sum fun i _ =>
      coverage_run tail early high endEpoch replayed debit i).trans
    apply (coverage_sum_events events _ debit).trans
    apply List.sum_le_sum
    intro event member
    cases debit
    · exact (bounded event member).1
    · exact (bounded event member).2
  exact ⟨result false, result true⟩

def initialExcess (x : ForkedBeaconState preset) : Nat :=
  ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
    actualBalanceAt x i.toNat - effectiveAt x i.toNat).sum

/-- Count future activations and previous-epoch voters, not validators that exited long ago. -/
def activationCarry (x : ForkedBeaconState preset) : Nat :=
  (x.state.validators.data.toList.zipIdx.map fun (v, i) =>
    if isActiveValidator v (getCurrentEpoch x.state) then 0
    else if isActiveValidator v (getPreviousEpoch x.state) ||
        getCurrentEpoch x.state < v.activationEpoch then max (effectiveAt x i) (actualBalanceAt x i)
    else 0).sum

def scheduledExitCarry (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  (x.state.validators.data.toList.filter fun v =>
    isActiveValidator v (getCurrentEpoch x.state) && v.exitEpoch != FAR_FUTURE_EPOCH &&
      v.exitEpoch.toNat ≤ high + 1).foldl
      (fun total v => total + v.effectiveBalance.toNat) 0

def queueCarry (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  if electra : .pectra ≤ x.fork then
    (if (x.state.earliestExitEpoch electra).toNat ≤ high + 1 then
      (x.state.exitBalanceToConsume electra).toNat else 0) +
    (if (x.state.earliestConsolidationEpoch electra).toNat ≤ high + 1 then
      (x.state.consolidationBalanceToConsume electra).toNat else 0)
  else 0

/-- Pre-Gloas consolidation churn is the whole balance churn less the activation/exit cap. -/
def consolidationRate (stake : Nat) : Nat :=
  max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
    (max preset.EFFECTIVE_BALANCE_INCREMENT.toNat stake / config.CHURN_LIMIT_QUOTIENT.toNat) -
      config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat

/-- Includes both epoch tests that can justify a target at high. -/
def driftHorizon (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  high + 2 - (getCurrentEpoch x.state).toNat

/-- New registry entries come from block deposits or the bounded pending-deposit pass. -/
def registryWindow (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  x.state.validators.data.size + driftHorizon x high *
    (preset.SLOTS_PER_EPOCH.toNat * preset.MAX_DEPOSITS.toNat +
      preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat)

/-- Electra deposit churn includes active top-ups, but not credits to already withdrawn keys. -/
def depositWindow (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  (if electra : .pectra ≤ x.fork then (x.state.depositBalanceToConsume electra).toNat else 0) +
    driftHorizon x high * config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat

/-- Funding that can still support active stake, including queued consolidation sources.

The maximum retains effective stake above actual balance without counting all registry entries. -/
def fundedStake (x : ForkedBeaconState preset) : Nat :=
  (x.state.validators.data.toList.zipIdx.map fun (v, i) =>
    let pending := if electra : .pectra ≤ x.fork then
      (x.state.pendingConsolidations electra).data.any (fun c => c.sourceIndex.toNat == i)
      else false
    if isActiveValidator v (getCurrentEpoch x.state) ||
        getCurrentEpoch x.state < v.activationEpoch || pending then
      max (effectiveAt x i) (actualBalanceAt x i)
    else 0).sum

/-- Retain withdrawn-source credits until queue chronology excludes them on reachable runs.

Those exception credits do not consume deposit churn and must remain explicit. -/
def withdrawnConsolidationCredit (event : BalanceEvent preset) : Nat :=
  if electra : .pectra ≤ event.before.fork then
    (event.before.state.validators.data.toList.zipIdx.map fun (v, i) =>
      if v.withdrawableEpoch.toNat ≤ (getCurrentEpoch event.before.state).toNat &&
          (event.before.state.pendingConsolidations electra).data.any
            (fun c => c.sourceIndex.toNat == i) then
        actualBalanceAt event.after i - actualBalanceAt event.before i
      else 0).sum
  else 0

/-- Consolidations move existing funding; deposits have churn and a withdrawn-source exception. -/
def fundingCredit (event : BalanceEvent preset) : Nat :=
  match event.source with
  | .consolidations => 0
  | .deposits => withdrawnConsolidationCredit event
  | _ => event.creditLimit

/-- Electra active stake is funded initially, by deposit churn, or by non-transfer credits.

Before Electra this retains the registry envelope until a count-churn funding proof is supplied. -/
def activeStakeWindow (x : ForkedBeaconState preset) (high : Nat)
    (events : List (BalanceEvent preset)) : Nat :=
  if .pectra ≤ x.fork ∧ 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat then
    fundedStake x + depositWindow (config := config) x high + (events.map fundingCredit).sum
  else registryWindow x high * preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat

/-- The post-Electra funding envelope bounds active stake without a registry-wide effective cap.

The bound retains withdrawn-source credits rather than assuming pending-source chronology. -/
theorem active_stake_le_window {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (withdrawalDelay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    Quorum.weight (effectiveWeight y.state) (activeKeys y.state) ≤
      activeStakeWindow (config := config) x high events := by
  sorry

def exitWindow (x : ForkedBeaconState preset) (high : Nat)
    (events : List (BalanceEvent preset)) : Nat :=
  scheduledExitCarry x high + queueCarry x high +
    driftHorizon x high *
      ((if x.fork < .pectra then max 1 (cohortCap config (registryWindow x high)) *
        preset.MAX_EFFECTIVE_BALANCE.toNat else 0) +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        consolidationRate (preset := preset) (config := config)
          (activeStakeWindow (config := config) x high events))

/-- Before Electra activations spend count churn; afterwards funding spends deposit churn.

Already funded inactive validators remain a carry-in because Electra activation has no count cap. -/
def activationWindow (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  activationCarry x + depositWindow (config := config) x high +
    (if x.fork < .pectra then driftHorizon x high * cohortCap config (registryWindow x high) *
      preset.MAX_EFFECTIVE_BALANCE.toNat else 0)

/-- Electra deposits use depositWindow; pre-Electra active top-ups remain here.

Across Electra, pre-upgrade funding can bypass later deposit churn, so retain all such credits. -/
def residualCredit (x : ForkedBeaconState preset) (high : Nat)
    (event : BalanceEvent preset) : Nat :=
  match event.source with
  | .deposits => if .pectra ≤ event.before.fork then 0 else
      if high + 1 < config.ELECTRA_FORK_EPOCH.toNat then
        ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
          actualBalanceAt event.after i.toNat - actualBalanceAt event.before i.toNat).sum
      else event.creditLimit
  | _ => event.creditLimit

/-- Per-reference-key non-slashing debits count while the key remains in the recent support. -/
def referenceDebit (i : Nat) (event : BalanceEvent preset) : Nat :=
  if event.source == .slashings then 0 else
    match event.before.state.validators.data[i]? with
    | none => 0
    | some v => if isActiveValidator v (getCurrentEpoch event.before.state) ||
        isActiveValidator v (getPreviousEpoch event.before.state) then
        actualBalanceAt event.before i - actualBalanceAt event.after i
      else 0

/-- Rounding is charged only to a key with initial slack or an actual non-slashing debit.

An aligned effective balance cannot fall below its starting value without such a deficit. -/
def lossCorrection (x : ForkedBeaconState preset) (events : List (BalanceEvent preset)) : Nat :=
  ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
    match x.state.validators.data[i.toNat]? with
    | none => 0
    | some v => if v.slashed then 0 else
      let deficit := effectiveAt x i.toNat - actualBalanceAt x i.toNat +
        (events.map (referenceDebit i.toNat)).sum
      if deficit = 0 then 0 else deficit + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1).sum

/-- No rounding allowance is needed when each unslashed reference key has no deficit. -/
theorem lossCorrection_eq_zero (x : ForkedBeaconState preset)
    (events : List (BalanceEvent preset))
    (funded : ∀ i ∈ getActiveValidatorIndices x.state (getCurrentEpoch x.state),
      ∀ v, x.state.validators.data[i.toNat]? = some v → v.slashed = false →
        effectiveAt x i.toNat ≤ actualBalanceAt x i.toNat)
    (noDebits : ∀ i ∈ getActiveValidatorIndices x.state (getCurrentEpoch x.state),
      (events.map (referenceDebit i.toNat)).sum = 0) : lossCorrection x events = 0 := by
  unfold lossCorrection
  apply List.sum_eq_zero
  intro value member
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp member
  cases found : x.state.validators.data[i.toNat]? with
  | none => simp
  | some v =>
    cases slashed : v.slashed with
    | true => simp [slashed]
    | false =>
      have balance := funded i hi v found slashed
      simp [slashed, Nat.sub_eq_zero_of_le balance, noDebits i hi]

private theorem registry_fold_bound {fork : Fork} {α : Type}
    {action : BeaconState preset fork → α → Except TransitionError (BeaconState preset fork)}
    (bound : ∀ s a t, action s a = .ok t →
      t.validators.data.size ≤ s.validators.data.size + 1)
    {items : List α} {s t : BeaconState preset fork}
    (ok : items.foldlM action s = .ok t) :
    t.validators.data.size ≤ s.validators.data.size + items.length := by
  induction items generalizing s with
  | nil => cases ok; simp
  | cons a rest ih =>
    simp only [List.foldlM_cons, bind_ok_iff] at ok
    obtain ⟨middle, first, last⟩ := ok
    have one := bound s a middle first
    have remaining := ih last
    simp only [List.length_cons]
    omega

private theorem registry_pending_bound {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork}
    (ok : processPendingDeposits config checks s electra = .ok t) :
    t.validators.data.size ≤ s.validators.data.size +
      preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  -- Applied deposits form a sublist of the bounded prefix read by this pass.
  obtain ⟨read, rest, applied, postponed, next, pending, carried,
    _, _, cap, subset, _, _, folded, rfl⟩ := processPendingDeposits_applied ok
  have growth := registry_fold_bound
    (fun _ _ _ h => (applyPendingDeposit_validators_size_le_and_mem h).1) folded
  have count := subset.length_le
  dsimp only
  omega

private theorem registry_deposit_bound {fork : Fork} {s t : BeaconState preset fork}
    {before : fork < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) :
    t.validators.data.size ≤ s.validators.data.size + 1 := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok ok
  unfold applyDeposit at applied
  split at applied
  · unfold applyDepositElectra at applied
    split at applied
    · simp only [bind_ok_iff] at applied
      obtain ⟨_, _, applied⟩ := applied
      split at applied
      · simp only [bind_ok_iff, liftAccessor_ok] at applied
        obtain ⟨_, added, pushed⟩ := applied
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
        rw [addValidatorToRegistry_validators_eq_push added]
        simp
      · cases applied; exact Nat.le_succ _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp applied)
      exact Nat.le_succ _
  · exact (applyPendingDeposit_validators_size_le_and_mem applied).1

private theorem registry_fold_size {fork : Fork} {α : Type}
    {action : BeaconState preset fork → α → Except TransitionError (BeaconState preset fork)}
    (keeps : ∀ s a t, action s a = .ok t → t.validators.data.size = s.validators.data.size)
    {items : List α} {s t : BeaconState preset fork}
    (ok : items.foldlM action s = .ok t) : t.validators.data.size = s.validators.data.size :=
  foldlM_ok_invariant (fun t => t.validators.data.size = s.validators.data.size)
    (fun _ _ _ prior ok => (keeps _ _ _ ok).trans prior) rfl ok

private theorem registry_operations_bound {fork : Fork} {s t : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {parentSlot : Slot} (early : fork < .glamsterdam)
    (ok : processOperations config checks s body parentSlot = .ok t) :
    t.validators.data.size ≤ s.validators.data.size + preset.MAX_DEPOSITS.toNat := by
  have notGloas : ¬ Fork.glamsterdam ≤ fork := fun h => Nat.not_le.mpr early h
  simp only [processOperations, notGloas, ↓reduceDIte,
    bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, _, _, _, a, proposers, b, attesters, c, attestations, d, deposits,
    e, exits, f, changes, requests⟩ := ok
  have sa := registry_fold_size (fun _ _ _ h => (sameSizes_processProposerSlashing h).1) proposers
  have sb := registry_fold_size (fun _ _ _ h => (sameSizes_processAttesterSlashing h).1) attesters
  have sc := registry_fold_size (fun _ _ _ h => (sameSizes_processAttestation h).1) attestations
  have sd := registry_fold_bound (fun _ _ _ h => registry_deposit_bound h) deposits
  have se := registry_fold_size (fun _ _ _ h => (sameSizes_processVoluntaryExit h).1) exits
  have sf : f.validators.data.size = e.validators.data.size := by
    unfold processBlsToExecutionChanges at changes
    split at changes
    · rw [← Array.foldlM_toList] at changes
      exact registry_fold_size (fun _ _ _ h => (sameSizes_processBlsToExecutionChange h).1) changes
    · cases changes; rfl
  have st : t.validators.data.size = f.validators.data.size := by
    split at requests
    · exact (sameSizes_processExecutionRequests requests).1
    · cases requests; rfl
  have cap := (body.deposits (Nat.lt_trans early (by decide))).bound early
  simp only [Array.length_toList] at sd
  omega

private theorem registry_execution_size {fork : Fork} {s t : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {engine : ExecutionEngine preset fork}
    {bellatrix : .bellatrix ≤ fork} (early : fork < .glamsterdam)
    (ok : processBlockExecution config checks engine s body bellatrix = .ok t) :
    t.validators.data.size = s.validators.data.size := by
  have notGloas : ¬ Fork.glamsterdam ≤ fork := fun h => Nat.not_le.mpr early h
  unfold processBlockExecution at ok
  simp only [notGloas, ↓reduceDIte] at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨withdrawn, wit, payload⟩ := ok
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok payload
    exact (sameSizes_processWithdrawals wit).1
  · split at ok
    · obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
      rfl
    · cases ok; rfl

private theorem registry_block_bound {fork : Fork} {s t : BeaconState preset fork}
    {block : BeaconBlock preset fork} {engine : ExecutionEngine preset fork}
    (early : fork < .glamsterdam)
    (ok : processBlock config checks engine s block = .ok t) :
    t.validators.data.size ≤ s.validators.data.size + preset.MAX_DEPOSITS.toNat := by
  have notGloas : ¬ Fork.glamsterdam ≤ fork := fun h => Nat.not_le.mpr early h
  unfold processBlock at ok
  split at ok
  · simp only [processBlockAltair, notGloas, ↓reduceDIte, pure_bind,
      bind_ok_iff] at ok
    obtain ⟨a, header, b, execution, c, randao, d, eth1, e, operations, sync⟩ := ok
    have ha := (sameSizes_processBlockHeader header).1
    have hb : b.validators.data.size = a.validators.data.size := by
      split at execution
      · exact registry_execution_size early execution
      · cases execution; rfl
    have hc := (sameSizes_processRandao randao).1
    have hd : d.validators.data.size = c.validators.data.size := by
      split at eth1
      · exact (sameSizes_processEth1Data eth1).1
      · cases eth1; rfl
    have he := registry_operations_bound early operations
    have ht : t.validators.data.size = e.validators.data.size := by
      unfold processSyncAggregate at sync
      simp only [bind_ok_iff] at sync
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := sync
      rw [← Array.foldlM_toList] at folded
      apply registry_fold_size (fun _ _ _ h => ?_) folded
      unfold applySyncReward at h
      split at h
      · simp only [bind_ok_iff, liftAccessor_ok] at h
        obtain ⟨_, raised, _, _, paid⟩ := h
        exact (sameSizes_increaseBalance paid).1.trans (sameSizes_increaseBalance raised).1
      · exact (sameSizes_decreaseBalance (liftAccessor_ok.mp h)).1
    omega
  · simp only [bind_ok_iff] at ok
    obtain ⟨a, header, b, randao, c, eth1, operations⟩ := ok
    have ha := (sameSizes_processBlockHeader header).1
    have hb := (sameSizes_processRandao randao).1
    have hc := (sameSizes_processEth1Data eth1).1
    have ht := registry_operations_bound early operations
    omega

private theorem registry_history_size {fork : Fork} {s t : BeaconState preset fork}
    (ok : processHistoricalRootsUpdate s = .ok t) :
    t.validators.data.size = s.validators.data.size := by
  unfold processHistoricalRootsUpdate at ok
  split at ok
  · cases ok
  simp only [bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    rfl
  · cases ok; rfl

private theorem registry_summary_size {fork : Fork} {s t : BeaconState preset fork}
    {capella : .shapella ≤ fork}
    (ok : processHistoricalSummariesUpdate s capella = .ok t) :
    t.validators.data.size = s.validators.data.size := by
  unfold processHistoricalSummariesUpdate at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals rfl

private theorem registry_reset_size {fork : Fork} {s t : BeaconState preset fork}
    {before : fork < .hegota} (ok : processEth1DataReset before s = .ok t) :
    t.validators.data.size = s.validators.data.size := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok <;> cases ok <;> rfl

private theorem registry_epoch_tail_size {fork : Fork} {altair : .altair ≤ fork}
    {rooted synced looked after : BeaconState preset fork}
    (sync : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair) altair =
      .ok synced)
    (look : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (window : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) :
    after.validators.data.size = rooted.validators.data.size := by
  have hs : synced.validators.data.size = rooted.validators.data.size := by
    unfold processSyncCommitteeUpdates at sync
    simp only [bind, Except.bind, pure, Except.pure] at sync
    repeat' (split at sync <;> try cases sync)
    all_goals rfl
  have hl : looked.validators.data.size = synced.validators.data.size := by
    split at look
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at look
      obtain ⟨_, _, _, _, rfl⟩ := look
      rfl
    · cases look; rfl
  have hw : after.validators.data.size = looked.validators.data.size := by
    split at window
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at window
      obtain ⟨_, _, _, _, rfl⟩ := window
      rfl
    · cases window; rfl
  exact hw.trans (hl.trans hs)

private theorem registry_epoch_bound {fork : Fork} {s t : BeaconState preset fork}
    (early : fork < .glamsterdam) (ok : processEpoch config checks s = .ok t) :
    t.validators.data.size ≤ s.validators.data.size +
      preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  have notGloas : ¬ Fork.glamsterdam ≤ fork := fun h => Nat.not_le.mpr early h
  unfold processEpoch at ok
  split at ok
  · simp only [processEpochAltair, notGloas, ↓reduceDIte, pure_bind, bind_ok_iff] at ok
    obtain ⟨a, justified, b, scored, c, rewarded, d, registered, e, slashed, f, reset,
      g, pending, h, balanced, i, cleared, j, mixed, rest⟩ := ok
    have ha := (sameSizes_processJustificationAndFinalization justified).1
    have hb : b.validators.data.size = a.validators.data.size := by
      unfold processInactivityUpdates at scored
      split at scored
      · cases scored; rfl
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at scored
        obtain ⟨_, _, _, _, rfl⟩ := scored
        rfl
    have hc := (processRewardsAndPenalties_sameSizes rewarded).1
    have hd := (sameSizes_processRegistryUpdates registered).1
    have he := (sameSizes_processSlashings slashed).1
    have hf : f.validators.data.size = e.validators.data.size := by
      split at reset
      · exact registry_reset_size reset
      · cases reset; rfl
    -- Only the pending-deposit pass can append validators during an epoch transition.
    have hg : g.validators.data.size ≤ f.validators.data.size +
        preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
      unfold processPendingBalances at pending
      split at pending
      · simp only [bind_ok_iff] at pending
        obtain ⟨deposited, dep, con⟩ := pending
        rw [(processPendingConsolidations_kept con).1]
        exact registry_pending_bound dep
      · cases pending; omega
    have hh := (sameSizes_processEffectiveBalanceUpdates balanced).1
    obtain ⟨_, _, _, _, hi⟩ := processSlashingsReset_eq cleared
    obtain ⟨_, _, _, _, _, _, hj⟩ := processRandaoMixesReset_eq mixed
    have ht : t.validators.data.size = j.validators.data.size := by
      split at rest <;> simp only [bind_ok_iff] at rest <;>
        obtain ⟨rooted, history, synced, sync, looked, look, window⟩ := rest
      · exact (registry_epoch_tail_size sync look (by simpa only [notGloas, ↓reduceDIte]
          using window)).trans (registry_summary_size history)
      · exact (registry_epoch_tail_size sync look (by simpa only [notGloas, ↓reduceDIte]
          using window)).trans (registry_history_size history)
    rw [hj, hi] at ht
    dsimp only at ht
    omega
  · simp only [bind_ok_iff] at ok
    obtain ⟨a, justified, b, rewarded, c, registered, d, slashed, e, reset, f, balanced,
      g, cleared, h, mixed, i, history, rotated⟩ := ok
    have ha := (sameSizes_processJustificationAndFinalization justified).1
    have hb := (processRewardsAndPenalties_sameSizes rewarded).1
    have hc := (sameSizes_processRegistryUpdates registered).1
    have hd := (sameSizes_processSlashings slashed).1
    have he := registry_reset_size reset
    have hf := (sameSizes_processEffectiveBalanceUpdates balanced).1
    obtain ⟨_, _, _, _, hg⟩ := processSlashingsReset_eq cleared
    obtain ⟨_, _, _, _, _, _, hh⟩ := processRandaoMixesReset_eq mixed
    have hi := registry_history_size history
    have ht : t.validators.data.size = i.validators.data.size := by
      unfold processParticipationRecordUpdates at rotated
      split at rotated
      · cases rotated
      · cases rotated; rfl
    rw [hh, hg] at hi
    dsimp only at hi
    omega

private theorem registry_upgrade_size {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (ok : upgradeNext config checks s = .ok t) :
    t.val.state.validators.data.size = s.state.validators.data.size := by
  obtain ⟨fork, state⟩ := s
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact congrArg Array.size (upgradeToAltair_spec upgraded).1
  · subst ok; rfl
  · subst ok; rfl
  · subst ok; rfl
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact (upgradeToElectra_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact congrArg Array.size (upgradeToFulu_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact congrArg Array.size (upgradeToGloas_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    rfl

private theorem registry_upgrades_size {s t : ForkedBeaconState preset}
    (ok : processUpgrades config checks s = .ok t) :
    t.state.validators.data.size = s.state.validators.data.size :=
  processUpgrades_induction
    (property := fun t => t.state.validators.data.size = s.state.validators.data.size)
    (fun prior ok => (registry_upgrade_size ok).trans prior) rfl ok

private theorem registry_slot_bound {s t : ForkedBeaconState preset}
    (early : t.fork < .glamsterdam)
    (ok : advanceSlotAcross config checks s = .ok t) :
    t.state.slot.toNat = s.state.slot.toNat + 1 ∧
      t.state.validators.data.size ≤ s.state.validators.data.size +
        ((getCurrentEpoch t.state).toNat - (getCurrentEpoch s.state).toNat) *
          preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  simp only [advanceSlotAcross, bind_ok_iff] at ok
  obtain ⟨advanced, slot, upgrades⟩ := ok
  have size := registry_upgrades_size upgrades
  have slotEq := processUpgrades_slot upgrades
  have forward := processUpgrades_fork_le upgrades
  have oldEarly : s.fork < .glamsterdam := Nat.lt_of_le_of_lt forward early
  obtain ⟨next, cached, epoched, nextOk, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok slot
  obtain ⟨_, _, _, _, cacheEq⟩ := processSlot_ok cachedOk
  have cacheSize : cached.validators.data.size = s.state.validators.data.size := by rw [cacheEq]
  have cacheSlot := processSlot_slot cachedOk
  have nextSlot : t.state.slot.toNat = s.state.slot.toNat + 1 := by
    rw [slotEq]
    exact nextOk
  refine ⟨nextSlot, ?_⟩
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    -- Charge the pending-deposit cap only when this slot crosses an epoch boundary.
    have epochs := nextSlot_epoch_of_boundary nextOk boundary
    have growth := registry_epoch_bound oldEarly epochedOk
    have diff : (getCurrentEpoch t.state).toNat - (getCurrentEpoch s.state).toNat = 1 := by
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, slotEq]
      dsimp only
      omega
    rw [diff, one_mul, size]
    dsimp only
    omega
  · cases epochedOk
    rw [size]
    dsimp only
    omega

private theorem registry_operations_header {fork : Fork} {s t : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {parentSlot : Slot} (early : fork < .glamsterdam)
    (ok : processOperations config checks s body parentSlot = .ok t) :
    t.latestBlockHeader = s.latestBlockHeader := by
  have foldHeader {α : Type} {f : BeaconState preset fork → α → Except TransitionError _}
      (keeps : ∀ s x t, f s x = .ok t → t.latestBlockHeader = s.latestBlockHeader)
      {s t : BeaconState preset fork} {xs : List α} (h : xs.foldlM f s = .ok t) :
      t.latestBlockHeader = s.latestBlockHeader :=
    foldlM_ok_invariant (fun t => t.latestBlockHeader = s.latestBlockHeader)
      (fun _ _ _ before ok => (keeps _ _ _ ok).trans before) rfl h
  have notGloas : ¬ Fork.glamsterdam ≤ fork := fun h => Nat.not_le.mpr early h
  simp only [processOperations, notGloas, ↓reduceDIte, bind_ok_iff, ensure_ok_iff,
    ← Array.foldlM_toList] at ok
  obtain ⟨_, _, _, _, _, proposers, _, attesters, _, attestations, _, deposits, exited,
    exits, changed, changes, requests⟩ := ok
  have changesKept : changed.latestBlockHeader = exited.latestBlockHeader := by
    unfold processBlsToExecutionChanges at changes
    split at changes
    · rw [← Array.foldlM_toList] at changes
      exact foldHeader (fun _ _ _ h =>
        (payloadInputs_processBlsToExecutionChange h).latestBlockHeader) changes
    · cases changes; rfl
  have requestsKept : t.latestBlockHeader = changed.latestBlockHeader := by
    split at requests
    · simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at requests
      obtain ⟨_, dep, _, wit, con⟩ := requests
      exact (foldHeader (fun _ _ _ h =>
        (payloadInputs_processConsolidationRequest h).latestBlockHeader) con).trans <|
        (foldHeader (fun _ _ _ h =>
          (payloadInputs_processWithdrawalRequest h).latestBlockHeader) wit).trans <|
        foldHeader (fun _ _ _ h => (payloadInputs_processDepositRequest h).latestBlockHeader) dep
    · cases requests; rfl
  exact requestsKept.trans <| changesKept.trans <|
    (foldHeader (fun _ _ _ h => (payloadInputs_processVoluntaryExit h).latestBlockHeader)
      exits).trans <|
    (foldHeader (fun _ _ _ h => by
      obtain ⟨_, _, _, _, applied⟩ := processDeposit_ok h
      exact (frame_applyDeposit applied).latestBlockHeader) deposits).trans <|
    (foldHeader (fun _ _ _ h => (payloadInputs_processAttestation h).latestBlockHeader)
      attestations).trans <|
    (foldHeader (fun _ _ _ h => (payloadInputs_processAttesterSlashing h).latestBlockHeader)
      attesters).trans <|
    foldHeader (fun _ _ _ h => (payloadInputs_processProposerSlashing h).latestBlockHeader)
      proposers

private theorem registry_execution_header {fork : Fork} {s t : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork} (early : fork < .glamsterdam)
    (ok : processBlockExecution config checks engine s body bellatrix = .ok t) :
    t.latestBlockHeader = s.latestBlockHeader := by
  have notGloas : ¬ Fork.glamsterdam ≤ fork := fun h => Nat.not_le.mpr early h
  unfold processBlockExecution at ok
  simp only [notGloas, ↓reduceDIte] at ok
  split at ok
  · obtain ⟨_, withdrawn, executed⟩ := bind_ok_iff.mp ok
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok executed
    exact (payloadInputs_processWithdrawals withdrawn).latestBlockHeader
  · split at ok
    · obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
      rfl
    · cases ok; rfl

private theorem registry_block_header {fork : Fork} {s t : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    (early : fork < .glamsterdam)
    (ok : processBlock config checks engine s block = .ok t) :
    t.latestBlockHeader.slot = s.slot ∧ s.latestBlockHeader.slot < s.slot := by
  obtain ⟨headed, headerOk⟩ := processBlock_header_of_lt_gloas early ok
  have checked := processBlockHeader_checks headerOk
  refine ⟨?_, checked.1 ▸ checked.2.1⟩
  suffices t.latestBlockHeader.slot = block.slot by exact this.trans checked.1
  have notGloas : ¬ Fork.glamsterdam ≤ fork := fun h => Nat.not_le.mpr early h
  unfold processBlock at ok
  split at ok
  · simp only [processBlockAltair, notGloas, ↓reduceDIte, pure_bind, bind_ok_iff] at ok
    obtain ⟨headed, headedOk, executed, executedOk, revealed, revealedOk, voted, votedOk,
      operated, operatedOk, synced⟩ := ok
    have executedKept : executed.latestBlockHeader = headed.latestBlockHeader := by
      split at executedOk
      · exact registry_execution_header early executedOk
      · cases executedOk; rfl
    have votedKept : voted.latestBlockHeader = revealed.latestBlockHeader := by
      split at votedOk
      · exact (payloadInputs_processEth1Data votedOk).latestBlockHeader
      · cases votedOk; rfl
    obtain ⟨_, _, eq⟩ := processBlockHeader_eq headedOk
    rw [(payloadInputs_processSyncAggregate synced).latestBlockHeader,
      registry_operations_header early operatedOk, votedKept,
      (payloadInputs_processRandao revealedOk).latestBlockHeader, executedKept, eq]
  · simp only [bind_ok_iff] at ok
    obtain ⟨headed, headedOk, revealed, revealedOk, voted, votedOk, operatedOk⟩ := ok
    obtain ⟨_, _, eq⟩ := processBlockHeader_eq headedOk
    rw [registry_operations_header early operatedOk,
      (payloadInputs_processEth1Data votedOk).latestBlockHeader,
      (payloadInputs_processRandao revealedOk).latestBlockHeader, eq]

-- An unused block slot retains its allowance until a successful header consumes it.
private def registry_block_allowance (s : ForkedBeaconState preset) : Nat :=
  if s.state.latestBlockHeader.slot < s.state.slot then preset.MAX_DEPOSITS.toNat else 0

private theorem registry_run_bound {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) :
    x.state.slot.toNat ≤ y.state.slot.toNat ∧
      y.state.validators.data.size + registry_block_allowance y ≤
        x.state.validators.data.size +
          (y.state.slot.toNat + 1 - x.state.slot.toNat) * preset.MAX_DEPOSITS.toNat +
          ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) *
            preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  induction tail with
  | nil =>
    constructor
    · exact Nat.le_refl _
    · simp only [Nat.add_sub_cancel_left, Nat.sub_self, Nat.zero_mul, Nat.add_zero, one_mul]
      unfold registry_block_allowance
      split <;> omega
  | @snoc middle last pre step ih =>
    have beforeEarly : middle.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt step.chainStep.fork_le early
    obtain ⟨slotsBefore, bound⟩ := ih beforeEarly
    have epochsBefore : (getCurrentEpoch x.state).toNat ≤
        (getCurrentEpoch middle.state).toNat := by
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
      exact Nat.div_le_div_right slotsBefore
    cases step with
    | slot ok =>
      obtain ⟨slot, growth⟩ := registry_slot_bound early ok
      have epochsAfter : (getCurrentEpoch middle.state).toNat ≤
          (getCurrentEpoch last.state).toNat := by
        rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
        exact Nat.div_le_div_right (by omega)
      have epochAdd : (getCurrentEpoch last.state).toNat - (getCurrentEpoch x.state).toNat =
          ((getCurrentEpoch middle.state).toNat - (getCurrentEpoch x.state).toNat) +
          ((getCurrentEpoch last.state).toNat - (getCurrentEpoch middle.state).toNat) := by omega
      have slotAdd : last.state.slot.toNat + 1 - x.state.slot.toNat =
          (middle.state.slot.toNat + 1 - x.state.slot.toNat) + 1 := by omega
      -- Advancing a slot supplies at most one fresh block allowance, even across upgrades.
      have allowance : registry_block_allowance last ≤ preset.MAX_DEPOSITS.toNat := by
        unfold registry_block_allowance
        split <;> omega
      constructor
      · omega
      · rw [slotAdd, epochAdd, Nat.add_mul, Nat.add_mul, one_mul]
        omega
    | @block fork before after engine signed due ok =>
      have processed := (applySignedBlock_ok ok).2.1
      have slot := (frame_processBlock processed).slot
      have header := registry_block_header early processed
      have growth := registry_block_bound early processed
      -- A successful block consumes the allowance and forbids another block at this slot.
      have used : ¬ after.latestBlockHeader.slot < after.slot := by
        rw [header.1, slot]
        exact UInt64.lt_irrefl _
      have oldAllowance : registry_block_allowance ⟨fork, before⟩ =
          preset.MAX_DEPOSITS.toNat := by simp only [registry_block_allowance, header.2, ↓reduceIte]
      have newAllowance : registry_block_allowance ⟨fork, after⟩ = 0 := by
        simp only [registry_block_allowance, used, ↓reduceIte]
      have epoch : getCurrentEpoch after = getCurrentEpoch before := by
        simp only [getCurrentEpoch, slot]
      simp only [oldAllowance] at bound
      simp only [newAllowance, Nat.add_zero, slot, epoch]
      exact ⟨slotsBefore, by omega⟩

/-- The registry envelope is independent of the endpoint, including a mid-epoch start. -/
theorem registry_le_window {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) :
    y.state.validators.data.size ≤ registryWindow x high := by
  obtain ⟨slots, bound⟩ := registry_run_bound tail early
  have epochs : (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch y.state).toNat := by
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
    exact Nat.div_le_div_right slots
  have epochCount : (getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat ≤
      driftHorizon x high := by unfold driftHorizon; omega
  have lastSlot : y.state.slot.toNat < (high + 2) * preset.SLOTS_PER_EPOCH.toNat := by
    rw [getCurrentEpoch_toNat] at endEpoch
    apply (Nat.div_lt_iff_lt_mul positive).mp
    omega
  have firstSlot : (getCurrentEpoch x.state).toNat * preset.SLOTS_PER_EPOCH.toNat ≤
      x.state.slot.toNat := by
    rw [getCurrentEpoch_toNat]
    exact Nat.div_mul_le_self _ _
  -- Include the initial slot: the run can start before that slot's block has arrived.
  have slotCount : y.state.slot.toNat + 1 - x.state.slot.toNat ≤
      driftHorizon x high * preset.SLOTS_PER_EPOCH.toNat := by
    unfold driftHorizon
    rw [Nat.sub_mul]
    omega
  have deposits := Nat.mul_le_mul_right preset.MAX_DEPOSITS.toNat slotCount
  have pending := Nat.mul_le_mul_right preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat epochCount
  unfold registryWindow
  rw [Nat.mul_add, ← Nat.mul_assoc]
  omega

private theorem intervalLoss_reference_split (x y : ForkedBeaconState preset) :
    referenceLoss x y =
      (∑ k ∈ ((activeKeys x.state).filter fun k =>
        ¬ ∃ v ∈ y.state.validators.data.toList, v.pubkey = k ∧ v.slashed = true),
        if k ∈ recentKeys y.state then 0 else effectiveWeight x.state k) +
      (∑ k ∈ ((activeKeys x.state).filter fun k =>
        ¬ ∃ v ∈ y.state.validators.data.toList, v.pubkey = k ∧ v.slashed = true),
        if k ∈ recentKeys y.state then effectiveWeight x.state k - effectiveWeight y.state k
        else 0) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  unfold Quorum.supported
  split <;> simp_all

private theorem intervalLoss_referenceDebit_of_recent (event : BalanceEvent preset)
    (i : Nat) (v : Validator) (found : event.before.state.validators.data[i]? = some v)
    (recent : isActiveValidator v (getCurrentEpoch event.before.state) = true ∨
      isActiveValidator v (getPreviousEpoch event.before.state) = true)
    (unslashed : event.source ≠ .slashings) :
    referenceDebit i event = actualBalanceAt event.before i - actualBalanceAt event.after i := by
  rcases recent with current | previous
  · simp [referenceDebit, unslashed, found, current]
  · simp [referenceDebit, unslashed, found, previous]

private theorem intervalLoss_recent_between {f h j : Fork}
    (s : BeaconState preset f) (middle : BeaconState preset h) (t : BeaconState preset j)
    (v w z : Validator) (first : ValidatorLifecycle v w) (last : ValidatorLifecycle w z)
    (epochsBefore : (getCurrentEpoch s).toNat ≤ (getCurrentEpoch middle).toNat)
    (epochsAfter : (getCurrentEpoch middle).toNat ≤ (getCurrentEpoch t).toNat)
    (active : isActiveValidator v (getCurrentEpoch s) = true)
    (recent : isActiveValidator z (getCurrentEpoch t) = true ∨
      isActiveValidator z (getPreviousEpoch t) = true) :
    isActiveValidator w (getCurrentEpoch middle) = true ∨
      isActiveValidator w (getPreviousEpoch middle) = true := by
  have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := by decide
  have activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
      UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at active
    have bound := v.exitEpoch.toNat_lt
    intro unset
    rw [unset, far] at active
    omega
  have activation := first.activationEpoch activated
  have finalActivation := last.activationEpoch (activation ▸ activated)
  by_cases assigned : w.exitEpoch = FAR_FUTURE_EPOCH
  · have bound := v.exitEpoch.toNat_lt
    have epoch := (getCurrentEpoch middle).toNat_lt
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
      UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, getPreviousEpoch_toNat] at active ⊢
    rw [activation, assigned]
    rw [far]
    omega
  · have exit := last.exitEpoch assigned
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
      UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, getPreviousEpoch_toNat] at active recent ⊢
    rw [activation]
    rw [exit, finalActivation, activation] at recent
    rcases recent with current | previous <;> omega

private theorem intervalLoss_filtered_coverage {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events)
    (i : Nat)
    (supported : ∀ event ∈ events, ∃ v, event.before.state.validators.data[i]? = some v ∧
      (isActiveValidator v (getCurrentEpoch event.before.state) = true ∨
        isActiveValidator v (getPreviousEpoch event.before.state) = true))
    (slashings : ∀ event ∈ events, event.source = .slashings →
      actualBalanceAt event.before i ≤ actualBalanceAt event.after i) :
    pathDebits i tail.balancePath ≤ (events.map (referenceDebit i)).sum := by
  apply (coverage_run tail early high endEpoch replayed true i).trans
  apply List.sum_le_sum
  intro event member
  change actualBalanceAt event.before i - actualBalanceAt event.after i ≤ referenceDebit i event
  by_cases slashed : event.source = .slashings
  · rw [Nat.sub_eq_zero_of_le (slashings event member slashed)]
    exact Nat.zero_le _
  · obtain ⟨v, found, recent⟩ := supported event member
    rw [intervalLoss_referenceDebit_of_recent event i v found recent slashed]

private theorem intervalLoss_delayed_slashing {fork : Fork} {s t : BeaconState preset fork}
    (early : fork < .glamsterdam) (ok : processSlashings s = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v)
    (unslashed : v.slashed = false) :
    actualBalanceAt ⟨fork, t⟩ i = actualBalanceAt ⟨fork, s⟩ i := by
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have notDue : ¬ SlashingPenaltyDue preset (getCurrentEpoch s) v := by
    simp [SlashingPenaltyDue, unslashed]
  by_cases electra : .pectra ≤ fork
  · obtain ⟨_, _, _, _, entries⟩ :=
      processSlashings_balances_of_electra electra (s.validators.bound early) ok
    obtain ⟨w, located, balance⟩ := (entries i).1 inside
    have same : w = v := Option.some.inj (located.symm.trans found)
    subst w
    simp only [notDue, ↓reduceIte] at balance
    simp [actualBalanceAt, balance]
  · obtain ⟨_, _, _, _, entries⟩ :=
      processSlashings_balances_of_lt_electra (Nat.lt_of_not_ge electra) ok
    obtain ⟨w, located, balance⟩ := (entries i).1 inside
    have same : w = v := Option.some.inj (located.symm.trans found)
    subst w
    simp only [notDue, ↓reduceIte] at balance
    simp [actualBalanceAt, balance]

private theorem intervalLoss_increase {fork : Fork} {s t : BeaconState preset fork}
    {index : ValidatorIndex} {amount : Gwei} (ok : increaseBalance s index amount = .ok t)
    (i : Nat) : actualBalanceAt ⟨fork, s⟩ i ≤ actualBalanceAt ⟨fork, t⟩ i := by
  cases found : s.balances.data[i]? with
  | none => simp [actualBalanceAt, found]
  | some balance =>
    obtain ⟨raised, located, value⟩ := balance_increaseBalance ok found
    simp only [actualBalanceAt, found, located, Option.map_some, Option.getD_some]
    omega

private theorem intervalLoss_initial_slashing {fork : Fork} {s t : BeaconState preset fork}
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (early : fork < .glamsterdam) (ok : slashValidator config s index whistleblower = .ok t)
    (i : Nat) (different : index.toNat ≠ i) :
    actualBalanceAt ⟨fork, s⟩ i ≤ actualBalanceAt ⟨fork, t⟩ i := by
  obtain ⟨exited, validator, withdrawable, marked, slashed, total, slashings, lowered,
    proposer, reward, raised, last, exitedOk, _, _, markedOk, _, _, _, lower, _, _,
    raise, pay, final⟩ := slashValidator_ok ok
  have first : marked.balances = s.balances := by
    obtain ⟨_, rfl⟩ := setValidator_ok markedOk
    simpa only [BeaconState.putValidator] using coverage_exit exitedOk
  have debit : actualBalanceAt ⟨fork, lowered⟩ i = actualBalanceAt ⟨fork, s⟩ i := by
    obtain ⟨inside, rfl⟩ := decreaseBalance_eq_ok_iff.mp lower
    simp [actualBalanceAt, BeaconState.putBalance, different, first]
  have one := intervalLoss_increase raise i
  have two := intervalLoss_increase pay i
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [notGloas, ↓reduceDIte] at final
  subst t
  omega

private theorem intervalLoss_unslashed_slashing {fork : Fork} {s t : BeaconState preset fork}
    {index other : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (early : fork < .glamsterdam) (ok : slashValidator config s index whistleblower = .ok t)
    (unslashed : slashedFlag t other = .ok false) :
    actualBalanceAt ⟨fork, s⟩ other.toNat ≤ actualBalanceAt ⟨fork, t⟩ other.toNat := by
  apply intervalLoss_initial_slashing early ok
  intro equal
  have same : index = other := UInt64.toNat_inj.mp equal
  have marked := (slashValidator_slashedFlag ok).1
  rw [same, unslashed] at marked
  cases marked

private theorem intervalLoss_attester_slashing {fork : Fork} {s t : BeaconState preset fork}
    (early : fork < .glamsterdam) (other : ValidatorIndex)
    (indices : List ValidatorIndex) (flag finalFlag : Bool)
    (ok : indices.foldlM (slashIfSlashable config) (s, flag) = .ok (t, finalFlag))
    (unslashed : slashedFlag t other = .ok false) :
    actualBalanceAt ⟨fork, s⟩ other.toNat ≤ actualBalanceAt ⟨fork, t⟩ other.toNat := by
  induction indices generalizing s flag with
  | nil => cases ok; exact Nat.le_refl _
  | cons index rest ih =>
    obtain ⟨⟨middle, nextFlag⟩, first, tail⟩ := bind_ok_iff.mp ok
    have beforeFalse : slashedFlag middle other = .ok false := by
      have flags := (foldlM_slashIfSlashable rest tail).2.1
      cases before : slashedFlag middle other with
      | error error =>
        have sizes := (foldlM_slashIfSlashable rest tail).1.1
        cases found : middle.validators.data[other.toNat]? with
        | some v => simp [slashedFlag, getValidator, found, Except.map] at before
        | none =>
          have outside := Array.getElem?_eq_none_iff.mp found
          have afterOutside : t.validators.data[other.toNat]? = none :=
            Array.getElem?_eq_none_iff.mpr (by simpa only [sizes] using outside)
          simp [slashedFlag, getValidator, afterOutside, Except.map] at unslashed
      | ok value =>
        cases value with
        | false => rfl
        | true => have marked := flags other before; rw [unslashed] at marked; cases marked
    have restBound := ih nextFlag tail
    have firstBound : actualBalanceAt ⟨fork, s⟩ other.toNat ≤
        actualBalanceAt ⟨fork, middle⟩ other.toNat := by
      simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at first
      obtain ⟨v, _, first⟩ := first
      split at first
      · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq,
          Prod.mk.injEq] at first
        obtain ⟨next, slashed, rfl, rfl⟩ := first
        exact intervalLoss_unslashed_slashing early slashed beforeFalse
      · cases first; exact Nat.le_refl _
    exact firstBound.trans restBound

private theorem intervalLoss_rounding (before after deficit increment : Nat)
    (positive : 0 < increment) (alignedBefore : before % increment = 0)
    (alignedAfter : after % increment = 0)
    (bound : before - after ≤ deficit + (increment - 1)) :
    before - after ≤ if deficit = 0 then 0 else deficit + increment - 1 := by
  split
  · rename_i zero
    have divides : increment ∣ before - after :=
      Nat.dvd_sub (Nat.dvd_of_mod_eq_zero alignedBefore) (Nat.dvd_of_mod_eq_zero alignedAfter)
    by_cases loss : 0 < before - after
    · have least := Nat.le_of_dvd loss divides
      omega
    · omega
  · omega

private theorem intervalLoss_effective_loss {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (aligned : MaxEffectiveBalancesAligned preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (early : y.fork < .glamsterdam)
    (i : Nat) (v : Validator) (found : x.state.validators.data[i]? = some v)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (events : List (BalanceEvent preset))
    (covered : pathDebits i tail.balancePath ≤ (events.map (referenceDebit i)).sum) :
    let deficit := effectiveAt x i - actualBalanceAt x i + (events.map (referenceDebit i)).sum
    effectiveAt x i - effectiveAt y i ≤
      if deficit = 0 then 0 else deficit + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1 := by
  have beforeEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have first := reachable_effective_alignment shared genesis aligned increment beforeEarly v
    (by simpa using Array.mem_of_getElem? found)
  obtain ⟨w, located, _⟩ := tail.registryLifecycle.validators i v found
  have last := reachable_effective_alignment (shared.append tail) genesis aligned increment
    early w (by simpa using Array.mem_of_getElem? located)
  have bound := effective_loss_from_balance shared tail genesis caps increment early i v found
    activated
  apply intervalLoss_rounding _ _ _ _ increment
  · simpa [effectiveAt, found] using first
  · simpa [effectiveAt, located] using last
  · omega

private theorem intervalLoss_consolidation_rate {fork : Fork}
    {s : BeaconState preset fork} (early : fork < .glamsterdam)
    {total churn : Gwei} (read : getTotalActiveBalance s = .ok total)
    (computed : getConsolidationChurnLimit config s = .ok churn)
    {stake : Nat} (bounded : total.toNat ≤ max preset.EFFECTIVE_BALANCE_INCREMENT.toNat stake) :
    churn.toNat ≤ consolidationRate (preset := preset) (config := config) stake := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [getConsolidationChurnLimit, notGloas, ↓reduceIte,
    getActivationExitChurnLimit, getBalanceChurnLimit, read,
    bind, Except.bind, pure, Except.pure, Except.ok.injEq] at computed
  subst churn
  have rounded : ∀ amount : Gwei, (roundToIncrement preset amount).toNat ≤ amount.toNat := by
    intro amount
    have remainder : amount % preset.EFFECTIVE_BALANCE_INCREMENT ≤ amount := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
      exact Nat.mod_le _ _
    simp only [roundToIncrement, UInt64.toNat_sub_of_le _ _ remainder]
    exact Nat.sub_le _ _
  have subtract : min config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT
      (roundToIncrement preset (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
        (total / config.CHURN_LIMIT_QUOTIENT))) ≤
      roundToIncrement preset (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
        (total / config.CHURN_LIMIT_QUOTIENT)) := by
    rw [UInt64.le_iff_toNat_le, Uint64.toNat_min]
    exact Nat.min_le_right _ _
  rw [UInt64.toNat_sub_of_le _ _ subtract, Uint64.toNat_min]
  have upper := rounded (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
    (total / config.CHURN_LIMIT_QUOTIENT))
  rw [Uint64.toNat_max, UInt64.toNat_div] at upper
  have rate := max_le_max_left config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
    (Nat.div_le_div_right bounded (c := config.CHURN_LIMIT_QUOTIENT.toNat))
  unfold consolidationRate
  omega

private theorem intervalLoss_exit_charge {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex} {v : Validator}
    (found : getValidator s index = .ok v) (unset : v.exitEpoch = FAR_FUTURE_EPOCH)
    (ok : initiateValidatorExit config s index = .ok t) :
    ∃ queued epoch first churn,
      computeExitEpochAndUpdateChurn config s electra v.effectiveBalance = .ok (queued, epoch) ∧
      computeActivationExitEpoch preset (getCurrentEpoch s) = .ok first ∧
      exitChurnLimit config s = .ok churn ∧
      (t.earliestExitEpoch electra) = epoch ∧
      v.effectiveBalance.toNat + (t.exitBalanceToConsume electra).toNat =
        (if s.earliestExitEpoch electra < max (s.earliestExitEpoch electra) first
          then churn.toNat else (s.exitBalanceToConsume electra).toNat) +
        (epoch.toNat - (max (s.earliestExitEpoch electra) first).toNat) * churn.toNat := by
  obtain ⟨w, located, same | ⟨_, queued, epoch, withdrawal, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · have equal := Except.ok.inj (located.symm.trans found)
    exact False.elim (same.1 (equal ▸ unset))
  · have equal := Except.ok.inj (located.symm.trans found)
    subst w
    simp only [exitQueue, electra, ↓reduceDIte] at queue
    obtain ⟨first, churn, firstOk, rate, spent⟩ := exit_queue_charge s queued electra _ _ queue
    have earliest := (computeExitEpochAndUpdateChurn_earliest queue).1
    obtain ⟨_, rfl⟩ := setValidator_ok set
    exact ⟨queued, epoch, first, churn, queue, firstOk, rate, earliest, spent⟩

private theorem intervalLoss_consolidation_charge {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    ∃ queued epoch first churn,
      computeConsolidationEpochAndUpdateChurn config s electra source.effectiveBalance =
        .ok (queued, epoch) ∧
      computeActivationExitEpoch preset (getCurrentEpoch s) = .ok first ∧
      getConsolidationChurnLimit config s = .ok churn ∧
      (t.earliestConsolidationEpoch electra) = epoch ∧
      source.effectiveBalance.toNat + (t.consolidationBalanceToConsume electra).toNat =
        (if s.earliestConsolidationEpoch electra <
            max (s.earliestConsolidationEpoch electra) first then churn.toNat
          else (s.consolidationBalanceToConsume electra).toNat) +
        (epoch.toNat - (max (s.earliestConsolidationEpoch electra) first).toNat) * churn.toNat := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨⟨queued, epoch⟩, queue, withdrawal, _, marked, set, pending, _, rfl⟩ := ok
  obtain ⟨first, churn, firstOk, rate, spent⟩ :=
    consolidation_queue_charge s queued electra _ _ queue
  have earliest := (computeConsolidationEpochAndUpdateChurn_earliest queue).1
  obtain ⟨_, rfl⟩ := setValidator_ok set
  exact ⟨queued, epoch, first, churn, queue, firstOk, rate, earliest, spent⟩

private theorem intervalLoss_preElectra_departures {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (early : y.fork < .pectra) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) :
    leaving x y ≤ exitWindow (config := config) x high events := by
  have before : x.fork < .pectra :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have registry := registry_le_window tail (Nat.lt_trans early (by decide)) high endEpoch
    (by have := parameters.slots; omega)
  have count : cohortCap config y.state.validators.data.size ≤
      cohortCap config (registryWindow x high) :=
    max_le_max_left _ (Nat.div_le_div_right registry)
  have horizon : (getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat ≤
      driftHorizon x high := by unfold driftHorizon; omega
  have departures := leaving_before_electra shared tail genesis parameters caps early
  have bounded := Nat.mul_le_mul_right preset.MAX_EFFECTIVE_BALANCE.toNat
    (Nat.mul_le_mul horizon (max_le_max_left 1 count))
  have total := departures.trans bounded
  unfold exitWindow
  rw [ite_eq_left before, Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc]
  omega

/-- Bound exits and retained-key losses, omitting keys with slashing evidence.

The source envelope can charge a pre-exit deficit as well as the later departure.

The exact referenceLoss does not double-count that key. -/
theorem nonaccountable_losses_over_interval {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    referenceLoss x y ≤
      exitWindow (config := config) x high events + lossCorrection x events := by
  sorry

private theorem intervalGain_existing_funding {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (i : Nat) (present : i < x.state.validators.data.size) :
    effectiveAt y i ≤ max (effectiveAt x i) (actualBalanceAt x i) +
      pathCredits i tail.balancePath := by
  -- Effective stake above actual balance is retained until a later update lowers it.
  have gain := effective_gain_from_balance tail early i present
  omega

private theorem intervalGain_no_reentry {x y : ForkedBeaconState preset}
    (kept : RegistryLifecycle x.state y.state) (i : Nat) (v w : Validator)
    (before : x.state.validators.data[i]? = some v)
    (after : y.state.validators.data[i]? = some w)
    (assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH)
    (exited : v.exitEpoch.toNat ≤ (getPreviousEpoch y.state).toNat) :
    isActiveValidator w (getCurrentEpoch y.state) = false ∧
      isActiveValidator w (getPreviousEpoch y.state) = false := by
  obtain ⟨last, found, lifecycle⟩ := kept.validators i v before
  have same : last = w := Option.some.inj (found.symm.trans after)
  have exit := same ▸ lifecycle.exitEpoch assigned
  have previous : (getPreviousEpoch y.state).toNat ≤ (getCurrentEpoch y.state).toNat := by
    rw [getPreviousEpoch_toNat]
    omega
  have currentExit : ¬ getCurrentEpoch y.state < w.exitEpoch := by
    rw [exit, UInt64.lt_iff_toNat_lt]
    omega
  have previousExit : ¬ getPreviousEpoch y.state < w.exitEpoch := by
    rw [exit, UInt64.lt_iff_toNat_lt]
    omega
  simp [isActiveValidator, currentExit, previousExit]

private theorem intervalGain_carry_cases {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (parameters : Parameters preset)
    (i : Nat) (v w : Validator)
    (before : x.state.validators.data[i]? = some v)
    (after : y.state.validators.data[i]? = some w)
    (inactive : isActiveValidator v (getCurrentEpoch x.state) = false)
    (recent : isActiveValidator w (getCurrentEpoch y.state) = true ∨
      isActiveValidator w (getPreviousEpoch y.state) = true) :
    isActiveValidator v (getPreviousEpoch x.state) = true ∨
      getCurrentEpoch x.state < v.activationEpoch := by
  have epochs : (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch y.state).toNat := by
    clear after recent
    induction tail with
    | nil => exact Nat.le_refl _
    | snoc pre step ih => exact ih.trans (coverage_step_epoch step)
  obtain ⟨last, found, lifecycle⟩ := tail.registryLifecycle.validators i v before
  have same : last = w := Option.some.inj (found.symm.trans after)
  subst last
  by_cases future : getCurrentEpoch x.state < v.activationEpoch
  · exact Or.inr future
  left
  have bounded : (getCurrentEpoch x.state).toNat < FAR_FUTURE_EPOCH.toNat := by
    have ne := getCurrentEpoch_ne_farFuture parameters.slots x.state
    have bound := (getCurrentEpoch x.state).toNat_lt_size
    have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    have different : (getCurrentEpoch x.state).toNat ≠ FAR_FUTURE_EPOCH.toNat := by
      exact fun h => ne (UInt64.toNat_inj.mp h)
    simp only [UInt64.size] at bound
    omega
  have assigned : v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    rw [UInt64.lt_iff_toNat_lt] at future
    intro eq
    rw [eq] at future
    omega
  have activation := lifecycle.activationEpoch assigned
  have exitAssigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH := by
    simp only [isActiveValidator, Bool.and_eq_false_iff, decide_eq_false_iff_not,
      UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at inactive
    rw [UInt64.lt_iff_toNat_lt] at future
    intro eq
    rw [eq] at inactive
    omega
  have exit := lifecycle.exitEpoch exitAssigned
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
    UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, getPreviousEpoch_toNat,
    activation, exit] at recent ⊢
  simp only [isActiveValidator, Bool.and_eq_false_iff, decide_eq_false_iff_not,
    UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at inactive
  rw [UInt64.lt_iff_toNat_lt] at future
  omega

private theorem intervalGain_electra_deposit {fork : Fork}
    {s t : BeaconState preset fork} {electra : .pectra ≤ fork}
    {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32}
    {amount : Gwei} {signature : Cryptography.Bls.BLSSignature}
    (matched : BalancesMatch s)
    (ok : applyDepositElectra config checks s electra key credentials amount signature = .ok t)
    (i : Nat) : actualBalanceAt ⟨fork, t⟩ i = actualBalanceAt ⟨fork, s⟩ i := by
  unfold applyDepositElectra at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨valid, checked, rest⟩ := ok
    split at rest
    · simp only [bind_ok_iff, liftAccessor_ok] at rest
      obtain ⟨added, admission, queued⟩ := rest
      obtain ⟨_, rfl⟩ := addPendingDeposit_eq queued
      -- Electra registers a new key with zero balance and queues its deposit separately.
      have balances := (addValidatorToRegistry_push admission matched).2
      simp only [actualBalanceAt, balances]
      by_cases atEnd : i = s.balances.data.size
      · subst i
        simp
      · simp [Array.getElem?_push, atEnd]
    · cases rest
      rfl
  · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp ok)
    rfl

private theorem intervalGain_withdrawn_excluded {x y : ForkedBeaconState preset}
    (kept : RegistryLifecycle x.state y.state) (parameters : Parameters preset)
    (ordered : ExitsOrdered x.state) (i : Nat) (v w : Validator)
    (before : x.state.validators.data[i]? = some v)
    (after : y.state.validators.data[i]? = some w)
    (withdrawn : v.withdrawableEpoch.toNat ≤ (getCurrentEpoch x.state).toNat)
    (later : (getCurrentEpoch x.state).toNat < (getCurrentEpoch y.state).toNat) :
    isActiveValidator w (getCurrentEpoch y.state) = false ∧
      isActiveValidator w (getPreviousEpoch y.state) = false := by
  have exit := UInt64.le_iff_toNat_le.mp (ordered v (Array.mem_of_getElem? before))
  have assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH := by
    have ne := getCurrentEpoch_ne_farFuture parameters.slots x.state
    have bound := (getCurrentEpoch x.state).toNat_lt_size
    have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    have different : (getCurrentEpoch x.state).toNat ≠ FAR_FUTURE_EPOCH.toNat := by
      exact fun h => ne (UInt64.toNat_inj.mp h)
    simp only [UInt64.size] at bound
    intro eq
    rw [eq] at exit
    omega
  apply intervalGain_no_reentry kept i v w before after assigned
  rw [getPreviousEpoch_toNat]
  omega

private theorem intervalGain_recent_not_withdrawn {x y : ForkedBeaconState preset}
    (kept : RegistryLifecycle x.state y.state) (parameters : Parameters preset)
    (ordered : ExitsOrdered x.state) (i : Nat) (v w : Validator)
    (before : x.state.validators.data[i]? = some v)
    (after : y.state.validators.data[i]? = some w)
    (later : (getCurrentEpoch x.state).toNat < (getCurrentEpoch y.state).toNat)
    (recent : isActiveValidator w (getCurrentEpoch y.state) = true ∨
      isActiveValidator w (getPreviousEpoch y.state) = true) :
    (getCurrentEpoch x.state).toNat < v.withdrawableEpoch.toNat := by
  by_contra withdrawn
  have excluded := intervalGain_withdrawn_excluded kept parameters ordered i v w before after
    (by omega) later
  rcases recent with current | previous
  · simp [excluded.1] at current
  · simp [excluded.2] at previous

private theorem intervalGain_index_bound {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (early : y.fork < .glamsterdam)
    (i : Nat) (w : Validator) (after : y.state.validators.data[i]? = some w)
    (recent : isActiveValidator w (getCurrentEpoch y.state) = true ∨
      isActiveValidator w (getPreviousEpoch y.state) = true) :
    effectiveAt y i -
        (if (x.state.validators.data[i]?.map fun v =>
          isActiveValidator v (getCurrentEpoch x.state)).getD false then effectiveAt x i else 0) ≤
      (match x.state.validators.data[i]? with
      | none => 0
      | some v => if isActiveValidator v (getCurrentEpoch x.state) then
          actualBalanceAt x i - effectiveAt x i
        else if isActiveValidator v (getPreviousEpoch x.state) ||
            getCurrentEpoch x.state < v.activationEpoch then
          max (effectiveAt x i) (actualBalanceAt x i)
        else 0) + pathCredits i tail.balancePath := by
  -- Admissions spend later credits; existing inactive keys retain their initial funding.
  cases before : x.state.validators.data[i]? with
  | none =>
    have absent : x.state.validators.data.size ≤ i := by
      simpa using (Array.getElem?_eq_none_iff.mp before)
    have present := (Array.getElem?_eq_some_iff.mp after).1
    have bound := joining_growth_from_admission shared tail genesis early i absent present
    simpa only [Option.map_none, Option.getD_none, Bool.false_eq_true, ↓reduceIte,
      Nat.sub_zero, Nat.zero_add] using bound
  | some v =>
    have present := (Array.getElem?_eq_some_iff.mp before).1
    cases active : isActiveValidator v (getCurrentEpoch x.state) with
    | true =>
      simpa only [Option.map_some, Option.getD_some, active, ↓reduceIte]
        using effective_gain_from_balance tail early i present
    | false =>
      have carried := intervalGain_carry_cases tail parameters i v w before after active recent
      have selected : (isActiveValidator v (getPreviousEpoch x.state) ||
          getCurrentEpoch x.state < v.activationEpoch) = true := by
        simpa only [Bool.or_eq_true, decide_eq_true_eq] using carried
      simpa only [Option.map_some, Option.getD_some, active, Bool.false_eq_true,
        ↓reduceIte, Nat.sub_zero, selected]
        using intervalGain_existing_funding tail early i present

private theorem intervalGain_weight_at {fork : Fork} (s : BeaconState preset fork)
    (unique : uniqueKeys s) (i : Nat) (v : Validator)
    (found : s.validators.data[i]? = some v) :
    effectiveWeight s v.pubkey = effectiveAt ⟨fork, s⟩ i := by
  have lookup (vs : List Validator) (distinct : (vs.map (·.pubkey)).Nodup)
      (v : Validator) (member : v ∈ vs) :
      vs.find? (fun w => w.pubkey == v.pubkey) = some v := by
    induction vs with
    | nil => simp at member
    | cons w ws ih =>
      simp only [List.map_cons, List.nodup_cons] at distinct
      rcases List.mem_cons.mp member with rfl | member
      · simp
      · have different : w.pubkey ≠ v.pubkey := by
          intro same
          exact distinct.1 (List.mem_map.mpr ⟨v, member, same.symm⟩)
        simp [different, ih distinct.2 member]
  have member : v ∈ s.validators.data.toList := by
    simpa using Array.mem_of_getElem? found
  simp [effectiveWeight, effectiveAt, found, lookup _ unique v member]

private theorem intervalGain_active_key {fork : Fork} (s : BeaconState preset fork)
    (parameters : Parameters preset) (within : s.RegistryWithinLimit) (unique : uniqueKeys s)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    v.pubkey ∈ activeKeys s ↔ isActiveValidator v (getCurrentEpoch s) = true := by
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have small : i < 2 ^ 64 := by
    exact (Nat.lt_of_lt_of_le inside within).trans parameters.registry
  have numeric : i.toUInt64.toNat = i := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small]
  constructor
  · intro member
    simp only [activeKeys, keysAt, List.mem_toFinset, List.mem_filterMap] at member
    obtain ⟨j, active, key⟩ := member
    obtain ⟨w, read, active⟩ := (mem_getActiveValidatorIndices within).mp active
    have sameKey : w.pubkey = v.pubkey := by simpa [read] using key
    obtain ⟨hi, vi⟩ := Array.getElem?_eq_some_iff.mp found
    obtain ⟨hj, wj⟩ := Array.getElem?_eq_some_iff.mp read
    have same : j.toNat = i := unique.eq_of_getElem_eq
      (by simpa [registryKeys] using hj) (by simpa [registryKeys] using hi)
      (by simpa [registryKeys, vi, wj] using sameKey)
    have equal : w = v := Option.some.inj ((same ▸ read).symm.trans found)
    simpa [equal] using active
  · intro active
    simp only [activeKeys, keysAt, List.mem_toFinset, List.mem_filterMap]
    refine ⟨i.toUInt64, (mem_getActiveValidatorIndices within).mpr
      ⟨v, by simpa [numeric] using found, active⟩, ?_⟩
    simp [numeric, found]

private theorem intervalGain_reference_at {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (early : y.fork < .glamsterdam)
    (i : Nat) (w : Validator) (after : y.state.validators.data[i]? = some w) :
    Quorum.supported (activeKeys x.state) (effectiveWeight x.state) w.pubkey =
      (if (x.state.validators.data[i]?.map fun v =>
        isActiveValidator v (getCurrentEpoch x.state)).getD false then effectiveAt x i else 0) := by
  have uniqueX := shared.unique (genesis_unique genesis)
  have uniqueY := (shared.append tail).unique (genesis_unique genesis)
  have earlyX := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have within := x.state.validators.bound earlyX
  have sameIndex {j : Nat} {v : Validator} (before : x.state.validators.data[j]? = some v)
      (key : v.pubkey = w.pubkey) : j = i := by
    obtain ⟨last, found, preserved⟩ := tail.key_preserved j v before
    obtain ⟨hj, lastEq⟩ := Array.getElem?_eq_some_iff.mp found
    obtain ⟨hi, wEq⟩ := Array.getElem?_eq_some_iff.mp after
    exact uniqueY.eq_of_getElem_eq
      (by simpa [registryKeys] using hj) (by simpa [registryKeys] using hi)
      (by simpa [registryKeys, lastEq, wEq] using preserved.trans key)
  cases before : x.state.validators.data[i]? with
  | none =>
    have absent : w.pubkey ∉ activeKeys x.state := by
      intro member
      simp only [activeKeys, keysAt, List.mem_toFinset, List.mem_filterMap] at member
      obtain ⟨j, active, key⟩ := member
      obtain ⟨v, found, _⟩ := (mem_getActiveValidatorIndices within).mp active
      have same := sameIndex found (by simpa [found] using key)
      rw [same, before] at found
      cases found
    simp [Quorum.supported, absent]
  | some v =>
    obtain ⟨last, found, preserved⟩ := tail.key_preserved i v before
    have same : last = w := Option.some.inj (found.symm.trans after)
    have key : w.pubkey = v.pubkey := same ▸ preserved
    rw [key]
    simp only [Quorum.supported, intervalGain_active_key x.state parameters within uniqueX
      i v before, intervalGain_weight_at x.state uniqueX i v before,
      Option.map_some, Option.getD_some]

private theorem intervalGain_recent_key {fork : Fork} (s : BeaconState preset fork)
    (parameters : Parameters preset) (within : s.RegistryWithinLimit)
    (key : Cryptography.Bls.BLSPubkey) :
    key ∈ recentKeys s ↔ ∃ (i : Nat) (v : Validator),
      s.validators.data[i]? = some v ∧ v.pubkey = key ∧
      (isActiveValidator v (getCurrentEpoch s) = true ∨
        isActiveValidator v (getPreviousEpoch s) = true) := by
  have member (epoch : Epoch) : key ∈ keysAt s (getActiveValidatorIndices s epoch) ↔
      ∃ (i : Nat) (v : Validator), s.validators.data[i]? = some v ∧ v.pubkey = key ∧
        isActiveValidator v epoch = true := by
    constructor
    · intro selected
      simp only [keysAt, List.mem_toFinset, List.mem_filterMap] at selected
      obtain ⟨i, active, keyEq⟩ := selected
      obtain ⟨v, found, active⟩ := (mem_getActiveValidatorIndices within).mp active
      exact ⟨i.toNat, v, found, by simpa [found] using keyEq, active⟩
    · rintro ⟨i, v, found, keyEq, active⟩
      have inside := (Array.getElem?_eq_some_iff.mp found).1
      have small := (Nat.lt_of_lt_of_le inside within).trans parameters.registry
      have numeric : i.toUInt64.toNat = i := by
        rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small]
      simp only [keysAt, List.mem_toFinset, List.mem_filterMap]
      refine ⟨i.toUInt64, (mem_getActiveValidatorIndices within).mpr
        ⟨v, by simpa [numeric] using found, active⟩, ?_⟩
      simp [numeric, found, keyEq]
  simp only [recentKeys, Finset.mem_union, activeKeys, member]
  constructor
  · rintro (⟨i, v, found, keyEq, active⟩ | ⟨i, v, found, keyEq, active⟩)
    · exact ⟨i, v, found, keyEq, Or.inl active⟩
    · exact ⟨i, v, found, keyEq, Or.inr active⟩
  · rintro ⟨i, v, found, keyEq, active | active⟩
    · exact Or.inl ⟨i, v, found, keyEq, active⟩
    · exact Or.inr ⟨i, v, found, keyEq, active⟩

private def intervalGain_indices (y : ForkedBeaconState preset) : Finset Nat :=
  (Finset.range y.state.validators.data.size).filter fun i =>
    ∃ w, y.state.validators.data[i]? = some w ∧
      (isActiveValidator w (getCurrentEpoch y.state) = true ∨
        isActiveValidator w (getPreviousEpoch y.state) = true)

private theorem intervalGain_reference_sum {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (early : y.fork < .glamsterdam) :
    referenceGain x y = ∑ i ∈ intervalGain_indices y,
      (effectiveAt y i -
        (if (x.state.validators.data[i]?.map fun v =>
          isActiveValidator v (getCurrentEpoch x.state)).getD false then
            effectiveAt x i else 0)) := by
  have unique := (shared.append tail).unique (genesis_unique genesis)
  have inside (i) (h : i ∈ intervalGain_indices y) : i < y.state.validators.data.size :=
    Finset.mem_range.mp (Finset.mem_filter.mp h).1
  let key (i : Nat) (h : i ∈ intervalGain_indices y) :=
    (y.state.validators.data[i]'(inside i h)).pubkey
  unfold referenceGain
  symm
  -- Unique keys and preserved registry positions identify the reference subtraction.
  apply Finset.sum_bij key
  · intro i hi
    obtain ⟨w, found, recent⟩ := (Finset.mem_filter.mp hi).2
    apply (intervalGain_recent_key y.state parameters (y.state.validators.bound early) _).mpr
    refine ⟨i, w, found, ?_, recent⟩
    simp only [key, (Array.getElem?_eq_some_iff.mp found).2]
  · intro i hi j hj equal
    exact unique.eq_of_getElem_eq
      (by simpa [registryKeys] using inside i hi)
      (by simpa [registryKeys] using inside j hj)
      (by simpa [registryKeys, key] using equal)
  · intro k hk
    obtain ⟨i, w, found, same, recent⟩ :=
      (intervalGain_recent_key y.state parameters (y.state.validators.bound early) k).mp hk
    have hi : i ∈ intervalGain_indices y := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1, w, found, recent⟩
    refine ⟨i, hi, ?_⟩
    simpa only [key, (Array.getElem?_eq_some_iff.mp found).2] using same
  · intro i hi
    obtain ⟨w, found, _⟩ := (Finset.mem_filter.mp hi).2
    have keyEq : key i hi = w.pubkey := by
      simp only [key, (Array.getElem?_eq_some_iff.mp found).2]
    rw [keyEq, intervalGain_weight_at y.state unique i w found,
      intervalGain_reference_at shared tail genesis parameters early i w found]

private def intervalGain_initial (x : ForkedBeaconState preset) (i : Nat) : Nat :=
  match x.state.validators.data[i]? with
  | none => 0
  | some v => if isActiveValidator v (getCurrentEpoch x.state) then
      actualBalanceAt x i - effectiveAt x i
    else if isActiveValidator v (getPreviousEpoch x.state) ||
        getCurrentEpoch x.state < v.activationEpoch then
      max (effectiveAt x i) (actualBalanceAt x i)
    else 0

private theorem intervalGain_path_bound {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (early : y.fork < .glamsterdam) :
    referenceGain x y ≤ (∑ i ∈ intervalGain_indices y, intervalGain_initial x i) +
      ∑ i ∈ intervalGain_indices y, pathCredits i tail.balancePath := by
  rw [intervalGain_reference_sum shared tail genesis parameters early, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i member
  obtain ⟨w, found, recent⟩ := (Finset.mem_filter.mp member).2
  exact intervalGain_index_bound shared tail genesis parameters early i w found recent

private theorem intervalGain_zip_sum (vs : List Validator) (f : Validator → Nat → Nat) :
    (vs.zipIdx.map fun (v, i) => f v i).sum =
      ∑ i ∈ Finset.range vs.length, (vs[i]?.map (fun v => f v i)).getD 0 := by
  let weight := fun i => (vs[i]?.map (fun v => f v i)).getD 0
  have same : vs.zipIdx.map (fun (v, i) => f v i) =
      (vs.zipIdx.map Prod.snd).map weight := by
    rw [List.map_map]
    apply List.map_congr_left
    rintro ⟨v, i⟩ member
    have found := List.mem_zipIdx_iff_getElem?.mp member
    simp [weight, found]
  rw [same, List.zipIdx_map_snd]
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range,
    Multiset.map_coe, Multiset.sum_coe, List.range_eq_range']

private theorem intervalGain_excess_sum (x : ForkedBeaconState preset)
    (parameters : Parameters preset) (early : x.fork < .glamsterdam) :
    initialExcess x = ∑ i ∈ Finset.range x.state.validators.data.size,
      (x.state.validators.data[i]?.map fun v =>
        if isActiveValidator v (getCurrentEpoch x.state) then
          actualBalanceAt x i - effectiveAt x i else 0).getD 0 := by
  have filterSum {α : Type} (xs : List α) (f : α → Option Nat) :
      (xs.filterMap f).sum = (xs.map fun a => (f a).getD 0).sum := by
    induction xs with
    | nil => rfl
    | cons a xs ih => cases h : f a <;> simp [h, ih]
  unfold initialExcess getActiveValidatorIndices
  rw [List.map_filterMap, filterSum]
  have zipped := intervalGain_zip_sum x.state.validators.data.toList
    (fun v i => if isActiveValidator v (getCurrentEpoch x.state) then
      actualBalanceAt x i - effectiveAt x i else 0)
  simp only [Array.length_toList, Array.getElem?_toList] at zipped
  rw [← zipped]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨v, i⟩ member
  have found := List.mem_zipIdx_iff_getElem?.mp member
  have inside := (List.getElem?_eq_some_iff.mp found).1
  have small : i < 2 ^ 64 :=
    (Nat.lt_of_lt_of_le (by simpa using inside) (x.state.validators.bound early)).trans
      parameters.registry
  have numeric : i.toUInt64.toNat = i := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small]
  dsimp only [Function.comp_def]
  split <;> simp_all
  all_goals simp only [Nat.mod_eq_of_lt small]

private theorem intervalGain_initial_sum (x : ForkedBeaconState preset)
    (parameters : Parameters preset) (early : x.fork < .glamsterdam) :
    (∑ i ∈ Finset.range x.state.validators.data.size, intervalGain_initial x i) =
      activationCarry x + initialExcess x := by
  rw [intervalGain_excess_sum x parameters early]
  unfold activationCarry
  rw [intervalGain_zip_sum x.state.validators.data.toList
    (fun v i => if isActiveValidator v (getCurrentEpoch x.state) then 0
      else if isActiveValidator v (getPreviousEpoch x.state) ||
          getCurrentEpoch x.state < v.activationEpoch then
        max (effectiveAt x i) (actualBalanceAt x i) else 0)]
  simp only [Array.length_toList, Array.getElem?_toList]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases found : x.state.validators.data[i]? with
  | none => simp [intervalGain_initial, found]
  | some v =>
    cases active : isActiveValidator v (getCurrentEpoch x.state) <;>
      simp [intervalGain_initial, found, active]

private theorem intervalGain_initial_subset (x y : ForkedBeaconState preset)
    (parameters : Parameters preset) (early : x.fork < .glamsterdam) :
    (∑ i ∈ intervalGain_indices y, intervalGain_initial x i) ≤
      activationCarry x + initialExcess x := by
  rw [← intervalGain_initial_sum x parameters early]
  apply Finset.sum_le_sum_of_ne_zero
  intro i _ nonzero
  apply Finset.mem_range.mpr
  by_contra outside
  have absent : x.state.validators.data[i]? = none := Array.getElem?_eq_none_iff.mpr (by omega)
  simp [intervalGain_initial, absent] at nonzero

private theorem intervalGain_replay_bound {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (early : y.fork < .glamsterdam)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    referenceGain x y ≤ activationCarry x + initialExcess x +
      (events.map fun e => ∑ i ∈ intervalGain_indices y,
        (actualBalanceAt e.after i - actualBalanceAt e.before i)).sum := by
  have gain := intervalGain_path_bound shared tail genesis parameters early
  have initial := intervalGain_initial_subset x y parameters
    (Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early)
  -- Keep the endpoint support restriction when replacing path credits by replay credits.
  have covered : (∑ i ∈ intervalGain_indices y, pathCredits i tail.balancePath) ≤
      ∑ i ∈ intervalGain_indices y,
        (events.map fun e => actualBalanceAt e.after i - actualBalanceAt e.before i).sum := by
    apply Finset.sum_le_sum
    intro i _
    exact coverage_run tail early high endEpoch replayed false i
  have exchange : (∑ i ∈ intervalGain_indices y,
      (events.map fun e => actualBalanceAt e.after i - actualBalanceAt e.before i).sum) =
      (events.map fun e => ∑ i ∈ intervalGain_indices y,
        (actualBalanceAt e.after i - actualBalanceAt e.before i)).sum := by
    clear replayed covered
    induction events with
    | nil => simp
    | cons e rest ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
  rw [exchange] at covered
  omega

private theorem intervalGain_selected_deposit (y : ForkedBeaconState preset)
    (parameters : Parameters preset) (e : BalanceEvent preset)
    (kept : RegistryLifecycle e.before.state y.state)
    (ordered : ExitsOrdered e.before.state)
    (later : (getCurrentEpoch e.before.state).toNat < (getCurrentEpoch y.state).toNat)
    (matched : BalancesMatch e.after.state) :
    (∑ i ∈ intervalGain_indices y, (actualBalanceAt e.after i - actualBalanceAt e.before i)) ≤
      ∑ i ∈ Finset.range e.after.state.validators.data.size,
        if (e.before.state.validators.data[i]?.map (fun v =>
            decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch e.before.state).toNat))).getD
            false then 0 else actualBalanceAt e.after i - actualBalanceAt e.before i := by
  have selected (i) (member : i ∈ intervalGain_indices y) :
      (e.before.state.validators.data[i]?.map (fun v =>
        decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch e.before.state).toNat))).getD
          false = false := by
    cases found : e.before.state.validators.data[i]? with
    | none => rfl
    | some v =>
      obtain ⟨w, after, recent⟩ := (Finset.mem_filter.mp member).2
      have notWithdrawn := intervalGain_recent_not_withdrawn kept parameters ordered i v w
        found after later recent
      simp only [Option.map_some, Option.getD_some, decide_eq_false_iff_not]
      omega
  calc
    _ = ∑ i ∈ intervalGain_indices y,
        if (e.before.state.validators.data[i]?.map (fun v =>
            decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch e.before.state).toNat))).getD
            false then 0 else actualBalanceAt e.after i - actualBalanceAt e.before i := by
      apply Finset.sum_congr rfl
      intro i member
      simp only [selected i member, Bool.false_eq_true, ↓reduceIte]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_ne_zero
      intro i _ nonzero
      apply Finset.mem_range.mpr
      by_contra outside
      have absent : e.after.state.balances.data[i]? = none :=
        Array.getElem?_eq_none_iff.mpr (by dsimp [BalancesMatch] at matched; omega)
      simp only [actualBalanceAt, absent, Option.map_none, Option.getD_none, Nat.zero_sub,
        ite_self] at nonzero
      exact nonzero rfl

private theorem intervalGain_event_credit (y : ForkedBeaconState preset)
    (e : BalanceEvent preset) (bounded : e.credits ≤ e.creditLimit) :
    (∑ i ∈ intervalGain_indices y, (actualBalanceAt e.after i - actualBalanceAt e.before i)) ≤
      e.creditLimit := by
  apply le_trans (b := e.credits) _ bounded
  unfold BalanceEvent.credits
  apply Finset.sum_le_sum_of_ne_zero
  intro i _ nonzero
  apply Finset.mem_range.mpr
  by_contra outside
  have absent : e.after.state.balances.data[i]? = none :=
    Array.getElem?_eq_none_iff.mpr (by omega)
  simp [actualBalanceAt, absent] at nonzero

private theorem intervalGain_residual_other (x : ForkedBeaconState preset) (high : Nat)
    (e : BalanceEvent preset) (other : e.source ≠ .deposits) :
    residualCredit (config := config) x high e = e.creditLimit := by
  cases source : e.source <;> simp_all [residualCredit]

private theorem intervalGain_residual_deposit (x : ForkedBeaconState preset) (high : Nat)
    (e : BalanceEvent preset) (deposit : e.source = .deposits) :
    residualCredit (config := config) x high e =
      if .pectra ≤ e.before.fork then 0 else
        if high + 1 < config.ELECTRA_FORK_EPOCH.toNat then
          ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
            actualBalanceAt e.after i.toNat - actualBalanceAt e.before i.toNat).sum
        else e.creditLimit := by
  simp only [residualCredit, deposit]

private theorem intervalGain_crossing_credit (x y : ForkedBeaconState preset) (high : Nat)
    (e : BalanceEvent preset) (crossing : e.source = .crossing)
    (bounded : e.credits ≤ e.creditLimit) :
    (∑ i ∈ intervalGain_indices y, (actualBalanceAt e.after i - actualBalanceAt e.before i)) ≤
      residualCredit (config := config) x high e := by
  rw [intervalGain_residual_other x high e (by simp [crossing])]
  exact intervalGain_event_credit y e bounded

private theorem intervalGain_preupgrade_credit (x y : ForkedBeaconState preset) (high : Nat)
    (e : BalanceEvent preset) (deposit : e.source = .deposits)
    (before : e.before.fork < .pectra)
    (crossing : config.ELECTRA_FORK_EPOCH.toNat ≤ high + 1)
    (bounded : e.credits ≤ e.creditLimit) :
    (∑ i ∈ intervalGain_indices y, (actualBalanceAt e.after i - actualBalanceAt e.before i)) ≤
      residualCredit (config := config) x high e := by
  rw [intervalGain_residual_deposit x high e deposit]
  have notElectra : ¬ Fork.pectra ≤ e.before.fork := Nat.not_le.mpr before
  have notBefore : ¬ high + 1 < config.ELECTRA_FORK_EPOCH.toNat := by omega
  simp only [notElectra, notBefore, ↓reduceIte]
  exact intervalGain_event_credit y e bounded

private theorem intervalGain_crossing_sources (x y : ForkedBeaconState preset) (high : Nat)
    (events : List (BalanceEvent preset))
    (crossing : config.ELECTRA_FORK_EPOCH.toNat ≤ high + 1)
    (bounded : ∀ e ∈ events, e.credits ≤ e.creditLimit)
    (depositBudget : Nat)
    (deposits : (events.map fun e =>
      if e.source = .deposits ∧ .pectra ≤ e.before.fork then
        ∑ i ∈ intervalGain_indices y, (actualBalanceAt e.after i - actualBalanceAt e.before i)
      else 0).sum ≤ depositBudget) :
    (events.map fun e => ∑ i ∈ intervalGain_indices y,
      (actualBalanceAt e.after i - actualBalanceAt e.before i)).sum ≤
      depositBudget + (events.map (residualCredit (config := config) x high)).sum := by
  have pointwise : ∀ e ∈ events,
      (∑ i ∈ intervalGain_indices y,
        (actualBalanceAt e.after i - actualBalanceAt e.before i)) ≤
      (if e.source = .deposits ∧ .pectra ≤ e.before.fork then
        ∑ i ∈ intervalGain_indices y, (actualBalanceAt e.after i - actualBalanceAt e.before i)
      else 0) + residualCredit (config := config) x high e := by
    intro e member
    by_cases deposit : e.source = .deposits
    · by_cases electra : .pectra ≤ e.before.fork
      · simp only [deposit, electra, and_self, ↓reduceIte]
        omega
      · simp only [deposit, electra, and_false, ↓reduceIte, Nat.zero_add]
        exact intervalGain_preupgrade_credit x y high e deposit (Nat.lt_of_not_le electra) crossing
          (bounded e member)
    · simp only [deposit, false_and, ↓reduceIte, Nat.zero_add]
      rw [intervalGain_residual_other x high e deposit]
      exact intervalGain_event_credit y e (bounded e member)
  have sum := List.sum_le_sum pointwise
  rw [List.sum_map_add] at sum
  omega

private theorem intervalGain_crossing_endpoint {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (early : y.fork < .glamsterdam)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events)
    (crossing : config.ELECTRA_FORK_EPOCH.toNat ≤ high + 1)
    (bounded : ∀ e ∈ events, e.credits ≤ e.creditLimit)
    (deposits : (events.map fun e =>
      if e.source = .deposits ∧ .pectra ≤ e.before.fork then
        ∑ i ∈ intervalGain_indices y, (actualBalanceAt e.after i - actualBalanceAt e.before i)
      else 0).sum ≤ depositWindow (config := config) x high) :
    referenceGain x y ≤ activationWindow (config := config) x high + initialExcess x +
      (events.map (residualCredit (config := config) x high)).sum := by
  have gain := intervalGain_replay_bound shared tail genesis parameters early high endEpoch
    events replayed
  have sources := intervalGain_crossing_sources x y high events crossing bounded
    (depositWindow (config := config) x high) deposits
  unfold activationWindow
  omega

private theorem intervalGain_deposit_epoch {a b y : ForkedBeaconState preset}
    (suffix : Run config checks b y)
    (advanced : (getCurrentEpoch a.state).toNat < (getCurrentEpoch b.state).toNat) :
    (getCurrentEpoch a.state).toNat < (getCurrentEpoch y.state).toNat := by
  have monotone : (getCurrentEpoch b.state).toNat ≤ (getCurrentEpoch y.state).toNat := by
    induction suffix with
    | nil => exact Nat.le_refl _
    | snoc pre step ih => exact ih.trans (coverage_step_epoch step)
  exact advanced.trans_le monotone

private theorem intervalGain_deposit_filter_sum (y : ForkedBeaconState preset)
    (parameters : Parameters preset) (events : List (BalanceEvent preset))
    (sites : ∀ e ∈ events, e.source = .deposits → .pectra ≤ e.before.fork →
      (∀ i, actualBalanceAt e.after i ≤ actualBalanceAt e.before i) ∨
      (RegistryLifecycle e.before.state y.state ∧ ExitsOrdered e.before.state ∧
        (getCurrentEpoch e.before.state).toNat < (getCurrentEpoch y.state).toNat ∧
        BalancesMatch e.after.state)) :
    (events.map fun e => if e.source = .deposits ∧ .pectra ≤ e.before.fork then
      ∑ i ∈ intervalGain_indices y, (actualBalanceAt e.after i - actualBalanceAt e.before i)
      else 0).sum ≤
    (events.map fun e => if e.source = .deposits ∧ .pectra ≤ e.before.fork then
      ∑ i ∈ Finset.range e.after.state.validators.data.size,
        if (e.before.state.validators.data[i]?.map (fun v =>
          decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch e.before.state).toNat))).getD
          false then 0 else actualBalanceAt e.after i - actualBalanceAt e.before i
      else 0).sum := by
  apply List.sum_le_sum
  intro e member
  split
  · rename_i selected
    rcases sites e member selected.1 selected.2 with zero | ⟨kept, ordered, later, matched⟩
    · simp only [Nat.sub_eq_zero_of_le (zero _), Finset.sum_const_zero, Nat.zero_le]
    · exact intervalGain_selected_deposit y parameters e kept ordered later matched
  · exact Nat.le_refl _

private theorem intervalGain_deposit_sites {x y : ForkedBeaconState preset}
    (events : List (BalanceEvent preset))
    (provenance : ∀ e ∈ events,
      RegistryLifecycle x.state e.before.state ∧
      RegistryLifecycle e.before.state e.after.state ∧
      RegistryLifecycle e.after.state y.state ∧
      ExitsOrdered e.before.state ∧ BalancesMatch e.after.state ∧
      (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch e.before.state).toNat ∧
      (getCurrentEpoch e.before.state).toNat ≤ (getCurrentEpoch y.state).toNat)
    (epochs : ∀ e ∈ events, e.source = .deposits → .pectra ≤ e.before.fork →
      (∀ i, actualBalanceAt e.after i ≤ actualBalanceAt e.before i) ∨
      (getCurrentEpoch e.before.state).toNat < (getCurrentEpoch y.state).toNat) :
    ∀ e ∈ events, e.source = .deposits → .pectra ≤ e.before.fork →
      (∀ i, actualBalanceAt e.after i ≤ actualBalanceAt e.before i) ∨
      (RegistryLifecycle e.before.state y.state ∧ ExitsOrdered e.before.state ∧
        (getCurrentEpoch e.before.state).toNat < (getCurrentEpoch y.state).toNat ∧
        BalancesMatch e.after.state) := by
  intro e member deposit electra
  rcases epochs e member deposit electra with zero | later
  · exact Or.inl zero
  · obtain ⟨_, first, last, ordered, matched, _⟩ := provenance e member
    exact Or.inr ⟨first.trans last, ordered, later, matched⟩

private theorem intervalGain_crossing_of_interfaces {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (early : y.fork < .glamsterdam)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events)
    (crossing : config.ELECTRA_FORK_EPOCH.toNat ≤ high + 1)
    (bounded : ∀ e ∈ events, e.credits ≤ e.creditLimit)
    (provenance : ∀ e ∈ events,
      RegistryLifecycle x.state e.before.state ∧
      RegistryLifecycle e.before.state e.after.state ∧
      RegistryLifecycle e.after.state y.state ∧
      ExitsOrdered e.before.state ∧ BalancesMatch e.after.state ∧
      (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch e.before.state).toNat ∧
      (getCurrentEpoch e.before.state).toNat ≤ (getCurrentEpoch y.state).toNat)
    (epochs : ∀ e ∈ events, e.source = .deposits → .pectra ≤ e.before.fork →
      (∀ i, actualBalanceAt e.after i ≤ actualBalanceAt e.before i) ∨
      (getCurrentEpoch e.before.state).toNat < (getCurrentEpoch y.state).toNat)
    (capacity : (events.map fun e => if e.source = .deposits ∧ .pectra ≤ e.before.fork then
      ∑ i ∈ Finset.range e.after.state.validators.data.size,
        if (e.before.state.validators.data[i]?.map (fun v =>
          decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch e.before.state).toNat))).getD
          false then 0 else actualBalanceAt e.after i - actualBalanceAt e.before i
      else 0).sum ≤ depositWindow (config := config) x high) :
    referenceGain x y ≤ activationWindow (config := config) x high + initialExcess x +
      (events.map (residualCredit (config := config) x high)).sum := by
  apply intervalGain_crossing_endpoint shared tail genesis parameters early high endEpoch
    events replayed crossing bounded
  exact (intervalGain_deposit_filter_sum y parameters events
    (intervalGain_deposit_sites events provenance epochs)).trans capacity

private theorem intervalGain_joining_split (x y : ForkedBeaconState preset)
    (newBound carryBound : Nat)
    (newKeys : Quorum.weight (effectiveWeight y.state)
      (recentKeys y.state \ recentKeys x.state) ≤ newBound)
    (oldKeys : Quorum.weight (effectiveWeight y.state)
      ((recentKeys y.state ∩ recentKeys x.state) \ activeKeys x.state) ≤ carryBound) :
    Quorum.weight (effectiveWeight y.state) (recentKeys y.state \ activeKeys x.state) ≤
      newBound + carryBound := by
  have active : activeKeys x.state ⊆ recentKeys x.state := by
    intro k member
    exact Finset.mem_union_left _ member
  have partition : recentKeys y.state \ activeKeys x.state =
      (recentKeys y.state \ recentKeys x.state) ∪
        ((recentKeys y.state ∩ recentKeys x.state) \ activeKeys x.state) := by
    ext k
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro ⟨recent, inactive⟩
      by_cases old : k ∈ recentKeys x.state
      · exact Or.inr ⟨⟨recent, old⟩, inactive⟩
      · exact Or.inl ⟨recent, old⟩
    · rintro (⟨recent, fresh⟩ | ⟨⟨recent, _⟩, inactive⟩)
      · exact ⟨recent, fun h => fresh (active h)⟩
      · exact ⟨recent, inactive⟩
  have disjoint : Disjoint (recentKeys y.state \ recentKeys x.state)
      ((recentKeys y.state ∩ recentKeys x.state) \ activeKeys x.state) := by
    apply Finset.disjoint_left.mpr
    intro k first last
    exact (Finset.mem_sdiff.mp first).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp last).1).2
  unfold Quorum.weight at *
  rw [partition, Finset.sum_union disjoint]
  exact Nat.add_le_add newKeys oldKeys

/-- Funding churn bounds Electra deposits that can contribute to recent voting stake.

Withdrawn-key exceptions do not reactivate an exited validator and contribute no such stake. -/
theorem gains_and_activations_over_interval {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (withdrawalDelay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    referenceGain x y ≤
      activationWindow (config := config) x high + initialExcess x +
        (events.map (residualCredit (config := config) x high)).sum := by
  sorry

/-- A conservative source envelope, separate from the exact observed-state drift.

The boundary term is supplied by boundaryWindow, not by the cumulative exit envelope.

Queue, registry and rounding bounds still need tighter transition proofs. -/
def sourceDrift (x : ForkedBeaconState preset) (high boundary : Nat)
    (events : List (BalanceEvent preset)) : Nat :=
  2 * (exitWindow (config := config) x high events + lossCorrection x events) +
    activationWindow (config := config) x high + initialExcess x +
    (events.map (residualCredit (config := config) x high)).sum + 2 * boundary

/-- Extending a replay prefix and its boundary budget cannot shrink the source envelope. -/
theorem sourceDrift_le_of_prefix (x : ForkedBeaconState preset) (high : Nat)
    {before after : List (BalanceEvent preset)} (initial : before <+: after)
    {first last : Nat} (boundary : first ≤ last) :
    sourceDrift (config := config) x high first before ≤
      sourceDrift (config := config) x high last after := by
  have sums (f : BalanceEvent preset → Nat) : (before.map f).sum ≤ (after.map f).sum := by
    obtain ⟨rest, rfl⟩ := initial
    simp only [List.map_append, List.sum_append]
    omega
  have loss : lossCorrection x before ≤ lossCorrection x after := by
    apply List.sum_le_sum
    intro i _
    cases found : x.state.validators.data[i.toNat]? with
    | none => simp
    | some v =>
      cases slashed : v.slashed with
      | true => simp [slashed]
      | false =>
        simp only [slashed, Bool.false_eq_true, ↓reduceIte]
        have monotone := sums (referenceDebit i.toNat)
        split <;> split <;> omega
  have active : activeStakeWindow (config := config) x high before ≤
      activeStakeWindow (config := config) x high after := by
    unfold activeStakeWindow
    split
    · have monotone := sums fundingCredit
      omega
    · exact Nat.le_refl _
  have rates : consolidationRate (preset := preset) (config := config)
      (activeStakeWindow (config := config) x high before) ≤
      consolidationRate (preset := preset) (config := config)
        (activeStakeWindow (config := config) x high after) :=
    Nat.sub_le_sub_right (max_le_max_left _
      (Nat.div_le_div_right (max_le_max_left _ active))) _
  have exits : exitWindow (config := config) x high before ≤
      exitWindow (config := config) x high after := by
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_left rates _)) _
  have credits := sums (residualCredit (config := config) x high)
  unfold sourceDrift
  omega

/-- The source envelope is a derived upper bound, not the definition of the safety loss. -/
theorem derivedDrift_le_sources {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (withdrawalDelay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (early : y.fork < .glamsterdam) (high : Nat)
    (startEpoch : (getCurrentEpoch x.state).toNat ≤ high + 1) :
    ∃ events, tail.balanceEvents high = .ok events ∧
      derivedDrift high tail ≤
        sourceDrift (config := config) x high (boundaryWindow high tail) events := by
  obtain ⟨events, replayed, bounds⟩ :=
    source_bounds_over_interval shared tail genesis parameters caps aligned early high
  clear bounds
  refine ⟨events, replayed, ?_⟩
  have atState {y : ForkedBeaconState preset} (run : Run config checks x y)
      (early : y.fork < .glamsterdam)
      (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
      (events : List (BalanceEvent preset)) (replayed : run.balanceEvents high = .ok events) :
      stateDrift x y ≤ sourceDrift (config := config) x high (boundaryStake y) events := by
    have losses := nonaccountable_losses_over_interval shared run genesis parameters caps
      aligned early high within events replayed
    have gains := gains_and_activations_over_interval shared run genesis parameters caps
      aligned withdrawalDelay early high within events replayed
    unfold stateDrift sourceDrift
    omega
  induction tail generalizing events with
  | nil => exact atState .nil early startEpoch events replayed
  | @snoc middle last pre step ih =>
    have beforeFork : middle.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt step.chainStep.fork_le early
    obtain ⟨prior, priorOk, initial⟩ := pre.balanceEvents_prefix
      (Run.nil.snoc step) high events replayed
    have before := ih beforeFork prior priorOk
    have budget := sourceDrift_le_of_prefix (config := config) x high initial
      (first := boundaryWindow high pre) (last := boundaryWindow high (pre.snoc step))
      (by simp only [boundaryWindow]; split <;> omega)
    have past := Nat.le_trans before budget
    simp only [derivedDrift, boundaryWindow]
    split
    · rename_i within
      simp only [boundaryWindow, within, ↓reduceIte] at past
      have current := atState (pre.snoc step) early within events replayed
      have enlarged := sourceDrift_le_of_prefix (config := config) x high
        (List.prefix_refl events) (Nat.le_max_right (boundaryWindow high pre) (boundaryStake last))
      exact max_le past (current.trans enlarged)
    · rename_i beyond
      simpa only [boundaryWindow, beyond, ↓reduceIte] using past

/-- Cache-preserving epoch calls inherit the exact budget of their selected prefix. -/
theorem quorum_drift_from_run {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (withdrawalDelay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (early : y.fork < .glamsterdam) (low high : Nat)
    (starts : x.state.slot.toNat ≤ low * preset.SLOTS_PER_EPOCH.toNat)
    (call : QuorumCall (shared.append tail))
    (lower : low ≤ call.target.epoch.toNat) (upper : call.target.epoch.toNat ≤ high) :
    ∃ loss gain outside,
        (∑ k ∈ (activeKeys x.state).filter (fun k => ¬ (shared.append tail).SlashingEvidence k),
          (effectiveWeight x.state k - Quorum.supported (recentKeys call.cached)
            (effectiveWeight call.cached) k)) ≤ loss ∧
        (∑ k ∈ recentKeys call.cached, (effectiveWeight call.cached k -
          Quorum.supported (activeKeys x.state)
            (effectiveWeight x.state) k)) ≤ gain ∧
        Quorum.weight (effectiveWeight call.cached)
          (recentKeys call.cached \ activeKeys call.cached) ≤ outside ∧
        2 * loss + gain + 2 * outside ≤ derivedDrift high tail := by
  classical
  have _ := caps
  have _ := aligned
  have _ := withdrawalDelay
  have member := call_after_reference shared tail parameters low starts call lower
  obtain ⟨pre, post, split⟩ := tail.contains_split (.slot call.advanced) member
  let before := call.before
  have cachedSlot := (frame_processSlot call.cachedOk).slot
  obtain ⟨_, _, _, _, validators, _⟩ := call.toEpochCall.selected_prefix
  have epochBound : (getCurrentEpoch before.state).toNat ≤ high + 1 := by
    have target : (getCurrentEpoch call.cached).toNat ≤ call.target.epoch.toNat + 1 := by
      rw [call.targetEpoch]
      cases call.current <;> simp [getPreviousEpoch_toNat]
      omega
    have epoch : getCurrentEpoch call.cached = getCurrentEpoch before.state := by
      simp only [getCurrentEpoch, cachedSlot, before]
    rw [epoch] at target
    omega
  have observed {z : ForkedBeaconState preset} (run : Run config checks x z)
      (bounded : (getCurrentEpoch z.state).toNat ≤ high + 1) :
      stateDrift x z ≤ derivedDrift high run := by
    cases run with
    | nil => exact Nat.le_refl _
    | snoc pre step => simp only [derivedDrift, ite_eq_left bounded]; exact Nat.le_max_right _ _
  have monotone {u v : ForkedBeaconState preset} (run : Run config checks x u)
      (rest : Run config checks u v) :
      derivedDrift high run ≤ derivedDrift high (run.append rest) := by
    induction rest with
    | nil => exact Nat.le_refl _
    | snoc rest step ih =>
      simp only [Run.append, derivedDrift]
      split
      · exact ih.trans (Nat.le_max_left _ _)
      · exact ih
  have budget : stateDrift x before ≤ derivedDrift high tail := by
    rw [split]
    apply (observed pre epochBound).trans
    apply le_trans (b := derivedDrift high (pre.snoc (.slot call.advanced)))
    · simp only [derivedDrift]
      split
      · exact Nat.le_max_left _ _
      · exact Nat.le_refl _
    · exact monotone _ post
  have evidence (k) (h : (shared.append pre).SlashingEvidence k) :
      (shared.append tail).SlashingEvidence k := by
    obtain ⟨u, v, step, inside, slashed⟩ := h
    refine ⟨u, v, step, ?_, slashed⟩
    rcases (shared.contains_append pre step).mp inside with inside | inside
    · exact (shared.contains_append tail step).mpr (.inl inside)
    · apply (shared.contains_append tail step).mpr
      right
      rw [split]
      exact ((pre.snoc (.slot call.advanced)).contains_append post step).mpr
        (.inl (.earlier inside _))
  have earlyBefore : before.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps
      ((Run.nil.snoc (.slot call.advanced)).append post).chainSteps) early
  have lossBound : (∑ k ∈ (activeKeys x.state).filter
      (fun k => ¬ (shared.append tail).SlashingEvidence k),
      (effectiveWeight x.state k - Quorum.supported (recentKeys before.state)
        (effectiveWeight before.state) k)) ≤ referenceLoss x before := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      obtain ⟨active, absent⟩ := Finset.mem_filter.mp hk
      refine Finset.mem_filter.mpr ⟨active, ?_⟩
      rintro ⟨v, found, key, slashed⟩
      exact absent (evidence k (key ▸
        (shared.append pre).slashed_evidence genesis earlyBefore v found slashed))
    · intros; exact Nat.zero_le _
  refine ⟨referenceLoss x before, referenceGain x before, boundaryStake before, ?_, ?_, ?_,
    budget⟩
  all_goals
    have weight : effectiveWeight call.cached = effectiveWeight before.state := by
      funext k
      simp only [effectiveWeight, validators, before]
    have active : activeKeys call.cached = activeKeys before.state := by
      simp only [activeKeys, keysAt, getActiveValidatorIndices, getCurrentEpoch,
        validators, cachedSlot, before]
      rfl
    have recent : recentKeys call.cached = recentKeys before.state := by
      simp only [recentKeys, active, keysAt, getActiveValidatorIndices, getPreviousEpoch,
        getCurrentEpoch, validators, cachedSlot, before]
      rfl
  · simpa only [weight, recent] using lossBound
  · exact (congrArg₂ (fun s w => ∑ k ∈ s,
        (w k - Quorum.supported (activeKeys x.state) (effectiveWeight x.state) k))
        recent weight).le
  · exact (congrArg₂ (fun w s => Quorum.weight w s) weight
      (congrArg₂ (· \ ·) recent active)).le

end

end EthLib.Consensus.DirectSafety
