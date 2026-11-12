module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Trace
import Mathlib.Tactic.FinCases

/-! Voting deadlines and boundary processing for the short execution.

The schedule meets the honest-duty assumptions used by arXiv 2405.00549v4, Sections 2 and 4.

The slot-zero deadline precedes the execution; the three later assigned honest duties all vote. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.FiveValidatorWitness.Trace

open Base Base.Uint64

/-- A successful time computation has the exact natural-number value, without wraparound. -/
theorem time_at_slot {slot : Slot} {time : UInt64}
    (read : computeTimeAtSlotMs config 0 slot = .ok time) : time.toNat = slot.toNat * 1000 := by
  simp only [computeTimeAtSlotMs, bind_ok_iff] at read
  obtain ⟨offset, multiplied, added⟩ := read
  have mul := (mulChecked_ok_iff.mp multiplied).2
  have add := (addChecked_ok_iff.mp added).2
  change offset.toNat = slot.toNat * 1000 at mul
  change time.toNat = 0 + offset.toNat at add
  omega

/-- The 333-millisecond attestation deadline and one-millisecond delay fit before the boundary. -/
theorem delay_fits : DelayFits .phase0 config 0 1 := by
  have dueOk : getAttestationDueMs config .phase0 = .ok 333 := rfl
  refine ⟨⟨333, dueOk⟩, ?_⟩
  intro slot next start due following nextOk startOk dueRead followingOk
  rw [dueOk, Except.ok.injEq] at dueRead
  subst due
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  rw [time_at_slot startOk, time_at_slot followingOk, nextNat]
  change slot.toNat * 1000 + 333 + 1 < (slot.toNat + 1) * 1000
  omega

/-- A decidable certificate of clock agreement and processing completeness. -/
def ReadySnapshot (w : Snapshot) (v : ValidatorIndex) : Prop :=
  match w.state v with
  | .running time count => w.time = time.toNat ∧ count ≤ 3 ∧ Ready time count (w.view v)
  | _ => False

instance (w : Snapshot) (v : ValidatorIndex) : Decidable (ReadySnapshot w v) := by
  unfold ReadySnapshot
  cases w.state v <;> infer_instance

/-- Interpreting a ready snapshot gives the original protocol's processing predicate. -/
theorem ready_snapshot {w : Snapshot} {v : ValidatorIndex} (ready : ReadySnapshot w v) :
    UpToDate config .acceptAll sources w.world.time (w.world.view v) (w.world.state v) := by
  cases eq : w.state v with
  | anchor => simp [ReadySnapshot, eq] at ready
  | ticked => simp [ReadySnapshot, eq] at ready
  | running time count =>
    simp only [ReadySnapshot, eq] at ready
    change UpToDate _ _ _ w.time _ (w.state v).store
    rw [eq, ready.1]
    exact running_up_to_date time ready.2.1 (ready_view ready.2.2)

/-- The four snapshots after all honest stores finish processing at a slot boundary. -/
def boundaryIndex (i : Fin 4) : Nat := 10 + 21 * i.val

/-- The three snapshots after all honest stores finish processing before the next boundary. -/
def beforeIndex (i : Fin 3) : Nat := 22 + 21 * i.val

/-- Every honest validator is ready at each boundary within the horizon. -/
theorem boundary_certificate : ∀ i : Fin 4, ∀ v : Fin 5, v.val.toUInt64 ∈ honest →
    (snapshot (boundaryIndex i)).time = (i.val + 1) * 1000 ∧
      ReadySnapshot (snapshot (boundaryIndex i)) v.val.toUInt64 := by
  decide +kernel

/-- Every honest validator is also ready one millisecond before each later boundary. -/
theorem before_certificate : ∀ i : Fin 3, ∀ v : Fin 5, v.val.toUInt64 ∈ honest →
    (snapshot (beforeIndex i)).time + 1 = (i.val + 2) * 1000 ∧
      ReadySnapshot (snapshot (beforeIndex i)) v.val.toUInt64 := by
  decide +kernel

/-- The finite certificates cover every boundary requested by the processing premise. -/
theorem prompt : Prompt execution 4000 := by
  intro w own slot start startOk started bounded
  have timeEq := time_at_slot startOk
  have low : 1 ≤ slot.toNat := by change 1000 ≤ start.toNat at started; omega
  have high : slot.toNat ≤ 4 := by omega
  obtain ⟨v, rfl⟩ := honest_index own
  constructor
  · let i : Fin 4 := ⟨slot.toNat - 1, by omega⟩
    have within : boundaryIndex i ≤ 73 := by dsimp [boundaryIndex, i]; omega
    refine ⟨boundaryIndex i, ?_, ?_⟩
    · rw [world_prefix _ within]
      have atTime := (boundary_certificate i v own).1
      change (snapshot (boundaryIndex i)).time = _
      rw [atTime, timeEq]
      congr 1
      change slot.toNat - 1 + 1 = slot.toNat
      omega
    · rw [world_prefix _ within]
      exact ready_snapshot (boundary_certificate i v own).2
  · intro strict
    have low : 2 ≤ slot.toNat := by change 1000 < start.toNat at strict; omega
    let i : Fin 3 := ⟨slot.toNat - 2, by omega⟩
    have within : beforeIndex i ≤ 73 := by dsimp [beforeIndex, i]; omega
    refine ⟨beforeIndex i, ?_, ?_⟩
    · rw [world_prefix _ within]
      have atTime := (before_certificate i v own).1
      change (snapshot (beforeIndex i)).time + 1 = _
      rw [atTime, timeEq]
      congr 1
      change slot.toNat - 2 + 2 = slot.toNat
      omega
    · rw [world_prefix _ within]
      exact ready_snapshot (before_certificate i v own).2

/-- The late-margin obligation is vacuous between this call and the execution's limit.

No whole epoch can start at or after time 3000 and finish by time 4000. -/
theorem no_complete_epoch {last : Nat} (bounded : last ≤ 4000) :
    ¬CompleteEpochWithin preset config 0 3000 last := by
  rintro ⟨epoch, first, next, start, stop, firstOk, nextOk, startOk, stopOk, after, before⟩
  have startNat := time_at_slot startOk
  have stopNat := time_at_slot stopOk
  have firstNat := (computeStartSlotAtEpoch_ok_iff.mp firstOk).2
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  change first.toNat = epoch.toNat * 4 at firstNat
  change next.toNat = first.toNat + 4 at nextNat
  omega

/-- Each candidate vote's target state is already cached. -/
theorem running_target_cached (time : UInt64) (count : Nat) (slot : Slot) :
    (running time count).storeTargetCheckpointState config .acceptAll (vote slot).data.target =
      .ok (running time count) := by
  simp [Store.storeTargetCheckpointState, running, admitted, ticked, anchor,
    vote, voteData, Checkpoint.compare, pure, Except.pure]

/-- The cached target state is the unchanged source of balances. -/
theorem running_target_state (time : UInt64) (count : Nat) (slot : Slot) :
    (running time count).checkpointState (vote slot).data.target = .ok (state bodyRoot) := by
  simp [Store.checkpointState, running, admitted, ticked, anchor, vote, voteData,
    pure, Except.pure]

/-- Each nonzero assigned slot has an actual honest send with the required vote reads. -/
theorem vote_at {slot : Slot} (within : slot = 1 ∨ slot = 2 ∨ slot = 3) :
    VoteAt execution (voter slot) slot 0 (slot * 1000 + 333).toNat
      (15 + 21 * (slot.toNat - 1)) (vote slot) (indexedVote slot) := by
  let n := 15 + 21 * (slot.toNat - 1)
  have bound : n ≤ 73 := by rcases within with rfl | rfl | rfl <;> decide
  have storeEq : (execution.world n).state (voter slot) =
      running (slot * 1000 + 333) (slot.toNat - 1) := by
    rw [world_prefix _ bound]
    rcases within with rfl | rfl | rfl <;> rfl
  have count : slot.toNat - 1 ≤ 3 := by rcases within with rfl | rfl | rfl <;> decide
  have clock : (running (slot * 1000 + 333) (slot.toNat - 1)).getCurrentStoreEpoch config =
      .ok 0 := by
    rw [Store.getCurrentStoreEpoch, running_clock]
    rcases within with rfl | rfl | rfl <;> rfl
  have timeEq : (execution.world n).time = (slot * 1000 + 333).toNat := by
    rw [world_prefix _ bound]
    rcases within with rfl | rfl | rfl <;> rfl
  refine ⟨?_, timeEq, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · rcases within with rfl | rfl | rfl <;> rfl
  · change ((execution.world n).state (voter slot)).genesisTimeMs = 0
    rw [storeEq]
    rfl
  · rw [← timeEq, world_prefix _ bound]
    apply ready_snapshot
    rcases within with rfl | rfl | rfl <;> decide +kernel
  · change HonestVoteData _ _ ((execution.world n).state (voter slot)) _ _ _
    rw [storeEq]
    exact running_vote_data _ _ count within clock (.inl rfl)
  · change ReadsAttestation _ _ ((execution.world n).state (voter slot)) _ _
    rw [storeEq]
    exact ⟨_, _, running_target_cached _ _ slot, running_target_state _ _ slot,
      vote_indexed within, vote_signature within⟩
  · intro withTarget target cached targetOk
    change ((execution.world n).state (voter slot)).storeTargetCheckpointState _ _ _ = _ at cached
    rw [storeEq, running_target_cached, Except.ok.injEq] at cached
    subst withTarget
    rw [running_target_state, Except.ok.injEq] at targetOk
    subst target
    exact vote_committees within

/-- Every honest duty whose deadline is inside the execution's horizon votes. -/
theorem votes : Votes execution.startTime 4000 execution := by
  intro v own slot index time assigned deadline started _ _
  obtain ⟨start, due, startOk, dueOk, timeEq⟩ := deadline
  have dueValue : getAttestationDueMs config .phase0 = .ok 333 := rfl
  rw [dueValue, Except.ok.injEq] at dueOk
  subst due
  have timeNat := time_at_slot startOk
  simp only [assignment] at assigned
  split at assigned
  · rename_i assignedSlot
    obtain ⟨_, rfl⟩ := assignedSlot
    cases assigned
    simp only [honest, Set.mem_insert_iff, Set.mem_singleton_iff] at own
    rcases own with rfl | rfl | rfl | rfl
    · change 1000 ≤ time at started
      change start.toNat = 0 at timeNat
      change time = start.toNat + 333 at timeEq
      omega
    · have same : time = (1 * 1000 + 333 : UInt64).toNat := by
        change start.toNat = 1000 at timeNat
        change time = start.toNat + 333 at timeEq
        change time = 1333
        omega
      rw [same]
      exact ⟨_, _, _, vote_at (.inl rfl)⟩
    · have same : time = (2 * 1000 + 333 : UInt64).toNat := by
        change start.toNat = 2000 at timeNat
        change time = start.toNat + 333 at timeEq
        change time = 2333
        omega
      rw [same]
      exact ⟨_, _, _, vote_at (.inr (.inl rfl))⟩
    · have same : time = (3 * 1000 + 333 : UInt64).toNat := by
        change start.toNat = 3000 at timeNat
        change time = start.toNat + 333 at timeEq
        change time = 3333
        omega
      rw [same]
      exact ⟨_, _, _, vote_at (.inr (.inr rfl))⟩
  · contradiction

end EthLib.Consensus.Models.Network.FiveValidatorWitness.Trace
