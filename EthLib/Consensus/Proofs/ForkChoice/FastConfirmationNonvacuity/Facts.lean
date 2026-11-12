module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Trace
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Bounds
import Mathlib.Tactic.FinCases

/-! State, stake, admission and checkpoint premises for the short execution.

These certificates concern Theorem 1 of arXiv 2405.00549v4, Section 4.

Every counted state is the anchor, its slot-one advance, or the child's post-state.

All three have the same active registry, balances, and slashing flags. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.EightValidatorWitness.Trace

open Base

set_option maxRecDepth 10000 in
/-- The increasing wait tail is already past the horizon after event 159. -/
theorem bounded_index {n : Nat} (bounded : (execution.world n).time ≤ 4000) : n ≤ 159 := by
  exact FinitePrefix.index_le_length_of_time_le events 4000
    (World.initial 1000 (fun _ => anchor)) final_clock n bounded

/-- Every store before the limit has one of the certified finite-prefix shapes. -/
theorem store_code {n : Nat} (bounded : (execution.world n).time ≤ 4000) (v : ValidatorIndex) :
    ∃ code : Local, (execution.world n).state v = code.store := by
  rw [world_prefix n (bounded_index bounded)]
  exact ⟨(snapshot n).state v, rfl⟩

/-- A held block is either the common anchor or the single broadcast child. -/
theorem local_block {code : Local} {root : Root} {block : BeaconBlock preset .phase0}
    (held : code.store.blocks[root]? = some block) :
    (root = anchorRoot ∧ block = anchorBlock stateRoot) ∨
    (root = blockRoot ∧ block = signedBlock.message) := by
  cases code <;>
    simp only [Local.store, running, admitted, ticked, anchor, getElem?_insert_root] at held
  all_goals
    split at held
    · subst root
      cases held
      first | exact .inl ⟨rfl, rfl⟩ | exact .inr ⟨rfl, rfl⟩
    · first
      | contradiction
      | split at held
        · subst root; cases held; exact .inl ⟨rfl, rfl⟩
        · contradiction

/-- The two stored block states have the same registry and epoch. -/
theorem local_block_state {code : Local} {root : Root} {s : BeaconState preset .phase0}
    (held : code.store.blockStates[root]? = some s) :
    (root = anchorRoot ∧ s = state bodyRoot) ∨ (root = blockRoot ∧ s = postState) := by
  cases code <;>
    simp only [Local.store, running, admitted, ticked, anchor, getElem?_insert_root] at held
  all_goals
    split at held
    · subst root
      cases held
      first | exact .inl ⟨rfl, rfl⟩ | exact .inr ⟨rfl, rfl⟩
    · first
      | contradiction
      | split at held
        · subst root; cases held; exact .inl ⟨rfl, rfl⟩
        · contradiction

/-- All successful checkpoint-state reads return the initial state. -/
theorem local_checkpoint {code : Local} {checkpoint : Checkpoint}
    {s : BeaconState preset .phase0} (read : code.store.checkpointState checkpoint = .ok s) :
    s = state bodyRoot := by
  cases code <;>
    simp only [Local.store, running, admitted, ticked, anchor,
      Store.checkpointState, Std.TreeMap.getElem?_insert] at read <;>
    split at read <;> simp_all [pure, Except.pure]

/-- Both held blocks carry their kernel-certified nonzero state roots. -/
theorem nonzero : ∀ w ∈ honest, ∀ k, (execution.world k).time ≤ 4000 →
    ∀ (root : Root) (block : BeaconBlock preset .phase0),
      ((execution.world k).state w).blocks[root]? = some block →
      block.stateRoot ≠ Vector.replicate 32 0 := by
  intro w _ k bounded root block held
  obtain ⟨code, eq⟩ := store_code bounded w
  rw [eq] at held
  rcases local_block held with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact stateRoot_ne_zero
  · exact postRoot_ne_zero

/-- No store holds a block at the anchor's zero parent root. -/
theorem anchor_parent : ∀ w ∈ honest, ∀ k, (execution.world k).time ≤ 4000 →
    ((execution.world k).state w).blocks[(anchorBlock stateRoot).parentRoot]? = none := by
  intro w _ k bounded
  obtain ⟨code, eq⟩ := store_code bounded w
  rw [eq]
  cases found : code.store.blocks[(anchorBlock stateRoot).parentRoot]? with
  | none => rfl
  | some block =>
    rcases local_block found with ⟨root, _⟩ | ⟨root, _⟩
    · exact False.elim (anchorRoot_ne_zero root.symm)
    · exact False.elim (blockRoot_ne_zero root.symm)

/-- Every checkpoint read has 1600 Gwei of active stake, below the approved supply cap. -/
theorem supply : ∀ w ∈ honest, ∀ k checkpoint s, (execution.world k).time ≤ 4000 →
    ((execution.world k).state w).checkpointState checkpoint = .ok s →
      ActiveStakeAtMost stakeCapGwei s := by
  intro w _ k checkpoint s bounded read
  obtain ⟨code, eq⟩ := store_code bounded w
  rw [eq] at read
  rw [local_checkpoint read]
  change stake (fun v => balanceAt (state bodyRoot) v.toNat) (activeVoters (state bodyRoot)) ≤ _
  rw [(stakes bodyRoot).1]
  decide

/-- The store clocks cannot exceed epoch one before the limit. -/
theorem in_horizon : ∀ w ∈ honest, ∀ k epoch, (execution.world k).time ≤ 4000 →
    ((execution.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ 1 := by
  intro w _ k epoch bounded clock
  have bounds := execution.clock_bounds w k
  have genesis : ((execution.world k).state w).genesisTimeMs = 0 := bounds.1
  have upper : ((execution.world k).state w).timeMs.toNat ≤ (execution.world k).time := by
    simpa only [show (execution.start w).timeMs.toNat = 0 from rfl, Nat.zero_max] using bounds.2.2
  exact UInt64.le_iff_toNat_le.mpr (current_epoch_le_one genesis (upper.trans bounded) clock)

/-- The descendant-relative target-inclusion premise holds only vacuously here.

Its guard requires a receiver two epochs after a target; receivers reach at most epoch one. -/
theorem included : TargetIncluded execution 4000 :=
  target_included execution (fun _ _ => rfl)

/-- The first empty slot reads no signature, regardless of the supplied signature checks. -/
theorem first_slot_any (checks : SignatureChecks) :
    processSlots config checks (state bodyRoot) 1 = .ok advanced := by
  have emptyHeader : (state bodyRoot).latestBlockHeader.stateRoot = Vector.replicate 32 0 := rfl
  change advanceSlots config checks 1 (state bodyRoot) = .ok advanced
  simp only [advanceSlots, advanceSlot, epochIfLast, processSlot,
    state_root, emptyHeader, ↓reduceIte, initial_header_root, liftSsz, liftAccessor,
    Except.mapError, bind, Except.bind, pure, Except.pure]
  rfl

/-- Counting can advance the anchor only as far as its sole child's slot. -/
theorem local_counts {code : Local} {s : BeaconState preset .phase0}
    (counts : code.store.Counts config s) :
    s = state bodyRoot ∨ s = postState ∨ s = advanced := by
  obtain ⟨root, source, held, rfl | ⟨checks, slot, childRoot, child, childHeld,
    parent, before, processed⟩⟩ := counts
  · rcases local_block_state held with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact .inl rfl
    · exact .inr (.inl rfl)
  · rcases local_block childHeld with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · change Vector.replicate 32 0 = root at parent
      rcases local_block_state held with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact False.elim (anchorRoot_ne_zero parent.symm)
      · exact False.elim (blockRoot_ne_zero parent.symm)
    · change anchorRoot = root at parent
      subst root
      rcases local_block_state held with ⟨_, rfl⟩ | ⟨impossible, _⟩
      · have lower := UInt64.lt_iff_toNat_lt.mp (processSlots_slot processed).1
        have upper := UInt64.le_iff_toNat_le.mp before
        change 0 < slot.toNat at lower
        change slot.toNat ≤ 1 at upper
        have equal : slot = 1 := UInt64.toNat_inj.mp (by change slot.toNat = 1; omega)
        subst slot
        rw [first_slot_any, Except.ok.injEq] at processed
        exact .inr (.inr processed.symm)
      · exact False.elim (blockRoot_ne_anchorRoot impossible.symm)

/-- The execution's counted states are exactly among these three candidates. -/
theorem counts {k : Nat} {w : ValidatorIndex} {s : BeaconState preset .phase0}
    (bounded : (execution.world k).time ≤ 4000)
    (counted : ((execution.world k).state w).Counts config s) :
    s = state bodyRoot ∨ s = postState ∨ s = advanced := by
  obtain ⟨code, eq⟩ := store_code bounded w
  rw [eq] at counted
  exact local_counts counted

/-- A counted state remains in epoch zero even when the store clock reaches epoch one. -/
theorem counted_epoch {k : Nat} {w : ValidatorIndex} {s : BeaconState preset .phase0}
    (bounded : (execution.world k).time ≤ 4000)
    (counted : ((execution.world k).state w).Counts config s) : getCurrentEpoch s = 0 := by
  rcases counts bounded counted with rfl | rfl | rfl <;> rfl

/-- The checked total active balance agrees with the mathematical stake sum. -/
theorem total_balance : getTotalActiveBalance (state bodyRoot) = .ok 1600 := by
  change getTotalBalance (state bodyRoot) [0, 1, 2, 3, 4, 5, 6, 7] = .ok 1600
  rw [getTotalBalance_ok_iff]
  simp only [List.forall_mem_cons, sumMarked_eq_sum, getElem?_markIndices]
  decide

/-- No validator is Byzantine, so the Byzantine stake is within twelve percent. -/
theorem byzantine : ∀ w ∈ honest, ∀ k (s : BeaconState preset .phase0) total,
    (execution.world k).time ≤ 4000 → ((execution.world k).state w).Counts config s →
    (getCurrentEpoch s).toNat ≤ (1 : Epoch).toNat + 1 →
    getTotalActiveBalance s = .ok total →
    100 * stake (fun v => balanceAt s v.toNat) {v ∈ quorumVoters s | v ∉ honest} ≤
      12 * total.toNat := by
  intro w _ k s total bounded counted _ totalOk
  rcases counts bounded counted with rfl | rfl | rfl
  all_goals
    have eq : getTotalActiveBalance (state bodyRoot) = .ok total := totalOk
    rw [total_balance, Except.ok.injEq] at eq
    subst total
    exact byzantine_stake bodyRoot

/-- None of the honest validators is slashed in any counted state. -/
theorem unslashed : ∀ w ∈ honest, ∀ k (s : BeaconState preset .phase0),
    (execution.world k).time ≤ 4000 → ((execution.world k).state w).Counts config s →
    ∀ v ∈ honest, NotSlashed s v := by
  intro w _ k s bounded counted v own
  rcases counts bounded counted with rfl | rfl | rfl
  all_goals
    change NotSlashed (state bodyRoot) v
    obtain ⟨v, rfl⟩ := honest_index own
    fin_cases v <;> rfl

/-- The total active stake exceeds the theorem's minimum relative to one increment. -/
theorem large : ∀ w ∈ honest, ∀ k (s : BeaconState preset .phase0),
    (execution.world k).time ≤ 4000 → ((execution.world k).state w).Counts config s →
    (getCurrentEpoch s).toNat ≤ (1 : Epoch).toNat + 1 →
    3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun v => balanceAt s v.toNat) (activeVoters s) := by
  intro w _ k s bounded counted _
  rcases counts bounded counted with rfl | rfl | rfl
  all_goals
    change 3 * 100 <
      2 * stake (fun v => balanceAt (state bodyRoot) v.toNat) (activeVoters (state bodyRoot))
    rw [(stakes bodyRoot).1]
    decide

/-- The three counted states have the registry of the anchor, all active in epoch zero. -/
theorem counted_active {s : BeaconState preset .phase0}
    (shape : s = state bodyRoot ∨ s = postState ∨ s = advanced) :
    activeVoters s = activeVoters (state bodyRoot) := by
  rcases shape with rfl | rfl | rfl <;> first | rfl | decide

/-- No validator leaves the active set between two counted states, so the exited stake is zero.

The exit reserve of the source bounds it, whatever its value. -/
theorem no_exited_stake {source later : BeaconState preset .phase0}
    (sourceShape : source = state bodyRoot ∨ source = postState ∨ source = advanced)
    (laterShape : later = state bodyRoot ∨ later = postState ∨ later = advanced) :
    stake (fun v => balanceAt source v.toNat)
        {v ∈ activeVoters source | v ∉ activeVoters later} ≤ exitReserve config source := by
  have empty : {v ∈ activeVoters source | v ∉ activeVoters later} = ∅ := by
    rw [counted_active sourceShape, counted_active laterShape]
    exact Finset.filter_false_of_mem fun v held => not_not.mpr held
  rw [empty, stake_empty]
  exact Nat.zero_le _

/-- The restricted trace and the certified distinct roots give cross-store block agreement. -/
theorem one_block : OneBlockPerRoot execution 4000 := by
  intro v _ w _ n k nb kb root first second firstHeld secondHeld
  obtain ⟨nc, ne⟩ := store_code nb v
  obtain ⟨kc, ke⟩ := store_code kb w
  rw [ne] at firstHeld
  rw [ke] at secondHeld
  rcases local_block firstHeld with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases local_block secondHeld with ⟨same, rfl⟩ | ⟨same, rfl⟩
  · rfl
  · exact False.elim (blockRoot_ne_anchorRoot same.symm)
  · exact False.elim (blockRoot_ne_anchorRoot same)
  · rfl

/-- Neither block introduces a positive-epoch unrealized justification. -/
theorem local_unrealized_epoch {code : Local} {root : Root} {cp : Checkpoint}
    (held : code.store.unrealizedJustifications[root]? = some cp) : cp.epoch = 0 := by
  cases code <;>
    simp only [Local.store, running, admitted, ticked, anchor, getElem?_insert_root] at held
  all_goals
    split at held
    · cases held; rfl
    · first
      | contradiction
      | split at held
        · cases held; rfl
        · contradiction

/-- Only the store's anchor checkpoint is justified, not the raw state's zero checkpoint. -/
theorem local_justified {code : Local} {cp : Checkpoint}
    (justified : code.store.Justified cp) : cp = ⟨0, anchorRoot⟩ := by
  rcases justified with rfl | rfl | ⟨positive, ⟨root, s, held, rfl⟩ | ⟨root, held⟩⟩
  · cases code <;> rfl
  · cases code <;> rfl
  · rcases local_block_state held with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> contradiction
  · rw [local_unrealized_epoch held] at positive
    contradiction

/-- All justified checkpoints agree, independently of which honest store observes them. -/
theorem unique : OneJustifiedPerEpoch execution 1 4000 := by
  intro u _ w _ n k nb kb first second fj sj _ _
  obtain ⟨nc, ne⟩ := store_code nb u
  obtain ⟨kc, ke⟩ := store_code kb w
  rw [ne] at fj
  rw [ke] at sj
  exact (local_justified fj).trans (local_justified sj).symm

/-- Every store retains the anchor entry. -/
theorem local_anchor (code : Local) : code.store.blocks[anchorRoot]? =
    some (anchorBlock stateRoot) := by
  cases code with
  | anchor => simp [Local.store, anchor]
  | ticked => simp [Local.store, ticked, anchor]
  | running time count => exact running_anchor time count

/-- The anchor is its own checkpoint block at epoch zero. -/
theorem local_checkpoint_root (code : Local) :
    code.store.getCheckpointBlock anchorRoot 0 = .ok anchorRoot := by
  have ancestor := Store.getAncestor_of_le (store := code.store)
    (node := ⟨anchorRoot, .pending⟩) (slot := 0) (local_anchor code) (by decide)
  change (do let node ← code.store.getAncestor ⟨anchorRoot, .pending⟩ 0
             pure node.root) = .ok anchorRoot
  rw [ancestor]
  rfl

/-- The fixed finalized checkpoint lies on the chain of every justified checkpoint. -/
theorem finalized_prefix : FinalizedPrefix execution 1 4000 := by
  intro u _ w _ n k nb kb cp justified _ _
  obtain ⟨nc, ne⟩ := store_code nb u
  obtain ⟨kc, ke⟩ := store_code kb w
  rw [ke] at justified
  rw [local_justified justified, ne, ke]
  have final : nc.store.finalizedCheckpoint = ⟨0, anchorRoot⟩ := by cases nc <;> rfl
  rw [final]
  exact local_checkpoint_root kc

/-- The only required balance comparisons are in epoch zero, where all balances agree.

The epoch-one comparisons are vacuous because no counted state reaches epoch one. -/
theorem head_drifts : ∀ w ∈ honest, ∀ n head headState epoch,
    (execution.world n).time ≤ 4000 →
    ((execution.world n).state w).getPulledUpHeadState config head = .ok headState →
    ((execution.world n).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ 1 →
    ∀ v ∈ honest, ∀ k (s : BeaconState preset .phase0), (execution.world k).time ≤ 4000 →
      ((execution.world k).state v).Counts config s →
      epoch.toNat ≤ (getCurrentEpoch s).toNat →
      (getCurrentEpoch s).toNat ≤ epoch.toNat + 1 → DriftAtMost headState s 0 := by
  intro w _ n head headState epoch nb pulled clock _ v _ k s kb counted low _
  have zero := counted_epoch kb counted
  rw [zero] at low
  have epochZero : epoch = 0 := UInt64.toNat_inj.mp (by simpa using low)
  subst epoch
  simp only [Store.getPulledUpHeadState, clock, bind_ok_iff] at pulled
  obtain ⟨raw, rawOk, pulled⟩ := pulled
  have rawEq : raw = headState := by simpa [pure, Except.pure] using pulled
  subst headState
  obtain ⟨code, eq⟩ := store_code nb w
  rw [eq] at rawOk
  rcases local_block_state (Store.blockState_ok_iff.mp rawOk) with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    rcases counts kb counted with rfl | rfl | rfl
  all_goals
    change DriftAtMost (state bodyRoot) (state bodyRoot) 0
    intro p _ total _ totalOk
    rw [total_balance, Except.ok.injEq] at totalOk
    subst total
    have same : quorumVoters (state bodyRoot) = activeVoters (state bodyRoot) := by decide
    rw [same, (stakes bodyRoot).1]
    exact Nat.le_refl _

/-- The child is the only block message in any view before the limit. -/
theorem block_in_view {n : Nat} {v : ValidatorIndex} {block : SignedBeaconBlock preset .phase0}
    (bounded : (execution.world n).time ≤ 4000)
    (held : .block block ∈ (execution.world n).view v) : block = signedBlock := by
  rw [world_prefix n (bounded_index bounded)] at held
  obtain ⟨tag, _, eq⟩ := held
  fin_cases tag <;> simp_all [message]

/-- Every relevant receiver can admit or reprocess that empty block through the full handler. -/
theorem blocks_admitted : BlocksAdmitted execution 0 1 4000 := by
  intro v _ u _ n k bounded block root s inView _ elapsed ready _ _
  have nb : (execution.world n).time ≤ 4000 := by omega
  rw [block_in_view nb inView]
  obtain ⟨code, eq⟩ := store_code bounded u
  rw [eq] at ready ⊢
  cases code with
  | anchor =>
    have lower := execution.monotone_time (Nat.zero_le k)
    change 1000 ≤ (execution.world k).time at lower
    have zero : 0 = (execution.world k).time := ready.1
    omega
  | ticked => exact ⟨admitted, first_admitted⟩
  | running time count => exact ⟨running time count, running_block_repeat time count⟩

end EthLib.Consensus.Models.Network.EightValidatorWitness.Trace
