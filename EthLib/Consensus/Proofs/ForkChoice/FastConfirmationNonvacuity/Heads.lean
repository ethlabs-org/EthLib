module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.Committees

/-! The short execution satisfies the head-following premise of Theorem 1.

The tree has only the anchor and one child, so every viable non-anchor block is the head.

All required past committee reads succeed before the time-4000 limit. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.EightValidatorWitness.Trace
open Base Base.Uint64

/-- A head is one of the two roots held by the witness stores. -/
theorem local_head_roots {code : Local} {head : ForkChoiceNode}
    (read : code.store.getHead config = .ok head) :
    head.root = anchorRoot ∨ head.root = blockRoot := by
  have descends := Store.isAncestor_getHead read
  have justified : code.store.justifiedCheckpoint = ⟨0, anchorRoot⟩ := by cases code <;> rfl
  rw [justified] at descends
  obtain ⟨block, held, _⟩ := Store.slot_le_of_isAncestor (local_anchor code) descends
  exact (local_block held).imp And.left And.left

/-- The only block with a held parent is the child, which is the head whenever viable. -/
theorem local_follows {code : Local} {head : ForkChoiceNode} {root : Root}
    {block parent : BeaconBlock preset .phase0} {nodes : List ForkChoiceNode}
    (headOk : code.store.getHead config = .ok head)
    (held : code.store.block root = .ok block)
    (parentOk : code.store.block block.parentRoot = .ok parent)
    (tree : code.store.getFilteredNodeTree config = .ok nodes)
    (viable : (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes) :
    code.store.isAncestor head ⟨root, .pending⟩ = .ok true := by
  have blockHeld := Store.block_ok_iff.mp held
  rcases local_block blockHeld with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases local_block (Store.block_ok_iff.mp parentOk) with ⟨bad, _⟩ | ⟨bad, _⟩
    · exact False.elim (anchorRoot_ne_zero bad.symm)
    · exact False.elim (blockRoot_ne_zero bad.symm)
  · have pending := Store.getHead_pending (by decide) headOk
    rcases local_head_roots headOk with atAnchor | atChild
    · obtain ⟨found, children, foundOk, childrenOk, leaf⟩ := Store.getHead_leaf headOk
      rw [tree, Except.ok.injEq] at foundOk
      subst found
      have child : (⟨blockRoot, .pending⟩ : ForkChoiceNode) ∈ children :=
        (Store.mem_getNodeChildren (by decide) childrenOk).mpr
          ⟨rfl, signedBlock.message, blockHeld, atAnchor.symm⟩
      exact False.elim (leaf _ child viable)
    · have same : head = ⟨blockRoot, .pending⟩ := by cases head; simp_all
      rw [same]
      exact Store.isAncestor_self blockHeld

/-- Every successful head read has its associated state. -/
theorem local_head_state {code : Local} {head : ForkChoiceNode}
    (read : code.store.getHead config = .ok head) :
    ∃ s, code.store.blockState head.root = .ok s := by
  have descends := Store.isAncestor_getHead read
  have justified : code.store.justifiedCheckpoint = ⟨0, anchorRoot⟩ := by cases code <;> rfl
  rw [justified] at descends
  obtain ⟨block, held, _⟩ := Store.slot_le_of_isAncestor (local_anchor code) descends
  rcases local_block held with ⟨root, _⟩ | ⟨root, _⟩
  · refine ⟨state bodyRoot, ?_⟩
    rw [root]
    cases code <;> simp [Local.store, Store.blockState, running, admitted, ticked, anchor,
      blockRoot_ne_anchorRoot, Std.TreeMap.getElem_insert, pure, Except.pure]
  · rw [root] at held ⊢
    cases code with
    | anchor => simp [Local.store, anchor, Ne.symm blockRoot_ne_anchorRoot] at held
    | ticked => simp [Local.store, ticked, anchor, Ne.symm blockRoot_ne_anchorRoot] at held
    | running time count =>
      exact ⟨postState, by
        simp [Local.store, Store.blockState, running, admitted, pure, Except.pure]⟩

/-- Both held states supply a committee for each slot of the first epoch. -/
theorem local_slot_exists {code : Local} {root : Root} {s : BeaconState preset .phase0}
    (stateOk : code.store.blockState root = .ok s) {slot : Slot} (past : slot < 4) :
    ∃ members, code.store.getSlotCommittee root slot = .ok members := by
  have shape := local_block_state (Store.blockState_ok_iff.mp stateOk)
  have count : getCommitteeCountPerSlot s (computeEpochAtSlot preset slot) = 1 := by
    rcases shape with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact slot_committee_count _ _
    · change getCommitteeCountPerSlot (state bodyRoot) (computeEpochAtSlot preset slot) = 1
      exact slot_committee_count _ _
  have slots : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by
    have nat : slot.toNat < 4 := past
    simp only [← UInt64.toNat_inj]
    change slot.toNat = 0 ∨ slot.toNat = 1 ∨ slot.toNat = 2 ∨ slot.toNat = 3
    omega
  have committee : ∃ members, getBeaconCommittee s slot 0 = .ok members := by
    rcases shape with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · rcases slots with rfl | rfl | rfl | rfl
      · exact ⟨_, (committees bodyRoot).1⟩
      · exact ⟨_, (committees bodyRoot).2.1⟩
      · exact ⟨_, (committees bodyRoot).2.2.1⟩
      · exact ⟨_, (committees bodyRoot).2.2.2⟩
    · rcases slots with rfl | rfl | rfl | rfl
      · exact ⟨_, post_committees.1⟩
      · exact ⟨_, post_committees.2.1⟩
      · exact ⟨_, post_committees.2.2.1⟩
      · exact ⟨_, post_committees.2.2.2⟩
  obtain ⟨members, committeeOk⟩ := committee
  simp only [Store.getSlotCommittee, stateOk, bind, Except.bind, count,
    show List.range (1 : UInt64).toNat = [0] from rfl, List.foldlM_cons, List.foldlM_nil,
    show (0 : Nat).toUInt64 = 0 from rfl, committeeOk, Except.mapError]
  exact ⟨_, rfl⟩

/-- Every range ending before epoch one has a successful committee read. -/
theorem local_range_exists {code : Local} {head : ForkChoiceNode} {first last : Slot}
    (read : code.store.getHead config = .ok head) (past : last < 4) :
    ∃ members, code.store.getCommitteesBetweenSlots head.root first last = .ok members := by
  obtain ⟨s, stateOk⟩ := local_head_state read
  have lastNat : last.toNat < 4 := past
  have afterOk : addChecked last 1 = .ok (last + 1) := by
    apply addChecked_ok_iff.mpr
    refine ⟨by change last.toNat + 1 < 2 ^ 64; omega, ?_⟩
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by change last.toNat + 1 < 2 ^ 64; omega)]
  simp only [Store.getCommitteesBetweenSlots, afterOk, Except.mapError, bind, Except.bind]
  apply foldlM_exists_ok_of_invariant (fun _ => True) _ _ trivial
  intro acc i inside _
  have offset := List.mem_range.mp inside
  have afterNat : (last + 1).toNat = last.toNat + 1 := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by change last.toNat + 1 < 2 ^ 64; omega)]
    rfl
  have offsetBound : i < 2 ^ 64 := by omega
  have offsetNat : i.toUInt64.toNat = i := by
    simp [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' offsetBound]
  have slotNat : (first + i.toUInt64).toNat = first.toNat + i := by
    rw [UInt64.toNat_add, offsetNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨committee, committeeOk⟩ := local_slot_exists stateOk
    (slot := first + i.toUInt64) (UInt64.lt_iff_toNat_lt.mpr (by
      rw [slotNat]; change first.toNat + i < 4; omega))
  exact ⟨committee.foldl (fun (set : Std.TreeSet ValidatorIndex) v => set.insert v) acc,
    by rw [committeeOk]; rfl, trivial⟩

/-- Honest heads supply all required reads and follow every viable child. -/
theorem head_follows : HeadFollowsSupport execution 4000 where
  reads := by
    intro w _ k bounded head _ read
    obtain ⟨code, eq⟩ := store_code bounded w
    have genesis : ((execution.world k).state w).genesisTimeMs = 0 := (execution.clock_bounds w k).1
    have current : ((execution.world k).state w).getCurrentSlot config =
        .ok (((execution.world k).state w).timeMs / 1000) := by
      simp [Store.getCurrentSlot, genesis, computeSlotAtTimeMs, subChecked, divChecked,
        show config.SLOT_DURATION_MS = 1000 from rfl, bind, Except.bind, Except.mapError]
    have below := current_slot_le_four bounded current
    rw [eq] at read
    obtain ⟨nodes, _, tree, _, _⟩ := Store.getHead_leaf read
    refine ⟨state bodyRoot, _, 0, nodes, ?_, current, proposer_score, ?_, ?_⟩
    · rw [eq]
      cases code <;> simp [Local.store, Store.checkpointState, running, admitted, ticked, anchor,
        pure, Except.pure]
    · rw [eq]; exact tree
    · intro first last past
      rw [eq]
      exact local_range_exists read (UInt64.lt_of_lt_of_le past below)
  follows := by
    intro w _ k bounded head s root block parent current epoch first last beforeBlock
      window score nodes parents _ headOk _ blockOk parentOk _ _ _ _ _ _ _ _ _ tree viable _ _ _
    obtain ⟨code, eq⟩ := store_code bounded w
    rw [eq] at headOk blockOk parentOk tree ⊢
    exact local_follows headOk blockOk parentOk tree viable

end EthLib.Consensus.Models.Network.EightValidatorWitness.Trace
