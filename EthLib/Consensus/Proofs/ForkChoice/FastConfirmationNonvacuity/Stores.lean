module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmationNonvacuity.DutyStates

/-! The witness stores keep one child and collect three votes before time 4000. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network.FiveValidatorWitness

open Base Serialization.Ssz

/-- The admitted child, the first `count` votes, and the clock at `time`.

The first slot retains the child's boost root; later slots clear it.

These are candidate states, not yet a certified network execution. -/
def running (time : UInt64) (count : Nat) : Store preset .phase0 :=
  { admitted with
    timeMs := time
    latestMessages := ([1, 2, 3].take count).foldl
      (fun messages slot => recordVote [] (LatestMessage.ofAttestation (vote slot))
        messages (voter slot)) ∅
    proposerBoostRoot := if time < 2000 then blockRoot else Vector.replicate 32 0 }

set_option maxRecDepth 10000 in
/-- The anchor has exactly the child, and the child has no descendant in these stores. -/
theorem running_children (time : UInt64) (count : Nat) :
    (running time count).getNodeChildren ⟨anchorRoot, .pending⟩ =
      .ok [⟨blockRoot, .pending⟩] ∧
    (running time count).getNodeChildren ⟨blockRoot, .pending⟩ = .ok [] := by
  have empty : (∅ : Std.TreeMap Root (BeaconBlock preset .phase0)).toList = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Std.TreeMap.length_toList]
    rfl
  -- The public permutation equations suffice; the map's traversal order is irrelevant.
  have initial : anchor.blocks.toList = [(anchorRoot, anchorBlock stateRoot)] := by
    have p := Std.TreeMap.toList_insert_perm (t := (∅ :
      Std.TreeMap Root (BeaconBlock preset .phase0)))
      (k := anchorRoot) (v := anchorBlock stateRoot)
    simpa [anchor, empty] using p
  have entries : (running time count).blocks.toList.Perm
      [(blockRoot, signedBlock.message), (anchorRoot, anchorBlock stateRoot)] := by
    have p := Std.TreeMap.toList_insert_perm (t := anchor.blocks)
      (k := blockRoot) (v := signedBlock.message)
    change (anchor.blocks.insert blockRoot signedBlock.message).toList.Perm _
    simpa [initial, blockRoot_ne_anchorRoot] using p
  have anchored := entries.filter (fun x => decide (x.2.parentRoot = anchorRoot))
  have child := entries.filter (fun x => decide (x.2.parentRoot = blockRoot))
  have zeroAnchor : (anchorBlock stateRoot).parentRoot ≠ anchorRoot :=
    Ne.symm anchorRoot_ne_zero
  have zeroChild : (anchorBlock stateRoot).parentRoot ≠ blockRoot := Ne.symm blockRoot_ne_zero
  simp only [List.filter_cons, List.filter_nil, zeroAnchor, zeroChild,
    show signedBlock.message.parentRoot = anchorRoot from rfl, Ne.symm blockRoot_ne_anchorRoot,
    decide_false, decide_true, Bool.false_eq_true, ↓reduceIte,
    List.perm_singleton, List.perm_nil] at anchored child
  simp only [Store.getNodeChildren, show ¬ Fork.glamsterdam ≤ Fork.phase0 by decide,
    false_and, ↓reduceDIte, ↓reduceIte, anchored, child]
  exact ⟨rfl, rfl⟩

/-- Admitting the distinct child preserves the anchor entry. -/
theorem running_anchor (time : UInt64) (count : Nat) :
    (running time count).blocks[anchorRoot]? = some (anchorBlock stateRoot) := by
  simp only [running, admitted, ticked, anchor, Std.TreeMap.getElem?_insert]
  simp [blockRoot_ne_anchorRoot]

/-- All candidate stores hold the child. -/
theorem running_child (time : UInt64) (count : Nat) :
    (running time count).blocks[blockRoot]? = some signedBlock.message := by
  simp [running, admitted]

/-- The child's ancestor at genesis is the anchor. -/
theorem running_checkpoint (time : UInt64) (count : Nat) :
    (running time count).getCheckpointBlock blockRoot 0 = .ok anchorRoot := by
  have parent : (running time count).blocks[signedBlock.message.parentRoot]? =
      some (anchorBlock stateRoot) := running_anchor time count
  have ancestor : (running time count).getAncestor ⟨blockRoot, .pending⟩ 0 =
      .ok ⟨anchorRoot, .pending⟩ :=
    Store.getAncestor_parent_of_slot_lt (node := ⟨blockRoot, .pending⟩)
    (running_child time count) parent
    (show signedBlock.message.slot > 0 by decide)
  change (do let node ← (running time count).getAncestor ⟨blockRoot, .pending⟩ 0
             pure node.root) = .ok anchorRoot
  rw [ancestor]
  rfl

set_option maxRecDepth 10000 in
/-- The child agrees with the genesis checkpoints in either epoch reached by the witness. -/
theorem running_viable (time : UInt64) (count : Nat) {epoch : Epoch}
    (current : (running time count).getCurrentStoreEpoch config = .ok epoch)
    (early : epoch = 0 ∨ epoch = 1) :
    (running time count).isViableLeaf config ⟨blockRoot, .pending⟩ = .ok true := by
  have blockOk : (running time count).block blockRoot = .ok signedBlock.message := by
    simp [Store.block, running_child, pure, Except.pure]
  have votingSource : (running time count).getVotingSource config blockRoot =
      .ok postState.currentJustifiedCheckpoint := by
    simp only [Store.getVotingSource, blockOk, current, bind, Except.bind]
    rcases early with rfl | rfl <;>
      simp [running, admitted, pure, Except.pure]
  simp only [Store.isViableLeaf, current, votingSource, running_checkpoint,
    show (running time count).finalizedCheckpoint = ⟨0, anchorRoot⟩ from rfl,
    show (running time count).justifiedCheckpoint = ⟨0, anchorRoot⟩ from rfl]
  rfl

set_option maxRecDepth 10000 in
/-- Viability filtering retains the child and anchor, in that order. -/
theorem running_filtered (time : UInt64) (count : Nat) {epoch : Epoch}
    (current : (running time count).getCurrentStoreEpoch config = .ok epoch)
    (early : epoch = 0 ∨ epoch = 1) :
    (running time count).getFilteredNodeTree config =
      .ok [⟨blockRoot, .pending⟩, ⟨anchorRoot, .pending⟩] := by
  have lower : (running time count).nodeRank ⟨blockRoot, .pending⟩ <
      (running time count).nodeRank ⟨anchorRoot, .pending⟩ := by
    simp only [Store.nodeRank, running_anchor, running_child]
    decide
  have leaf : (running time count).filterNodeTree config ⟨blockRoot, .pending⟩ =
      .ok [⟨blockRoot, .pending⟩] := by
    rw [Store.filterNodeTree, (running_children time count).2]
    simp [running_viable time count current early, bind, Except.bind, pure, Except.pure]
  change (running time count).filterNodeTree config ⟨anchorRoot, .pending⟩ = _
  rw [Store.filterNodeTree, (running_children time count).1]
  simp [lower, leaf, bind, Except.bind, pure, Except.pure]

set_option maxRecDepth 10000 in
/-- Each received vote adds 200 Gwei of honest support for the child. -/
theorem running_tally (time : UInt64) (count : Nat) (bound : count ≤ 3) :
    (running time count).justifiedTally = .ok
      ⟨if count = 0 then [] else [(⟨blockRoot, .pending⟩, 200 * count)], none⟩ := by
  have target : (running time count).checkpointState
      (running time count).justifiedCheckpoint = .ok (state bodyRoot) := by
    simp [Store.checkpointState, running, admitted, ticked, anchor, pure, Except.pure]
  simp only [Store.justifiedTally, target, bind, Except.bind, pure, Except.pure]
  have balances : unslashedActiveBalances (state bodyRoot) =
      [(0, 200), (1, 200), (2, 200), (3, 100), (4, 200)] := rfl
  simp only [Store.tallyVotes, balances]
  have cases : count = 0 ∨ count = 1 ∨ count = 2 ∨ count = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;>
    simp [Store.groupVotes, running, Store.getSupportedNode, recordVote, voter,
      admitted, ticked, anchor, LatestMessage.ofAttestation, vote, voteData,
      Std.TreeMap.getElem_insert, Std.TreeMap.getD_insert,
      show ¬ Fork.glamsterdam ≤ Fork.phase0 by decide, pure, Except.pure]

set_option maxRecDepth 10000 in
/-- The child has only its attestation weight because the configured proposer score is zero. -/
theorem running_weight (time : UInt64) (count : Nat) (bound : count ≤ 3) :
    (running time count).getWeight config (running time count).justifiedTally
      ⟨blockRoot, .pending⟩ = .ok (200 * count).toUInt64 := by
  have blockOk : (running time count).block blockRoot = .ok signedBlock.message := by
    simp [Store.block, running_child, pure, Except.pure]
  have ancestor : (running time count).getAncestor ⟨blockRoot, .pending⟩ 1 =
      .ok ⟨blockRoot, .pending⟩ := Store.getAncestor_of_le (running_child time count)
        (show signedBlock.message.slot ≤ 1 by decide)
  have reflexive : (running time count).isAncestor ⟨blockRoot, .pending⟩
      ⟨blockRoot, .pending⟩ = .ok true := by
    simp only [Store.isAncestor, blockOk, show signedBlock.message.slot = 1 from rfl,
      ancestor, bind, Except.bind]
    rfl
  have score : (running time count).scoreFromTally
      ⟨if count = 0 then [] else [(⟨blockRoot, .pending⟩, 200 * count)], none⟩
      ⟨blockRoot, .pending⟩ = .ok (200 * count).toUInt64 := by
    by_cases zero : count = 0
    · subst count
      rfl
    · simp [Store.scoreFromTally, zero, reflexive, bind, Except.bind, pure, Except.pure]
      omega
  have proposer : (running time count).getProposerScore config = .ok 0 := by
    have target : (running time count).checkpointState
        (running time count).justifiedCheckpoint = .ok (state bodyRoot) := by
      simp [Store.checkpointState, running, admitted, ticked, anchor, pure, Except.pure]
    simp only [Store.getProposerScore, target, bind, Except.bind]
    have total : getTotalBalance (state bodyRoot) [0, 1, 2, 3, 4] = .ok 900 := by
      rw [getTotalBalance_ok_iff]
      simp only [List.forall_mem_cons,
        sumMarked_eq_sum, getElem?_markIndices]
      decide
    have balances : unslashedActiveBalances (state bodyRoot) =
        [(0, 200), (1, 200), (2, 200), (3, 100), (4, 200)] := rfl
    simp only [computeProposerScore, calculateCommitteeFraction, balances, List.map_cons,
      List.map_nil, total, Except.mapError, bind, Except.bind]
    rfl
  simp only [Store.getWeight, show ¬ Fork.glamsterdam ≤ Fork.phase0 by decide,
    ↓reduceIte, ↓reduceDIte, running_tally time count bound, score, bind, Except.bind,
    pure, Except.pure]
  by_cases boosted : time < 2000
  · have boostRoot : (running time count).proposerBoostRoot = blockRoot := by
      simp [running, boosted]
    simp only [boostRoot, blockRoot_ne_zero, ne_eq, not_false_eq_true, decide_true,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, reflexive, proposer]
    simp [Uint64.addChecked, Nat.mod_lt _ (by decide : 0 < 18446744073709551616)]
    rfl
  · have boostRoot : (running time count).proposerBoostRoot = Vector.replicate 32 0 := by
      simp [running, boosted]
    simp [boostRoot]

set_option maxRecDepth 10000 in
/-- LMD-GHOST selects the child even before the first attestation is received. -/
theorem running_head (time : UInt64) (count : Nat) (bound : count ≤ 3) {epoch : Epoch}
    (current : (running time count).getCurrentStoreEpoch config = .ok epoch)
    (early : epoch = 0 ∨ epoch = 1) :
    (running time count).getHead config = .ok ⟨blockRoot, .pending⟩ := by
  let nodes : List ForkChoiceNode := [⟨blockRoot, .pending⟩, ⟨anchorRoot, .pending⟩]
  have weighted : (running time count).weighNode config (running time count).justifiedTally
      ⟨blockRoot, .pending⟩ = .ok (⟨blockRoot, .pending⟩, (200 * count).toUInt64, 0) := by
    simp only [Store.weighNode, running_weight time count bound, bind, Except.bind]
    rfl
  have picked : (running time count).heaviestChild config (running time count).justifiedTally
      nodes ⟨anchorRoot, .pending⟩ = .ok (some ⟨blockRoot, .pending⟩) := by
    simp [Store.heaviestChild, (running_children time count).1, nodes, weighted,
      chooseHeaviest, bind, Except.bind, pure, Except.pure]
  have leaf : (running time count).heaviestChild config (running time count).justifiedTally
      nodes ⟨blockRoot, .pending⟩ = .ok none := by
    simp [Store.heaviestChild, (running_children time count).2, chooseHeaviest,
      bind, Except.bind, pure, Except.pure]
  have lower : (running time count).nodeRank ⟨blockRoot, .pending⟩ <
      (running time count).nodeRank ⟨anchorRoot, .pending⟩ := by
    simp only [Store.nodeRank, running_anchor, running_child]
    decide
  simp only [Store.getHead, running_filtered time count current early, bind, Except.bind]
  change (running time count).getHeadFrom config (running time count).justifiedTally
    nodes ⟨anchorRoot, .pending⟩ = .ok ⟨blockRoot, .pending⟩
  rw [Store.getHeadFrom, picked]
  simp only [bind, Except.bind, lower, ↓reduceDIte]
  rw [Store.getHeadFrom, leaf]
  rfl

set_option maxRecDepth 10000 in
/-- Each vote passes the time and ancestry checks in the slot following its duty. -/
theorem running_vote_valid (time : UInt64) (count : Nat) {slot : Slot}
    (within : slot = 1 ∨ slot = 2 ∨ slot = 3)
    (clock : (running time count).getCurrentSlot config = .ok (slot + 1)) :
    (running time count).validateOnAttestation config (vote slot) false = .ok () := by
  have anchorOk : (running time count).block anchorRoot = .ok (anchorBlock stateRoot) := by
    simp [Store.block, running_anchor, pure, Except.pure]
  have blockOk : (running time count).block blockRoot = .ok signedBlock.message := by
    simp [Store.block, running_child, pure, Except.pure]
  have recent : (running time count).validateTargetEpochAgainstCurrentTime config
      (vote slot) = .ok () := by
    simp only [Store.validateTargetEpochAgainstCurrentTime, Store.getCurrentStoreEpoch, clock,
      bind, Except.bind, pure, Except.pure]
    rcases within with rfl | rfl | rfl <;> rfl
  simp only [Store.validateOnAttestation, recent, bind, Except.bind,
    show (vote slot).data.target = ⟨0, anchorRoot⟩ from rfl,
    show (vote slot).data.beaconBlockRoot = blockRoot from rfl,
    show (vote slot).data.slot = slot from rfl,
    anchorOk, blockOk, running_checkpoint, clock,
    show ¬ Fork.glamsterdam ≤ Fork.phase0 by decide, ↓reduceDIte]
  rcases within with rfl | rfl | rfl <;> rfl

set_option maxRecDepth 10000 in
/-- The attestation handler records the vote after checking its cached target state. -/
theorem running_vote_accepted (time : UInt64) (count : Nat) {slot : Slot}
    (within : slot = 1 ∨ slot = 2 ∨ slot = 3)
    (clock : (running time count).getCurrentSlot config = .ok (slot + 1)) :
    (running time count).onAttestation config .acceptAll (vote slot) false =
      .ok ((running time count).updateLatestMessages [voter slot] (vote slot)) := by
  have cached : (running time count).storeTargetCheckpointState config .acceptAll
      (vote slot).data.target = .ok (running time count) := by
    simp [Store.storeTargetCheckpointState, running, admitted, ticked, anchor,
      vote, voteData, Checkpoint.compare, pure, Except.pure]
  have target : (running time count).checkpointState (vote slot).data.target =
      .ok (state bodyRoot) := by
    simp [Store.checkpointState, running, admitted, ticked, anchor, vote, voteData,
      pure, Except.pure]
  simp only [Store.onAttestation, running_vote_valid time count within clock,
    cached, target, vote_committees within, vote_indexed within, vote_signature within,
    Except.mapError, bind, Except.bind]
  rfl

/-- The selected child supplies the honest vote data throughout the first epoch. -/
theorem running_vote_data (time : UInt64) (count : Nat) (bound : count ≤ 3) {slot : Slot}
    (within : slot = 1 ∨ slot = 2 ∨ slot = 3) {epoch : Epoch}
    (current : (running time count).getCurrentStoreEpoch config = .ok epoch)
    (early : epoch = 0 ∨ epoch = 1) :
    HonestVoteData config .acceptAll (running time count) slot 0 (voteData slot) := by
  obtain ⟨currentState, advanced, data⟩ := exists_vote_state within
  refine ⟨⟨blockRoot, .pending⟩, signedBlock.message, postState, currentState,
    running_head time count bound current early, running_child time count, ?_, advanced, data⟩
  simp [Store.blockState, running, admitted, pure, Except.pure]

end EthLib.Consensus.Models.Network.FiveValidatorWitness
