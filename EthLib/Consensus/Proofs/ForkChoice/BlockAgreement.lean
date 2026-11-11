module

public import EthLib.Consensus.Proofs.ForkChoice.HonestDuties
public import EthLib.Consensus.Proofs.ForkChoice.Reachable

/-!
# Statements: honest stores agree on the blocks of an honest chain

This file states part of step 3 of the plan for the safety of the fast confirmation rule.

The rule is that of [arXiv 2405.00549v4][fcr].

The proofs are placeholders, and each statement may still change.

A block of an honest store is a block of its start, or came in a signed block of its view.

Its state is then the state transition of that signed block, from the state of its parent.

So two honest stores with the same start hold the same state at a root that both hold.

That needs the two stores to hold the same block wherever both hold one.

`OneBlockPerRoot` excludes conflicting held blocks at one root, without assuming hash injectivity.

Under synchrony, a block of an honest store reaches the view of each honest validator.

It is there one delay later.

An up-to-date honest store then holds it, when its checks of a new block pass.

The parent comes first, so the statement asks for the chain of the block down to the start.

The finalized checkpoint of the receiver must sit on that chain.

From Gloas the receiver must have verified each payload that the first store has verified.

The receiver must admit a delayed block held by an honest source when its block validation passes.

That last hypothesis covers the steps of the handler after the checks, and the votes of the block.

In the model here a vote that the store rejects makes the store reject its block.

The agreement follows two lemmas of [verified-fast-confirmation][vfc].

They are `WellFormedExecution.blocks_agree` and `WalkCoveredBy.receiver_walk`.

There a root names one block by construction, and a rejected event leaves the store as it is.

[fcr]: https://arxiv.org/abs/2405.00549v4
[vfc]: https://github.com/fradamt/verified-fast-confirmation
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

section ForkChoice

variable {ν κ : Type*} [DecidableEq ν] {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {signed : Message preset fork → Set (ν × κ)}
  {sends : ν → ℕ → Set (Message preset fork) → Store preset fork → Message preset fork → Prop}
  {J : Set ν}

/-- A block of an honest store is a block of its start, or came in a signed block of its view.

In the second case the store holds the state of the parent of the block.

The state of the block is the state transition of the signed block from that state. -/
theorem Execution.exists_signed_of_blocks
    (e : Execution (forkChoice config checks sources signed sends) J) {u : ν} (honest : u ∈ J)
    {n : ℕ} {root : Root} {block : BeaconBlock preset fork}
    (found : ((e.world n).state u).blocks[root]? = some block) :
    ((e.start u).blocks[root]? = some block ∧
        ((e.world n).state u).blockStates[root]? = (e.start u).blockStates[root]?) ∨
      ∃ signedBlock : SignedBeaconBlock preset fork, ∃ pre state,
        .block signedBlock ∈ (e.world n).view u ∧ signedBlock.message = block ∧
        SszType.hashTreeRoot signedBlock.message = .ok root ∧
        ((e.world n).state u).blockStates[block.parentRoot]? = some pre ∧
        stateTransition config checks sources.engine pre signedBlock true = .ok state ∧
        ((e.world n).state u).blockStates[root]? = some state := by
  have _ := honest
  -- Keep the parent's block as well as its state, so later insertions cannot replace that state.
  let P (view : Set (Message preset fork)) (s : Store preset fork) : Prop :=
    ∀ r b, s.blocks[r]? = some b →
      ((e.start u).blocks[r]? = some b ∧ s.blockStates[r]? = (e.start u).blockStates[r]?) ∨
      ∃ sb pre post parent, .block sb ∈ view ∧ sb.message = b ∧
        SszType.hashTreeRoot sb.message = .ok r ∧
        s.blocks[b.parentRoot]? = some parent ∧ s.blockStates[b.parentRoot]? = some pre ∧
        stateTransition config checks sources.engine pre sb true = .ok post ∧
        s.blockStates[r]? = some post
  have maps {v v' : Set (Message preset fork)} {s t : Store preset fork}
      (h : P v s) (incl : v ⊆ v') (blocks : t.blocks = s.blocks)
      (states : t.blockStates = s.blockStates) : P v' t := by
    intro r b found
    rw [blocks] at found
    rcases h r b found with old | ⟨sb, pre, post, parent, mem, rest⟩
    · exact .inl ⟨old.1, states ▸ old.2⟩
    · right
      exact ⟨sb, pre, post, parent, incl mem, rest.1, rest.2.1,
        blocks ▸ rest.2.2.1, states ▸ rest.2.2.2.1, rest.2.2.2.2.1,
        states ▸ rest.2.2.2.2.2⟩
  have step {v : Set (Message preset fork)} {s t : Store preset fork}
      {sb : SignedBeaconBlock preset fork} (h : P v s) (mem : .block sb ∈ v)
      (added : s.onBlock config checks sources sb = .ok t) : P v t := by
    rcases Store.onBlock_same_or_insert added with
      same | ⟨r, hashed, fresh, blocks, pre, post, preFound, transition, states⟩
    · exact same ▸ h
    have parentKnown : ∃ parent, s.blocks[sb.message.parentRoot]? = some parent := by
      have checks := (Store.onBlock_checks hashed (by
        simp [Std.TreeMap.contains_eq_isSome_getElem?, fresh]) added).2.2
      unfold Store.getCheckpointBlock at checks
      simp only [bind_ok_iff] at checks
      obtain ⟨slot, _, ancestor, walked, _⟩ := checks
      cases known : s.blocks[sb.message.parentRoot]? with
      | none =>
        rw [Store.getAncestor] at walked
        dsimp only at walked
        rw [known] at walked
        simp [throw, throwThe, MonadExceptOf.throw] at walked
      | some parent => exact ⟨parent, rfl⟩
    obtain ⟨parent, parentFound⟩ := parentKnown
    have different : r ≠ sb.message.parentRoot := by
      intro same
      rw [← same, fresh] at parentFound
      cases parentFound
    intro q b found
    rw [blocks, getElem?_insert_root] at found
    by_cases same : r = q
    · subst q
      simp only [↓reduceIte, Option.some.injEq] at found
      subst b
      right
      refine ⟨sb, pre, post, parent, mem, rfl, hashed, ?_, ?_, transition, ?_⟩
      · simpa [blocks, getElem?_insert_root, different] using parentFound
      · simpa [states, getElem?_insert_root, different] using preFound
      · simp [states]
    · simp only [same, ↓reduceIte] at found
      rcases h q b found with old | ⟨sb', pre', post', parent', mem', msg, hash,
        parentFound', preFound', transition', postFound'⟩
      · exact .inl ⟨old.1, by simpa [states, getElem?_insert_root, same] using old.2⟩
      · have different' : r ≠ b.parentRoot := by
          intro eq
          rw [← eq, fresh] at parentFound'
          cases parentFound'
        right
        refine ⟨sb', pre', post', parent', mem', msg, hash, ?_, ?_, transition', ?_⟩
        · simpa [blocks, getElem?_insert_root, different'] using parentFound'
        · simpa [states, getElem?_insert_root, different'] using preFound'
        · simpa [states, getElem?_insert_root, same] using postFound'
  have holds : ∀ i, P ((e.world i).view u) ((e.world i).state u) := by
    intro i
    induction i with
    | zero => exact fun _ _ known => .inl ⟨known, rfl⟩
    | succ i ih =>
      have incl := e.monotone_view u (Nat.le_succ i)
      rcases e.state_succ i u with same | ⟨_, moved⟩
      · exact maps ih incl (congrArg Store.blocks same) (congrArg Store.blockStates same)
      have ih' := maps ih incl rfl rfl
      cases moved with
      | tick _ _ ticked =>
        exact maps ih' (fun _ h => h) (Store.onTick_frame ticked).2.2.1
          (Store.onTick_frame ticked).2.2.2
      | block mem added =>
        exact Store.onBlockWithVotes_preserves (fun h added => step h (incl mem) added)
          (fun _ h a => maps h (fun _ h => h) (Store.onAttestation_frame a).2.1
            (Store.onAttestation_frame a).2.2)
          (fun _ h a => maps h (fun _ h => h) (Store.onAttesterSlashing_frame a).2.1
            (Store.onAttesterSlashing_frame a).2.2) ih' added
      | attestation _ a =>
        exact maps ih' (fun _ h => h) (Store.onAttestation_frame a).2.1
          (Store.onAttestation_frame a).2.2
      | attesterSlashing _ a =>
        exact maps ih' (fun _ h => h) (Store.onAttesterSlashing_frame a).2.1
          (Store.onAttesterSlashing_frame a).2.2
      | payloadAttestation _ a =>
        exact maps ih' (fun _ h => h) (Store.onPayloadAttestationMessage_onlyPtcVotes a).frame.2.1
          (Store.onPayloadAttestationMessage_onlyPtcVotes a).frame.2.2
      | envelope _ a =>
        exact maps ih' (fun _ h => h) (Store.onExecutionPayloadEnvelope_frame a).2.1
          (Store.onExecutionPayloadEnvelope_frame a).2.2
      | inclusionList _ a =>
        exact maps ih' (fun _ h => h) (Store.onInclusionList_frame a).2.1
          (Store.onInclusionList_frame a).2.2
  rcases holds n root block found with old | ⟨sb, pre, post, _, mem, msg, hash, _, rest⟩
  · exact .inl old
  · exact .inr ⟨sb, pre, post, mem, msg, hash, rest⟩

/-- Two honest stores with one start hold the same state at a root that both hold.

The two stores must hold the same block wherever both hold one.

Both validators start from a store built from an anchor. -/
theorem Execution.blockStates_eq (e : Execution (forkChoice config checks sources signed sends) J)
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    {u w : ν} (first : u ∈ J) (second : w ∈ J) (startFirst : e.start u = anchor)
    (startSecond : e.start w = anchor) {n k : ℕ}
    (sameBlocks : ∀ (root : Root) left right, ((e.world n).state u).blocks[root]? = some left →
      ((e.world k).state w).blocks[root]? = some right → left = right)
    {root : Root} {left right : BeaconState preset fork}
    (leftFound : ((e.world n).state u).blockStates[root]? = some left)
    (rightFound : ((e.world k).state w).blockStates[root]? = some right) :
    left = right := by
  have reached {v : ν} (start : e.start v = anchor) (i : ℕ) :
      Store.Reachable config anchorState anchorBlock ((e.world i).state v) := by
    induction i with
    | zero =>
      change Store.Reachable config anchorState anchorBlock (e.start v)
      rw [start]
      exact .anchor anchored
    | succ i ih =>
      rcases e.state_succ i v with same | ⟨_, moved⟩
      · exact same ▸ ih
      · exact moved.reachable ih
  -- A known block protects its state from every later insertion, including at the anchor root.
  have keep {v : ν} {r : Root} {b : BeaconBlock preset fork}
      (known : (e.start v).blocks[r]? = some b) (i : ℕ) :
      ((e.world i).state v).blockStates[r]? = (e.start v).blockStates[r]? := by
    have blockStep {s t : Store preset fork} {sb : SignedBeaconBlock preset fork}
        (h : s.blocks[r]? = some b ∧ s.blockStates[r]? = (e.start v).blockStates[r]?)
        (added : s.onBlock config checks sources sb = .ok t) :
        t.blocks[r]? = some b ∧ t.blockStates[r]? = (e.start v).blockStates[r]? := by
      refine ⟨Store.onBlock_blocks_of_found added h.1, ?_⟩
      rcases Store.onBlock_same_or_insert added with
        same | ⟨q, _, fresh, _, _, _, _, _, states⟩
      · exact same ▸ h.2
      have different : q ≠ r := by
        intro eq
        rw [eq, h.1] at fresh
        cases fresh
      simpa [states, getElem?_insert_root, different] using h.2
    have maps {s t : Store preset fork}
        (h : s.blocks[r]? = some b ∧ s.blockStates[r]? = (e.start v).blockStates[r]?)
        (blocks : t.blocks = s.blocks) (states : t.blockStates = s.blockStates) :
        t.blocks[r]? = some b ∧ t.blockStates[r]? = (e.start v).blockStates[r]? :=
      ⟨blocks ▸ h.1, states ▸ h.2⟩
    suffices h : ((e.world i).state v).blocks[r]? = some b ∧
        ((e.world i).state v).blockStates[r]? = (e.start v).blockStates[r]? from h.2
    induction i with
    | zero => exact ⟨known, rfl⟩
    | succ i ih =>
      rcases e.state_succ i v with same | ⟨_, moved⟩
      · exact same ▸ ih
      cases moved with
      | tick _ _ a => exact maps ih (Store.onTick_frame a).2.2.1 (Store.onTick_frame a).2.2.2
      | block _ a =>
        exact Store.onBlockWithVotes_preserves blockStep
          (fun _ h a => maps h (Store.onAttestation_frame a).2.1
            (Store.onAttestation_frame a).2.2)
          (fun _ h a => maps h (Store.onAttesterSlashing_frame a).2.1
            (Store.onAttesterSlashing_frame a).2.2) ih a
      | attestation _ a =>
        exact maps ih (Store.onAttestation_frame a).2.1 (Store.onAttestation_frame a).2.2
      | attesterSlashing _ a =>
        exact maps ih (Store.onAttesterSlashing_frame a).2.1 (Store.onAttesterSlashing_frame a).2.2
      | payloadAttestation _ a =>
        exact maps ih (Store.onPayloadAttestationMessage_onlyPtcVotes a).frame.2.1
          (Store.onPayloadAttestationMessage_onlyPtcVotes a).frame.2.2
      | envelope _ a =>
        exact maps ih (Store.onExecutionPayloadEnvelope_frame a).2.1
          (Store.onExecutionPayloadEnvelope_frame a).2.2
      | inclusionList _ a =>
        exact maps ih (Store.onInclusionList_frame a).2.1 (Store.onInclusionList_frame a).2.2
  generalize bound : left.slot.toNat = height
  induction height using Nat.strong_induction_on generalizing root left right with
  | h height ih =>
    obtain ⟨lb, lbFound⟩ := (reached startFirst n).known_of_blockState leftFound
    obtain ⟨rb, rbFound⟩ := (reached startSecond k).known_of_blockState rightFound
    have message := sameBlocks root lb rb lbFound rbFound
    subst rb
    cases initial : anchor.blocks[root]? with
    | some b =>
      have leftKept := keep (v := u) (startFirst.symm ▸ initial) n
      have rightKept := keep (v := w) (startSecond.symm ▸ initial) k
      rw [startFirst] at leftKept
      rw [startSecond] at rightKept
      exact Option.some.inj (leftFound.symm.trans (leftKept.trans
        (rightKept.symm.trans rightFound)))
    | none =>
      rcases e.exists_signed_of_blocks first lbFound with old | lnew
      · rw [startFirst, initial] at old
        cases old.1
      rcases e.exists_signed_of_blocks second rbFound with old | rnew
      · rw [startSecond, initial] at old
        cases old.1
      obtain ⟨lsb, lp, ls, _, lmsg, _, lpFound, lt, lsFound⟩ := lnew
      obtain ⟨rsb, rp, rs, _, rmsg, _, rpFound, rt, rsFound⟩ := rnew
      have leq := Option.some.inj (lsFound.symm.trans leftFound)
      have req := Option.some.inj (rsFound.symm.trans rightFound)
      subst ls
      subst rs
      -- The parent state is strictly earlier, so agreement follows by induction on its slot.
      obtain ⟨earlier, atSlot⟩ := stateTransition_slot lt
      have lower : lp.slot.toNat < height := by
        rw [← bound, atSlot]
        exact UInt64.lt_iff_toNat_lt.mp earlier
      have parents := ih lp.slot.toNat lower lpFound rpFound rfl
      -- Signatures can differ, but both successful transitions process the same message.
      obtain ⟨la, lslots, _, _, lprocess, _⟩ := stateTransition_ok lt
      obtain ⟨ra, rslots, _, _, rprocess, _⟩ := stateTransition_ok rt
      rw [parents, lmsg] at lslots
      rw [rmsg] at rslots
      have advanced := Except.ok.inj (lslots.symm.trans rslots)
      rw [advanced, lmsg] at lprocess
      rw [rmsg] at rprocess
      exact Except.ok.inj (lprocess.symm.trans rprocess)

end ForkChoice

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- Honest stores agree on blocks at shared roots.

This is a collision-exclusion hypothesis on held blocks, not hash injectivity. -/
def OneBlockPerRoot
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) : Prop :=
  ∀ v ∈ J, ∀ u ∈ J, ∀ n k (root : Root) left right,
    ((e.world n).state v).blocks[root]? = some left →
    ((e.world k).state u).blocks[root]? = some right → left = right

/-- A delayed block of an honest view passes the remaining handler checks when block validation passes.

Partial synchrony supplies view membership, not successful `onBlockWithVotes`.

The latter can fail on a carried vote even when the block transition succeeds.

This hypothesis isolates that admission gap at the receiver and at the delivery deadline. -/
def BlocksAdmitted
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (GST Δ : ℕ) : Prop :=
  ∀ v ∈ J, ∀ u ∈ J, ∀ n k signedBlock blockRoot state,
    .block signedBlock ∈ (e.world n).view v →
    ((e.world n).state v).blocks[blockRoot]? = some signedBlock.message →
    max (e.world n).time GST + Δ ≤ (e.world k).time →
    UpToDate config checks sources (e.world k).time ((e.world k).view u)
      ((e.world k).state u) →
    SszType.hashTreeRoot signedBlock.message = .ok blockRoot →
    ((e.world k).state u).validateOnBlock config checks sources signedBlock blockRoot =
      .ok state →
    ∃ after, ((e.world k).state u).onBlockWithVotes config checks sources signedBlock = .ok after

/-- Under synchrony, an up-to-date honest store holds a block that an honest store held before.

The first store holds the block at an event, and the receiver is up to date one delay later.

Both validators start from a store built from the anchor.

The two stores hold the same block wherever both hold one.

The receiver takes each signed block of its view that passes its checks of a new block.

From Gloas the receiver has verified each payload that the first store has verified.

In the first store, the chain of the block holds the finalized checkpoint of the receiver.

The receiver then holds the block.

It also finds each checkpoint block of the chain that the first store finds. -/
theorem Execution.blocks_of_partiallySynchronous {GST Δ : ℕ}
    (sync : e.PartiallySynchronous GST Δ)
    (oneBlock : OneBlockPerRoot e) (admitted : BlocksAdmitted e GST Δ)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {v u : ValidatorIndex} (honest : v ∈ J)
    (receiver : u ∈ J) {n k : ℕ}
    (late : max (e.world n).time GST + Δ ≤ (e.world k).time)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view u)
      ((e.world k).state u))
    (payloads : ∀ gloas : .glamsterdam ≤ fork, ∀ parent,
      ((e.world n).state v).isPayloadVerified gloas parent = true →
      ((e.world k).state u).isPayloadVerified gloas parent = true)
    {root : Root} {block : BeaconBlock preset fork}
    (found : ((e.world n).state v).blocks[root]? = some block)
    (final : ((e.world n).state v).getCheckpointBlock root
      ((e.world k).state u).finalizedCheckpoint.epoch =
        .ok ((e.world k).state u).finalizedCheckpoint.root) :
    ((e.world k).state u).blocks[root]? = some block ∧
      ∀ epoch checkpointRoot,
        ((e.world n).state v).getCheckpointBlock root epoch = .ok checkpointRoot →
        ((e.world k).state u).getCheckpointBlock root epoch = .ok checkpointRoot := by
  sorry

/-- Admission at an earlier event gives knownness at every later event.

Finalized-chain compatibility is checked at admission, not at the later observation.

The caller can choose a pre-boundary admission event supplied by prompt processing.

This is the persistence step of the delivery argument in arXiv 2405.00549v4, Section 2. -/
theorem Execution.blocks_after_partiallySynchronous {GST Δ : ℕ}
    (sync : e.PartiallySynchronous GST Δ)
    (oneBlock : OneBlockPerRoot e) (admitted : BlocksAdmitted e GST Δ)
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {v u : ValidatorIndex} (honest : v ∈ J)
    (receiver : u ∈ J) {n arrival k : ℕ}
    (late : max (e.world n).time GST + Δ ≤ (e.world arrival).time)
    (upToDate : UpToDate config checks sources (e.world arrival).time
      ((e.world arrival).view u) ((e.world arrival).state u))
    (payloads : ∀ gloas : .glamsterdam ≤ fork, ∀ parent,
      ((e.world n).state v).isPayloadVerified gloas parent = true →
      ((e.world arrival).state u).isPayloadVerified gloas parent = true)
    {root : Root} {block : BeaconBlock preset fork}
    (found : ((e.world n).state v).blocks[root]? = some block)
    (final : ((e.world n).state v).getCheckpointBlock root
      ((e.world arrival).state u).finalizedCheckpoint.epoch =
        .ok ((e.world arrival).state u).finalizedCheckpoint.root)
    (later : arrival ≤ k) : ((e.world k).state u).blocks[root]? = some block := by
  have held := (e.blocks_of_partiallySynchronous sync oneBlock admitted anchored start
    honest receiver late upToDate payloads found final).1
  exact e.blocks_of_le later held

end EthLib.Consensus.Models.Network
