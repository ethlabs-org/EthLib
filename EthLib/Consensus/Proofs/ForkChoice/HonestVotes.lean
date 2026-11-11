module

public import EthLib.Consensus.Proofs.ForkChoice.HonestDuties
public import EthLib.Consensus.Proofs.ForkChoice.VoteOrigins
public import EthLib.Consensus.Proofs.Models.Network.Signers

/-!
# Statements: the votes that honest stores hold for honest validators

This file states part of step 3 of the plan for the safety of the fast confirmation rule.

The rule is that of [arXiv 2405.00549v4][fcr].

The proofs are placeholders, and each statement may still change.

Each statement of an honest validator in a sent message is a vote that its duty allowed.

Two such statements of one validator are never slashable together.

So no honest store counts an honest validator among the equivocators.

Each latest vote of an honest store comes from a statement of a message of its view.

So the latest vote that an honest store holds for an honest validator is a vote of its duty.

Two lemmas of [verified-fast-confirmation][vfc] state the same facts.

They are `Execution.honest_not_equivocating` and `Execution.latest_message_eq_honest_vote`.

There the premises `no_forgery`, `not_slashable` and `votes_assigned` are assumed.

Here the network model and the duty of an honest validator give them.

[fcr]: https://arxiv.org/abs/2405.00549v4
[vfc]: https://github.com/fradamt/verified-fast-confirmation
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- A statement of an honest validator in a sent message is a vote that its duty allowed.

The validator could sign it at an earlier event, with its view and its store there. -/
theorem Execution.exists_maySign_of_signed {n : ℕ} {m : Message preset fork}
    (sent : m ∈ (e.world n).sent) {v : ValidatorIndex} {data : AttestationData}
    (signed : (v, data) ∈ statements config checks anchorState anchorBlock m) (honest : v ∈ J) :
    ∃ k < n, MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
      (e.world k).time ((e.world k).view v) ((e.world k).state v) data := by
  obtain ⟨k, before, first, sends, carries, fresh⟩ :=
    e.exists_first_send_of_signed sent signed honest
  have allowed := e.allowed_world k
  rw [sends] at allowed
  rcases allowed.2 honest (v, data) carries rfl with ⟨earlier, seen, carried⟩ | duty
  · exact (fresh earlier (e.view_subset_sent k v seen) carried).elim
  · exact ⟨k, before, duty⟩

/-- Two statements of one honest validator in sent messages are not slashable together.

Slots must last a positive time, so that one time is the attestation deadline of one slot. -/
theorem Execution.isSlashableAttestationData_of_signed (slots : 0 < config.SLOT_DURATION_MS)
    {n : ℕ} {first second : Message preset fork} (sentFirst : first ∈ (e.world n).sent)
    (sentSecond : second ∈ (e.world n).sent) {v : ValidatorIndex} {data other : AttestationData}
    (signedFirst : (v, data) ∈ statements config checks anchorState anchorBlock first)
    (signedSecond : (v, other) ∈ statements config checks anchorState anchorBlock second)
    (honest : v ∈ J) : isSlashableAttestationData data other = false := by
  obtain ⟨k, _, first, firstEvent, firstSigned, firstFresh⟩ :=
    e.exists_first_send_of_signed sentFirst signedFirst honest
  obtain ⟨l, _, second, secondEvent, secondSigned, secondFresh⟩ :=
    e.exists_first_send_of_signed sentSecond signedSecond honest
  have firstAllowed := e.allowed_world k
  have secondAllowed := e.allowed_world l
  rw [firstEvent] at firstAllowed
  rw [secondEvent] at secondAllowed
  have firstDuty := firstAllowed.2 honest (v, data) firstSigned rfl
  have secondDuty := secondAllowed.2 honest (v, other) secondSigned rfl
  rcases firstDuty with ⟨m, seen, signed⟩ | firstDuty
  · exact (firstFresh m (e.view_subset_sent k v seen) signed).elim
  rcases secondDuty with ⟨m, seen, signed⟩ | secondDuty
  · exact (secondFresh m (e.view_subset_sent l v seen) signed).elim
  obtain ⟨i, assigned, deadline, _, _, made, protection⟩ := firstDuty
  obtain ⟨j, assigned', deadline', _, _, made', protected'⟩ := secondDuty
  rcases lt_trichotomy k l with before | same | after
  · apply (protected' first (e.monotone_view v before ?_) (v, data) firstSigned rfl).1
    simp [e.world_succ, firstEvent, World.apply]
  · subst l
    -- At one event, a positive slot duration fixes the slot and hence the duty data.
    obtain ⟨s, d, slotOk, dueOk, atTime⟩ := deadline
    obtain ⟨s', d', slotOk', dueOk', atTime'⟩ := deadline'
    have dueSame := Except.ok.inj (dueOk.symm.trans dueOk')
    subst d'
    have startSame : s = s' := UInt64.toNat_inj.mp (by omega)
    subst s'
    have slotSame := Except.ok.inj
      ((computeSlotAtTimeMs_computeTimeAtSlotMs slots slotOk).symm.trans
        (computeSlotAtTimeMs_computeTimeAtSlotMs slots slotOk'))
    rw [← slotSame, assigned] at assigned'
    have indexSame := Option.some.inj assigned'
    subst j
    obtain ⟨head, block, hs, state, h, b, st, look, dataOk⟩ := made
    obtain ⟨head', block', hs', state', h', b', st', look', dataOk'⟩ := made'
    have he := Except.ok.inj (h.symm.trans h')
    subst head'
    have be := Option.some.inj (b.symm.trans b')
    subst block'
    have se := Except.ok.inj (st.symm.trans st')
    subst hs'
    rw [← slotSame, look] at look'
    have le := Except.ok.inj look'
    subst state'
    have de := Except.ok.inj (dataOk.symm.trans dataOk')
    change data = other at de
    subst other
    exact isSlashableAttestationData_self data
  · apply (protection second (e.monotone_view v after ?_) (v, other) secondSigned rfl).2
    simp [e.world_succ, secondEvent, World.apply]

/-- No honest store counts an honest validator among the equivocators.

Each honest validator must start with no equivocator.

Slots must last a positive time. -/
theorem Execution.not_mem_equivocatingIndices (slots : 0 < config.SLOT_DURATION_MS)
    (start : ∀ u ∈ J, (e.start u).equivocatingIndices = []) {u v : ValidatorIndex}
    (receiver : u ∈ J) (honest : v ∈ J) (n : ℕ) :
    v ∉ ((e.world n).state u).equivocatingIndices := by
  have updated : ∀ (s : Store preset fork) j f,
      (s.updateCheckpoints j f).equivocatingIndices = s.equivocatingIndices := by
    intro s j f
    by_cases hj : s.justifiedCheckpoint.epoch < j.epoch <;>
      by_cases hf : s.finalizedCheckpoint.epoch < f.epoch <;>
      simp [Store.updateCheckpoints, hj, hf]
  have tickSlot : ∀ {s s' : Store preset fork} {t},
      s.onTickPerSlot config t = .ok s' → s'.equivocatingIndices = s.equivocatingIndices := by
    intro s s' t step
    unfold Store.onTickPerSlot at step
    simp only [bind_ok_iff] at step
    obtain ⟨_, _, _, _, step⟩ := step
    split at step <;>
      · obtain ⟨_, _, step⟩ := step
        split at step <;> simp only [pure, Except.pure, Except.ok.injEq] at step <;>
          subst s' <;> simp only [updated]
  have catchUp : ∀ {s s' : Store preset fork} {slot},
      Store.catchUp config s slot = .ok s' → s'.equivocatingIndices = s.equivocatingIndices := by
    intro s s' slot step
    induction s using Store.catchUp.induct config slot with
    | _ s ih =>
      rw [Store.catchUp.eq_1] at step
      simp only [bind_ok_iff] at step
      obtain ⟨_, _, step⟩ := step
      split at step
      · simp only [bind_ok_iff] at step
        obtain ⟨_, _, _, _, ticked, tick, step⟩ := step
        split at step
        · exact (ih ticked ‹_› step).trans (tickSlot tick)
        · cases step
      · simp only [pure, Except.pure, Except.ok.injEq] at step
        exact congrArg Store.equivocatingIndices step.symm
  have attestation : ∀ {s s' : Store preset fork} {a b},
      s.onAttestation config checks a b = .ok s' →
        s'.equivocatingIndices = s.equivocatingIndices := by
    intro s s' a b step
    unfold Store.onAttestation at step
    simp only [bind_ok_iff] at step
    obtain ⟨_, _, stored, storing, _, _, _, _, _, _, _, _, step⟩ := step
    split at step
    · simp only [pure, Except.pure, Except.ok.injEq] at step
      subst s'
      change stored.equivocatingIndices = s.equivocatingIndices
      unfold Store.storeTargetCheckpointState at storing
      split at storing
      · simp only [pure, Except.pure, Except.ok.injEq] at storing
        exact congrArg Store.equivocatingIndices storing.symm
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at storing
        obtain ⟨_, _, rfl⟩ := storing
        rfl
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at step
  have block : ∀ {s s' : Store preset fork} {signed},
      s.onBlock config checks sources signed = .ok s' →
        s'.equivocatingIndices = s.equivocatingIndices := by
    intro s s' signed step
    cases root : SszType.hashTreeRoot signed.message with
    | error err => simp [Store.onBlock, root, bind, Except.bind, Except.mapError] at step
    | ok blockRoot =>
      by_cases known : s.blocks.contains blockRoot
      · rw [Store.onBlock_known root known] at step
        exact congrArg Store.equivocatingIndices (Except.ok.inj step).symm
      simp only [Store.onBlock, root, known, bind, Except.bind, Except.mapError,
        ↓reduceIte, Bool.false_eq_true] at step
      unfold Store.addBlock at step
      simp only [bind_ok_iff] at step
      obtain ⟨state, _, head, _, voted, vote, recorded, record, boosted, boost, step⟩ := step
      obtain ⟨_, _, rfl⟩ := Store.recordBlockPtcVotes_onlyPtcVotes vote
      have recordedKept : recorded.equivocatingIndices = s.equivocatingIndices := by
        unfold Store.recordBlockTimeliness at record
        simp only [bind_ok_iff, pure, Except.pure] at record
        obtain ⟨_, _, _, _, _, _, _, _, record⟩ := record
        split at record
        · simp only [bind_ok_iff, Except.ok.injEq] at record
          obtain ⟨_, _, rfl⟩ := record
          rfl
        · cases record; rfl
      have boostedKept : boosted.equivocatingIndices = recorded.equivocatingIndices := by
        unfold Store.updateProposerBoostRoot at boost
        split at boost
        rotate_left
        · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at boost
        simp only [bind_ok_iff, pure_bind] at boost
        obtain ⟨_, _, _, _, _, _, boost⟩ := boost
        split at boost <;> simp only [pure, Except.pure, Except.ok.injEq] at boost <;>
          subst boosted <;> rfl
      have pulled : ∀ {s s' : Store preset fork} {root},
          s.computePulledUpTip config root = .ok s' →
            s'.equivocatingIndices = s.equivocatingIndices := by
        have unrealized : ∀ (s : Store preset fork) j f,
            (s.updateUnrealizedCheckpoints j f).equivocatingIndices =
              s.equivocatingIndices := by
          intro s j f
          by_cases hj : s.unrealizedJustifiedCheckpoint.epoch < j.epoch <;>
            by_cases hf : s.unrealizedFinalizedCheckpoint.epoch < f.epoch <;>
            simp [Store.updateUnrealizedCheckpoints, hj, hf]
        intro s s' root step
        unfold Store.computePulledUpTip at step
        simp only [bind_ok_iff] at step
        obtain ⟨_, _, _, _, _, _, _, _, step⟩ := step
        split at step <;> simp only [pure, Except.pure, Except.ok.injEq] at step <;>
          subst s' <;> simp only [updated, unrealized]
      rw [pulled step]
      rw [updated, boostedKept, recordedKept]
  have foldStep : ∀ {α : Type} (xs : List α) (f : Store preset fork → α →
      Except ForkChoiceError (Store preset fork)) (P : Store preset fork → Prop),
      (∀ a ∈ xs, ∀ s s', P s → f s a = .ok s' → P s') →
      ∀ s s', P s → xs.foldlM f s = .ok s' → P s' := by
    intro α xs f P
    induction xs with
    | nil =>
      intro _ s s' holds step
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at step
      exact step ▸ holds
    | cons a rest ih =>
      intro keeps s s' holds step
      rw [List.foldlM_cons, bind_ok_iff] at step
      obtain ⟨mid, first, restOk⟩ := step
      exact ih (fun a mem => keeps a (List.mem_cons_of_mem _ mem)) mid s'
        (keeps a List.mem_cons_self s mid holds first) restOk
  induction n with
  | zero => simp [e.world_zero, World.initial, start u receiver]
  | succ n ih =>
    -- A valid slashing cannot contain this honest validator in both indexed votes.
    have slashing : ∀ {s s' : Store preset fork} {sl : AttesterSlashing preset fork},
        (∃ m ∈ (e.world n).view u,
          indexedStatements sl.attestation1 ∪ indexedStatements sl.attestation2 ⊆
            statements config checks anchorState anchorBlock m) →
        v ∉ s.equivocatingIndices → s.onAttesterSlashing config checks sl = .ok s' →
        v ∉ s'.equivocatingIndices := by
      intro s s' sl ⟨m, seen, carries⟩ absent step
      unfold Store.onAttesterSlashing at step
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
      obtain ⟨_, valid, rfl⟩ := step
      have notBoth : v ∉ sl.attestation1.attestingIndices.data.toList.filter
          (· ∈ sl.attestation2.attestingIndices.data.toList) := by
        intro both
        simp only [List.mem_filter, decide_eq_true_eq] at both
        have safe := e.isSlashableAttestationData_of_signed slots
          (e.view_subset_sent n u seen) (e.view_subset_sent n u seen)
          (carries (Or.inl ⟨by simpa using both.1, rfl⟩))
          (carries (Or.inr ⟨by simpa using both.2, rfl⟩)) honest
        simp [Store.validateOnAttesterSlashing, safe, throw, throwThe,
          MonadExceptOf.throw, bind, Except.bind] at valid
      change v ∉ List.foldl _ s.equivocatingIndices _
      clear valid
      generalize sl.attestation1.attestingIndices.data.toList.filter
        (· ∈ sl.attestation2.attestingIndices.data.toList) = indices at *
      induction indices generalizing s with
      | nil => exact absent
      | cons index rest ih =>
        rw [List.foldl_cons]
        split
        · exact ih absent (fun h => notBoth (List.mem_cons_of_mem _ h))
        · exact ih (s := { s with equivocatingIndices := s.equivocatingIndices ++ [index] })
            (by simp_all) (fun h => notBoth (List.mem_cons_of_mem _ h))
    rcases e.state_succ n u with same | ⟨_, handles⟩
    · simpa only [same] using ih
    cases handles with
    | tick _ _ step =>
      unfold Store.onTick at step
      simp only [bind_ok_iff] at step
      obtain ⟨_, _, _, caught, ticked⟩ := step
      simpa only [tickSlot ticked, catchUp caught] using ih
    | attestation _ step => simpa only [attestation step] using ih
    | attesterSlashing seen step => exact slashing ⟨_, seen, fun _ h => h⟩ ih step
    | block seen step =>
      rename_i signed
      unfold Store.onBlockWithVotes at step
      simp only [bind_ok_iff, ← Array.foldlM_toList] at step
      obtain ⟨blocked, blockOk, voted, votesOk, slashingsOk⟩ := step
      have blockedOk : v ∉ blocked.equivocatingIndices := by
        simpa only [block blockOk] using ih
      have votedOk : v ∉ voted.equivocatingIndices :=
        foldStep _ _ (fun s => v ∉ s.equivocatingIndices)
          (fun _ _ _ _ absent step => by simpa only [attestation step] using absent)
          blocked voted blockedOk votesOk
      exact foldStep _ _ (fun s => v ∉ s.equivocatingIndices)
        (fun sl mem _ _ absent step => slashing
          ⟨.block signed, seen, fun _ h => Or.inr ⟨sl, by simpa using mem, h⟩⟩ absent step)
        voted _ votedOk slashingsOk
    | payloadAttestation _ step =>
      obtain ⟨_, _, same⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes step
      simpa only [same] using ih
    | envelope _ step =>
      obtain ⟨_, _, _, _, _, record, same⟩ := Store.onExecutionPayloadEnvelope_ok step
      rw [same]
      obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
      exact ih
    | inclusionList _ step =>
      obtain ⟨_, _, same⟩ := Store.onInclusionList_ok ‹_› step
      simpa only [same] using ih

/-- Each latest vote of an honest store is a statement of a message of its view.

Each honest validator must start from a store built from the anchor. -/
theorem Execution.exists_signed_of_latestMessages {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {u : ValidatorIndex} (receiver : u ∈ J) {n : ℕ}
    {v : ValidatorIndex} {message : LatestMessage fork}
    (found : ((e.world n).state u).latestMessages[v]? = some message) :
    ∃ attestation : Attestation preset fork, ∃ m ∈ (e.world n).view u,
      message = LatestMessage.ofAttestation attestation ∧
      (v, attestation.data) ∈ statements config checks anchorState anchorBlock m := by
  let Origin := fun (view : Set (Message preset fork)) (store : Store preset fork) =>
    ∀ (v : ValidatorIndex) (message : LatestMessage fork),
      store.latestMessages[v]? = some message →
      ∃ a : Attestation preset fork, ∃ m ∈ view,
        message = LatestMessage.ofAttestation a ∧
          (v, a.data) ∈ statements config checks anchorState anchorBlock m
  have attestationStep : ∀ {store after : Store preset fork} {view}
      {a : Attestation preset fork} {fromBlock : Bool},
      Store.Reachable config anchorState anchorBlock store → Origin view store →
      (∃ m ∈ view, attestationStatements (config := config) (checks := checks)
        anchorState anchorBlock a ⊆ statements config checks anchorState anchorBlock m) →
      store.onAttestation config checks a fromBlock = .ok after → Origin view after := by
    intro store after view a fromBlock reachable old ⟨m, seen, carried⟩ handled v message found
    unfold Store.onAttestation at handled
    simp only [bind_ok_iff] at handled
    obtain ⟨_, _, stored, storing, target, targetOk, _, _, indexed, indexedOk,
      valid, validOk, handled⟩ := handled
    split at handled
    · rename_i validTrue
      simp only [pure, Except.pure, Except.ok.injEq] at handled
      subst after
      rcases Store.foldl_recordVote_cases _ _ found with previous | ⟨member, same⟩
      · have kept : stored.latestMessages = store.latestMessages := by
          unfold Store.storeTargetCheckpointState at storing
          split at storing
          · simp only [pure, Except.pure, Except.ok.injEq] at storing
            exact congrArg Store.latestMessages storing.symm
          · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at storing
            obtain ⟨_, _, rfl⟩ := storing
            rfl
        exact old v message (kept ▸ previous)
      · have indexedOk := mapError_ok_iff.mp indexedOk
        have dataSame : indexed.data = a.data := by
          obtain ⟨indices, indicesOk, _⟩ := getAttestingIndices_of_getIndexedAttestation indexedOk
          obtain ⟨indexed', made, _, dataSame, _⟩ :=
            getIndexedAttestation_of_getAttestingIndices indicesOk
          have same := Except.ok.inj (indexedOk.symm.trans made)
          exact same ▸ dataSame
        refine ⟨a, m, seen, same, carried ?_⟩
        exact ⟨store, indexed, reachable,
          ⟨stored, target, storing, targetOk, indexedOk,
            by simpa [validTrue] using mapError_ok_iff.mp validOk⟩,
          by simpa [indexedStatements, dataSame] using member⟩
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at handled
  have foldStep : ∀ {α : Type} (xs : List α) (f : Store preset fork → α →
      Except ForkChoiceError (Store preset fork)) (P : Store preset fork → Prop),
      (∀ a ∈ xs, ∀ s s', P s → f s a = .ok s' → P s') →
      ∀ s s', P s → xs.foldlM f s = .ok s' → P s' := by
    intro α xs f P
    induction xs with
    | nil =>
      intro _ s s' holds step
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at step
      exact step ▸ holds
    | cons a rest ih =>
      intro keeps s s' holds step
      rw [List.foldlM_cons, bind_ok_iff] at step
      obtain ⟨mid, first, restOk⟩ := step
      exact ih (fun a mem => keeps a (List.mem_cons_of_mem _ mem)) mid s'
        (keeps a List.mem_cons_self s mid holds first) restOk
  have invariant : ∀ n, Origin ((e.world n).view u) ((e.world n).state u) := by
    intro n
    induction n with
    | zero =>
      intro v message found
      change (e.start u).latestMessages[v]? = some message at found
      obtain ⟨_, _, empty, _⟩ := getForkchoiceStore_fields anchored
      rw [start u receiver, empty] at found
      simp at found
    | succ n ih =>
      have extend : ∀ {s}, Origin ((e.world n).view u) s →
          Origin ((e.world (n + 1)).view u) s := by
        intro s origin v message found
        obtain ⟨a, m, seen, same, signed⟩ := origin v message found
        exact ⟨a, m, e.monotone_view u (Nat.le_succ n) seen, same, signed⟩
      rcases e.state_succ n u with same | ⟨_, handles⟩
      · rw [same]
        exact extend ih
      apply extend
      have reachable := e.reachable
        (fun w hw => (start w hw) ▸ Store.Reachable.anchor anchored) n u receiver
      cases handles with
      | tick _ _ ticked =>
        intro v message found
        exact ih v message ((Store.onTick_checkpointStates_latestMessages ticked).2 ▸ found)
      | attestation seen handled =>
        exact attestationStep reachable ih ⟨_, seen, fun _ h => h⟩ handled
      | attesterSlashing _ handled =>
        intro v message found
        exact ih v message
          ((Store.onAttesterSlashing_checkpointStates_latestMessages handled).2 ▸ found)
      | block seen handled =>
        rename_i signed
        unfold Store.onBlockWithVotes at handled
        simp only [bind_ok_iff, ← Array.foldlM_toList] at handled
        obtain ⟨blocked, blockOk, voted, votedOk, slashedOk⟩ := handled
        -- Each carried attestation is read in its own reachable intermediate store.
        let P := fun s => Store.Reachable config anchorState anchorBlock s ∧
          Origin ((e.world n).view u) s
        have blockedP : P blocked := ⟨reachable.block blockOk, fun v message found =>
          ih v message ((Store.onBlock_checkpointStates_latestMessages blockOk).2 ▸ found)⟩
        have votedP : P voted := foldStep _ _ P (fun a mem s s' holds step =>
          ⟨holds.1.attestation step, attestationStep holds.1 holds.2
            ⟨.block signed, seen, fun _ statement =>
              Or.inl ⟨a, by simpa using mem, statement⟩⟩
            step⟩) blocked voted blockedP votedOk
        exact (foldStep _ _ P (fun sl _ s s' holds step =>
          ⟨holds.1.attesterSlashing step, fun v message found => holds.2 v message
            ((Store.onAttesterSlashing_checkpointStates_latestMessages step).2 ▸ found)⟩)
          voted _ votedP slashedOk).2
      | payloadAttestation _ handled =>
        obtain ⟨_, _, same⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes handled
        rw [same]
        exact ih
      | envelope _ handled =>
        obtain ⟨_, _, _, _, _, record, same⟩ := Store.onExecutionPayloadEnvelope_ok handled
        rw [same]
        obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
        exact ih
      | inclusionList _ handled =>
        obtain ⟨_, _, same⟩ := Store.onInclusionList_ok ‹_› handled
        rw [same]
        exact ih
  exact invariant n v message found

/-- The latest vote that an honest store holds for an honest validator is a vote of its duty.

The validator could sign its data at an earlier event, with its view and its store there.

Each honest validator must start from a store built from the anchor. -/
theorem Execution.exists_maySign_of_latestMessages {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ u ∈ J, e.start u = anchor) {u v : ValidatorIndex} (receiver : u ∈ J)
    (honest : v ∈ J) {n : ℕ} {message : LatestMessage fork}
    (found : ((e.world n).state u).latestMessages[v]? = some message) :
    ∃ attestation : Attestation preset fork, ∃ k < n,
      message = LatestMessage.ofAttestation attestation ∧
      MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
        (e.world k).time ((e.world k).view v) ((e.world k).state v) attestation.data := by
  obtain ⟨attestation, m, seen, same, signed⟩ :=
    e.exists_signed_of_latestMessages anchored start receiver found
  obtain ⟨k, before, duty⟩ :=
    e.exists_maySign_of_signed (e.view_subset_sent n u seen) signed honest
  exact ⟨attestation, k, before, same, duty⟩

end EthLib.Consensus.Models.Network
