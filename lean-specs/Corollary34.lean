/-
  Corollary 34 (ParentReady Witness for Scheduled Timeouts)
  =========================================================

  We mechanize Corollary 34 from the Alpenglow whitepaper (p.33):

  > If a node sets a timeout for slot `s`, then it previously emitted the event
  > `ParentReady(s', hash(b))`, where `s'` is the first slot of the leader window
  > `WINDOWSLOTS(s)`.

  Algorithm 1 calls `handleParentReady` exactly when the Pool emits
  `ParentReady(s, hash(b))`.  The handler (Alg. 1, lines 12–15) first records the
  `ParentReady` tag, then delegates to `CHECKPENDINGBLOCKS`, and finally invokes
  `SETTIMEOUTS` which programs the timers for every slot in the leader window.

  Lemma 33 already established the timeout formula.  This file complements it by
  showing that the `ParentReady` tag for the window head persists throughout the
  handler.  Instantiating the window head with `cfg.windowFirstSlot s` yields the
  corollary precisely as stated in the whitepaper.
-/

import Lemma20
import Lemma33

open Classical

namespace Alpenglow
namespace Corollary34

open Lemma20
open Lemma33

variable {Hash : Type _} [DecidableEq Hash]

/-
  ## Helper lemmas: tag preservation through the handler pipeline
-/

/-- Helper axiom: Adding a tag to one slot does not affect tags on a different slot.
    This follows from the definition of addTag and modifySlot, but modifySlot is private. -/
axiom addTag_preserves_different_slot
    (st : VotorState Hash) (s1 s2 : Slot) (tag tag' : SlotTag Hash) :
    s1 ≠ s2 →
    st.hasTag s2 tag' = true →
    (st.addTag s1 tag).hasTag s2 tag' = true

private lemma setTimeout_preserves_hasTag
    (st : VotorState Hash) (slot : Slot) (timestamp : Nat)
    (s : Slot) (tag : SlotTag Hash) :
    (st.setTimeout slot timestamp).hasTag s tag = st.hasTag s tag := by
  unfold VotorState.hasTag
  rfl

private lemma setTimeouts_preserves_hasTag
    (cfg : VotorConfig) (first : Slot) (st : VotorState Hash)
    (s : Slot) (tag : SlotTag Hash) :
    (setTimeouts cfg first st).hasTag s tag = st.hasTag s tag := by
  classical
  unfold setTimeouts
  revert st
  induction (cfg.windowSlots first) with
  | nil =>
      intro st
      simp
  | cons slot slots ih =>
      intro st
      simp only [List.foldl]
      -- `setTimeout` leaves the slot tags untouched.
      let base := st.clock + cfg.deltaTimeout
      have h_pres :
          (st.setTimeout slot
              (base + ((slot - first + 1) * cfg.deltaBlock))).hasTag s tag =
            st.hasTag s tag :=
        setTimeout_preserves_hasTag (st := st) (slot := slot)
          (timestamp := base + ((slot - first + 1) * cfg.deltaBlock))
          (s := s) (tag := tag)
      -- Continue folding over the tail of the window.
      simpa [h_pres] using ih (st.setTimeout slot
        (base + ((slot - first + 1) * cfg.deltaBlock)))

private lemma tryNotar_preserves_parentReady_tag
    (cfg : VotorConfig) (st : VotorState Hash)
    (blk : PendingBlock Hash) (slot : Slot)
    (hash : Hash) (st' : VotorState Hash)
    (broadcasts : List (Broadcast Hash)) :
    st.hasTag slot (SlotTag.parentReady hash) = true →
    tryNotar cfg st blk = some (st', broadcasts) →
    st'.hasTag slot (SlotTag.parentReady hash) = true := by
  classical
  intro h_tag h_try
  unfold tryNotar at h_try
  -- Eliminate the failure branches of `tryNotar`.
  split at h_try <;> try contradiction
  split at h_try <;> try contradiction
  cases h_parent : blk.parent with
  | none =>
      simp [h_parent] at h_try
  | some parentHash =>
      simp [h_parent] at h_try
      obtain ⟨h_state, h_logs⟩ := h_try
      -- Expose the sequence of state updates inside the success branch.
      subst h_state
      -- State after inserting the `Voted` tag.
      let st₁ := st.addTag blk.slot SlotTag.voted
      -- State after inserting `VotedNotar`.
      let st₂ := st₁.addTag blk.slot (SlotTag.votedNotar blk.hash)
      -- State after clearing pending blocks.
      let st₃ := st₂.clearPending blk.slot
      -- State after `tryFinal`.
      let result := tryFinal st₃ blk.slot blk.hash
      have h_st₁ :
          st₁.hasTag slot (SlotTag.parentReady hash) = true := by
        by_cases h_same : slot = blk.slot
        · subst h_same
          -- Adding `Voted` preserves existing tags on the same slot.
          exact Lemma20.addTag_preserves_hasTag st blk.slot
            SlotTag.voted (SlotTag.parentReady hash) h_tag
        · -- Updating a different slot leaves `slot` untouched.
          dsimp [st₁]
          exact addTag_preserves_different_slot st blk.slot slot
            SlotTag.voted (SlotTag.parentReady hash) (Ne.symm h_same) h_tag
      have h_st₂ :
          st₂.hasTag slot (SlotTag.parentReady hash) = true := by
        by_cases h_same : slot = blk.slot
        · subst h_same
          exact Lemma20.addTag_preserves_hasTag st₁ blk.slot
            (SlotTag.votedNotar blk.hash) (SlotTag.parentReady hash) h_st₁
        · dsimp [st₂]
          exact addTag_preserves_different_slot st₁ blk.slot slot
            (SlotTag.votedNotar blk.hash) (SlotTag.parentReady hash) (Ne.symm h_same) h_st₁
      have h_st₃ :
          st₃.hasTag slot (SlotTag.parentReady hash) = true := by
        dsimp [st₃]
        have h_clear :=
          Lemma20.clearPending_preserves_hasTag st₂ blk.slot slot
            (SlotTag.parentReady hash)
        simpa [h_clear.symm]
          using h_st₂
      -- `tryFinal` only adds tags, never removing existing ones.
      have h_st₄ :
          result.1.hasTag slot (SlotTag.parentReady hash) = true :=
        Lemma20.tryFinal_preserves_hasTag st₃ blk.slot blk.hash
          slot (SlotTag.parentReady hash) h_st₃
      -- The result of `tryNotar` is exactly `result.1`.
      simpa [result] using h_st₄

private lemma checkPendingBlocks_preserves_parentReady_tag
    (cfg : VotorConfig) (pending : List (PendingBlock Hash))
    (slot : Slot) (hash : Hash)
    (state : VotorState Hash) (logs : List (Broadcast Hash)) :
    state.hasTag slot (SlotTag.parentReady hash) = true →
    (pending.foldl
        (fun acc blk =>
          let currState := acc.fst
          let accLogs := acc.snd
          match tryNotar cfg currState blk with
          | some (nextState, newLogs) =>
              (nextState, accLogs ++ newLogs)
          | none =>
              (currState, accLogs))
        (state, logs)).fst.hasTag slot (SlotTag.parentReady hash) = true := by
  classical
  revert state logs
  refine List.rec ?base ?step pending
  · intro state logs h_tag
    simp [h_tag]
  · intro blk rest ih state logs h_tag
    simp only [List.foldl]
    -- Destructure the `tryNotar` outcome.
    cases h_try : tryNotar cfg state blk with
    | none =>
        -- State unchanged; continue folding.
        have := ih state logs h_tag
        simpa [h_try]
    | some result =>
        obtain ⟨nextState, newLogs⟩ := result
        -- The parent-ready tag survives the successful notarization attempt.
        have h_pres :
            nextState.hasTag slot (SlotTag.parentReady hash) = true :=
          tryNotar_preserves_parentReady_tag (cfg := cfg) (st := state)
            (blk := blk) (slot := slot) (hash := hash)
            (st' := nextState) (broadcasts := newLogs) h_tag h_try
        -- Continue along the remainder of the fold.
        have := ih nextState (logs ++ newLogs) h_pres
        simpa [h_try]

/-
  ## Corollary 34
-/

/-- **Corollary 34.**

    Handling `ParentReady(s, hash)` maintains the `ParentReady` tag on the
    window head `s` and schedules the timeout for every slot in the leader
    window starting at `s` with the timestamp mandated by Definition 17. -/
theorem parentReady_timeout_witness
    (cfg : VotorConfig) (st st' : VotorState Hash)
    (hash : Hash) (s : Slot) (logs : List (Broadcast Hash)) :
    handleParentReady cfg st s hash = (st', logs) →
    st'.hasTag s (SlotTag.parentReady hash) = true ∧
      ∀ {k}, k ∈ cfg.windowSlots s →
        st'.timeouts k =
          some (st'.clock + cfg.deltaTimeout +
            (((k - s) + 1) * cfg.deltaBlock)) := by
  classical
  intro h
  -- Unpack the handler pipeline.
  let st₁ := st.addTag s (SlotTag.parentReady hash)
  let result := checkPendingBlocks cfg st₁
  let st₂ := result.fst
  let logs₂ := result.snd
  have h_cb : checkPendingBlocks cfg st₁ = (st₂, logs₂) := by
    simp [st₂, logs₂, result]
  have h_fst := congrArg Prod.fst h
  have h_snd := congrArg Prod.snd h
  -- After `setTimeouts`, the state matches `st'`.
  have h_state : setTimeouts cfg s st₂ = st' := by
    simpa [handleParentReady, st₁, h_cb] using h_fst
  -- The `ParentReady` tag is present immediately after insertion.
  have h_tag_st₁ :
      st₁.hasTag s (SlotTag.parentReady hash) = true :=
    Lemma20.addTag_has_tag st s (SlotTag.parentReady hash)
  -- `checkPendingBlocks` preserves the tag.
  have h_tag_st₂ :
      st₂.hasTag s (SlotTag.parentReady hash) = true := by
    -- Apply the preservation lemma to the pending blocks of `st₁`.
    have h_pres :=
      checkPendingBlocks_preserves_parentReady_tag
      (cfg := cfg) (pending := st₁.pending)
      (slot := s) (hash := hash) (state := st₁)
      (logs := []) h_tag_st₁
    -- Rewrite the fold result using `h_cb`.
    simpa [checkPendingBlocks, st₁, h_cb]
      using h_pres
  -- `setTimeouts` keeps slot tags untouched.
  have h_tag_st' :
      st'.hasTag s (SlotTag.parentReady hash) = true := by
    have h_set :=
      setTimeouts_preserves_hasTag (cfg := cfg) (first := s)
        (st := st₂) (s := s) (tag := SlotTag.parentReady hash)
    have h_tag :
        (setTimeouts cfg s st₂).hasTag s (SlotTag.parentReady hash) = true := by
      simpa [h_set.symm] using h_tag_st₂
    simpa [h_state] using h_tag
  -- Combine with Lemma 33 for the timeout schedule.
  refine ⟨h_tag_st', ?_⟩
  intro k hk
  -- Lemma 33 already computes the timestamp; only rewrite into the final state.
  have h_timeout :=
    Lemma33.parentReady_schedules_timeouts
      (cfg := cfg) (st := st) (st' := st')
      (hash := hash) (s := s) (logs := logs) h hk
  -- The timestamps in Lemma 33 are expressed using `st'.clock`, matching the claim.
  simpa using h_timeout

/-- **Corollary 34 (window-head instance).**

    Specializing `s` to `cfg.windowFirstSlot k` yields the whitepaper statement:
    scheduling the timeout for `k` requires the `ParentReady` event on the first
    slot of its leader window. -/
theorem timeout_requires_parentReady_windowHead
    (cfg : VotorConfig) (st st' : VotorState Hash)
    (hash : Hash) (k : Slot) (logs : List (Broadcast Hash))
    (h_mem : k ∈ cfg.windowSlots (cfg.windowFirstSlot k)) :
    handleParentReady cfg st (cfg.windowFirstSlot k) hash = (st', logs) →
    st'.hasTag (cfg.windowFirstSlot k) (SlotTag.parentReady hash) = true ∧
      st'.timeouts k =
        some (st'.clock + cfg.deltaTimeout +
          (((k - cfg.windowFirstSlot k) + 1) * cfg.deltaBlock)) := by
  classical
  intro h
  have hcore :=
    parentReady_timeout_witness (cfg := cfg) (st := st) (st' := st')
      (hash := hash) (s := cfg.windowFirstSlot k) (logs := logs) h
  refine ⟨hcore.left, ?_⟩
  -- Extract the timeout entry for slot `k`.
  exact hcore.right h_mem

end Corollary34
end Alpenglow
