/-
  Lemma 28 (Window-Ancestor Voting Closure)
  ========================================

  We mechanize Lemma 28 from the Alpenglow whitepaper (p.30):

  > If a correct node `v` cast the notarization vote for block `b` in slot
  > `s = slot(b)`, then for every slot `s' ≤ s` such that
  > `s' ∈ WINDOWSLOTS(s)`, `v` cast the notarization vote for the ancestor
  > `b'` of `b` in slot `s' = slot(b')`.

  **Whitepaper intuition:**
  Notarization votes produced by a correct node inside a leader window form a
  contiguous chain anchored at the window's first slot.  Algorithm 2 enforces
  this via the `TRYNOTAR` guard: to vote in slot `s`, the node must already
  hold `VotedNotar` for the parent block in `s-1` (or, for the first slot of
  the window, a `ParentReady` marker identifying the parent block outside the
  window).  Whenever a correct node succeeds in `TRYNOTAR`, the vote for the
  parent block is already in place.  Iterating this guard across the window
  yields the ancestry closure claimed by Lemma 28.

  **Lean strategy:**
  We introduce a lightweight block topology recording each block's slot and
  parent hash, alongside axioms abstracting the `TRYNOTAR` guard:

  * `vote_slot_consistency` — votes align with the block's slot,
  * `parent_exists_for_slot` — non-first slots obtain a parent inside the window,
  * `correct_vote_implies_parent_vote` — correct votes propagate to the parent.

  Two mild axioms about `WINDOWSLOTS` capture that leader windows are
  contiguous ranges headed by `windowFirstSlot`.  Armed with these ingredients,
  the lemma follows by downward induction on `s - s'`, successively peeling
  off parents until reaching the required ancestor slot.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Lemma20
import Lemma21

open Classical

namespace Alpenglow
namespace Lemma28

open Lemma21

variable {Hash : Type _} [DecidableEq Hash]

/-
  ## Block Topology

  We abstract the parent pointers and slot indices of blocks into a minimal
  structure that suffices for reasoning about ancestry inside a window.
-/

/-- Block topology capturing the slot index and parent pointer of every block. -/
structure BlockTopology (Hash : Type _) where
  slotOf   : Hash → Slot
  parentOf : Hash → Option Hash

namespace BlockTopology

variable (topo : BlockTopology Hash)

/-- Ancestor relation induced by repeatedly following parent pointers. -/
inductive IsAncestor : Hash → Hash → Prop
  | refl {b} : IsAncestor b b
  | step {anc parent child} :
      topo.parentOf child = some parent →
      IsAncestor anc parent →
      IsAncestor anc child

lemma ancestor_parent {parent child : Hash}
    (h : topo.parentOf child = some parent) :
    BlockTopology.IsAncestor topo parent child :=
  IsAncestor.step h IsAncestor.refl

lemma ancestor_trans {a b c : Hash}
    (h₁ : BlockTopology.IsAncestor topo a b)
    (h₂ : BlockTopology.IsAncestor topo b c) :
    BlockTopology.IsAncestor topo a c := by
  revert a h₁
  induction h₂ with
  | refl =>
      intro a h₁
      simpa using h₁
  | step h_parent h_mid ih =>
      intro a h₁
      exact IsAncestor.step h_parent (ih h₁)

end BlockTopology

/-
  ## Window Structure Axioms

  Leader windows form contiguous slot ranges headed by `windowFirstSlot`.
  We encode only the properties needed for Lemma 28.
-/

/-- The first slot of a window belongs to the window enumeration. -/
axiom window_first_mem (cfg : VotorConfig) (s : Slot) :
    cfg.windowFirstSlot s ∈ cfg.windowSlots s

/-- The window enumeration is bounded below by its first slot. -/
axiom window_first_le (cfg : VotorConfig) (s : Slot) :
    ∀ {t}, t ∈ cfg.windowSlots s → cfg.windowFirstSlot s ≤ t

/-- Window slots are contiguous: every predecessor of the top slot has its
    successor listed as well. -/
axiom window_succ_closed (cfg : VotorConfig) (s : Slot) :
    ∀ {t}, t ∈ cfg.windowSlots s → t < s → Nat.succ t ∈ cfg.windowSlots s

/-
  ## TRYNOTAR Guard Axioms

  The following axioms summarize the behaviour enforced by Algorithm 2.
-/

/-- Votes reference the slot of their block. -/
axiom vote_slot_consistency
    (topo : BlockTopology Hash)
    {votes : Finset (NotarVote Hash)} {s : Slot} {b : Hash} {v : NodeId} :
    v ∈ notarVotesFor s b votes →
    topo.slotOf b = s

/-- Non-first slots in a window have a parent inside the same window. -/
axiom parent_exists_for_slot
    (cfg : VotorConfig) (topo : BlockTopology Hash)
    (topSlot : Slot)
    {slot : Slot} {block : Hash} :
    topo.slotOf block = slot →
    slot ∈ cfg.windowSlots topSlot →
    cfg.windowFirstSlot topSlot < slot →
    ∃ parent,
      topo.parentOf block = some parent ∧
      topo.slotOf parent = Nat.pred slot ∧
      Nat.pred slot ∈ cfg.windowSlots topSlot

/-- Correct votes propagate to the parent block when TRYNOTAR succeeds. -/
axiom correct_vote_implies_parent_vote
    (cfg : VotorConfig) (topo : BlockTopology Hash)
    (topSlot : Slot) (correct : IsCorrect)
    {slot : Slot} {block parent : Hash}
    {votes : Finset (NotarVote Hash)} {v : NodeId} :
    topo.slotOf block = slot →
    slot ∈ cfg.windowSlots topSlot →
    cfg.windowFirstSlot topSlot < slot →
    topo.parentOf block = some parent →
    topo.slotOf parent = Nat.pred slot →
    v ∈ notarVotesFor slot block votes →
    correct v →
    v ∈ notarVotesFor (Nat.pred slot) parent votes

/-
  ## Lemma 28
-/

/-- Helper arithmetic fact for natural numbers. If `s - t = succ d`, then the
    predecessor slot `t.succ` pulls the difference down by one. -/
private lemma sub_succ_of_sub_succ
    {s t d : Nat} (h : s - t = Nat.succ d) :
    s - Nat.succ t = d := by
  revert s
  induction t with
  | zero =>
      intro s h
      cases s with
      | zero =>
          -- Impossible: `0 = succ d`
          cases h
      | succ s =>
          have hs : s = d := Nat.succ_injective h
          simpa [Nat.succ_sub_one, hs]
  | succ t ih =>
      intro s h
      cases s with
      | zero =>
          -- `0 - succ t = 0`, contradiction with `succ d`
          simp at h
      | succ s =>
          have h' : s - t = Nat.succ d := by
            simpa [Nat.succ_sub_succ_eq_sub] using h
          have := ih h'
          simpa [Nat.succ_sub_succ_eq_sub] using this

/-- **Lemma 28 (Voting respects window ancestry).**

    If a correct node `v` casts a notarization vote for block `b` in slot `s`,
    then for every slot `s' ≤ s` with `s' ∈ cfg.windowSlots s`, the node also
    voted for the unique ancestor `b'` of `b` that resides in slot `s'`. -/
theorem correct_node_votes_all_ancestors
    (cfg : VotorConfig) (topo : BlockTopology Hash)
    (correct : IsCorrect)
    (votes : Finset (NotarVote Hash))
    {v : NodeId} {s : Slot} {b : Hash}
    (h_vote : v ∈ notarVotesFor s b votes)
    (h_correct : correct v) :
    ∀ {s'}, s' ∈ cfg.windowSlots s → s' ≤ s →
      ∃ b', topo.slotOf b' = s' ∧ BlockTopology.IsAncestor topo b' b ∧
            v ∈ notarVotesFor s' b' votes := by
  classical
  -- Slot(s) consistency for the target block.
  have h_slot_b : topo.slotOf b = s :=
    vote_slot_consistency (topo := topo) h_vote
  -- Define the induction predicate over the distance `s - t`.
  let P : ℕ → Prop := fun d =>
    ∀ {t : Slot},
      t ∈ cfg.windowSlots s →
      t ≤ s →
      s - t = d →
      ∃ b', topo.slotOf b' = t ∧ BlockTopology.IsAncestor topo b' b ∧
            v ∈ notarVotesFor t b' votes
  -- Establish the predicate for every natural number by recursion on `d`.
  have hP : ∀ d, P d := by
    refine Nat.rec ?base ?step
    · -- Base case: `s - t = 0` implies `t = s`, so reuse the original vote.
      intro t h_mem h_le h_diff
      have h_zero : s - t = 0 := by simpa using h_diff
      have h_le' : s ≤ t :=
        (Nat.sub_eq_zero_iff_le).mp h_zero
      have h_eq : t = s := Nat.le_antisymm h_le h_le'
      refine ⟨b, ?_, ?_, ?_⟩
      · simpa [h_eq] using h_slot_b
      ·
        simpa [h_eq] using
          (BlockTopology.IsAncestor.refl (topo := topo) (b := b))
      · simpa [h_eq] using h_vote
    · -- Inductive step: strip one level of ancestry via the parent pointer.
      intro d ih t h_mem h_le h_diff
      have h_diff_succ : s - t = Nat.succ d := by simpa using h_diff
      -- Since the distance is positive, we must have `t < s`.
      have h_ne : t ≠ s := by
        intro h_eq
        have : Nat.succ d = 0 := by
          simpa [h_eq] using h_diff_succ.symm
        exact Nat.succ_ne_zero _ this
      have h_lt : t < s := by
        by_contra h_not
        have h_le' : s ≤ t := le_of_not_gt h_not
        have : s - t = 0 := Nat.sub_eq_zero_of_le h_le'
        simpa [h_diff_succ] using this
      -- Move one slot towards `s`, apply the induction hypothesis.
      set u := Nat.succ t
      have h_u_mem : u ∈ cfg.windowSlots s :=
        window_succ_closed (cfg := cfg) (s := s) h_mem h_lt
      have h_u_le : u ≤ s := Nat.succ_le_of_lt h_lt
      have h_diff_u :
          s - u = d :=
        sub_succ_of_sub_succ (s := s) (t := t) (d := d) h_diff_succ
      -- Apply the induction hypothesis to obtain the vote in slot `u`.
      obtain ⟨bu, h_slot_bu, h_anc_bu, h_vote_bu⟩ :=
        ih h_u_mem h_u_le h_diff_u
      -- Recover the parent block located in slot `t`.
      have h_first_le_t :
          cfg.windowFirstSlot s ≤ t :=
        window_first_le (cfg := cfg) (s := s) h_mem
      have h_first_lt_u :
          cfg.windowFirstSlot s < u :=
        lt_of_le_of_lt h_first_le_t (Nat.lt_succ_self t)
      obtain ⟨parent, h_parent, h_slot_parent, h_parent_mem⟩ :=
        parent_exists_for_slot (cfg := cfg) (topo := topo) s
          (slot := u) (block := bu)
          h_slot_bu h_u_mem h_first_lt_u
      -- Correctness propagates the vote to the parent slot.
      have h_vote_parent :
          v ∈ notarVotesFor (Nat.pred u) parent votes :=
        correct_vote_implies_parent_vote
          (cfg := cfg) (topo := topo) s (correct := correct)
          (slot := u) (block := bu) (parent := parent)
          h_slot_bu h_u_mem h_first_lt_u h_parent h_slot_parent
          h_vote_bu h_correct
      -- Assemble the ancestor information for slot `t = pred u`.
      have h_slot_parent_t :
          topo.slotOf parent = t := by
        simpa [u, Nat.pred_succ] using h_slot_parent
      have h_vote_parent_t :
          v ∈ notarVotesFor t parent votes := by
        simpa [u, Nat.pred_succ] using h_vote_parent
      have h_anc_parent_bu :
          BlockTopology.IsAncestor topo parent bu :=
        BlockTopology.ancestor_parent (topo := topo) h_parent
      have h_anc_parent_b :
          BlockTopology.IsAncestor topo parent b :=
        BlockTopology.ancestor_trans (topo := topo) h_anc_parent_bu h_anc_bu
      refine ⟨parent, h_slot_parent_t, h_anc_parent_b, h_vote_parent_t⟩
  -- Apply the established predicate to the requested slot `s'`.
  intro s' h_mem h_le
  have := hP (s - s') h_mem h_le rfl
  simpa using this

end Lemma28
end Alpenglow
