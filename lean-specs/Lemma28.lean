/-
  Lemma 28: Window-Ancestor Voting Closure
  =========================================

  Whitepaper reference: Lemma 28, page 31

  Statement:
  If a correct node v cast the notarization vote for block b in slot s = slot(b),
  then for every slot s' ≤ s such that s' ∈ WINDOWSLOTS(s), v cast the notarization
  vote for the ancestor b' of b in slot s' = slot(b').

  Proof intuition from whitepaper:
  The condition in line 11 of Algorithm 2 (TRYNOTAR function, page 25) enforces that
  to cast a notarization vote for block b in slot s:
  - If s is the first slot: ParentReady(hash_parent) ∈ state[s]
  - If s is not the first slot: VotedNotar(hash_parent) ∈ state[s-1]

  The VotedNotar object is added to state[s-1] only when casting a notarization vote
  (line 13 of Algorithm 2). By induction, v cast notarization votes for all ancestors
  of b in slots s' < s within the same leader window.

  Formalization approach:
  Block topology models slot assignment and parent pointers. Axioms capture the
  TRYNOTAR guard behavior and window structure. The main theorem uses downward
  induction on slot distance s - s'.
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
set_option linter.unusedSectionVars false

/-! Block topology: abstracts parent pointers and slot indices for ancestry reasoning. -/

/- Block topology capturing slot index and parent pointer of each block. -/
structure BlockTopology (Hash : Type _) where
  slotOf   : Hash → Slot
  parentOf : Hash → Option Hash

namespace BlockTopology

variable (topo : BlockTopology Hash)

/- Ancestor relation: transitive closure of parent pointers. -/
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

/-! Window structure: leader windows are contiguous slot ranges starting at windowFirstSlot. -/

/- The first slot of a window belongs to the window enumeration. -/
axiom window_first_mem (cfg : VotorConfig) (s : Slot) :
    cfg.windowFirstSlot s ∈ cfg.windowSlots s

/- The window enumeration is bounded below by its first slot. -/
axiom window_first_le (cfg : VotorConfig) (s : Slot) :
    ∀ {t}, t ∈ cfg.windowSlots s → cfg.windowFirstSlot s ≤ t

/- Window slots are contiguous: if t is in the window and t < s, then t+1 is also in the window. -/
axiom window_succ_closed (cfg : VotorConfig) (s : Slot) :
    ∀ {t}, t ∈ cfg.windowSlots s → t < s → Nat.succ t ∈ cfg.windowSlots s

/-! TRYNOTAR guard axioms: capture the voting requirements from Algorithm 2, page 25. -/

/- Votes reference the slot of their block. -/
axiom vote_slot_consistency
    (topo : BlockTopology Hash)
    {votes : Finset (NotarVote Hash)} {s : Slot} {b : Hash} {v : NodeId} :
    v ∈ notarVotesFor s b votes →
    topo.slotOf b = s

/- Non-first slots in a window have a parent inside the same window. -/
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

/- Correct votes propagate to parent: if v votes for block, it must have voted for parent (line 11 of Algorithm 2). -/
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

/- Helper: if s - t = succ d, then s - (t+1) = d. -/
private lemma sub_succ_of_sub_succ
    {s t d : Nat} (h : s - t = Nat.succ d) :
    s - Nat.succ t = d := by
  revert s
  induction t with
  | zero =>
      intro s h
      cases s with
      | zero =>
          cases h
      | succ s =>
          have hs : s = d := Nat.succ_injective h
          simpa [Nat.succ_sub_one, hs]
  | succ t ih =>
      intro s h
      cases s with
      | zero =>
          simp at h
      | succ s =>
          have h' : s - t = Nat.succ d := by
            simpa [Nat.succ_sub_succ_eq_sub] using h
          have := ih h'
          simpa [Nat.succ_sub_succ_eq_sub] using this

/- Lemma 28: If a correct node v votes for block b in slot s, then for every
    slot s' ≤ s in the same window, v voted for the ancestor b' of b in slot s'. -/
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
  have h_slot_b : topo.slotOf b = s :=
    vote_slot_consistency (topo := topo) h_vote
  -- Induct on the distance s - t.
  let P : ℕ → Prop := fun d =>
    ∀ {t : Slot},
      t ∈ cfg.windowSlots s →
      t ≤ s →
      s - t = d →
      ∃ b', topo.slotOf b' = t ∧ BlockTopology.IsAncestor topo b' b ∧
            v ∈ notarVotesFor t b' votes
  have hP : ∀ d, P d := by
    refine Nat.rec ?base ?step
    · -- Base case: s - t = 0 implies t = s.
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
    · -- Inductive step: use parent pointer to step backward through ancestors.
      intro d ih t h_mem h_le h_diff
      have h_diff_succ : s - t = Nat.succ d := by simpa using h_diff
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
      set u := Nat.succ t
      have h_u_mem : u ∈ cfg.windowSlots s :=
        window_succ_closed (cfg := cfg) (s := s) h_mem h_lt
      have h_u_le : u ≤ s := Nat.succ_le_of_lt h_lt
      have h_diff_u : s - u = d :=
        sub_succ_of_sub_succ (s := s) (t := t) (d := d) h_diff_succ
      obtain ⟨bu, h_slot_bu, h_anc_bu, h_vote_bu⟩ :=
        ih h_u_mem h_u_le h_diff_u
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
      have h_vote_parent :
          v ∈ notarVotesFor (Nat.pred u) parent votes :=
        correct_vote_implies_parent_vote
          (cfg := cfg) (topo := topo) s (correct := correct)
          (slot := u) (block := bu) (parent := parent)
          h_slot_bu h_u_mem h_first_lt_u h_parent h_slot_parent
          h_vote_bu h_correct
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
  intro s' h_mem h_le
  have := hP (s - s') h_mem h_le rfl
  simpa using this

end Lemma28
end Alpenglow
