/-
  Lemma 30 (Window Ancestor Coverage with Support)
  ================================================

  We mechanize Lemma 30 from the Alpenglow whitepaper (p.31):

  > Suppose a block `b` in slot `s` is notarized or notarized-fallback. Then,
  > for every slot `s' ≤ s` such that `s' ∈ WINDOWSLOTS(s)`, there is an ancestor
  > `b'` of `b` in slot `s'`. Moreover, either correct nodes with more than 40%
  > of stake cast notarization votes for `b'`, or some correct node cast a
  > notar-fallback vote for `b'`.

  **Strategy.**
  Starting from the certificate on `b`, we obtain support for `b` in one of two
  forms: a correct-notar majority (>40% stake) or a correct notar-fallback vote.
  Majority support propagates to all ancestors via Lemma 28 (correct votes for
  the child imply votes for its parent), while notar-fallback support lifts to
  the parent using Lemma 29.  We iterate this reasoning down the window slots.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Lemma21
import Lemma23
import Lemma26
import Lemma27
import Lemma28
import Lemma29

open Classical

namespace Alpenglow
namespace Lemma30

open Lemma21
open Lemma23
open Lemma26
open Lemma28
open Lemma29

variable {Hash : Type _} [DecidableEq Hash]

/-
  ## Window and Ancestry Structure

  We introduce a mild structural axiom ensuring that every slot inside a window
  agrees on the window's first slot.  This reflects the schedule semantics from
  Algorithm 2: all slots listed by `windowSlots s` belong to the same leader
  window headed by `windowFirstSlot s`.
-/

axiom window_first_slot_eq
    (cfg : VotorConfig) (s t : Slot) :
    t ∈ cfg.windowSlots s → cfg.windowFirstSlot t = cfg.windowFirstSlot s

/-
  ## Support Predicate

  A block enjoys *support* if either correct notar voters alone contribute more
  than 40% stake, or some correct node issued a notar-fallback vote for it.
-/

def BlockSupport
    (w : StakeWeight) (correct : IsCorrect)
    (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash))
    (slot : Slot) (block : Hash) : Prop :=
  stakeSum w ((notarVotesFor slot block notarVotes).filter correct) > fallbackThreshold ∨
  ∃ n, correct n ∧ n ∈ notarFallbackVotesFor slot block fallbackVotes

/-
  Basic arithmetic helper reused from Lemma 28: lowering the predecessor slot
  decreases the distance `s - t` by one.
-/
lemma sub_succ_of_sub_succ
    {s t d : Nat} (h : s - t = Nat.succ d) :
    s - Nat.succ t = d := by
  revert s
  induction t with
  | zero =>
      intro s h
      cases s with
      | zero => cases h
      | succ s =>
          have hs : s = d := Nat.succ_injective h
          simpa [Nat.succ_sub_one, hs]
  | succ t ih =>
      intro s h
      cases s with
      | zero =>
          -- `0 - succ t = 0`, contradicting `succ d`
          simp at h
      | succ s =>
          have h' : s - t = Nat.succ d := by
            simpa [Nat.succ_sub_succ_eq_sub] using h
          have := ih h'
          simpa [Nat.succ_sub_succ_eq_sub] using this

/-
  ## Certificates Yield Support

  A notarization certificate immediately yields majority support by Lemma 23.
  A notar-fallback certificate triggers the SafeToNotar guard, which (via the
  axioms in Lemma 29) produces either a correct fallback voter or a correct
  notar majority.
-/

lemma support_of_certificate
    (w : StakeWeight) (correct : IsCorrect)
    (byzBound : ByzantineStakeBound w correct)
    (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash))
    (slot : Slot) (block : Hash)
    (h_cert :
      stakeSum w (notarVotesFor slot block notarVotes) >= notarizationThreshold ∨
      stakeSum w
          (notarVotesFor slot block notarVotes ∪
        notarFallbackVotesFor slot block fallbackVotes) >=
        notarizationThreshold) :
    BlockSupport w correct notarVotes fallbackVotes slot block := by
  classical
  cases h_cert with
  | inl h_notarized_raw =>
      -- Direct notarization: correct voters alone exceed 40% stake.
      refine Or.inl ?_
      have h_notarized :
          IsNotarized w slot block notarVotes := by
        simpa [IsNotarized] using h_notarized_raw
      have h_majority :=
        notarized_has_correct_majority w correct byzBound slot block notarVotes
          h_notarized
      simpa using h_majority
  | inr h_fallback =>
      -- SafeToNotar certificate: apply the fallback axiom from Lemma 29.
      have h :=
        certificate_yields_fallback_or_majority
          (w := w) (correct := correct) (byzBound := byzBound)
          (slot := slot) (b := block)
          (notarVotes := notarVotes) (fallbackVotes := fallbackVotes) h_fallback
      cases h with
      | inl h_fallback_vote =>
          exact Or.inr h_fallback_vote
      | inr h_majority =>
          exact Or.inl h_majority

/-
  ## Majority Support Propagates to the Parent

  Whenever correct notar voters hold >40% stake for a child block, Algorithm 2's
  guard (Lemma 28) forces those voters to also notarize the parent.  Hence the
  parent inherits the same stake majority.
-/

lemma majority_support_parent
    (cfg : VotorConfig) (topo : BlockTopology Hash)
    (w : StakeWeight) (correct : IsCorrect)
    (notarVotes : Finset (NotarVote Hash))
    (topSlot : Slot)
    {slot : Slot} {child parent : Hash}
    (h_slot_child : topo.slotOf child = slot)
    (h_child_mem : slot ∈ cfg.windowSlots topSlot)
    (h_first_lt : cfg.windowFirstSlot topSlot < slot)
    (h_parent_edge :
      topo.parentOf child = some parent ∧
      topo.slotOf parent = Nat.pred slot ∧
      Nat.pred slot ∈ cfg.windowSlots topSlot)
    (h_majority :
      stakeSum w ((notarVotesFor slot child notarVotes).filter correct) >
        fallbackThreshold) :
    stakeSum w
        ((notarVotesFor (Nat.pred slot) parent notarVotes).filter correct) >
      fallbackThreshold := by
  classical
  obtain ⟨h_parent, h_slot_parent, h_parent_mem⟩ := h_parent_edge
  -- Every correct voter for the child also votes for the parent.
  have h_subset :
      (notarVotesFor slot child notarVotes).filter correct ⊆
        (notarVotesFor (Nat.pred slot) parent notarVotes).filter correct := by
    intro n hn
    obtain ⟨h_vote_child, h_corr⟩ := Finset.mem_filter.mp hn
    have h_vote_parent :
        n ∈ notarVotesFor (Nat.pred slot) parent notarVotes := by
      -- Apply Lemma 28's parent-propagation guard.
      have h :=
        correct_vote_implies_parent_vote
          (cfg := cfg) (topo := topo) topSlot (correct := correct)
          (slot := slot) (block := child) (parent := parent)
          h_slot_child h_child_mem h_first_lt h_parent h_slot_parent
          h_vote_child h_corr
      simpa using h
    exact Finset.mem_filter.mpr ⟨h_vote_parent, h_corr⟩
  -- Stake monotonicity transports the >40% bound to the parent.
  have h_le :
      stakeSum w ((notarVotesFor slot child notarVotes).filter correct) ≤
        stakeSum w ((notarVotesFor (Nat.pred slot) parent notarVotes).filter correct) :=
    stakeSum_subset_le w _ _ h_subset
  exact lt_of_lt_of_le h_majority h_le

/-
  ## Main Result: Every Window Slot Has a Supported Ancestor
-/

theorem window_ancestors_supported
    (cfg : VotorConfig) (topo : BlockTopology Hash)
    (w : StakeWeight) (correct : IsCorrect)
    (byzBound : ByzantineStakeBound w correct)
    (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash))
    {s : Slot} {b : Hash}
    (h_slot : topo.slotOf b = s)
    (h_cert :
      stakeSum w (notarVotesFor s b notarVotes) >= notarizationThreshold ∨
      stakeSum w
          (notarVotesFor s b notarVotes ∪
            notarFallbackVotesFor s b fallbackVotes) >=
        notarizationThreshold) :
    ∀ {s'}, s' ∈ cfg.windowSlots s → s' ≤ s →
      ∃ b', topo.slotOf b' = s' ∧ BlockTopology.IsAncestor topo b' b ∧
            BlockSupport w correct notarVotes fallbackVotes s' b' := by
  classical
  -- Support at the top slot provided by the certificate.
  have h_support_top :
      BlockSupport w correct notarVotes fallbackVotes s b :=
    support_of_certificate w correct byzBound notarVotes fallbackVotes s b h_cert
  -- Recurrence over the distance `s - t`.
  have h_slot_b := h_slot
  let P : ℕ → Prop := fun d =>
    ∀ {t : Slot},
      t ∈ cfg.windowSlots s →
      t ≤ s →
      s - t = d →
      ∃ b', topo.slotOf b' = t ∧ BlockTopology.IsAncestor topo b' b ∧
            BlockSupport w correct notarVotes fallbackVotes t b'
  -- Establish `P d` for all distances by recursion on `d`.
  have hP : ∀ d, P d := by
    refine Nat.rec ?base ?step
    · -- Base case: distance zero, i.e. slot `t = s`.
      intro t h_mem h_le h_diff
      have h_zero : s - t = 0 := by simpa using h_diff
      have h_ge : s ≤ t := (Nat.sub_eq_zero_iff_le).mp h_zero
      have h_eq : t = s := Nat.le_antisymm h_le h_ge
      refine ⟨b, ?_, ?_, ?_⟩
      · simpa [h_eq] using h_slot_b
      · simpa [h_eq] using
          (BlockTopology.IsAncestor.refl (topo := topo) (b := b))
      · simpa [h_eq] using h_support_top
    · -- Inductive step: distance `Nat.succ d`.
      intro d ih t h_mem h_le h_diff
      have h_diff_succ : s - t = Nat.succ d := by simpa using h_diff
      -- Since the distance is positive, `t < s`.
      have h_lt : t < s := by
        have h_zero_ne : s - t ≠ 0 := by
          simpa [h_diff_succ] using (Nat.succ_ne_zero d)
        have h_not_le : ¬s ≤ t := by
          intro h_ge'
          have : s - t = 0 := Nat.sub_eq_zero_of_le h_ge'
          exact h_zero_ne this
        exact lt_of_not_ge h_not_le
      -- Step forward to slot `u = succ t` and invoke the induction hypothesis.
      set u := Nat.succ t
      have h_u_mem : u ∈ cfg.windowSlots s :=
        window_succ_closed (cfg := cfg) (s := s) h_mem h_lt
      have h_u_le : u ≤ s := Nat.succ_le_of_lt h_lt
      have h_diff_u :
          s - u = d :=
        by
          have := sub_succ_of_sub_succ (s := s) (t := t) (d := d) h_diff_succ
          simpa [u] using this
      -- Apply the induction hypothesis to slot `u`.
      obtain ⟨bu, h_slot_bu, h_anc_bu, h_support_bu⟩ :=
        ih h_u_mem h_u_le h_diff_u
      -- Recover the parent block inhabiting slot `t`.
      have h_first_le_t :
          cfg.windowFirstSlot s ≤ t :=
        window_first_le (cfg := cfg) (s := s) h_mem
      have h_first_lt_u :
          cfg.windowFirstSlot s < u :=
        lt_of_le_of_lt h_first_le_t (Nat.lt_succ_self t)
      have h_first_u :
          cfg.windowFirstSlot u = cfg.windowFirstSlot s :=
        window_first_slot_eq cfg s u h_u_mem
      obtain ⟨parent, h_parent, h_slot_parent, h_parent_mem⟩ :=
        parent_exists_for_slot (cfg := cfg) (topo := topo) s
          (slot := u) (block := bu)
          h_slot_bu h_u_mem (by simpa [h_first_u] using h_first_lt_u)
      -- Slot arithmetic: `Nat.pred u = t`.
      have h_slot_parent_t :
          topo.slotOf parent = t := by
        simpa [u, Nat.pred_succ] using h_slot_parent
      have h_parent_mem_t :
          t ∈ cfg.windowSlots s := by
        simpa [u, Nat.pred_succ] using h_parent_mem
      -- Establish support for the parent using the support of `bu`.
      have h_support_parent :
          BlockSupport w correct notarVotes fallbackVotes t parent := by
        cases h_support_bu with
        | inl h_majority =>
            -- Majority support propagates via notar votes.
            refine Or.inl ?_
            have h_first_lt_u' :
                cfg.windowFirstSlot s < u :=
              h_first_lt_u
            have h_parent_sup :=
              majority_support_parent (cfg := cfg) (topo := topo) (w := w)
                (correct := correct) (notarVotes := notarVotes) s
                (slot := u) (child := bu) (parent := parent)
                h_slot_bu h_u_mem h_first_lt_u'
                ⟨h_parent, h_slot_parent, h_parent_mem⟩ h_majority
            simpa [u, Nat.pred_succ] using h_parent_sup
        | inr h_fallback =>
            -- A correct notar-fallback vote for `bu` lifts to the parent.
            obtain ⟨n, h_corr, h_vote⟩ := h_fallback
            have h_support_parent_or :=
              parent_support_for_fallback
                (cfg := cfg) (topo := topo) (w := w) (correct := correct)
                (byzBound := byzBound)
                (notarVotes := notarVotes) (fallbackVotes := fallbackVotes)
                (h_slot := h_slot_bu) (h_parent := h_parent)
                (h_not_first := by
                  simpa [h_first_u] using h_first_lt_u)
                (h_vote := h_vote) (h_correct := h_corr)
            -- Reorder the disjunction to match `BlockSupport`.
            cases h_support_parent_or with
            | inl h_fallback_parent =>
                exact Or.inr (by simpa [h_slot_parent_t] using h_fallback_parent)
            | inr h_majority_parent =>
                exact Or.inl (by simpa [h_slot_parent_t] using h_majority_parent)
      -- Assemble the ancestor info for slot `t`.
      have h_anc_parent :
          BlockTopology.IsAncestor topo parent b :=
        BlockTopology.ancestor_trans (topo := topo)
          (BlockTopology.ancestor_parent (topo := topo) h_parent)
          h_anc_bu
      exact ⟨parent, h_slot_parent_t, h_anc_parent, h_support_parent⟩
  -- Instantiate the recurrence at the requested slot `s'`.
  intro s' h_mem h_le
  exact hP (s - s') h_mem h_le rfl

end Lemma30
end Alpenglow
