/-
  Lemma 38 (Notar-Fallback Certificates From Correct Majority)
  ============================================================

  Whitepaper statement (p.34):

  > If correct nodes with more than 40% of stake cast notarization votes for
  > block `b`, all correct nodes will observe a notar-fallback certificate for `b`.

  We follow the proof sketch from the whitepaper via strong induction over the
  distance between `slot(b)` and the first slot of its leader window.  The base
  case (first-slot blocks) relies on an abstract axiom stating that the
  `SafeToNotar` guard compels every correct node to either notarize or cast the
  notar-fallback vote, thereby reaching the 60% certificate threshold.  The
  inductive step handles non-first slots: once the parent block accumulates a
  notar- or notar-fallback certificate, the guard again forces notar-fallback
  votes for the child block, provided we already have a >40% correct notar
  majority for that child.  Lemma 28 supplies the link between child and parent
  notar voters.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Lemma20
import Lemma21
import Lemma23
import Lemma26
import Lemma28
import Lemma29
import Lemma30

open Classical

namespace Alpenglow
namespace Lemma38

open Lemma20
open Lemma21
open Lemma23
open Lemma26
open Lemma28
open Lemma29
open Lemma30

-- variable {Hash : Type _} [DecidableEq Hash]

/-
  ## SafeToNotar Behaviour Axioms
-/

/-- Base-case axiom: in the first slot of a leader window, a correct notar
    majority forces the notar/ fallback votes for block `b` across all correct
    nodes, yielding a notar-fallback certificate. -/
axiom first_slot_majority_certificate
    (cfg : VotorConfig) (topo : BlockTopology Hash)
    (w : StakeWeight) (correct : IsCorrect)
    (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash))
    {s : Slot} {b : Hash} :
    topo.slotOf b = s →
    cfg.windowFirstSlot s = s →
    CorrectMajorityVoted w correct s b notarVotes →
    stakeSum w
      (notarVotesFor s b notarVotes ∪
        notarFallbackVotesFor s b fallbackVotes) ≥
      notarizationThreshold

/-- Inductive-step axiom: if block `b` resides in a non-first slot, already
    enjoys a correct notar majority, and its parent carries a notar- or
    notar-fallback certificate, then `b` itself accumulates a notar-fallback
    certificate. -/
axiom majority_with_parent_certificate_propagates
    (cfg : VotorConfig) (topo : BlockTopology Hash)
    (w : StakeWeight) (correct : IsCorrect)
    (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash))
    {s : Slot} {b parent : Hash} :
    topo.slotOf b = s →
    topo.parentOf b = some parent →
    cfg.windowFirstSlot s < s →
    CorrectMajorityVoted w correct s b notarVotes →
    stakeSum w
        (notarVotesFor (topo.slotOf parent) parent notarVotes ∪
          notarFallbackVotesFor (topo.slotOf parent) parent fallbackVotes) ≥
          notarizationThreshold →
    stakeSum w
        (notarVotesFor s b notarVotes ∪
          notarFallbackVotesFor s b fallbackVotes) ≥
        notarizationThreshold

/-
  ## Lemma 38
-/

/-- **Lemma 38.** A correct notar majority for block `b` guarantees that every
    correct node observes a notar-fallback certificate for `b`. -/
theorem notar_fallback_certificate_from_correct_majority
    (cfg : VotorConfig) (topo : BlockTopology Hash)
    (w : StakeWeight) (correct : IsCorrect)
    (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash))
    {s : Slot} {b : Hash}
    (h_slot : topo.slotOf b = s)
    (h_majority : CorrectMajorityVoted w correct s b notarVotes) :
    stakeSum w
        (notarVotesFor s b notarVotes ∪
          notarFallbackVotesFor s b fallbackVotes) ≥
        notarizationThreshold := by
  classical
  -- Induction over the distance to the window head.
  set first := cfg.windowFirstSlot s with h_first
  have h_s_mem : s ∈ cfg.windowSlots s :=
    slot_in_own_window (cfg := cfg) s
  have h_first_le_s :
      first ≤ s :=
    window_first_le (cfg := cfg) (s := s) h_s_mem
  let P : Nat → Prop := fun d =>
    ∀ ⦃t : Slot⦄,
      t ∈ cfg.windowSlots s →
      cfg.windowFirstSlot t = first →
      t ≤ s →
      t - first = d →
      ∀ ⦃b_t : Hash⦄,
        topo.slotOf b_t = t →
        CorrectMajorityVoted w correct t b_t notarVotes →
        stakeSum w
            (notarVotesFor t b_t notarVotes ∪
              notarFallbackVotesFor t b_t fallbackVotes) ≥
          notarizationThreshold
  -- Establish the induction.
  have hP : ∀ d, P d := by
    refine Nat.rec ?base ?step
    · -- Base case: slot aligns with the window head.
      intro t h_mem h_first_t h_le h_diff b_t h_slot_t h_majority_t
      -- `t - first = 0` implies `t = first`.
      have h_first_le_t :
          first ≤ t :=
        window_first_le (cfg := cfg) (s := s) h_mem
      have h_eq_t_first : t = first := by
        have h_t_le_first :
            t ≤ first :=
          Nat.sub_eq_zero_iff_le.mp h_diff
        exact Nat.le_antisymm h_t_le_first h_first_le_t
      -- First-slot guard yields the certificate.
      have h_first_slot : cfg.windowFirstSlot t = t := by
        simpa [h_eq_t_first] using h_first_t
      have h_slot_eq : topo.slotOf b_t = t := h_slot_t
      simpa [h_slot_eq, h_eq_t_first] using
        first_slot_majority_certificate
          (cfg := cfg) (topo := topo)
          (w := w) (correct := correct)
          (notarVotes := notarVotes)
          (fallbackVotes := fallbackVotes)
          (s := t) (b := b_t) h_slot_t h_first_slot h_majority_t
    · -- Inductive step: move one slot closer to the window head.
      intro d ih t h_mem h_first_t h_le h_diff b_t h_slot_t h_majority_t
      -- Positive distance ⇒ non-first slot in the window.
      have h_diff_succ : t - first = Nat.succ d := by simpa using h_diff
      have h_first_le_t :
          first ≤ t :=
        window_first_le (cfg := cfg) (s := s) h_mem
      have h_first_ne_t :
          first ≠ t := by
        intro h_eq
        have : (0 : Nat) = Nat.succ d := by
          simpa [h_eq] using h_diff_succ
        exact (Nat.succ_ne_zero d) this.symm
      have h_first_lt_t :
          cfg.windowFirstSlot t < t := by
        simpa [h_first_t] using
          lt_of_le_of_ne h_first_le_t h_first_ne_t
      have h_first_lt_nat : first < t :=
        lt_of_le_of_ne h_first_le_t h_first_ne_t
      have h_first_lt_s : cfg.windowFirstSlot s < t := by
        simpa [h_first] using h_first_lt_nat
      -- Parent information supplied by Lemma 28 axioms.
      obtain ⟨parent, h_parent_edge⟩ :=
        parent_exists_for_slot
          (cfg := cfg) (topo := topo) s
          (slot := t) (block := b_t)
          h_slot_t h_mem h_first_lt_s
      obtain ⟨h_parent, h_slot_parent, h_parent_mem⟩ := h_parent_edge
      have h_parent_slot :
          topo.slotOf parent = Nat.pred t := h_slot_parent
      -- Window first-slot consistency for the parent.
      have h_first_parent :
          cfg.windowFirstSlot (Nat.pred t) = first := by
        have h_first_eq :=
          window_first_slot_eq (cfg := cfg) s (Nat.pred t) h_parent_mem
        simpa [h_first] using h_first_eq
      -- The parent resides earlier in the window.
      have h_parent_le :
          Nat.pred t ≤ s := by
        exact Nat.le_trans (Nat.pred_le _) h_le
      -- Distance drops by one.
      have h_parent_diff :
          Nat.pred t - first = d := by
        have h_sub :
            t - (first + 1) = d := by
          simpa [Nat.succ_eq_add_one, Nat.add_comm] using
            (sub_succ_of_sub_succ (s := t) (t := first) (d := d) h_diff_succ)
        have h_goal :
            t - 1 - first = t - (first + 1) := by
          simpa [Nat.add_comm] using (Nat.sub_sub t 1 first)
        simpa [Nat.pred_eq_sub_one, h_goal] using h_sub
      -- Correct notar voters for `b_t` also voted for its parent.
      have h_subset_parent :
          (notarVotesFor t b_t notarVotes).filter correct ⊆
            (notarVotesFor (Nat.pred t) parent notarVotes).filter correct := by
        intro n hn
        have h_vote_child :
            n ∈ notarVotesFor t b_t notarVotes :=
          (Finset.mem_filter.mp hn).1
        have h_corr : correct n := (Finset.mem_filter.mp hn).2
        have h_vote_parent :
            n ∈ notarVotesFor (Nat.pred t) parent notarVotes :=
          correct_vote_implies_parent_vote
            (cfg := cfg) (topo := topo)
            s (correct := correct)
            (slot := t) (block := b_t) (parent := parent)
            h_slot_t h_mem h_first_lt_s h_parent h_slot_parent
            h_vote_child h_corr
        exact Finset.mem_filter.mpr ⟨h_vote_parent, h_corr⟩
      -- Transfer the >40% bound to the parent.
      have h_parent_majority :
          CorrectMajorityVoted w correct (Nat.pred t) parent notarVotes := by
        unfold CorrectMajorityVoted at h_majority_t ⊢
        exact lt_of_lt_of_le h_majority_t
          (stakeSum_subset_le w
            ((notarVotesFor t b_t notarVotes).filter correct)
            ((notarVotesFor (Nat.pred t) parent notarVotes).filter correct)
            h_subset_parent)
      -- Apply the induction hypothesis to the parent block.
      have h_parent_cert :=
        ih h_parent_mem h_first_parent h_parent_le h_parent_diff
          (b_t := parent) h_parent_slot h_parent_majority
      -- SafeToNotar guard propagates the certificate to `b_t`.
      exact
        majority_with_parent_certificate_propagates
          (cfg := cfg) (topo := topo)
          (w := w) (correct := correct)
          (notarVotes := notarVotes)
          (fallbackVotes := fallbackVotes)
          (s := t) (b := b_t) (parent := parent)
          h_slot_t h_parent h_first_lt_t h_majority_t
          (by simpa [h_parent_slot] using h_parent_cert)
  -- Instantiate the induction for `t = s`.
  have h_first_s : cfg.windowFirstSlot s = first := h_first
  exact
    hP (s - first) h_s_mem h_first_s (le_of_eq rfl) rfl h_slot h_majority

end Lemma38
end Alpenglow
