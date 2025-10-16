/-
  Lemma 31: Same-Window Finalization Ancestry

  Reference: Alpenglow whitepaper, page 32

  Statement: Suppose some correct node finalizes a block b_i and b_k is a block
  in the same leader window with slot(b_i) <= slot(b_k). If any correct node
  observes a notarization or notar-fallback certificate for b_k, then b_k is a
  descendant of b_i.

  Proof (from whitepaper):
  Assume b_k is not a descendant of b_i. By Lemmas 21 and 26, slot(b_i) ≠ slot(b_k),
  so slot(b_i) < slot(b_k). By Lemma 30, there is an ancestor b_j of b_k in slot
  slot(b_i) + 1 with support (either >40% correct notarization votes or a correct
  notar-fallback vote). The parent b'_i of b_j lives in slot(b_i) but differs from b_i.

  If a correct node cast a notar-fallback vote for b_j, by Definition 16, b'_i is
  notarized or notarized-fallback, contradicting Lemmas 21 or 26.

  Otherwise, if correct nodes with >40% stake cast notarization votes for b_j, by
  Lemma 28, these nodes also cast notarization votes for b'_i, contradicting Lemma 23.
-/

import Mathlib.Data.Nat.Basic
import Lemma21
import Lemma23
import Lemma28
import Lemma29
import Lemma30

open Classical

namespace Alpenglow
namespace Lemma31

open Lemma21
open Lemma23
open Lemma28
open Lemma29
open Lemma30
open BlockTopology

variable {Hash : Type _} [DecidableEq Hash]

/- Slot exclusivity: no competing block in slot s can achieve notarization
    or notar-fallback certification. This captures the exclusivity property from
    Lemmas 21 and 26. -/
def SlotExclusive
    (topo : BlockTopology Hash)
    (w : StakeWeight)
    (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash))
    (s : Slot) (main : Hash) : Prop :=
  ∀ ⦃b : Hash⦄, topo.slotOf b = s → b ≠ main →
    stakeSum w (notarVotesFor s b notarVotes) < notarizationThreshold ∧
      stakeSum w
          (notarVotesFor s b notarVotes ∪
            notarFallbackVotesFor s b fallbackVotes) <
        notarizationThreshold

/- Lemma 31: If b_i is finalized and b_k has a certificate in the same leader
    window with slot(b_i) <= slot(b_k), then b_k descends from b_i. -/
theorem descendant_of_finalized_window_block
    (cfg : VotorConfig) (topo : BlockTopology Hash)
    (w : StakeWeight) (correct : IsCorrect)
    (byzBound : ByzantineStakeBound w correct)
    (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash))
    {b_i b_k : Hash} {s_i s_k : Slot}
    (_h_slot_i : topo.slotOf b_i = s_i)
    (h_slot_k : topo.slotOf b_k = s_k)
    (h_window : s_i ∈ cfg.windowSlots s_k)
    (h_slot_le : s_i ≤ s_k)
    (h_notarized_bi :
      stakeSum w (notarVotesFor s_i b_i notarVotes) >= notarizationThreshold)
    (h_exclusive :
      SlotExclusive topo w notarVotes fallbackVotes s_i b_i)
    (h_cert_k :
      stakeSum w (notarVotesFor s_k b_k notarVotes) >= notarizationThreshold ∨
      stakeSum w
          (notarVotesFor s_k b_k notarVotes ∪
            notarFallbackVotesFor s_k b_k fallbackVotes) >=
        notarizationThreshold) :
    IsAncestor topo b_i b_k := by
  classical

  -- Apply Lemma 30: any slot in the window has an ancestor of b_k with support
  -- (either >40% correct notarization votes or a correct notar-fallback vote).
  have h_window_support :
      ∀ {s'}, s' ∈ cfg.windowSlots s_k → s' ≤ s_k →
        ∃ b', topo.slotOf b' = s' ∧ BlockTopology.IsAncestor topo b' b_k ∧
              BlockSupport w correct notarVotes fallbackVotes s' b' :=
    window_ancestors_supported
      (cfg := cfg) (topo := topo) (w := w) (correct := correct)
      (byzBound := byzBound) (notarVotes := notarVotes)
      (fallbackVotes := fallbackVotes)
      (s := s_k) (b := b_k) h_slot_k h_cert_k

  -- Proof by contradiction: assume b_k is not a descendant of b_i.
  by_contra h_not_descends

  have h_bk_ne_bi : b_k ≠ b_i := by
    intro h_eq
    apply h_not_descends
    simpa [h_eq] using (IsAncestor.refl (topo := topo) (b := b_i))

  -- By Lemmas 21 and 26: slot(b_i) ≠ slot(b_k), otherwise exclusivity is violated.
  have h_si_ne_sk : s_i ≠ s_k := by
    intro h_eq
    have h_slot_bk_si : topo.slotOf b_k = s_i := by
      simp [h_eq, h_slot_k]
    obtain ⟨h_notar_lt, h_union_lt⟩ :=
      h_exclusive h_slot_bk_si h_bk_ne_bi
    cases h_cert_k with
    | inl h_notar_ge =>
        have h_notar_ge' : stakeSum w (notarVotesFor s_i b_k notarVotes) >= notarizationThreshold := by
          simp [← h_eq] at h_notar_ge
          exact h_notar_ge
        exact (not_lt_of_ge h_notar_ge') h_notar_lt
    | inr h_union_ge =>
        have h_union_ge' : stakeSum w (notarVotesFor s_i b_k notarVotes ∪
                                         notarFallbackVotesFor s_i b_k fallbackVotes) >= notarizationThreshold := by
          simp [← h_eq] at h_union_ge
          exact h_union_ge
        exact (not_lt_of_ge h_union_ge') h_union_lt

  have h_si_lt_sk : s_i < s_k := lt_of_le_of_ne h_slot_le h_si_ne_sk

  have h_succ_mem :
      Nat.succ s_i ∈ cfg.windowSlots s_k :=
    window_succ_closed (cfg := cfg) (s := s_k) h_window h_si_lt_sk

  -- Obtain b_j: the ancestor of b_k in slot(b_i) + 1 with support (Lemma 30).
  obtain ⟨b_j, h_slot_bj, h_anc_bj, h_support_bj⟩ :=
    h_window_support h_succ_mem (Nat.succ_le_of_lt h_si_lt_sk)

  -- Extract parent of b_j, which lives in slot(b_i).
  have h_first_le_si :
      cfg.windowFirstSlot s_k ≤ s_i :=
    window_first_le (cfg := cfg) (s := s_k) h_window
  have h_first_lt_succ :
      cfg.windowFirstSlot s_k < Nat.succ s_i :=
    lt_of_le_of_lt h_first_le_si (Nat.lt_succ_self _)
  obtain ⟨parent, h_parent_edge⟩ :=
    parent_exists_for_slot (cfg := cfg) (topo := topo) s_k
      (slot := Nat.succ s_i) (block := b_j)
      h_slot_bj h_succ_mem h_first_lt_succ
  obtain ⟨h_parent, h_slot_parent, h_parent_mem⟩ := h_parent_edge
  have h_slot_parent_si :
      topo.slotOf parent = s_i := by
    simpa [Nat.pred_succ] using h_slot_parent

  -- This parent b'_i differs from b_i (else b_k would descend from b_i).
  have h_parent_ne_bi : parent ≠ b_i := by
    intro h_eq
    apply h_not_descends
    have h_anc_parent_bj :
        IsAncestor topo parent b_j :=
      ancestor_parent (topo := topo) h_parent
    have h_anc_parent_bk :
        IsAncestor topo parent b_k :=
      ancestor_trans (topo := topo) h_anc_parent_bj h_anc_bj
    simpa [h_eq] using h_anc_parent_bk

  -- Case analysis on support for b_j (from Lemma 30).
  cases h_support_bj with
  | inl h_majority =>
      -- Case 1: >40% correct nodes notarized b_j.
      -- By Lemma 28, these votes propagate to parent b'_i.
      -- This contradicts Lemma 23 since both b_i and b'_i would be notarized.
      have h_parent_majority :
          stakeSum w
              ((notarVotesFor s_i parent notarVotes).filter correct) >
            fallbackThreshold := by
        have :=
          majority_support_parent
            (cfg := cfg) (topo := topo) (w := w) (correct := correct)
            (notarVotes := notarVotes)
            s_k (slot := Nat.succ s_i)
            (child := b_j) (parent := parent)
            h_slot_bj h_succ_mem h_first_lt_succ
            ⟨h_parent, h_slot_parent, h_parent_mem⟩ h_majority
        simpa [Nat.pred_succ] using this
      have h_parent_correct_majority :
          CorrectMajorityVoted w correct s_i parent notarVotes := by
        unfold CorrectMajorityVoted
        simpa using h_parent_majority
      have h_no_notar :=
        lemma23_no_other_block_notarized
          (w := w) (correct := correct)
          (s := s_i) (b := parent) (b' := b_i) (votes := notarVotes)
          h_parent_correct_majority h_parent_ne_bi
      exact h_no_notar h_notarized_bi
  | inr h_fallback =>
      -- Case 2: A correct node cast a notar-fallback vote for b_j.
      -- By Definition 16 (via Lemma 29), parent b'_i is notarized or notarized-fallback.
      -- This contradicts slot exclusivity (Lemmas 21 or 26).
      obtain ⟨v, h_v_corr, h_v_vote⟩ := h_fallback
      have h_first_eq :
          cfg.windowFirstSlot (Nat.succ s_i) =
            cfg.windowFirstSlot s_k :=
        window_first_slot_eq cfg s_k (Nat.succ s_i) h_succ_mem
      have h_not_first :
          cfg.windowFirstSlot (Nat.succ s_i) < Nat.succ s_i := by
        simpa [h_first_eq] using h_first_lt_succ
      have h_parent_cert :
          stakeSum w
              (notarVotesFor s_i parent notarVotes ∪
                notarFallbackVotesFor s_i parent fallbackVotes) ≥
            notarizationThreshold := by
        have :=
          fallback_vote_requires_parent_certificate
            (cfg := cfg) (topo := topo) (w := w) (correct := correct)
            (notarVotes := notarVotes) (fallbackVotes := fallbackVotes)
            (v := v) (s := Nat.succ s_i) (b := b_j) (parent := parent)
            h_slot_bj h_parent h_not_first h_v_vote h_v_corr
        simpa [h_slot_parent, Nat.pred_succ] using this
      obtain ⟨_, h_union_lt⟩ :=
        h_exclusive h_slot_parent_si h_parent_ne_bi
      exact (not_lt_of_ge h_parent_cert) h_union_lt

end Lemma31
end Alpenglow
