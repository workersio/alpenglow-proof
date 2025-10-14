/-
  Lemma 31 (Same-Window Finalization Ancestry)
  ============================================

  We mechanize Lemma 31 from the Alpenglow whitepaper (p.32):

  > Suppose some correct node finalizes a block `bᵢ` and `b_k` is a block in the
  > same leader window with `slot(bᵢ) ≤ slot(b_k)`.  If any correct node observes
  > a notarization or notar-fallback certificate for `b_k`, then `b_k` is a
  > descendant of `bᵢ`.

  **Intuition.**
  Finalization of `bᵢ` rules out any competing certificates in slot `slot(bᵢ)`
  (Lemmas 21 and 26) and, by Lemma 25, `bᵢ` itself is notarized.  We reason by
  contradiction: assume some certified block `b_k` in the same leader window is
  *not* a descendant of `bᵢ`.  Lemma 30 lifts the certificate on `b_k` to every
  earlier slot within the window, providing either a correct notar-fallback
  voter or a >40% correct notar majority for the ancestor `b_j` in slot
  `slot(bᵢ)+1`.  Following the parent pointer from `b_j` yields a block `bᵢ'`
  that lives in slot `slot(bᵢ)` but differs from `bᵢ`.

  * If the support for `b_j` contains a correct notar-fallback vote, the guard
    from Lemma 29 ensures a notarization-or-fallback certificate already exists
    for `bᵢ'`, contradicting finalization exclusivity in slot `slot(bᵢ)`.
  * Otherwise, >40% correct stake notarized `b_j`, and Lemma 28 pushes these
    votes to `bᵢ'`.  Applying Lemma 23 with `bᵢ'` and the known notarization of
    `bᵢ` again contradicts exclusivity in slot `slot(bᵢ)`.

  Hence every certified block in the window must extend the finalized block.
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

/-- Slot exclusivity for finalized blocks: no competing block in slot `s`
    admits either a notarization certificate or a notar-fallback certificate. -/
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

/-- **Lemma 31 (Finalization implies window ancestry).**

    Let `bᵢ` be a finalized block in slot `sᵢ`, and suppose there exists a
    notarization or notar-fallback certificate for some block `b_k` located in
    slot `s_k` of the same leader window with `sᵢ ≤ s_k`.  If the finalized slot
    is exclusive (no competing certificates) and `bᵢ` is notarized, then `b_k`
    must be a descendant of `bᵢ`. -/
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

  -- Certified blocks in the window provide supported ancestors via Lemma 30.
  -- This lemma states that for any slot s' in the window of s_k with s' ≤ s_k,
  -- there exists an ancestor block with support.
  have h_window_support :
      ∀ {s'}, s' ∈ cfg.windowSlots s_k → s' ≤ s_k →
        ∃ b', topo.slotOf b' = s' ∧ BlockTopology.IsAncestor topo b' b_k ∧
              BlockSupport w correct notarVotes fallbackVotes s' b' :=
    window_ancestors_supported
      (cfg := cfg) (topo := topo) (w := w) (correct := correct)
      (byzBound := byzBound) (notarVotes := notarVotes)
      (fallbackVotes := fallbackVotes)
      (s := s_k) (b := b_k) h_slot_k h_cert_k

  -- Assume towards contradiction that `b_k` does not descend from `bᵢ`.
  by_contra h_not_descends

  -- A non-descendant must differ from `bᵢ`.
  have h_bk_ne_bi : b_k ≠ b_i := by
    intro h_eq
    apply h_not_descends
    simpa [h_eq] using (IsAncestor.refl (topo := topo) (b := b_i))

  -- The finalized slot cannot equal `s_k`; otherwise, exclusivity contradicts the certificate.
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

  -- Numerical: `sᵢ < s_k`.
  have h_si_lt_sk : s_i < s_k := lt_of_le_of_ne h_slot_le h_si_ne_sk

  -- The successor slot remains in the same leader window.
  have h_succ_mem :
      Nat.succ s_i ∈ cfg.windowSlots s_k :=
    window_succ_closed (cfg := cfg) (s := s_k) h_window h_si_lt_sk

  -- An ancestor `b_j` exists in slot `sᵢ + 1` with window support.
  obtain ⟨b_j, h_slot_bj, h_anc_bj, h_support_bj⟩ :=
    h_window_support h_succ_mem (Nat.succ_le_of_lt h_si_lt_sk)

  -- Parent information for `b_j`.
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

  -- If the parent were `bᵢ`, then ancestry would follow immediately.
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

  -- Decide between the support alternatives for `b_j`.
  cases h_support_bj with
  | inl h_majority =>
      -- Majority support propagates to the parent, which contradicts `bᵢ`'s notarization.
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
      -- A correct notar-fallback vote on `b_j` implies a certificate for the parent.
      obtain ⟨v, h_v_corr, h_v_vote⟩ := h_fallback
      -- All slots in the window share the same first slot; reuse the earlier inequality.
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
