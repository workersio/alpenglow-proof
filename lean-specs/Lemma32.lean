/-
  Lemma 32 (Cross-Window Finalization Ancestry)
  =============================================

  We mechanize Lemma 32 from the Alpenglow whitepaper (p.32):

  > Suppose some correct node finalizes a block `bᵢ` and `b_k` is a block in a
  > different leader window with `slot(bᵢ) < slot(b_k)`.  If any correct node
  > observes a notarization or notar-fallback certificate for `b_k`, then `b_k`
  > is a descendant of `bᵢ`.

  **Outline.**
  * We consider the earliest (highest, in the whitepaper terminology) ancestor
    of `b_k` whose slot lies at or beyond the finalized slot `sᵢ` and already
    enjoys a certificate.
  * If that ancestor lives in the same leader window as `bᵢ`, Lemma 31 applies
    directly, yielding the desired ancestry relation.
  * Otherwise, the ancestor inhabits a later leader window whose first slot
    strictly exceeds `sᵢ`.  Lemma 27 supplies a correct notar voter for this
    ancestor, and Lemma 28 pushes that vote to the first slot of the window.
    Voting in the first slot requires a `ParentReady` witness: the parent block
    carries a notarization or notar-fallback certificate, and every slot
    between the parent and the window head possesses a skip certificate.
  * Finalization exclusivity (Lemmas 21/26) precludes both a rival certificate
    and a skip certificate in slot `sᵢ`.  The `ParentReady` witness therefore
    forces the parent block to coincide with `bᵢ`, which immediately yields the
    ancestry claim.

  The mechanization introduces two lightweight axioms reflecting the behaviour
  of Algorithm 2 in first-window slots:

  1. `fallback_certificate_requires_notar_support` — any notar-fallback
     certificate aggregates ≥20% notar stake on the block itself.
  2. `first_slot_vote_parent_ready` — a correct notar vote in the first slot of
     a window requires `ParentReady`, which exposes the certified parent block
     and the skip certificates for the intervening slots.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Lemma21
import Lemma27
import Lemma28
import Lemma29
import Lemma30
import Lemma31

open Classical

namespace Alpenglow
namespace Lemma32

open Lemma21
open Lemma27
open Lemma28
open Lemma29
open Lemma30
open Lemma31
open BlockTopology

variable {Hash : Type _} [DecidableEq Hash]

/-
  ## ParentReady Axioms
-/

/-- Notar-fallback certificates (Definition 16) require at least 20% stake in
    notar votes alone.  With <20% byzantine stake, this guarantees the presence
    of a correct notar voter. -/
axiom fallback_certificate_requires_notar_support
    (w : StakeWeight) (s : Slot) (b : Hash)
    (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash)) :
    stakeSum w
        (notarVotesFor s b notarVotes ∪
          notarFallbackVotesFor s b fallbackVotes) ≥
      notarizationThreshold →
    stakeSum w (notarVotesFor s b notarVotes) ≥ (20 : Real)

/-- Voting to notarize the first slot of a leader window requires a
    `ParentReady` witness.  This witness exposes the certified parent block and
    the skip certificates for every slot between the parent and the window
    head. -/
axiom first_slot_vote_parent_ready
    (cfg : VotorConfig) (topo : BlockTopology Hash)
    (w : StakeWeight) (correct : IsCorrect)
    (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash))
    (skipVotes : Finset SkipVote)
    {v : NodeId} {s : Slot} {child : Hash} :
    topo.slotOf child = s →
    cfg.windowFirstSlot s = s →
    v ∈ notarVotesFor s child notarVotes →
    correct v →
    ∃ parent,
      topo.parentOf child = some parent ∧
        ((stakeSum w (notarVotesFor (topo.slotOf parent) parent notarVotes) ≥
            notarizationThreshold) ∨
          stakeSum w
              (notarVotesFor (topo.slotOf parent) parent notarVotes ∪
                notarFallbackVotesFor (topo.slotOf parent) parent fallbackVotes) ≥
            notarizationThreshold) ∧
        topo.slotOf parent < s ∧
        ∀ {t}, topo.slotOf parent < t → t < s →
          stakeSum w (skipVotesFor t skipVotes) ≥ notarizationThreshold

/-
  ## Window Arithmetic Helpers
-/

/-- Every slot between the first slot of a window and the top slot belongs to
    the window enumeration. -/
lemma mem_window_of_interval (cfg : VotorConfig)
    {s t : Slot}
    (h_first_le : cfg.windowFirstSlot s ≤ t)
    (h_le : t ≤ s) :
    t ∈ cfg.windowSlots s := by
  classical
  set first := cfg.windowFirstSlot s with h_first_def
  have h_first_mem : first ∈ cfg.windowSlots s :=
    window_first_mem (cfg := cfg) s
  -- Induction on the distance from the first slot.
  have h_aux :
      ∀ d, first + d ≤ s →
        first + d ∈ cfg.windowSlots s := by
    intro d
    induction d with
    | zero =>
        intro _
        rw [Nat.add_zero]
        exact h_first_mem
    | succ d ih =>
        intro h_le'
        have h_prev_lt : first + d < s :=
          lt_of_lt_of_le (Nat.lt_succ_self (first + d)) h_le'
        have h_prev_le : first + d ≤ s := le_of_lt h_prev_lt
        have h_prev_mem := ih h_prev_le
        have h_succ_def : first + Nat.succ d = first + d + 1 := by
          rw [Nat.succ_eq_add_one, Nat.add_assoc]
        rw [h_succ_def]
        exact window_succ_closed (cfg := cfg) (s := s) h_prev_mem h_prev_lt
  have h_eq : t = first + (t - first) := (Nat.add_sub_of_le h_first_le).symm
  have h_le' : first + (t - first) ≤ s := by rw [← h_eq]; exact h_le
  rw [h_eq]
  exact h_aux (t - first) h_le'

/-- A slot always belongs to its own leader window. -/
axiom self_mem_window (cfg : VotorConfig) (s : Slot) :
    s ∈ cfg.windowSlots s

/-
  ## Certified Ancestors Between Slot Bounds
-/

/-- Predicate capturing an ancestor of `b_k` located in slot `s` that already
    admits a notarization or notar-fallback certificate. -/
structure CertifiedAncestor
    (topo : BlockTopology Hash)
    (w : StakeWeight)
    (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash))
    (b_k : Hash) (b : Hash) (s : Slot) : Prop where
  slot_eq : topo.slotOf b = s
  ancestor : IsAncestor topo b b_k
  cert :
    stakeSum w (notarVotesFor s b notarVotes) ≥ notarizationThreshold ∨
      stakeSum w
          (notarVotesFor s b notarVotes ∪
            notarFallbackVotesFor s b fallbackVotes) ≥ notarizationThreshold

/-
  ## Helper Lemmas for Certificate Case Analysis
-/

/-- Helper lemma: exclusivity contradicts any certificate for a different block. -/
lemma exclusive_blocks_no_cert
    (topo : BlockTopology Hash)
    (w : StakeWeight)
    (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash))
    {s : Slot} {b b' : Hash}
    (h_exclusive : SlotExclusive topo w notarVotes fallbackVotes s b)
    (h_slot : topo.slotOf b' = s)
    (h_ne : b' ≠ b)
    (h_cert :
      stakeSum w (notarVotesFor s b' notarVotes) ≥ notarizationThreshold ∨
      stakeSum w
          (notarVotesFor s b' notarVotes ∪
            notarFallbackVotesFor s b' fallbackVotes) ≥ notarizationThreshold) :
    False := by
  have h_conflict := h_exclusive h_slot h_ne
  cases h_cert with
  | inl h_notar => exact (not_lt_of_ge h_notar) h_conflict.1
  | inr h_union => exact (not_lt_of_ge h_union) h_conflict.2

/-- Helper lemma: any certificate implies existence of correct notar voter
    (with bounded Byzantine stake). -/
lemma cert_has_correct_voter
    (w : StakeWeight)
    (correct : IsCorrect)
    (byzBound : ByzantineStakeBound w correct)
    (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash))
    {s : Slot} {b : Hash}
    (h_cert :
      stakeSum w (notarVotesFor s b notarVotes) ≥ notarizationThreshold ∨
      stakeSum w
          (notarVotesFor s b notarVotes ∪
            notarFallbackVotesFor s b fallbackVotes) ≥ notarizationThreshold) :
    ∃ v, correct v ∧ v ∈ notarVotesFor s b notarVotes := by
  classical
  cases h_cert with
  | inl h_notar =>
      by_contra h_none
      have h_all_byz : ∀ n ∈ notarVotesFor s b notarVotes, ¬correct n := by
        intro n hn
        by_contra h_corr
        exact h_none ⟨n, h_corr, hn⟩
      have h_byz : stakeSum w (notarVotesFor s b notarVotes) < 20 :=
        byzBound.bound _ h_all_byz
      have : (60 : Real) < 20 := lt_of_le_of_lt h_notar h_byz
      norm_num at this
  | inr h_fallback =>
      have h_notar_support :
          stakeSum w (notarVotesFor s b notarVotes) ≥ (20 : Real) :=
        fallback_certificate_requires_notar_support
          (w := w) (s := s) (b := b)
          (notarVotes := notarVotes) (fallbackVotes := fallbackVotes)
          h_fallback
      by_contra h_none
      have h_all_byz : ∀ n ∈ notarVotesFor s b notarVotes, ¬correct n := by
        intro n hn
        by_contra h_corr
        exact h_none ⟨n, h_corr, hn⟩
      have h_byz : stakeSum w (notarVotesFor s b notarVotes) < 20 :=
        byzBound.bound _ h_all_byz
      exact (not_lt_of_ge h_notar_support) h_byz

/-
  ## Main Lemma
-/

/-- **Lemma 32 (Finalization implies cross-window ancestry).** -/
theorem descendant_across_windows
    (cfg : VotorConfig) (topo : BlockTopology Hash)
    (w : StakeWeight) (correct : IsCorrect)
    (byzBound : ByzantineStakeBound w correct)
    (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash))
    (skipVotes : Finset SkipVote)
    {b_i b_k : Hash} {s_i s_k : Slot}
    (h_slot_i : topo.slotOf b_i = s_i)
    (h_slot_k : topo.slotOf b_k = s_k)
    (h_window_disjoint : s_i ∉ cfg.windowSlots s_k)
    (h_slot_lt : s_i < s_k)
    (h_notarized_bi :
      stakeSum w (notarVotesFor s_i b_i notarVotes) ≥ notarizationThreshold)
    (h_exclusive :
      SlotExclusive topo w notarVotes fallbackVotes s_i b_i)
    (h_no_skip :
      stakeSum w (skipVotesFor s_i skipVotes) < notarizationThreshold)
    (h_cert_k :
      stakeSum w (notarVotesFor s_k b_k notarVotes) ≥ notarizationThreshold ∨
      stakeSum w
          (notarVotesFor s_k b_k notarVotes ∪
            notarFallbackVotesFor s_k b_k fallbackVotes) ≥ notarizationThreshold) :
    IsAncestor topo b_i b_k := by
  classical
  -- Assume towards contradiction that `b_i` is not an ancestor of `b_k`.
  by_contra h_not_desc
  -- Collect the set of ancestor slots with certificates at or beyond `s_i`.
  let HasCert : Slot → Prop := fun s =>
    s_i ≤ s ∧ s ≤ s_k ∧
      ∃ b,
        topo.slotOf b = s ∧
        IsAncestor topo b b_k ∧
        (stakeSum w (notarVotesFor s b notarVotes) ≥ notarizationThreshold ∨
          stakeSum w
              (notarVotesFor s b notarVotes ∪
                notarFallbackVotesFor s b fallbackVotes) ≥ notarizationThreshold)
  have h_cert_exists : ∃ s, HasCert s := by
    refine ⟨s_k, ?_⟩
    refine ⟨le_of_lt h_slot_lt, le_rfl, ?_⟩
    refine ⟨b_k, h_slot_k, ?_, h_cert_k⟩
    exact IsAncestor.refl (topo := topo) (b := b_k)
  -- Pick the minimal certified slot.
  let s_j := Nat.find h_cert_exists
  have h_sj_spec : HasCert s_j := Nat.find_spec h_cert_exists
  obtain ⟨h_si_le_sj, h_sj_le_sk, h_exist_bj⟩ := h_sj_spec
  obtain ⟨b_j, h_slot_bj, h_anc_bj, h_cert_bj⟩ := h_exist_bj
  -- If the certificate already sits in slot `s_i`, we are done immediately.
  have h_sj_ne_si : s_j ≠ s_i := by
    intro h_eq
    have h_slot_bj_si : topo.slotOf b_j = s_i := by
      rw [h_slot_bj, h_eq]
    have h_cert_bj_si : stakeSum w (notarVotesFor s_i b_j notarVotes) ≥ notarizationThreshold ∨
        stakeSum w
            (notarVotesFor s_i b_j notarVotes ∪
              notarFallbackVotesFor s_i b_j fallbackVotes) ≥ notarizationThreshold := by
      rw [← h_eq]
      exact h_cert_bj
    have h_bj_eq : b_j = b_i := by
      by_contra h_diff
      exact exclusive_blocks_no_cert topo w notarVotes fallbackVotes
        h_exclusive h_slot_bj_si h_diff h_cert_bj_si
    -- Now b_j = b_i is an ancestor of b_k, contradicting h_not_desc
    rw [h_bj_eq] at h_anc_bj
    have h_bi_refl := IsAncestor.refl (topo := topo) (b := b_i)
    have h_desc := ancestor_trans (topo := topo) h_bi_refl h_anc_bj
    exact h_not_desc h_desc
  have h_si_lt_sj : s_i < s_j := Ne.lt_of_le (Ne.symm h_sj_ne_si) h_si_le_sj
  -- Characterise the minimality: no smaller slot reaches a certificate.
  have h_minimal : ∀ {t}, t < s_j → ¬HasCert t := by
    intro t h_lt h_cert
    have h_le := Nat.find_min' h_cert_exists h_cert
    omega
  -- `b_j` cannot descend from `b_i`; otherwise ancestry would follow.
  have h_bj_not_desc :
      ¬IsAncestor topo b_i b_j := by
    intro h_desc
    apply h_not_desc
    exact ancestor_trans (topo := topo) h_desc h_anc_bj
  -- Compare the leader windows of `b_j` and `b_i`.
  -- If the leader windows agree, invoke Lemma 31 to finish.
  by_cases h_window_eq : cfg.windowFirstSlot s_j = cfg.windowFirstSlot s_i
  · -- Case: same window
      -- `s_i` lies inside the window of `s_j`.
      have h_si_mem :
          s_i ∈ cfg.windowSlots s_j := by
        have h_first_le :
            cfg.windowFirstSlot s_j ≤ s_i := by
          simpa [h_window_eq] using
            (window_first_le (cfg := cfg) (s := s_i)
              (self_mem_window (cfg := cfg) s_i))
        have h_le : s_i ≤ s_j := le_of_lt h_si_lt_sj
        exact mem_window_of_interval (cfg := cfg) h_first_le h_le
      -- Apply Lemma 31 to obtain ancestry.
      have h_desc :
          IsAncestor topo b_i b_j :=
        descendant_of_finalized_window_block
          (cfg := cfg) (topo := topo) (w := w) (correct := correct)
          (byzBound := byzBound)
          (notarVotes := notarVotes) (fallbackVotes := fallbackVotes)
          (b_i := b_i) (b_k := b_j) (s_i := s_i) (s_k := s_j)
          h_slot_i h_slot_bj h_si_mem (le_of_lt h_si_lt_sj)
          h_notarized_bi h_exclusive h_cert_bj
      apply h_not_desc
      exact ancestor_trans (topo := topo) h_desc h_anc_bj
  · -- Case: different windows
      -- The first slot of `b_j` strictly exceeds `s_i`, as otherwise windows agree.
      have h_first_gt :
          s_i < cfg.windowFirstSlot s_j := by
        by_contra h_not
        have h_le :
            cfg.windowFirstSlot s_j ≤ s_i :=
          le_of_not_gt h_not
        have h_mem :
            s_i ∈ cfg.windowSlots s_j :=
          mem_window_of_interval (cfg := cfg) (s := s_j) (t := s_i)
            h_le (le_of_lt h_si_lt_sj)
        have h_window_eq' :
            cfg.windowFirstSlot s_j = cfg.windowFirstSlot s_i := by
          have h_first :=
            window_first_slot_eq cfg s_j s_i h_mem
          exact h_first.symm
        exact h_window_eq h_window_eq'
      -- Produce a correct notar voter for `b_j` using the helper lemma.
      obtain ⟨v, h_v_corr, h_v_vote⟩ :=
        cert_has_correct_voter w correct byzBound notarVotes fallbackVotes h_cert_bj
      -- Cache the first slot of the window to avoid repeated computation.
      let s_first := cfg.windowFirstSlot s_j
      have h_first_mem :
          s_first ∈ cfg.windowSlots s_j :=
        window_first_mem (cfg := cfg) s_j
      have h_sj_mem : s_j ∈ cfg.windowSlots s_j := self_mem_window (cfg := cfg) s_j
      have h_first_le_sj :
          s_first ≤ s_j :=
        window_first_le (cfg := cfg) (s := s_j) h_sj_mem
      obtain ⟨b_first, h_slot_first, h_anc_first, h_vote_first⟩ :=
        correct_node_votes_all_ancestors
          (cfg := cfg) (topo := topo) (correct := correct)
          (votes := notarVotes) (v := v) (s := s_j) (b := b_j)
          h_v_vote h_v_corr
          (s' := s_first) h_first_mem h_first_le_sj
      -- The vote in the first slot triggers ParentReady.
      have h_first_first :
          cfg.windowFirstSlot s_first = s_first :=
        window_first_slot_eq cfg s_j s_first h_first_mem
      obtain ⟨parent, h_parent_edge, h_parent_cert, h_parent_lt, h_skip_parent⟩ :=
        first_slot_vote_parent_ready
          (cfg := cfg) (topo := topo) (w := w) (correct := correct)
          (notarVotes := notarVotes) (fallbackVotes := fallbackVotes)
          (skipVotes := skipVotes)
          (s := s_first) (child := b_first)
          h_slot_first h_first_first h_vote_first h_v_corr
      -- Parent ancestry towards `b_k`: break up transitive chains.
      have h_anc_parent_first : IsAncestor topo parent b_first :=
        ancestor_parent (topo := topo) h_parent_edge
      have h_anc_first_bj : IsAncestor topo b_first b_j := h_anc_first
      have h_anc_parent_bj : IsAncestor topo parent b_j :=
        ancestor_trans (topo := topo) h_anc_parent_first h_anc_first_bj
      have h_anc_parent_bk : IsAncestor topo parent b_k :=
        ancestor_trans (topo := topo) h_anc_parent_bj h_anc_bj
      -- The parent must have slot strictly below `s_j`.
      have h_slot_parent_lt_first : topo.slotOf parent < s_first := h_parent_lt
      have h_slot_first_le_sj : s_first ≤ s_j := h_first_le_sj
      have h_slot_parent_lt_sj : topo.slotOf parent < s_j :=
        lt_of_lt_of_le h_slot_parent_lt_first h_slot_first_le_sj
      -- Use minimality to constrain the parent slot.
      have h_parent_slot_bounds :
          topo.slotOf parent < s_i ∨ topo.slotOf parent = s_i := by
        by_cases h_lt : topo.slotOf parent < s_i
        · exact Or.inl h_lt
        · have h_ge : s_i ≤ topo.slotOf parent := le_of_not_lt h_lt
          by_cases h_eq : topo.slotOf parent = s_i
          · exact Or.inr h_eq
          ·
            have h_parent_has_cert : HasCert (topo.slotOf parent) := by
              refine ⟨h_ge, ?_, ?_⟩
              · exact le_trans (Nat.le_of_lt h_slot_parent_lt_sj) h_sj_le_sk
              · refine ⟨parent, ?_, h_anc_parent_bk, ?_⟩
                · rfl
                · exact h_parent_cert
            exact (False.elim (h_minimal h_slot_parent_lt_sj h_parent_has_cert))
      -- Case analysis on the parent slot.
      cases h_parent_slot_bounds with
      | inl h_parent_lt_si =>
          -- Skip certificate in slot `sᵢ`, contradicting exclusivity.
          have h_si_lt_first :
              s_i < s_first := h_first_gt
          have h_skip_si :
              stakeSum w (skipVotesFor s_i skipVotes) ≥ notarizationThreshold :=
            h_skip_parent
              (t := s_i)
              (by exact h_parent_lt_si)
              (by exact h_si_lt_first)
          exact (not_lt_of_ge h_skip_si) h_no_skip
      | inr h_parent_eq_si =>
          -- Either the parent matches `bᵢ`, or we contradict exclusivity.
          have h_parent_slot : topo.slotOf parent = s_i := h_parent_eq_si
          by_cases h_eq : parent = b_i
          · -- If parent = b_i, then b_i is an ancestor of b_k.
            rw [h_eq] at h_anc_parent_bk
            exact h_not_desc h_anc_parent_bk
          · -- If parent ≠ b_i, exclusivity contradicts the parent certificate.
            have h_parent_cert_si : stakeSum w (notarVotesFor s_i parent notarVotes) ≥ notarizationThreshold ∨
                stakeSum w
                    (notarVotesFor s_i parent notarVotes ∪
                      notarFallbackVotesFor s_i parent fallbackVotes) ≥ notarizationThreshold := by
              rw [← h_parent_slot]
              exact h_parent_cert
            exact exclusive_blocks_no_cert topo w notarVotes fallbackVotes
              h_exclusive h_parent_slot h_eq h_parent_cert_si

end Lemma32
end Alpenglow
