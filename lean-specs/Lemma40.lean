/-
  Lemma 40: ParentReady After Window Timeouts

  Whitepaper (pp.35-36): If all correct nodes set the timeouts for slots WINDOWSLOTS(s),
  then all correct nodes will emit the event ParentReady(s+, ...), where s+ > s is
  the first slot of the following leader window.

  Proof strategy from whitepaper:

  Case (i): All correct nodes observe skip certificates for all slots in WINDOWSLOTS(s).
    By Corollary 34, node v had emitted ParentReady(k, hash(b)) where k is the first
    slot of WINDOWSLOTS(s). By Definition 15, there is a block b with a notar-fallback
    certificate and skip certificates for all slots between slot(b) and k. Since skip
    certificates exist for all slots in WINDOWSLOTS(s), they exist for all slots
    between slot(b) and s+. By Definition 15, v will emit ParentReady(s+, hash(b)).

  Case (ii): Some correct node does not observe a skip certificate for some slot in WINDOWSLOTS(s).
    Let s' be the highest such slot. By Lemma 39, v will observe a notar-fallback
    certificate for some block b in slot s'. By maximality of s', v will observe
    skip certificates for all slots between slot(b) and s+. By Definition 15,
    v will emit ParentReady(s+, hash(b)).

  Definition 15 (ParentReady event): Slot s is the first of its leader window, and
  Pool holds a notarization or notar-fallback certificate for a previous block b,
  and skip certificates for every slot s' between b and s (slot(b) < s' < s).

  The mechanization represents Definition 15 as ParentReadyWitness.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Lemma21
import Lemma28
import Lemma29
import Lemma37
import Lemma39

open Classical

namespace Alpenglow
namespace Lemma40

open Lemma21
open Lemma28
open Lemma29
open Lemma37
open Lemma39

/- ParentReady Witness (Definition 15 from whitepaper, p.20)

   Witness for emitting ParentReady(s, ...):
   - s is the first slot of its leader window
   - some block parent in an earlier slot has a notar-fallback certificate
   - every slot between parent and s has a skip certificate -/
structure ParentReadyWitness
    (cfg : VotorConfig) (topo : BlockTopology Hash)
    (w : StakeWeight) (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash))
    (skipVotes : Finset SkipVote) (s : Slot) : Prop where
  first_slot :
      cfg.windowFirstSlot s = s
  parent_exists :
      ∃ parent : Hash,
        topo.slotOf parent < s ∧
        stakeSum w
            (notarVotesFor (topo.slotOf parent) parent notarVotes ∪
              notarFallbackVotesFor (topo.slotOf parent) parent fallbackVotes) ≥
          notarizationThreshold ∧
        ∀ {t}, topo.slotOf parent < t → t < s →
          stakeSum w (skipVotesFor t skipVotes) ≥ notarizationThreshold

/- Helper lemma: find the maximal element in a bounded set.
   Used to identify the highest slot without a skip certificate (Case ii). -/
private lemma exists_max_of_bounded
    {S : Nat → Prop} [DecidablePred S] (B : Nat)
    (h_nonempty : ∃ n, S n)
    (h_bdd : ∀ n, S n → n ≤ B) :
    ∃ m, S m ∧ ∀ n, S n → n ≤ m := by
  classical
  let satisfying := (Finset.range (B + 1)).filter S
  have h_nonempty_finset : satisfying.Nonempty := by
    rcases h_nonempty with ⟨n, hSn⟩
    refine ⟨n, ?_⟩
    simp only [satisfying, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (h_bdd n hSn), hSn⟩
  let m := satisfying.max' h_nonempty_finset
  refine ⟨m, ?_, ?_⟩
  · have : m ∈ satisfying := Finset.max'_mem satisfying h_nonempty_finset
    simp only [satisfying, Finset.mem_filter] at this
    exact this.2
  · intro n hSn
    have hn_mem : n ∈ satisfying := by
      simp only [satisfying, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le (h_bdd n hSn), hSn⟩
    exact Finset.le_max' satisfying n hn_mem

/- Lemma 40 (whitepaper pp.35-36)

   Given timeout witnesses for all slots in WINDOWSLOTS(s) and the current window
   head's parent-ready witness (from Corollary 34), we construct a parent-ready
   witness for the next window head sPlus. -/
theorem window_timeouts_emit_parent_ready
    (cfg : VotorConfig) (topo : BlockTopology Hash)
    (w : StakeWeight) (correct : IsCorrect)
    (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash))
    (skipVotes : Finset SkipVote)
    {s sPlus : Slot}
    (window_upper :
      ∀ {t}, t ∈ cfg.windowSlots s →
        t < sPlus)
    (window_cover :
      ∀ {t}, cfg.windowFirstSlot s ≤ t → t < sPlus →
        t ∈ cfg.windowSlots s)
    (sPlus_first : cfg.windowFirstSlot sPlus = sPlus)
    (head_witness :
      ParentReadyWitness cfg topo w notarVotes fallbackVotes skipVotes
        (cfg.windowFirstSlot s))
    (timeouts :
      ∀ {t}, t ∈ cfg.windowSlots s →
        TimeoutStakeWitness w correct t notarVotes skipVotes) :
    ParentReadyWitness cfg topo w notarVotes fallbackVotes skipVotes sPlus := by
  classical
  set head := cfg.windowFirstSlot s with h_head_def
  have head_mem :
      head ∈ cfg.windowSlots s :=
    window_first_mem (cfg := cfg) s
  have head_lt_sPlus :
      head < sPlus := window_upper (t := head) head_mem
  let hasSkip : Slot → Prop :=
    fun t => stakeSum w (skipVotesFor t skipVotes) ≥ notarizationThreshold
  -- By Lemma 39, each slot has either a skip certificate or a notar-fallback certificate.
  have certificates_or_skips :
      ∀ {t}, t ∈ cfg.windowSlots s →
        hasSkip t ∨
          ∃ b,
            topo.slotOf b = t ∧
              stakeSum w
                  (notarVotesFor t b notarVotes ∪
                    notarFallbackVotesFor t b fallbackVotes) ≥
                notarizationThreshold :=
    window_timeouts_yield_certificates
      (cfg := cfg) (topo := topo)
      (w := w) (correct := correct)
      (notarVotes := notarVotes) (fallbackVotes := fallbackVotes)
      (skipVotes := skipVotes) (s := s)
      (timeouts := timeouts)
  -- Case split: all slots have skip certificates (Case i), or some slot lacks one (Case ii).
  by_cases h_all_skip : ∀ t ∈ cfg.windowSlots s, hasSkip t
  · -- Case (i): All slots have skip certificates.
    -- Extend the parent-ready witness from Corollary 34 across the whole window.
    rcases head_witness with ⟨head_first, ⟨parent, parent_lt_head, parent_cert, parent_chain⟩⟩
    refine
      { first_slot := sPlus_first
        parent_exists := ⟨parent, ?_, ?_, ?_⟩ }
    · exact lt_trans parent_lt_head head_lt_sPlus
    · exact parent_cert
    · intro t h_parent_lt h_t_lt
      by_cases h_t_before_head : t < head
      · exact parent_chain h_parent_lt h_t_before_head
      · have h_head_le_t :
            head ≤ t := le_of_not_gt h_t_before_head
        have h_t_mem :
            t ∈ cfg.windowSlots s :=
          window_cover (t := t) h_head_le_t h_t_lt
        exact h_all_skip t h_t_mem
  · -- Case (ii): Some slot lacks a skip certificate.
    -- Find the highest slot s' without a skip certificate.
    push_neg at h_all_skip
    obtain ⟨t₀, t₀_mem, t₀_no_skip⟩ := h_all_skip
    have t₀_lt_sPlus :
        t₀ < sPlus := window_upper (t := t₀) t₀_mem
    let Bad : Nat → Prop :=
      fun t => t < sPlus ∧ t ∈ cfg.windowSlots s ∧ ¬ hasSkip t
    have h_bad_nonempty :
        ∃ t, Bad t :=
      ⟨t₀, t₀_lt_sPlus, t₀_mem, t₀_no_skip⟩
    have h_bad_bounded :
        ∀ t, Bad t → t ≤ sPlus :=
      by
        intro t ht
        exact Nat.le_of_lt ht.1
    obtain ⟨s', hs', h_max⟩ :=
      exists_max_of_bounded (S := Bad) sPlus h_bad_nonempty h_bad_bounded
    have s'_lt_sPlus : s' < sPlus := hs'.1
    have s'_mem_window : s' ∈ cfg.windowSlots s := (hs'.2).1
    have s'_no_skip : ¬ hasSkip s' := (hs'.2).2
    -- By Lemma 39, s' must have a notar-fallback certificate for some block.
    cases certificates_or_skips (t := s') s'_mem_window with
    | inl h_skip =>
        exact False.elim (s'_no_skip h_skip)
    | inr h_block =>
        rcases h_block with ⟨parent, h_parent_slot, h_parent_cert⟩
        -- By maximality of s', all slots after s' have skip certificates.
        have skips_after :
            ∀ {t}, s' < t → t < sPlus → hasSkip t := by
          intro t ht_gt ht_lt
          have head_le_s' :
              head ≤ s' :=
            window_first_le (cfg := cfg) (s := s) s'_mem_window
          have head_le_t :
              head ≤ t :=
            le_trans head_le_s' (Nat.le_of_lt ht_gt)
          have t_mem_window :
              t ∈ cfg.windowSlots s :=
            window_cover (t := t) head_le_t ht_lt
          by_contra h_no_skip_t
          have h_bad_t :
              Bad t :=
            ⟨ht_lt, t_mem_window, h_no_skip_t⟩
          have ht_le_s' :
                t ≤ s' := h_max t h_bad_t
          have ht_lt_self : t < t := lt_of_le_of_lt ht_le_s' ht_gt
          exact (Nat.lt_irrefl _ ht_lt_self)
        refine
          { first_slot := sPlus_first
            parent_exists := ⟨parent, ?_, ?_, ?_⟩ }
        · simpa [h_parent_slot] using s'_lt_sPlus
        · simpa [h_parent_slot] using h_parent_cert
        · intro t h_parent_lt h_t_lt
          have h_s'_lt : s' < t := by simpa [h_parent_slot] using h_parent_lt
          exact skips_after h_s'_lt h_t_lt

end Lemma40
end Alpenglow
