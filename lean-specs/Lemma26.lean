/-
  Lemma 26 (Slow-Finalization Property)
  =====================================

  Reference: Alpenglow whitepaper p.30, lines 872-880

  Statement: If a block b is slow-finalized then:
    (i)   no other block b' in the same slot can be notarized,
    (ii)  no other block b' in the same slot can be notarized-fallback,
    (iii) there cannot exist a skip certificate for the same slot.

  Whitepaper proof:
  Suppose some correct node slow-finalized block b in slot s. By Definition 14,
  nodes holding at least 60% of stake cast finalization votes in slot s. Since
  byzantine nodes hold < 20% stake, a set V of correct nodes holding > 40% stake
  cast finalization votes. By Algorithm 2 line 19, nodes in V observed a
  notarization certificate for some block. By Lemma 24, all nodes in V observed
  the same certificate for block b, so all nodes in V previously cast a
  notarization vote for b. By Lemmas 20 and 22, nodes in V cast no other votes
  in slot s besides the notarization vote for b and the finalization vote. Since
  V holds > 40% stake and every certificate requires >= 60% stake, no skip
  certificate or certificate on another block b' != b can be produced.

  Implementation approach:
  We establish that correct final voters form a majority (> 40% stake) that
  all voted to notarize b. This lets us invoke Lemma 23 for notarization
  exclusivity. Vote exclusivity from Lemma 20 ensures this majority cannot
  appear in competing vote sets, and stake arithmetic ensures the remaining
  stake is insufficient (< 60%) to form any conflicting certificate.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Lemma21
import Lemma23

open Classical

namespace Alpenglow
namespace Lemma26

open Lemma21
open Lemma23

variable {Hash : Type _} [DecidableEq Hash]

/-
  Stake Arithmetic Axioms

  These axioms capture basic arithmetic properties needed for the proof.
  See AXIOMS_TO_PROVE.md for whitepaper references.
-/

/-- Given 60% stake and < 20% byzantine, correct voters contribute > 40%. -/
axiom final_votes_imply_correct_majority
    (w : StakeWeight) (correct : IsCorrect)
    (byzBound : ByzantineStakeBound w correct)
    (finalVotes : Finset NodeId) :
    stakeSum w finalVotes >= notarizationThreshold →
    stakeSum w (finalVotes.filter correct) > fallbackThreshold

/-- Monotonicity: enlarging a voter set cannot decrease total stake. -/
axiom stakeSum_subset_le
    (w : StakeWeight) (A B : Finset NodeId) :
    (∀ ⦃n⦄, n ∈ A → n ∈ B) →
    stakeSum w A ≤ stakeSum w B

/-- If correct voters hold > 40%, any disjoint set holds < 60% (certificate threshold). -/
axiom complement_stake_lt_threshold
    (w : StakeWeight) (correct : IsCorrect)
    (majority : Finset NodeId) :
    (∀ n ∈ majority, correct n) →
    stakeSum w majority > fallbackThreshold →
    ∀ (others : Finset NodeId),
      (∀ n ∈ others, n ∉ majority) →
      stakeSum w others < notarizationThreshold

/-
  Main Theorem
-/

variable {w : StakeWeight} {correct : IsCorrect}

/-- Lemma 26: If slot s has a slow-finalization certificate for block b, and
    correct final voters already cast notarization votes for b, then:
    (i)   no other block in slot s reaches notarization threshold,
    (ii)  no other block in slot s can form a notar-fallback certificate,
    (iii) slot s cannot form a skip certificate. -/
theorem slow_finalization_exclusivity
    (byzBound : ByzantineStakeBound w correct)
    (s : Slot) (b : Hash)
    (finalVotes : Finset NodeId)
    (notarVotes : Finset (NotarVote Hash))
    (skipVotes : Finset SkipVote)
    (h_final_threshold : stakeSum w finalVotes >= notarizationThreshold)
    (h_final_notar :
      ∀ ⦃n⦄, n ∈ finalVotes.filter correct →
        n ∈ (notarVotesFor s b notarVotes).filter correct) :
    (∀ b', b' ≠ b →
        stakeSum w (notarVotesFor s b' notarVotes) < notarizationThreshold) ∧
    (∀ b', b' ≠ b →
        stakeSum w (notarVotesFor s b' notarVotes ∪ skipVotesFor s skipVotes)
          < notarizationThreshold) ∧
    stakeSum w (skipVotesFor s skipVotes) < notarizationThreshold := by
  classical
  set majority := finalVotes.filter correct
  have h_majority_gt40 :
      stakeSum w majority > fallbackThreshold :=
    final_votes_imply_correct_majority w correct byzBound finalVotes h_final_threshold
  have h_majority_correct :
      ∀ n ∈ majority, correct n := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have h_majority_subset_notar :
      ∀ {n}, n ∈ majority →
        n ∈ (notarVotesFor s b notarVotes).filter correct := by
    intro n hn
    simpa [majority] using h_final_notar (by simpa [majority] using hn)
  -- Correct notarization voters for b also exceed 40% stake (by monotonicity).
  have h_correct_maj_notar :
      CorrectMajorityVoted w correct s b notarVotes := by
    unfold CorrectMajorityVoted
    have h_subset_sum :
        stakeSum w majority ≤
          stakeSum w ((notarVotesFor s b notarVotes).filter correct) :=
      stakeSum_subset_le w majority _ (by
        intro n hn
        exact h_majority_subset_notar (by simpa using hn))
    exact lt_of_lt_of_le h_majority_gt40 h_subset_sum
  have h_majority_notar :
      ∀ {n}, n ∈ majority → n ∈ notarVotesFor s b notarVotes := by
    intro n hn
    have h := h_majority_subset_notar (by simpa using hn)
    exact (Finset.mem_filter.mp h).1
  refine ⟨?_, ?_, ?_⟩
  · -- (i) Use Lemma 23: if b' were notarized, contradicts correct majority for b.
    intro b' h_diff
    have h_no_conflict :=
      lemma23_no_other_block_notarized w correct s b b' notarVotes
        h_correct_maj_notar h_diff.symm
    by_contra h_ge
    have h_is_notarized : IsNotarized w s b' notarVotes := by
      unfold IsNotarized notarizationThreshold
      exact not_lt.mp h_ge
    exact h_no_conflict h_is_notarized
  · -- (ii) Majority cannot vote for b' or skip (by Lemma 20), so remaining stake < 60%.
    intro b' h_diff
    have h_disjoint :
        ∀ n ∈ (notarVotesFor s b' notarVotes ∪ skipVotesFor s skipVotes),
          n ∉ majority := by
      intro n hn_union hn_majority
      have h_correct : correct n := h_majority_correct n hn_majority
      have h_voted_b : n ∈ notarVotesFor s b notarVotes :=
        h_majority_notar (by simpa using hn_majority)
      cases Finset.mem_union.mp hn_union with
      | inl h_voted_b' =>
          exact
            Lemma21.correct_node_single_notar_vote correct s b b' notarVotes
              n h_correct h_diff.symm h_voted_b h_voted_b'
      | inr h_skip =>
          exact
            Lemma21.correct_node_notar_excludes_skip correct s b notarVotes
              skipVotes n h_correct h_voted_b h_skip
    have :=
      complement_stake_lt_threshold w correct majority
        h_majority_correct h_majority_gt40
        (notarVotesFor s b' notarVotes ∪ skipVotesFor s skipVotes)
        (by
          intro n hn_union hn_majority
          exact (h_disjoint n hn_union) hn_majority)
    exact this
  · -- (iii) Similar argument: majority cannot skip (by Lemma 20), so skip votes < 60%.
    have h_disjoint_skip :
        ∀ n ∈ skipVotesFor s skipVotes, n ∉ majority := by
      intro n h_skip h_majority
      have h_correct : correct n := h_majority_correct n h_majority
      have h_voted_b : n ∈ notarVotesFor s b notarVotes :=
        h_majority_notar (by simpa using h_majority)
      exact
        Lemma21.correct_node_notar_excludes_skip correct s b notarVotes
          skipVotes n h_correct h_voted_b h_skip
    exact
      complement_stake_lt_threshold w correct majority
        h_majority_correct h_majority_gt40
        (skipVotesFor s skipVotes)
        (by
          intro n h_skip hn_majority
          exact h_disjoint_skip n h_skip hn_majority)

end Lemma26
end Alpenglow
