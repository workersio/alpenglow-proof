/-
  Lemma 26 (Slow-Finalization Property)
  =====================================

  We mechanize Lemma 26 from the Alpenglow whitepaper (p.30):

  > If a block `b` is slow-finalized then:
  > (i)  No other block `b'` in the same slot can be notarized.
  > (ii) No other block `b'` in the same slot can be notarized-fallback.
  > (iii) There cannot exist a skip certificate for the same slot.

  **Whitepaper Proof Sketch:**
  A slow-finalization certificate on slot `s` requires 60% of stake to cast a
  finalization vote, and by assumption byzantine nodes control < 20% stake.
  Therefore, a set `V` of correct nodes with > 40% stake finalizes slot `s`.
  The guard of Algorithm 2, line 19, ensures that every correct node in `V`
  already emitted a notarization vote for the same block `b`.  Lemmas 20 and 22
  guarantee that these correct nodes have not cast any conflicting votes in the
  same slot.  Since every certificate threshold is 60%, the remaining < 60% stake
  cannot produce a notarization / notar-fallback / skip certificate contradicting
  `b`.

  **Lean Strategy:**
  We parameterize over abstract stake accounting (borrowed from Lemma 21) and
  assume:

  * a finalization certificate witnessing 60% stake in `finalVotes`,
  * correct final voters lie inside the notarization voters for `b`,
  * byzantine stake is bounded by 20%.

  From these assumptions we derive that correct notarization voters for `b`
  hold > 40% stake (`CorrectMajorityVoted`), enabling reuse of Lemma 23.  The
  exclusivity axioms exported from Lemma 20 ensure that this majority never
  appears in competing vote sets, and a mild stake arithmetic axiom bounds the
  remaining stake strictly below the 60% certificate threshold.
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
  ## Stake Arithmetic Axioms

  The following axioms abstract simple arithmetic facts about stake accounting.
  They are mild strengthening of the axioms already assumed in Lemma 21.
-/

/-- If a set of voters accumulates 60% total stake and byzantine nodes control
    < 20%, then correct voters inside the set contribute > 40% stake. -/
axiom final_votes_imply_correct_majority
    (w : StakeWeight) (correct : IsCorrect)
    (byzBound : ByzantineStakeBound w correct)
    (finalVotes : Finset NodeId) :
    stakeSum w finalVotes >= notarizationThreshold →
    stakeSum w (finalVotes.filter correct) > fallbackThreshold

/-- Monotonicity of `stakeSum`: enlarging the voter set cannot decrease stake. -/
axiom stakeSum_subset_le
    (w : StakeWeight) (A B : Finset NodeId) :
    (∀ ⦃n⦄, n ∈ A → n ∈ B) →
    stakeSum w A ≤ stakeSum w B

/-- If correct voters control > 40% stake, any disjoint set of other voters
    holds strictly less than the 60% certificate threshold. -/
axiom complement_stake_lt_threshold
    (w : StakeWeight) (correct : IsCorrect)
    (majority : Finset NodeId) :
    (∀ n ∈ majority, correct n) →
    stakeSum w majority > fallbackThreshold →
    ∀ (others : Finset NodeId),
      (∀ n ∈ others, n ∉ majority) →
      stakeSum w others < notarizationThreshold

/-
  ## Slow-Finalization Exclusivity

  The main lemma mirrors the whitepaper statement using the abstract vote
  sets introduced in Lemma 21 and Lemma 23.
-/

variables {w : StakeWeight} {correct : IsCorrect}

/-- **Lemma 26 (Slow-Finalization Property).**

    Suppose slot `s` carries a slow-finalization certificate (60% stake in
    `finalVotes`) for block `b`, and every correct final voter already cast a
    notarization vote for `b`.  Then:

    1. No other block in slot `s` reaches notarization threshold.
    2. No other block in slot `s` can accumulate enough stake (notar or skip)
       to trigger a notar-fallback certificate.
    3. Slot `s` cannot accumulate enough skip votes to form a skip certificate.
-/
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
    -- (i) No other block can be notarized
    (∀ b', b' ≠ b →
        stakeSum w (notarVotesFor s b' notarVotes) < notarizationThreshold) ∧
    -- (ii) No other block can reach notar-fallback threshold
    (∀ b', b' ≠ b →
        stakeSum w (notarVotesFor s b' notarVotes ∪ skipVotesFor s skipVotes)
          < notarizationThreshold) ∧
    -- (iii) No skip certificate can exist
    stakeSum w (skipVotesFor s skipVotes) < notarizationThreshold := by
  classical
  -- Correct final voters form the majority set `majority`.
  set majority := finalVotes.filter correct
  -- Their stake exceeds 40%.
  have h_majority_gt40 :
      stakeSum w majority > fallbackThreshold :=
    final_votes_imply_correct_majority w correct byzBound finalVotes h_final_threshold
  -- Every element of `majority` is correct by construction.
  have h_majority_correct :
      ∀ n ∈ majority, correct n := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  -- The majority embeds into the notarization voters of block `b`.
  have h_majority_subset_notar :
      ∀ {n}, n ∈ majority →
        n ∈ (notarVotesFor s b notarVotes).filter correct := by
    intro n hn
    simpa [majority] using h_final_notar (by simpa [majority] using hn)
  -- Therefore correct notarization voters for `b` also exceed 40% stake.
  have h_correct_maj_notar :
      CorrectMajorityVoted w correct s b notarVotes := by
    unfold CorrectMajorityVoted
    -- Monotonicity lifts the >40% bound from `majority` to the larger set.
    have h_subset_sum :
        stakeSum w majority ≤
          stakeSum w ((notarVotesFor s b notarVotes).filter correct) :=
      stakeSum_subset_le w majority _ (by
        intro n hn
        exact h_majority_subset_notar (by simpa using hn))
    exact lt_of_lt_of_le h_majority_gt40 h_subset_sum
  -- Helper: every node in `majority` also voted to notarize `b`.
  have h_majority_notar :
      ∀ {n}, n ∈ majority → n ∈ notarVotesFor s b notarVotes := by
    intro n hn
    have h := h_majority_subset_notar (by simpa using hn)
    exact (Finset.mem_filter.mp h).1
  -- Assemble the three exclusivity clauses.
  refine ⟨?_, ?_, ?_⟩
  · -- (i) No other block notarized.
    intro b' h_diff
    have h_no_conflict :=
      lemma23_no_other_block_notarized w correct s b b' notarVotes
        h_correct_maj_notar h_diff.symm
    -- If the stake were ≥ 60, we would contradict Lemma 23.
    by_contra h_ge
    have h_is_notarized : IsNotarized w s b' notarVotes := by
      unfold IsNotarized notarizationThreshold
      exact le_of_not_lt h_ge
    exact h_no_conflict h_is_notarized
  · -- (ii) No notar-fallback certificate on a different block.
    intro b' h_diff
    -- Voters in `majority` cannot appear in the union:
    -- they are correct, notarized `b`, hence cannot notarize `b'`
    -- (Lemma 20) nor skip the slot.
    have h_disjoint :
        ∀ n ∈ (notarVotesFor s b' notarVotes ∪ skipVotesFor s skipVotes),
          n ∉ majority := by
      intro n hn_union hn_majority
      have h_correct : correct n := h_majority_correct n hn_majority
      have h_voted_b : n ∈ notarVotesFor s b notarVotes :=
        h_majority_notar (by simpa using hn_majority)
      cases Finset.mem_union.mp hn_union with
      | inl h_voted_b' =>
          -- Contradiction: correct node voted for both `b` and `b'`.
          exact
            Lemma21.correct_node_single_notar_vote correct s b b' notarVotes
              n h_correct h_diff.symm h_voted_b h_voted_b'
      | inr h_skip =>
          -- Contradiction: correct node voted notarize `b` and skip.
          exact
            Lemma21.correct_node_notar_excludes_skip correct s b notarVotes
              skipVotes n h_correct h_voted_b h_skip
    -- Apply the complement stake bound with `others = notarVotes ∪ skipVotes`.
    have :=
      complement_stake_lt_threshold w correct majority
        h_majority_correct h_majority_gt40
        (notarVotesFor s b' notarVotes ∪ skipVotesFor s skipVotes)
        (by
          intro n hn_union hn_majority
          exact (h_disjoint n hn_union) hn_majority)
    exact this
  · -- (iii) No skip certificate in slot `s`.
    -- The same complement argument applies with just the skip votes.
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
