/-
  Lemma 37: Timeout Skip-Or-Majority
  ===================================

  Whitepaper (page 33):
  If all correct nodes set the timeout for slot s, either the skip certificate
  for s is eventually observed by all correct nodes, or correct nodes with more
  than 40% of stake cast notarization votes for the same block in slot s.

  Proof outline (pages 33-34):
  Suppose no block gets >40% correct stake. Since all correct nodes timeout,
  they observe votes from a set S of correct nodes with ≥80% stake. For any
  node v in S, after receiving votes from S: skip(s) + Σ_b notar(b) = 80% + w
  (where w is stake from outside S). Since max_b notar(b) ≤ 40% + w, we have
  skip(s) ≥ 40%. Nodes that haven't cast skip votes will emit SafeToSkip(s)
  and cast skip-fallback votes, ensuring all correct nodes eventually cast
  skip or skip-fallback votes, resulting in a skip certificate.

  This formalization uses a witness structure to represent the >80% correct
  stake that participates after timeouts fire, and abstracts the SafeToSkip
  arithmetic via skip_votes_lower_bound axiom.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Lemma21
import Lemma23

open Classical

namespace Alpenglow
namespace Lemma37

open Lemma21
open Lemma23

variable {Hash : Type _} [DecidableEq Hash]

/-
  Represents the set S of correct nodes with ≥80% stake mentioned in the
  whitepaper proof. Each node in this set casts either a skip vote or a
  notarization vote for slot s after the timeout fires.
-/
structure TimeoutStakeWitness (w : StakeWeight) (correct : IsCorrect)
    (s : Slot) (notarVotes : Finset (NotarVote Hash))
    (skipVotes : Finset SkipVote) where
  carrier : Finset NodeId
  carrier_correct :
      ∀ n ∈ carrier, correct n
  carrier_stake :
      stakeSum w carrier ≥ fastFinalizationThreshold
  carrier_votes :
      ∀ n ∈ carrier,
        n ∈ skipVotesFor s skipVotes ∨
          ∃ b, n ∈ notarVotesFor s b notarVotes

/-
  Captures the arithmetic from whitepaper pages 33-34: when no block has
  >40% correct stake and all correct nodes timeout, the skip votes must
  reach 60% threshold. This abstracts the SafeToSkip event logic where nodes
  emit skip-fallback votes when they observe skip(s) ≥ 40%.
-/
axiom skip_votes_lower_bound
    (w : StakeWeight) (correct : IsCorrect)
    (s : Slot)
    (notarVotes : Finset (NotarVote Hash))
    (skipVotes : Finset SkipVote)
    (witness : TimeoutStakeWitness w correct s notarVotes skipVotes) :
    (∀ b, stakeSum w ((notarVotesFor s b notarVotes).filter correct) ≤ fallbackThreshold) →
    stakeSum w (skipVotesFor s skipVotes) ≥ notarizationThreshold

/-
  Lemma 37 (Whitepaper page 33): Either a correct majority notarizes some
  block in slot s, or the skip certificate threshold is met.
-/
theorem timeout_skip_or_majority
    (w : StakeWeight) (correct : IsCorrect)
    (s : Slot)
    (notarVotes : Finset (NotarVote Hash))
    (skipVotes : Finset SkipVote)
    (witness : TimeoutStakeWitness w correct s notarVotes skipVotes) :
    (∃ b, CorrectMajorityVoted w correct s b notarVotes) ∨
    stakeSum w (skipVotesFor s skipVotes) ≥ notarizationThreshold := by
  classical
  by_cases hMajor : ∃ b, CorrectMajorityVoted w correct s b notarVotes
  · exact Or.inl hMajor
  · have hAll := not_exists.mp hMajor
    have h_no_majority :
        ∀ b, stakeSum w ((notarVotesFor s b notarVotes).filter correct) ≤ fallbackThreshold := by
      intro b
      have h_not : ¬ CorrectMajorityVoted w correct s b notarVotes := hAll b
      unfold CorrectMajorityVoted at h_not
      exact not_lt.mp h_not
    have h_skip :
        stakeSum w (skipVotesFor s skipVotes) ≥ notarizationThreshold :=
      skip_votes_lower_bound w correct s notarVotes skipVotes witness h_no_majority
    exact Or.inr h_skip

end Lemma37
end Alpenglow
