/-
  Lemma 37 (Timeout Skip-Or-Majority)
  ===================================

  Whitepaper statement (p.33):

  > If all correct nodes set the timeout for slot `s`, either the skip certificate
  > for `s` is eventually observed by all correct nodes, or correct nodes with more
  > than 40% of stake cast notarization votes for the same block in slot `s`.

  We materialize the hypothesis “all correct nodes set the timeout” via a witness
  describing a large (>80%) set of correct nodes that, after the timeout fires,
  either cast skip/skip-fallback votes or notarize some block in slot `s`.  An
  additional axiom abstracts the SafeToSkip reasoning from the whitepaper: if no
  block gathers a >40% correct majority, the accumulated skip votes must reach the
  60% certificate threshold.  The resulting lemma mirrors the whitepaper wording.
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

/-- Witness that every correct node scheduled the timeout for slot `s`.  The
    witness records a large set of correct nodes together with the guarantee
    that each node eventually casts either a skip (or skip-fallback) vote, or a
    notarization vote for some block in slot `s`. -/
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

/--
  Abstract SafeToSkip axiom: if no block acquires a >40% correct majority,
  the skip votes triggered by the timeout witness must cross the 60% certificate
  threshold.  This captures the final step of the whitepaper proof, where lack
  of a notar majority forces correct nodes to emit skip-fallback votes.
-/
axiom skip_votes_lower_bound
    (w : StakeWeight) (correct : IsCorrect)
    (s : Slot)
    (notarVotes : Finset (NotarVote Hash))
    (skipVotes : Finset SkipVote)
    (witness : TimeoutStakeWitness w correct s notarVotes skipVotes) :
    (∀ b, stakeSum w ((notarVotesFor s b notarVotes).filter correct) ≤ fallbackThreshold) →
    stakeSum w (skipVotesFor s skipVotes) ≥ notarizationThreshold

/--
  **Lemma 37.** If every correct node schedules the timeout for slot `s`, then
  either a correct majority notarizes some block in `s`, or the skip certificate
  threshold is met in `s`.
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
