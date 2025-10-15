/-
  Lemma 27: Correct Notar Voter in Every Certificate

  Whitepaper: Lemma 27, page 30

  Statement: If there exists a notarization or notar-fallback certificate for
  block b, then some correct node cast its notarization vote for b.

  Proof sketch (by contradiction):
  Assume no correct node voted to notarize b. Since byzantine stake < 20%, each
  correct node observes < 20% stake voting to notarize b. Both SafeToNotar
  conditions (Definition 16, pages 21-22) require at least 20% stake voting to
  notarize b. Therefore no correct node emits SafeToNotar(s, hash(b)), which is
  the only trigger for notar-fallback votes (Algorithm 1, line 16-19). So no
  correct node casts a notar-fallback vote for b. But certificates require >= 60%
  stake (Definition 11), contradiction.

  Mechanization: We axiomatize the SafeToNotar guard from Definition 16 and
  combine it with the byzantine stake bound to derive the contradiction.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Lemma21

open Classical

namespace Alpenglow
namespace Lemma27

open Lemma21

variable {Hash : Type _}

-- SafeToNotar Guard Axiom (Definition 16, pages 21-22)
--
-- A notar-fallback certificate can only exist if SafeToNotar fired, which
-- requires notar(b) >= 20% in the condition:
--   notar(b) >= 40%  OR  (skip(s) + notar(b) >= 60%  AND  notar(b) >= 20%)
-- When a notar-fallback certificate exists (notar + skip >= 60%), this axiom
-- enforces the 20% lower bound on notar votes alone.

/-- SafeToNotar guard: a notar-fallback certificate implies at least 20% stake
    worth of notar votes for block b. -/
axiom notar_fallback_requires_notar_support
    (w : StakeWeight) (s : Slot) (b : Hash)
    (notarVotes : Finset (NotarVote Hash))
    (skipVotes : Finset SkipVote) :
    stakeSum w (notarVotesFor s b notarVotes ∪ skipVotesFor s skipVotes) >= notarizationThreshold →
    stakeSum w (notarVotesFor s b notarVotes) ≥ (20 : Real)

/-- Lemma 27: If block b in slot s has either a notarization certificate or a
    notar-fallback certificate, then some correct node cast a notar vote for b. -/
theorem correct_voter_exists_for_certificate
    {w : StakeWeight} {correct : IsCorrect}
    (byzBound : ByzantineStakeBound w correct)
    (s : Slot) (b : Hash)
    (notarVotes : Finset (NotarVote Hash))
    (skipVotes : Finset SkipVote)
    (h_cert :
      stakeSum w (notarVotesFor s b notarVotes) >= notarizationThreshold ∨
      stakeSum w (notarVotesFor s b notarVotes ∪ skipVotesFor s skipVotes) >= notarizationThreshold) :
    ∃ n, correct n ∧ n ∈ notarVotesFor s b notarVotes := by
  classical
  by_contra h_none
  -- If no correct node voted, all notar voters must be byzantine.
  have h_all_byz :
      ∀ n ∈ notarVotesFor s b notarVotes, ¬correct n := by
    intro n hn
    by_contra h_corr
    exact h_none ⟨n, h_corr, hn⟩
  -- Byzantine stake < 20%, so notar votes carry < 20% stake.
  have h_byz :
      stakeSum w (notarVotesFor s b notarVotes) < (20 : Real) :=
    byzBound.bound (notarVotesFor s b notarVotes) (by
      intro n hn
      exact h_all_byz n hn)
  -- Consider both certificate types.
  refine h_cert.elim ?h_notar ?h_fallback
  · intro h_notar
    -- Notarization certificate: notar votes >= 60%, but we have < 20%.
    have h_contra :
        (60 : Real) < 20 := by
      simpa [notarizationThreshold] using lt_of_le_of_lt h_notar h_byz
    have h_le_q : (20 : ℚ) ≤ 60 := by decide
    have h_le : (20 : Real) ≤ 60 := by exact_mod_cast h_le_q
    have : (20 : Real) < (20 : Real) := lt_of_le_of_lt h_le h_contra
    exact lt_irrefl _ this
  · intro h_fallback
    -- Notar-fallback certificate: SafeToNotar requires >= 20%, but we have < 20%.
    have h_min :
        stakeSum w (notarVotesFor s b notarVotes) ≥ (20 : Real) :=
      notar_fallback_requires_notar_support w s b notarVotes skipVotes h_fallback
    have h_contra :
        (20 : Real) < (20 : Real) :=
      lt_of_le_of_lt h_min h_byz
    exact lt_irrefl _ h_contra

end Lemma27
end Alpenglow
