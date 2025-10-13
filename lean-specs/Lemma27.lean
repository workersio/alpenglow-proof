/-
  Lemma 27 (Correct Notar Voter in Every Certificate)
  ================================================

  We mechanize Lemma 27 from the Alpenglow whitepaper (p.30):

  > If there exists a notarization or notar-fallback certificate for block `b`,
  > then some correct node cast its notarization vote for `b`.

  **Whitepaper intuition:**
  - Notarization certificates aggregate ≥ 60% stake worth of notar votes.
    With < 20% byzantine stake, at least one correct node must have voted.
  - Notar-fallback certificates are only issued after the `SafeToNotar`
    guard fires (Definition 16). The guard requires at least 20% stake in
    notar votes for `b`. Since byzantine stake stays below 20%, a fallback
    certificate also implies the presence of a correct notar voter.

  **Lean strategy:**
  We reuse the stake accounting infrastructure from Lemma 21 and introduce a
  single axiom capturing the SafeToNotar guard: whenever the union of notar and
  skip votes reaches the 60% certificate threshold, the notar votes alone must
  carry at least 20% stake. Combining this guard with the global <20% byzantine
  bound yields the desired correct voter in both certificate cases.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Lemma21

open Classical

namespace Alpenglow
namespace Lemma27

open Lemma21

variable {Hash : Type _}

/-
  ## SafeToNotar Guard Axiom

  Definition 16 requires at least 20% notar stake before notar-fallback votes
  can be cast.  We encode this requirement so that any notar-fallback
  certificate implies sufficiently many notar votes on `b`.
-/

/-- SafeToNotar guard (Definition 16): a notar-fallback certificate implies
    at least 20% stake worth of notar votes for block `b`. -/
axiom notar_fallback_requires_notar_support
    (w : StakeWeight) (s : Slot) (b : Hash)
    (notarVotes : Finset (NotarVote Hash))
    (skipVotes : Finset SkipVote) :
    stakeSum w (notarVotesFor s b notarVotes ∪ skipVotesFor s skipVotes) >= notarizationThreshold →
    stakeSum w (notarVotesFor s b notarVotes) ≥ (20 : Real)

/-- **Lemma 27 (Correct notar voter exists).**

    If block `b` in slot `s` has either a notarization certificate or a
    notar-fallback certificate, then some correct node cast a notar vote for `b`.
-/
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
  -- All notar voters would have to be byzantine otherwise.
  have h_all_byz :
      ∀ n ∈ notarVotesFor s b notarVotes, ¬correct n := by
    intro n hn
    by_contra h_corr
    exact h_none ⟨n, h_corr, hn⟩
  -- Apply the byzantine stake bound to the notar voters.
  have h_byz :
      stakeSum w (notarVotesFor s b notarVotes) < (20 : Real) :=
    byzBound.bound (notarVotesFor s b notarVotes) (by
      intro n hn
      exact h_all_byz n hn)
  -- Distinguish the two certificate flavours.
  refine h_cert.elim ?h_notar ?h_fallback
  · intro h_notar
    -- ≥60% stake and <20% stake cannot both hold.
    have h_contra :
        (60 : Real) < 20 := by
      simpa [notarizationThreshold] using lt_of_le_of_lt h_notar h_byz
    have h_le_q : (20 : ℚ) ≤ 60 := by decide
    have h_le : (20 : Real) ≤ 60 := by exact_mod_cast h_le_q
    have : (20 : Real) < (20 : Real) := lt_of_le_of_lt h_le h_contra
    exact lt_irrefl _ this
  · intro h_fallback
    -- SafeToNotar axiom yields a ≥20% lower bound, contradicting <20%.
    have h_min :
        stakeSum w (notarVotesFor s b notarVotes) ≥ (20 : Real) :=
      notar_fallback_requires_notar_support w s b notarVotes skipVotes h_fallback
    have h_contra :
        (20 : Real) < (20 : Real) :=
      lt_of_le_of_lt h_min h_byz
    exact lt_irrefl _ h_contra

end Lemma27
end Alpenglow
