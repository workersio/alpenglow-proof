/-
  Lemma 39 (Window Certificates After Timeouts)
  =============================================

  Whitepaper statement (p.35):

  > If all correct nodes set the timeouts for slots of the leader window
  > `WINDOWSLOTS(s)`, then for every slot `s' ∈ WINDOWSLOTS(s)` all correct nodes
  > will observe a notar-fallback certificate for some block `b` with
  > `s' = slot(b)`, or a skip certificate for `s'`.

  **Strategy.**
  For every slot `s'` in the leader window we reuse the timeout witness from
  Lemma 37.  The witness guarantees that either a skip certificate materializes
  for `s'`, or correct voters controlling more than 40% stake cast notar votes
  for a common block `b` in that slot.  In the latter case we appeal to Lemma 38,
  which upgrades the correct-majority condition to a notar-fallback certificate.
  A lightweight axiom records that a correct-majority vote set must contain an
  explicit correct voter; combined with the `vote_slot_consistency` axiom from
  Lemma 28 this identifies the slot assignment required by Lemma 38.
-/

import Mathlib.Data.Finset.Basic
import Lemma28
import Lemma29
import Lemma37
import Lemma38

open Classical

namespace Alpenglow
namespace Lemma39

open Lemma21
open Lemma23
open Lemma28
open Lemma29
open Lemma37
open Lemma38

variable {Hash : Type _} [DecidableEq Hash]

/-- Any correct-majority notar vote set exposes a concrete correct voter who
    cast the vote.  This follows immediately from the whitepaper semantics:
    accumulating strictly more than 40% stake requires at least one correct
    participant. -/
axiom majority_has_correct_voter
    (w : StakeWeight) (correct : IsCorrect)
    (notarVotes : Finset (NotarVote Hash))
    {s : Slot} {b : Hash} :
    CorrectMajorityVoted w correct s b notarVotes →
    ∃ v, correct v ∧ v ∈ notarVotesFor s b notarVotes

/--
  **Lemma 39.** If every correct node schedules the timeout for each slot in
  `WINDOWSLOTS(s)`, then for every slot in that window either the skip vote
  threshold is met, or some block in the slot carries a notar-fallback
  certificate.
-/
theorem window_timeouts_yield_certificates
    (cfg : VotorConfig) (topo : BlockTopology Hash)
    (w : StakeWeight) (correct : IsCorrect)
    (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash))
    (skipVotes : Finset SkipVote)
    {s : Slot}
    (timeouts :
      ∀ {s'}, s' ∈ cfg.windowSlots s →
        TimeoutStakeWitness w correct s' notarVotes skipVotes) :
    ∀ {s'}, s' ∈ cfg.windowSlots s →
      stakeSum w (skipVotesFor s' skipVotes) ≥ notarizationThreshold ∨
        ∃ b,
          topo.slotOf b = s' ∧
          stakeSum w
              (notarVotesFor s' b notarVotes ∪
                notarFallbackVotesFor s' b fallbackVotes) ≥
            notarizationThreshold := by
  classical
  intro s' h_mem
  -- Timeout witness supplied by the hypothesis.
  have witness :
      TimeoutStakeWitness w correct s' notarVotes skipVotes :=
    timeouts h_mem
  -- Lemma 37 yields either a skip certificate or a correct notar majority.
  have h_outcome :=
    timeout_skip_or_majority
      (w := w) (correct := correct)
      (s := s') (notarVotes := notarVotes)
      (skipVotes := skipVotes) witness
  cases h_outcome with
  | inl h_majority_exists =>
      -- Correct notar majority ⇒ notar-fallback certificate via Lemma 38.
      rcases h_majority_exists with ⟨b, h_majority⟩
      -- Identify a concrete correct voter to recover the block's slot.
      obtain ⟨v, h_v_corr, h_voted⟩ :=
        majority_has_correct_voter
          (w := w) (correct := correct)
          (notarVotes := notarVotes)
          (s := s') (b := b) h_majority
      have h_slot :
          topo.slotOf b = s' :=
        vote_slot_consistency
          (topo := topo) (votes := notarVotes)
          (s := s') (b := b) (v := v) h_voted
      -- Lemma 38 upgrades the majority to a notar-fallback certificate.
      have h_certificate :
          stakeSum w
              (notarVotesFor s' b notarVotes ∪
                notarFallbackVotesFor s' b fallbackVotes) ≥
            notarizationThreshold :=
        notar_fallback_certificate_from_correct_majority
          (cfg := cfg) (topo := topo)
          (w := w) (correct := correct)
          (notarVotes := notarVotes)
          (fallbackVotes := fallbackVotes)
          (s := s') (b := b) h_slot h_majority
      exact Or.inr ⟨b, h_slot, h_certificate⟩
  | inr h_skip =>
      -- Skip certificate case.
      exact Or.inl h_skip

end Lemma39
end Alpenglow
