/-
  Lemma 39: Window Certificates After Timeouts

  Whitepaper: Lemma 39, page 35

  Statement from whitepaper:
  If all correct nodes set the timeouts for slots of the leader window
  WINDOWSLOTS(s), then for every slot s' in WINDOWSLOTS(s) all correct nodes
  will observe a notar-fallback certificate for b in slot s' = slot(b), or a
  skip certificate for s'.

  Proof from whitepaper (page 35):
  If correct nodes observe skip certificates in all slots, we are done.
  Otherwise, let s' be any slot for which a correct node will not observe a
  skip certificate. By Lemma 37, there is a block b in slot s' = slot(b) such
  that correct nodes with more than 40% of stake cast the notarization vote for
  b. By Lemma 38, correct nodes will observe a notar-fallback certificate for b.

  Proof strategy:
  For each slot s' in the window, apply Lemma 37 using the timeout witness.
  This yields either a skip certificate or >40% correct notar votes for some
  block b. In the latter case, identify a concrete correct voter (axiom
  majority_has_correct_voter) to determine the slot assignment via Lemma 28,
  then apply Lemma 38 to obtain the notar-fallback certificate.
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

/- Accumulating >40% stake requires at least one correct participant. -/
axiom majority_has_correct_voter
    (w : StakeWeight) (correct : IsCorrect)
    (notarVotes : Finset (NotarVote Hash))
    {s : Slot} {b : Hash} :
    CorrectMajorityVoted w correct s b notarVotes →
    ∃ v, correct v ∧ v ∈ notarVotesFor s b notarVotes

/- Lemma 39: If every correct node schedules the timeout for each slot in
    WINDOWSLOTS(s), then for every slot in that window either the skip vote
    threshold is met, or some block in the slot carries a notar-fallback
    certificate. -/
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
  have witness :
      TimeoutStakeWitness w correct s' notarVotes skipVotes :=
    timeouts h_mem
  -- Apply Lemma 37.
  have h_outcome :=
    timeout_skip_or_majority
      (w := w) (correct := correct)
      (s := s') (notarVotes := notarVotes)
      (skipVotes := skipVotes) witness
  cases h_outcome with
  | inl h_majority_exists =>
      -- Case: >40% correct notar votes for some block b.
      rcases h_majority_exists with ⟨b, h_majority⟩
      -- Extract a concrete correct voter to determine b's slot assignment.
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
      -- Apply Lemma 38.
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
      exact Or.inl h_skip

end Lemma39
end Alpenglow
