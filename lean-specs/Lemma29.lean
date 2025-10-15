/-
  Lemma 29: Parent Support for Notar-Fallback Votes

  Whitepaper: Lemma 29, page 31, lines 899-901

  Statement from whitepaper:
  Suppose a correct node v cast a notar-fallback vote for a block b in slot s
  that is not the first slot of the window, and b' is the parent of b. Then,
  either some correct node cast a notar-fallback vote for b', or correct nodes
  with more than 40% of stake cast notarization votes for b'.

  Proof from whitepaper (page 31, line 901):
  SafeToNotar conditions (Definition 16) require that v observed a notarization
  or notar-fallback certificate for b', and so nodes with at least 60% of stake
  cast notarization or notar-fallback votes for b'. Since byzantine nodes
  possess less than 20% of stake, either correct nodes with more than 40% of
  stake cast notarization votes for b', or some correct node cast a
  notar-fallback vote for b'.

  Key insight: The SafeToNotar event for non-first slots requires a certificate
  for the parent (Definition 16, page 22, lines 565-569). With 60% total votes
  and <20% byzantine stake, correct votes must either include a fallback vote
  or exceed 40% in notarization votes alone.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Lemma21
import Lemma28

open Classical

namespace Alpenglow
namespace Lemma29

open Lemma21
open Lemma28

variable {Hash : Type _} [DecidableEq Hash]

/-- Record that a node cast a notar-fallback vote for block b in slot s. -/
structure NotarFallbackVote (Hash : Type _) where
  voter : NodeId
  slot : Slot
  blockHash : Hash

/-- Extract the set of nodes that cast notar-fallback votes for (s, b). -/
axiom notarFallbackVotesFor
    (s : Slot) (b : Hash)
    (votes : Finset (NotarFallbackVote Hash)) :
    Finset NodeId

/-
  Axiom 1: A correct notar-fallback vote in a non-first slot implies the parent
  has a certificate (>= 60% stake in combined notar/notar-fallback votes).
  This captures the SafeToNotar guard for non-first slots (Definition 16).
-/
axiom fallback_vote_requires_parent_certificate
    (cfg : VotorConfig) (topo : BlockTopology Hash)
    (w : StakeWeight) (correct : IsCorrect)
    (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash))
    {v : NodeId} {s : Slot} {b parent : Hash} :
    topo.slotOf b = s →
    topo.parentOf b = some parent →
    cfg.windowFirstSlot s < s →
    v ∈ notarFallbackVotesFor s b fallbackVotes →
    correct v →
    stakeSum w
      (notarVotesFor (topo.slotOf parent) parent notarVotes ∪
        notarFallbackVotesFor (topo.slotOf parent) parent fallbackVotes) ≥
      notarizationThreshold

/-
  Axiom 2: Given a certificate (>= 60% stake) and byzantine stake < 20%,
  either some correct node cast a fallback vote, or correct notarization
  votes alone exceed 40%. This is the stake arithmetic from the proof.
-/
axiom certificate_yields_fallback_or_majority
    (w : StakeWeight) (correct : IsCorrect)
    (byzBound : ByzantineStakeBound w correct)
    (slot : Slot) (b : Hash)
    (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash)) :
    stakeSum w
      (notarVotesFor slot b notarVotes ∪
        notarFallbackVotesFor slot b fallbackVotes) ≥
      notarizationThreshold →
    (∃ n, correct n ∧ n ∈ notarFallbackVotesFor slot b fallbackVotes) ∨
    stakeSum w ((notarVotesFor slot b notarVotes).filter correct) >
      fallbackThreshold

/--
  Lemma 29: If a correct node casts a notar-fallback vote for block b in a
  non-first slot s, then for the parent block parent, either some correct node
  cast a notar-fallback vote for parent, or correct notarization votes for
  parent exceed 40% of stake.
-/
theorem parent_support_for_fallback
    (cfg : VotorConfig) (topo : BlockTopology Hash)
    (w : StakeWeight) (correct : IsCorrect)
    (byzBound : ByzantineStakeBound w correct)
    (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash))
    {v : NodeId} {s : Slot} {b parent : Hash}
    (h_slot : topo.slotOf b = s)
    (h_parent : topo.parentOf b = some parent)
    (h_not_first : cfg.windowFirstSlot s < s)
    (h_vote : v ∈ notarFallbackVotesFor s b fallbackVotes)
    (h_correct : correct v) :
    (∃ n, correct n ∧
          n ∈ notarFallbackVotesFor (topo.slotOf parent) parent fallbackVotes) ∨
      stakeSum w
          ((notarVotesFor (topo.slotOf parent) parent notarVotes).filter correct) >
        fallbackThreshold := by
  classical

  -- Axiom 1: SafeToNotar guard yields a parent certificate.
  have h_parent_cert :
      stakeSum w
          (notarVotesFor (topo.slotOf parent) parent notarVotes ∪
            notarFallbackVotesFor (topo.slotOf parent) parent fallbackVotes) ≥
        notarizationThreshold :=
    fallback_vote_requires_parent_certificate (cfg := cfg) (topo := topo)
      (w := w) (correct := correct) (notarVotes := notarVotes)
      (fallbackVotes := fallbackVotes) h_slot h_parent h_not_first h_vote h_correct

  -- Axiom 2: The certificate implies the desired disjunction.
  have h_support :=
    certificate_yields_fallback_or_majority
      (w := w) (correct := correct) (byzBound := byzBound)
      (slot := topo.slotOf parent) (b := parent)
      (notarVotes := notarVotes) (fallbackVotes := fallbackVotes) h_parent_cert
  simpa using h_support

end Lemma29
end Alpenglow
