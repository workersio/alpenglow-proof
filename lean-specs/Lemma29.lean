/-
  Lemma 29 (Parent Support for Notar-Fallback Votes)
  ================================================

  We mechanize Lemma 29 from the Alpenglow whitepaper (p.31):

  > Suppose a correct node `v` cast a notar-fallback vote for a block `b` in
  > slot `s` that is not the first slot of the window, and `b'` is the parent
  > of `b`. Then, either some correct node cast a notar-fallback vote for `b'`,
  > or correct nodes with more than 40% of stake cast notarization votes for `b'`.

  **Whitepaper intuition:**
  - Casting a notar-fallback vote in a non-first slot requires `SafeToNotar`
    to fire. For these slots, the guard first retrieves the parent block and
    only emits the event once the parent has a notarization or notar-fallback
    certificate.
  - Such a certificate aggregates at least 60% stake in notar or notar-fallback
    votes for the parent. Since byzantine stake stays below 20%, either some
    correct node contributed a fallback vote for the parent, or correct nodes
    alone contributed over 40% stake in notarization votes.

  **Lean strategy:**
  We introduce a lightweight `NotarFallbackVote` record mirroring notarization
  votes and an abstract extractor `notarFallbackVotesFor`. The interaction
  between `SafeToNotar` and the parent certificate is summarized by two axioms:

  1. `fallback_vote_requires_parent_certificate` — every correct notar-fallback
     vote in a non-first slot witnesses a parent certificate combining notar and
     notar-fallback votes (≥ 60% stake).
  2. `certificate_yields_fallback_or_majority` — whenever such a certificate
     exists, either some correct fallback vote is present or the correct notar
     voters alone exceed the 40% fallback threshold.

  Combining both axioms produces the desired disjunction for the parent block.
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

/-
  ## Notar-Fallback Votes
-/

/-- Record that a node cast a notar-fallback vote for block `b` in slot `s`. -/
structure NotarFallbackVote (Hash : Type _) where
  voter : NodeId
  slot : Slot
  blockHash : Hash

/-- Extract the set of nodes that cast notar-fallback votes for `(s, b)`. -/
axiom notarFallbackVotesFor
    (s : Slot) (b : Hash)
    (votes : Finset (NotarFallbackVote Hash)) :
    Finset NodeId

/-
  ## SafeToNotar Guard Axioms
-/

/-- Casting a notar-fallback vote in a non-first slot necessitates observing a
    notarization or notar-fallback certificate for the parent block. -/
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

/-- Certificates aggregating ≥60% stake in notar/notar-fallback votes either
    include a correct fallback voter or grant >40% correct notar support. -/
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

/-
  ## Lemma 29
-/

/-- **Lemma 29 (Parent support for notar-fallback votes).**

    If a correct node casts a notar-fallback vote for block `b` in a non-first
    slot `s`, then the parent block `parent` enjoys one of two guarantees:

    * some correct node emitted a notar-fallback vote for `parent`, or
    * correct notar voters for `parent` alone exceed the 40% fallback threshold.
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
  -- SafeToNotar guard yields a parent certificate.
  have h_parent_cert :
      stakeSum w
          (notarVotesFor (topo.slotOf parent) parent notarVotes ∪
            notarFallbackVotesFor (topo.slotOf parent) parent fallbackVotes) ≥
        notarizationThreshold :=
    fallback_vote_requires_parent_certificate (cfg := cfg) (topo := topo)
      (w := w) (correct := correct) (notarVotes := notarVotes)
      (fallbackVotes := fallbackVotes) h_slot h_parent h_not_first h_vote h_correct
  -- The certificate implies either a correct fallback voter or >40% correct notar stake.
  have h_support :=
    certificate_yields_fallback_or_majority
      (w := w) (correct := correct) (byzBound := byzBound)
      (slot := topo.slotOf parent) (b := parent)
      (notarVotes := notarVotes) (fallbackVotes := fallbackVotes) h_parent_cert
  simpa using h_support

end Lemma29
end Alpenglow
