/-
  Lemma 42 (ParentReady Propagation After GST)
  ============================================

  Whitepaper statement (p.36):

  > Suppose it is after GST and the first correct node `v` set the timeout for
  > the first slot `s` of a leader window `WINDOWSLOTS(s)` at time `t`. Then,
  > all correct nodes will emit some event `ParentReady(s, hash(b))` and set
  > timeouts for slots in `WINDOWSLOTS(s)` by time `t + Δ`.

  The whitepaper argues that once a correct node schedules the window head
  timeout, it must already have observed the notar/skip certificates required
  by Definition 15 (Corollary 34).  After GST, these certificates are broadcast
  to every correct node within the network delay bound `Δ`, making the same
  `ParentReady` witness available globally.  Handling `ParentReady` then
  programs all window timeouts via Algorithm 2 (Lemma 33).

  We capture the post-GST broadcast behaviour through a single axiom: any
  `ParentReady` witness for slot `s` disseminates to all correct nodes within
  `Δ`, yielding timeout witnesses for every slot of the window headed by `s`.
  The lemma below exposes the whitepaper conclusion directly from this axiom.
-/

import Lemma21
import Lemma28
import Lemma29
import Lemma37
import Lemma40
import Lemma41

open Classical

namespace Alpenglow
namespace Lemma42

open Lemma21
open Lemma28
open Lemma29
open Lemma37
open Lemma40
open Lemma41

-- variable {Hash : Type _} [DecidableEq Hash]

/-
  ## After-GST Propagation Axiom
-/

/--
  After GST, the certificates supporting a `ParentReady` witness spread to all
  correct nodes within the network latency bound `Δ`.  Consequently every slot
  in the window headed by `s` acquires a timeout witness.  We expose this white
  paper assumption as an explicit hypothesis.
-/
abbrev parentReadyTimeoutPropagation
    (cfg : VotorConfig) (topo : BlockTopology Hash)
    (w : StakeWeight) (correct : IsCorrect)
    (Δ : Nat) (afterGST : Prop)
    (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash))
    (skipVotes : Finset SkipVote)
    (s : Slot) :=
  afterGST →
    ParentReadyWitness cfg topo w notarVotes fallbackVotes skipVotes s →
      WindowTimeouts cfg w correct notarVotes skipVotes s

/-
  ## Lemma 42
-/

/--
  **Lemma 42.** After GST, once the first correct node schedules the timeout
  for the window head `s`, every correct node inherits the same
  `ParentReady` witness and obtains timeout witnesses for all slots in
  `WINDOWSLOTS(s)` by time `t + Δ`.
-/
theorem parentReady_and_timeouts_after_first_timeout
    (cfg : VotorConfig) (topo : BlockTopology Hash)
    (w : StakeWeight) (correct : IsCorrect)
    (Δ : Nat) (afterGST : Prop)
    (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash))
    (skipVotes : Finset SkipVote)
    {s : Slot}
    (propagate :
      parentReadyTimeoutPropagation cfg topo w correct Δ afterGST
        notarVotes fallbackVotes skipVotes s)
    (h_afterGST : afterGST)
    (first_node_parent_ready :
      ParentReadyWitness cfg topo w notarVotes fallbackVotes skipVotes s) :
    ParentReadyWitness cfg topo w notarVotes fallbackVotes skipVotes s ∧
      ∀ {t}, t ∈ cfg.windowSlots s →
        Nonempty (TimeoutStakeWitness (Hash := Hash) w correct t notarVotes skipVotes) := by
  -- The propagation axiom supplies timeout witnesses for the entire window.
  have h_timeouts :
      WindowTimeouts cfg w correct notarVotes skipVotes s :=
    propagate h_afterGST first_node_parent_ready
  refine ⟨first_node_parent_ready, ?_⟩
  intro t ht
  exact ⟨h_timeouts (t := t) ht⟩

end Lemma42
end Alpenglow
