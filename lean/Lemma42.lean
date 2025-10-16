/-
  Lemma 42: ParentReady Propagation After GST
  ===========================================

  Whitepaper reference: Page 36, Section 2.10 (Liveness)

  Statement: Suppose it is after GST and the first correct node v set the
  timeout for the first slot s of a leader window WINDOWSLOTS(s) at time t.
  Then, all correct nodes will emit some event ParentReady(s, hash(b)) and set
  timeouts for slots in WINDOWSLOTS(s) by time t + Δ.

  Proof sketch: By Corollary 34 and Definition 15, v observed a notar-fallback
  certificate for some block b and skip certificates for all slots i such that
  slot(b) < i < s by time t. Since v is correct, it broadcast the certificates,
  which were also observed by all correct nodes by time t + Δ. Therefore, all
  correct nodes emitted ParentReady(s, hash(b)) by time t + Δ and set the
  timeouts for all slots in WINDOWSLOTS(s).

  Formalization approach: We introduce parentReadyTimeoutPropagation as an
  axiom capturing the broadcast behavior after GST. Any ParentReady witness
  disseminates to all correct nodes within Δ, yielding timeout witnesses for
  every slot in the window.
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

/-
  Axiom: After GST, certificates supporting a ParentReady witness spread to all
  correct nodes within Δ. Consequently every slot in the window acquires a
  timeout witness.
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
  Lemma 42. After GST, once the first correct node schedules the timeout for
  the window head s, every correct node inherits the same ParentReady witness
  and obtains timeout witnesses for all slots in WINDOWSLOTS(s) by time t + Δ.
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
  have h_timeouts :
      WindowTimeouts cfg w correct notarVotes skipVotes s :=
    propagate h_afterGST first_node_parent_ready
  refine ⟨first_node_parent_ready, ?_⟩
  intro t ht
  exact ⟨h_timeouts (t := t) ht⟩

end Lemma42
end Alpenglow
