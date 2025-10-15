/-
  Theorem 2 (Liveness)
  ====================

  This module mechanizes Theorem 2 from the Alpenglow whitepaper (p.36):

  > Let `v_ℓ` be a correct leader of the window `WINDOWSLOTS(s)`. Assume that
  > no correct node set the timeouts for slots in this window before GST and
  > that Rotor dissemination succeeds for every slot of the window. Then every
  > block produced by `v_ℓ` in `WINDOWSLOTS(s)` is finalized by all correct
  > nodes.

  The proof assembles the window-level lemmas developed in Section 4:

  * Lemma 42 propagates a `ParentReady` witness across the window once GST has
    passed, providing timeout witnesses for every slot.
  * Lemma 39 turns those timeout witnesses into notar/skip certificates.
  * Rotor success rules out the skip alternative, leaving a notar-fallback
    certificate for the block disseminated by the leader in each slot.
  * A final context assumption converts these certificates into finalized
    blocks for the participating correct nodes.
-/

import Lemma21
import Lemma28
import Lemma29
import Lemma39
import Lemma40
import Lemma42

open Classical

namespace Alpenglow
namespace Theorem2

open Lemma21
  ( StakeWeight IsCorrect stakeSum notarizationThreshold
    NotarVote SkipVote notarVotesFor skipVotesFor )
open Lemma29 (NotarFallbackVote notarFallbackVotesFor)
open Lemma37 (TimeoutStakeWitness)
open Lemma40 (ParentReadyWitness)

variable {Hash : Type _} [DecidableEq Hash]

/--
  Context describing a single leader window operated by a correct leader.
  The record bundles the static protocol data (configuration, topology and
  vote sets), the target block for every slot of the window, and the liveness
  assumptions imported from the whitepaper (after-GST parent-ready witness,
  Rotor success, and the fact that notar certificates for the leader’s block
  yield finalization).
-/
structure WindowContext (Hash : Type _) [DecidableEq Hash] where
  cfg        : VotorConfig
  topo       : Lemma28.BlockTopology Hash
  stakeWeight : StakeWeight
  correct    : IsCorrect
  notarVotes : Finset (NotarVote Hash)
  fallbackVotes : Finset (NotarFallbackVote Hash)
  skipVotes  : Finset SkipVote
  finalized  : Slot → Hash → Prop
  head       : Slot
  blockFor   : Slot → Hash
  block_slot :
      ∀ {t}, t ∈ cfg.windowSlots head →
        topo.slotOf (blockFor t) = t
  parent_ready :
      ParentReadyWitness cfg topo stakeWeight notarVotes fallbackVotes skipVotes head
  Δ          : Nat
  afterGST   : Prop
  afterGST_holds : afterGST
  rotor_no_skip :
      ∀ {t}, t ∈ cfg.windowSlots head →
        stakeSum stakeWeight (skipVotesFor t skipVotes) < notarizationThreshold
  certificate_identifies_block :
      ∀ {t b},
        t ∈ cfg.windowSlots head →
        topo.slotOf b = t →
        stakeSum stakeWeight
            (notarVotesFor t b notarVotes ∪
              notarFallbackVotesFor t b fallbackVotes) ≥ notarizationThreshold →
        b = blockFor t
  certificate_finalizes :
      ∀ {t},
        t ∈ cfg.windowSlots head →
        stakeSum stakeWeight
            (notarVotesFor t (blockFor t) notarVotes ∪
              notarFallbackVotesFor t (blockFor t) fallbackVotes) ≥ notarizationThreshold →
        finalized t (blockFor t)

/--
  **Theorem 2 (liveness).**

  Under the assumptions encoded in `WindowContext`, every slot of the leader
  window `WINDOWSLOTS(head)` finalizes the block disseminated by the correct
  leader.
-/
theorem liveness_window_blocks_finalized
    (ctx : WindowContext Hash) :
    ∀ {t}, t ∈ ctx.cfg.windowSlots ctx.head →
      ctx.finalized t (ctx.blockFor t) := by
  classical
  -- After GST the initial ParentReady witness propagates across the window,
  -- yielding timeout witnesses for every slot.
  obtain ⟨_, timeoutWitness⟩ :=
    Lemma42.parentReady_and_timeouts_after_first_timeout
      (cfg := ctx.cfg)
      (topo := ctx.topo)
      (w := ctx.stakeWeight)
      (correct := ctx.correct)
      (Δ := ctx.Δ)
      (afterGST := ctx.afterGST)
      (notarVotes := ctx.notarVotes)
      (fallbackVotes := ctx.fallbackVotes)
      (skipVotes := ctx.skipVotes)
      (h_afterGST := ctx.afterGST_holds)
      (first_node_parent_ready := ctx.parent_ready)
  -- Extract concrete timeout witnesses from the non-emptiness packaging.
  have timeouts {t} (ht : t ∈ ctx.cfg.windowSlots ctx.head) :
      TimeoutStakeWitness ctx.stakeWeight ctx.correct t
        ctx.notarVotes ctx.skipVotes :=
    Classical.choice (timeoutWitness ht)
  -- Timeout witnesses generate notar-fallback certificates or skip certificates.
  have certificates :=
    @Lemma39.window_timeouts_yield_certificates Hash _ ctx.cfg ctx.topo ctx.stakeWeight ctx.correct
      ctx.notarVotes ctx.fallbackVotes ctx.skipVotes ctx.head timeouts
  -- Specialise to each slot of the leader window.
  intro t ht
  have h_outcome := certificates ht
  -- Rotor success precludes skip certificates, so we must be in the notar branch.
  cases h_outcome with
  | inl h_skip =>
      exact absurd h_skip (not_le_of_gt (ctx.rotor_no_skip ht))
  | inr h_cert =>
      obtain ⟨b, h_slot, h_votes⟩ := h_cert
      -- Identify the leader's block for slot `t`.
      have h_block_eq :
          b = ctx.blockFor t :=
        ctx.certificate_identifies_block ht h_slot h_votes
      -- Certificates translate into finalized blocks per the context assumption.
      have h_final :=
        ctx.certificate_finalizes ht
          (by simpa [h_block_eq] using h_votes)
      simpa [h_block_eq] using h_final

end Theorem2
end Alpenglow
