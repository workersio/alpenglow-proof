/-
  Theorem 1 (Safety) — Finalization implies ancestry
  ===================================================

  This module assembles the supporting lemmas developed in Lemmas 20–32 to
  mechanize Theorem 1 from the Alpenglow whitepaper:

  > If a correct node finalizes block `b` in slot `s` and any correct node
  > later finalizes block `b'` in slot `s' ≥ s`, then `b'` is a descendant of
  > `b`.

  The proof works with the abstract voting model used across the lemmas.  We
  package the necessary global assumptions (stake distribution, vote sets,
  leader windows, and block topology) into `SafetyContext`, and record the
  invariants that any finalized block must satisfy in `FinalizedWitness`.
  Under these hypotheses the ancestry claim follows by a case split on whether
  the two slots belong to the same leader window (Lemma 31) or not (Lemma 32).
-/

import Basics
import Algorithm2
import Lemma21
import Lemma28
import Lemma29
import Lemma31
import Lemma32

open Classical

namespace Alpenglow
namespace Theorem1_new

open Lemma21 (StakeWeight IsCorrect stakeSum notarizationThreshold notarVotesFor skipVotesFor)
open Lemma29 (NotarFallbackVote notarFallbackVotesFor)
open Lemma31 (SlotExclusive)
open Lemma28.BlockTopology

variable {Hash : Type _} [DecidableEq Hash]

/-- Global safety context bundling all proof-wide assumptions. -/
structure SafetyContext (Hash : Type _) where
  cfg           : VotorConfig
  topo          : Lemma28.BlockTopology Hash
  stakeWeight   : StakeWeight
  correct       : IsCorrect
  byzBound      : Lemma21.ByzantineStakeBound stakeWeight correct
  notarVotes    : Finset (Lemma21.NotarVote Hash)
  fallbackVotes : Finset (NotarFallbackVote Hash)
  skipVotes     : Finset Lemma21.SkipVote

namespace SafetyContext

/-- Witness that a specific block/slot pair has been finalized by a correct node. -/
structure FinalizedWitness {Hash : Type _} (ctx : SafetyContext Hash) where
  block         : Hash
  slot          : Slot
  slot_eq       : ctx.topo.slotOf block = slot
  notarized     :
    stakeSum ctx.stakeWeight (notarVotesFor slot block ctx.notarVotes) ≥ notarizationThreshold
  slotExclusive :
    SlotExclusive ctx.topo ctx.stakeWeight ctx.notarVotes ctx.fallbackVotes slot block
  skipBound     :
    stakeSum ctx.stakeWeight (skipVotesFor slot ctx.skipVotes) < notarizationThreshold

end SafetyContext

open SafetyContext

/--
  **Theorem 1 (Safety).**

  In any safety context, if `bᵢ` finalizes in slot `sᵢ` and `b_k` finalizes in slot
  `s_k ≥ sᵢ`, then `b_k` is a descendant of `bᵢ`.
-/
theorem safety_descendant
    {Hash : Type _} [DecidableEq Hash]
    (ctx : SafetyContext Hash)
    (fi fk : FinalizedWitness ctx)
    (h_order : fi.slot ≤ fk.slot) :
    IsAncestor ctx.topo fi.block fk.block := by
  classical
  -- Detect whether the slots coincide.
  by_cases h_slots : fi.slot = fk.slot
  · -- Same-slot finalizations must reference the identical block.
    have h_slot_bk : ctx.topo.slotOf fk.block = fi.slot := by
      simpa [h_slots] using fk.slot_eq
    have h_ge :
        stakeSum ctx.stakeWeight (notarVotesFor fi.slot fk.block ctx.notarVotes) ≥
          notarizationThreshold := by
      simpa [h_slots] using fk.notarized
    have h_block_eq : fk.block = fi.block := by
      by_contra h_diff
      have h_forbid := fi.slotExclusive h_slot_bk h_diff
      exact (not_lt_of_ge h_ge) h_forbid.1
    have h_refl : IsAncestor ctx.topo fi.block fi.block :=
      IsAncestor.refl (topo := ctx.topo)
    simpa [h_block_eq] using h_refl
  · -- Slots differ; derive the strict inequality needed for case analysis.
    have h_lt : fi.slot < fk.slot := lt_of_le_of_ne h_order h_slots
    by_cases h_window : fi.slot ∈ ctx.cfg.windowSlots fk.slot
    · -- Same leader window: apply Lemma 31.
      have h_cert :
          stakeSum ctx.stakeWeight (notarVotesFor fk.slot fk.block ctx.notarVotes) ≥
            notarizationThreshold ∨
            stakeSum ctx.stakeWeight
                (notarVotesFor fk.slot fk.block ctx.notarVotes ∪
                  notarFallbackVotesFor fk.slot fk.block ctx.fallbackVotes) ≥
              notarizationThreshold :=
        Or.inl fk.notarized
      exact
        Lemma31.descendant_of_finalized_window_block
          (cfg := ctx.cfg)
          (topo := ctx.topo)
          (w := ctx.stakeWeight)
          (correct := ctx.correct)
          (byzBound := ctx.byzBound)
          (notarVotes := ctx.notarVotes)
          (fallbackVotes := ctx.fallbackVotes)
          (b_i := fi.block) (b_k := fk.block)
          (s_i := fi.slot) (s_k := fk.slot)
          fi.slot_eq fk.slot_eq h_window h_order
          fi.notarized fi.slotExclusive h_cert
    · -- Different windows: invoke Lemma 32.
      have h_cert :
          stakeSum ctx.stakeWeight (notarVotesFor fk.slot fk.block ctx.notarVotes) ≥
            notarizationThreshold ∨
            stakeSum ctx.stakeWeight
                (notarVotesFor fk.slot fk.block ctx.notarVotes ∪
                  notarFallbackVotesFor fk.slot fk.block ctx.fallbackVotes) ≥
              notarizationThreshold :=
        Or.inl fk.notarized
      exact
        Lemma32.descendant_across_windows
          (cfg := ctx.cfg)
          (topo := ctx.topo)
          (w := ctx.stakeWeight)
          (correct := ctx.correct)
          (byzBound := ctx.byzBound)
          (notarVotes := ctx.notarVotes)
          (fallbackVotes := ctx.fallbackVotes)
          (skipVotes := ctx.skipVotes)
          fi.slot_eq fk.slot_eq h_window h_lt
          fi.notarized fi.slotExclusive fi.skipBound h_cert

end Theorem1_new
end Alpenglow
