/-
  Standstill Recovery (Network Partition Guarantee)
  ================================================

  Section 3.3 of the Alpenglow whitepaper describes the network standstill
  routine: when progress stalls because of a partition or message loss,
  correct nodes rebroadcast the highest finalized slot along with all votes
  they have for higher slots.  Safety relies on the fact that any future
  finalization must extend the last finalized block (Theorem 1), while
  liveness after communication recovers is supplied by the window-level
  progress theorem (Theorem 2).

  This module packages those results to obtain a clean “network partition
  recovery” statement: once a correct node observes the standstill witness,
  every later finalization extends it, and the next leader window eventually
  finalizes its blocks again.
-/

import Theorem1_new
import Theorem2

open Classical

namespace Alpenglow
namespace StandstillRecovery

open Theorem1_new
open Theorem2

section

variable {Hash : Type _} [DecidableEq Hash]

/-- Recovery context bundling the common configuration used by the safety and
    liveness arguments.  The record stores a `WindowContext` for the upcoming
    leader window together with the Byzantine-stake bound required by
    `SafetyContext`. -/
structure RecoveryContext (Hash : Type _) [DecidableEq Hash] where
  window   : WindowContext Hash
  byzBound :
      Lemma21.ByzantineStakeBound
        (window.stakeWeight) (window.correct)

/-- The safety context induced by a recovery context.  Both Theorem 1 and the
    standstill discussion reason about the same configuration data, hence we
    project the shared pieces into `SafetyContext`. -/
def RecoveryContext.safetyContext
    (ctx : RecoveryContext Hash) :
    SafetyContext Hash :=
  { cfg           := ctx.window.cfg
    topo          := ctx.window.topo
    stakeWeight   := ctx.window.stakeWeight
    correct       := ctx.window.correct
    byzBound      := ctx.byzBound
    notarVotes    := ctx.window.notarVotes
    fallbackVotes := ctx.window.fallbackVotes
    skipVotes     := ctx.window.skipVotes }

/-- A standstill witness consists of the highest finalized block known to the
    recovering node together with all invariants required by Theorem 1. -/
structure StandstillWitness (ctx : RecoveryContext Hash) where
  witness :
    SafetyContext.FinalizedWitness ctx.safetyContext

/-- Any later finalization (with slot ≥ the standstill slot) must extend the
    standstill block.  This is the direct application of Theorem 1 in the
    recovery setting. -/
theorem descendant_after_standstill
    (ctx : RecoveryContext Hash)
    (baseline : StandstillWitness ctx)
    {later : SafetyContext.FinalizedWitness ctx.safetyContext}
    (h_order : baseline.witness.slot ≤ later.slot) :
    Lemma28.BlockTopology.IsAncestor ctx.window.topo baseline.witness.block later.block :=
  safety_descendant
    (ctx := ctx.safetyContext)
    (fi := baseline.witness)
    (fk := later)
    h_order

/-- Once communication recovers, the upcoming leader window regains liveness.
    This is precisely Theorem 2 instantiated with the recovery context. -/
theorem resumed_window_progress
    (ctx : RecoveryContext Hash) :
    ∀ {t}, t ∈ ctx.window.cfg.windowSlots ctx.window.head →
      ctx.window.finalized t (ctx.window.blockFor t) :=
  liveness_window_blocks_finalized ctx.window

/-- Network partition recovery guarantee.  A standstill witness anchors the
    chain (every subsequent finalization extends it), and the next leader
    window eventually finalizes its blocks once the network is synchronous
    again. -/
theorem network_partition_recovery
    (ctx : RecoveryContext Hash)
    (baseline : StandstillWitness ctx) :
    (∀ {later : SafetyContext.FinalizedWitness ctx.safetyContext},
        baseline.witness.slot ≤ later.slot →
          Lemma28.BlockTopology.IsAncestor ctx.window.topo baseline.witness.block later.block) ∧
      ∀ {t}, t ∈ ctx.window.cfg.windowSlots ctx.window.head →
        ctx.window.finalized t (ctx.window.blockFor t) := by
  refine ⟨?desc, ?live⟩
  · intro later h_le
    exact descendant_after_standstill ctx baseline h_le
  · intro t ht
    exact resumed_window_progress ctx ht

end

end StandstillRecovery
end Alpenglow

