/-
  Lemma 41: Global Timeout Scheduling

  Whitepaper (page 36):
  All correct nodes will set the timeouts for all slots.

  Proof: Follows by induction from Lemma 33 and Lemma 40.

  The whitepaper proof combines:
  - Lemma 33 (page 33): When a correct node emits ParentReady(s, ...), it sets
    timeouts for all slots in WINDOWSLOTS(s).
  - Lemma 40 (page 35): If all correct nodes set timeouts for WINDOWSLOTS(s),
    they all emit ParentReady(s+, ...) for the next window.

  This creates window-by-window propagation: ParentReady for window n gives
  timeouts for that window, which triggers ParentReady for window n+1, repeating
  indefinitely.

  The mechanization enumerates windows by their first slot and uses induction to
  propagate ParentReady and timeout witnesses across all windows, requiring:
  - Initial ParentReady witness for window 0
  - Each ParentReady witness implies timeout witnesses for that entire window
  - Structural properties ensuring windows cover all slots
-/

import Lemma21
import Lemma28
import Lemma29
import Lemma37
import Lemma40

open Classical

namespace Alpenglow
namespace Lemma41

open Lemma21
open Lemma28
open Lemma29
open Lemma37
open Lemma40

variable {Hash : Type _} [DecidableEq Hash]

/- Timeout witnesses for every slot in the leader window headed by `s`. -/
abbrev WindowTimeouts
    (cfg : VotorConfig) (w : StakeWeight) (correct : IsCorrect)
    (notarVotes : Finset (NotarVote Hash)) (skipVotes : Finset SkipVote)
    (s : Slot) :=
  ∀ {t : Slot}, t ∈ cfg.windowSlots s →
    TimeoutStakeWitness w correct t notarVotes skipVotes

/-
  Lemma 41. If we enumerate leader windows by their first slot through
  windowHead with:
  - each windowHead n being the first slot of its window,
  - the structural bounds required by Lemma 40,
  - every slot belonging to some enumerated window, and
  - every ParentReady witness yielding timeout witnesses for the whole window
    (materializing Lemma 33 for correct nodes),

  then an initial window ParentReady witness implies all slots admit a timeout
  witness.
-/
theorem all_correct_nodes_set_timeouts
    (cfg : VotorConfig) (topo : BlockTopology Hash)
    (w : StakeWeight) (correct : IsCorrect)
    (notarVotes : Finset (NotarVote Hash))
    (fallbackVotes : Finset (NotarFallbackVote Hash))
    (skipVotes : Finset SkipVote)
    (windowHead : ℕ → Slot)
    (window_head_first :
      ∀ n, cfg.windowFirstSlot (windowHead n) = windowHead n)
    (window_head_upper :
      ∀ n {t}, t ∈ cfg.windowSlots (windowHead n) →
        t < windowHead (Nat.succ n))
    (window_head_cover :
      ∀ n {t}, windowHead n ≤ t → t < windowHead (Nat.succ n) →
        t ∈ cfg.windowSlots (windowHead n))
    (window_cover_all :
      ∀ s, ∃ n, s ∈ cfg.windowSlots (windowHead n))
    (base_parent_ready :
      ParentReadyWitness cfg topo w notarVotes fallbackVotes skipVotes
        (windowHead 0))
    (timeouts_from_parent_ready :
      ∀ {s},
        ParentReadyWitness cfg topo w notarVotes fallbackVotes skipVotes s →
          WindowTimeouts cfg w correct notarVotes skipVotes s) :
    ∀ s, Nonempty (TimeoutStakeWitness w correct s notarVotes skipVotes) := by
  classical
  -- Inductive construction: ParentReady for window n implies ParentReady for window n+1.
  have parent_ready_all :
      ∀ n,
        ParentReadyWitness cfg topo w notarVotes fallbackVotes skipVotes
          (windowHead n) := by
    refine Nat.rec ?base ?step
    · exact base_parent_ready
    · intro n ih
      -- ParentReady for window n gives timeout witnesses for all its slots.
      have timeouts :
          ∀ {t}, t ∈ cfg.windowSlots (windowHead n) →
            TimeoutStakeWitness w correct t notarVotes skipVotes :=
        timeouts_from_parent_ready ih
      have window_upper_fun :
          ∀ {t}, t ∈ cfg.windowSlots (windowHead n) →
            t < windowHead (Nat.succ n) :=
        fun {t} ht => window_head_upper n ht
      have window_cover_fun :
          ∀ {t}, cfg.windowFirstSlot (windowHead n) ≤ t →
            t < windowHead (Nat.succ n) →
            t ∈ cfg.windowSlots (windowHead n) :=
        fun {t} h_le h_lt =>
          window_head_cover n
            (by simpa [window_head_first n] using h_le) h_lt
      have ih_first : ParentReadyWitness cfg topo w notarVotes fallbackVotes skipVotes
          (cfg.windowFirstSlot (windowHead n)) := by
        rw [window_head_first n]
        exact ih
      -- Apply Lemma 40: timeouts for window n trigger ParentReady for window n+1.
      exact
        window_timeouts_emit_parent_ready
          (cfg := cfg) (topo := topo)
          (w := w) (correct := correct)
          (notarVotes := notarVotes)
          (fallbackVotes := fallbackVotes)
          (skipVotes := skipVotes)
          (s := windowHead n)
          (sPlus := windowHead (Nat.succ n))
          (window_upper := window_upper_fun)
          (window_cover := window_cover_fun)
          (sPlus_first := window_head_first (Nat.succ n))
          (head_witness := ih_first)
          (timeouts := timeouts)
  have timeouts_all :
      ∀ n,
        WindowTimeouts cfg w correct notarVotes skipVotes (windowHead n) :=
    fun n => timeouts_from_parent_ready (parent_ready_all n)
  -- Every slot belongs to some window, so extract its timeout witness.
  intro s
  obtain ⟨n, h_mem⟩ := window_cover_all s
  exact Nonempty.intro ((timeouts_all n) h_mem)

end Lemma41
end Alpenglow
