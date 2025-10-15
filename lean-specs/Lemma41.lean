/-
  Lemma 41 (Global Timeout Scheduling)
  ====================================

  Whitepaper statement (p.36):

  > All correct nodes will set the timeouts for all slots.

  The whitepaper derives this property by combining Lemma 33—showing that
  handling `ParentReady` programs the timeouts for the entire leader window—
  with Lemma 40, which establishes that once a window’s timeouts are set,
  correct nodes emit the `ParentReady` event for the subsequent leader window.

  The argument therefore proceeds window-by-window: a `ParentReady` witness for
  the current leader window yields timeout witnesses for every slot in that
  window (Lemma 33).  These witnesses trigger a `ParentReady` witness for the
  next window (Lemma 40), and the process repeats.  Abstracting this reasoning
  into a simple induction across an enumeration of leader windows gives the
  global timeout property stated in Lemma 41.

  The mechanization below captures this pattern.  We assume:

  * an infinite enumeration `windowHead` listing the first slot of each leader
    window, together with the structural facts required by Lemma 40
    (`window_head_upper`/`window_head_cover`);
  * a base `ParentReady` witness for the initial window; and
  * a procedure turning any `ParentReady` witness into timeout witnesses for the
    slots of that window (realized in practice via Lemma 33 together with
    system-level reasoning about correct nodes).

  Strong induction over `windowHead` then supplies timeout witnesses for every
  slot in the schedule.
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

/-- Timeout witnesses for every slot in the leader window headed by `s`. -/
abbrev WindowTimeouts
    (cfg : VotorConfig) (w : StakeWeight) (correct : IsCorrect)
    (notarVotes : Finset (NotarVote Hash)) (skipVotes : Finset SkipVote)
    (s : Slot) :=
  ∀ {t : Slot}, t ∈ cfg.windowSlots s →
    TimeoutStakeWitness w correct t notarVotes skipVotes

/--
  **Lemma 41.** Suppose we enumerate leader windows by their first slot through
  `windowHead`, and assume:

  * each `windowHead n` is indeed the first slot of its window,
  * the enumeration supplies the structural bounds required by Lemma 40,
  * every slot belongs to some enumerated window, and
  * every `ParentReady` witness yields timeout witnesses for the whole window
    (materializing the effect of Lemma 33 for correct nodes).

  If the initial window carries a `ParentReady` witness, then all slots admit a
  timeout witness—i.e. all correct nodes set the timeouts for every slot.
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
  -- Parent-ready witnesses for every window head, obtained inductively via Lemma 40.
  have parent_ready_all :
      ∀ n,
        ParentReadyWitness cfg topo w notarVotes fallbackVotes skipVotes
          (windowHead n) := by
    refine Nat.rec ?base ?step
    · exact base_parent_ready
    · intro n ih
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
  -- Timeout witnesses for every enumerated window follow from the parent-ready witnesses.
  have timeouts_all :
      ∀ n,
        WindowTimeouts cfg w correct notarVotes skipVotes (windowHead n) :=
    fun n => timeouts_from_parent_ready (parent_ready_all n)
  -- Every slot lies in some window; extract its witness from the corresponding window.
  intro s
  obtain ⟨n, h_mem⟩ := window_cover_all s
  exact Nonempty.intro ((timeouts_all n) h_mem)

end Lemma41
end Alpenglow
