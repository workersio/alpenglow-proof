/-
  Lemma 33 (Timeout Scheduling after ParentReady)
  ================================================

  We mechanize Lemma 33 from the Alpenglow whitepaper (p.33):

  > If a correct node emits the event ParentReady(s, …), then for every slot k
  > in the leader window beginning with s the node will emit the event Timeout(k).

  In Algorithm 1 (lines 12–15), handling ParentReady first records the event,
  then invokes CHECKPENDINGBLOCKS, and finally calls SETTIMEOUTS.  The helper
  SETTIMEOUTS (Algorithm 2, lines 3–5) iterates over all slots in the leader
  window and programs a timeout for each slot at

      clock() + Δ_timeout + (k - s + 1) · Δ_block          (Definition 17).

  The Lean development below exposes this behaviour through two steps:

  1. A structural lemma about SETTIMEOUTS showing that it updates the timeout
     map exactly on the slots returned by `windowSlots`.
  2. A proof that the ParentReady handler merely adds the tag, runs
     CHECKPENDINGBLOCKS (which leaves the clock untouched), and delegates to
     SETTIMEOUTS, hence inheriting the timeout guarantees.
-/

import Mathlib.Data.List.Basic
import Algorithm1
import Algorithm2

open Classical

namespace Alpenglow
namespace Lemma33

variable {Hash : Type _} [DecidableEq Hash]

/-
  ## List-fold helpers
 -/

/-- Evaluating a `foldl` that repeatedly applies `Function.update` with a fixed
    value formula. -/
private lemma foldl_update_const_apply
    {α β : Type _} [DecidableEq α] (h : α → β) :
    ∀ (l : List α) (f : α → β) (x : α),
      (l.foldl (fun g a => Function.update g a (h a)) f) x =
        if x ∈ l then h x else f x := by
  intro l
  induction l with
  | nil =>
      intro f x
      simp
  | cons a l ih =>
      intro f x
      have hrec := ih (Function.update f a (h a)) x
      by_cases hx : x = a
      · subst hx
        simp [Function.update] at hrec
        simpa [List.foldl, List.mem_cons] using hrec
      · simp [Function.update, hx] at hrec
        simpa [List.mem_cons, hx] using hrec

/-- Eliminating the `VotorState` wrapper to reason about the timeout map. -/
private lemma fold_setTimeout_timeouts
    (cfg : VotorConfig) (first : Slot) (base : Nat)
    (slots : List Slot) (st : VotorState Hash) :
    (slots.foldl
        (fun acc slot =>
          let offset := slot - first
          let timestamp := base + ((offset + 1) * cfg.deltaBlock)
          acc.setTimeout slot timestamp)
        st).timeouts =
      (slots.foldl
        (fun acc slot =>
          let offset := slot - first
          let timestamp := base + ((offset + 1) * cfg.deltaBlock)
          Function.update acc slot (some timestamp))
        st.timeouts) := by
  classical
  induction slots generalizing st with
  | nil =>
      simp [List.foldl]
  | cons slot slots ih =>
      simp only [List.foldl]
      let offset := slot - first
      let timestamp := base + ((offset + 1) * cfg.deltaBlock)
      show (slots.foldl _ (st.setTimeout slot timestamp)).timeouts = _
      rw [ih]
      rfl

/-
  ## Behaviour of `SETTIMEOUTS`
-/

/-- Evaluate the timeout map produced by `SETTIMEOUTS`. -/
private lemma setTimeouts_timeouts_eval
    (cfg : VotorConfig) (st : VotorState Hash)
    (first slot : Slot) :
    let base := st.clock + cfg.deltaTimeout
    (setTimeouts cfg first st).timeouts slot =
      if slot ∈ cfg.windowSlots first then
        some (base + (((slot - first) + 1) * cfg.deltaBlock))
      else
        st.timeouts slot := by
  classical
  let base := st.clock + cfg.deltaTimeout
  have hfold :=
    fold_setTimeout_timeouts (cfg := cfg) (first := first)
      (base := base) (slots := cfg.windowSlots first) (st := st)
  -- Apply setTimeouts definition and use hfold
  have hfold' : (setTimeouts cfg first st).timeouts =
      (cfg.windowSlots first).foldl
        (fun acc slot =>
          Function.update acc slot (some (base + ((slot - first + 1) * cfg.deltaBlock))))
        st.timeouts := by
    simp only [setTimeouts, base]
    exact hfold
  -- Apply the foldl evaluation lemma
  have hupdate :=
    foldl_update_const_apply
      (α := Slot) (β := Option Nat)
      (h := fun s => some (base + ((s - first + 1) * cfg.deltaBlock)))
      (l := cfg.windowSlots first) (f := st.timeouts) (x := slot)
  rw [hfold']
  exact hupdate

/-- `SETTIMEOUTS` programmes a timeout for every slot of the leader window. -/
lemma setTimeouts_timeout_of_mem
    (cfg : VotorConfig) (st : VotorState Hash)
    (first slot : Slot) (h_mem : slot ∈ cfg.windowSlots first) :
    (setTimeouts cfg first st).timeouts slot =
      some (st.clock + cfg.deltaTimeout +
        (((slot - first) + 1) * cfg.deltaBlock)) := by
  classical
  have h :=
    setTimeouts_timeouts_eval (cfg := cfg) (st := st)
      (first := first) (slot := slot)
  simpa [h_mem] using h

/-- `SETTIMEOUTS` does not modify the local clock. -/
lemma setTimeouts_preserves_clock
    (cfg : VotorConfig) (st : VotorState Hash) (first : Slot) :
    (setTimeouts cfg first st).clock = st.clock := by
  classical
  simp only [setTimeouts]
  let base := st.clock + cfg.deltaTimeout
  let slots := cfg.windowSlots first
  suffices ∀ (acc : VotorState Hash), (slots.foldl (fun (acc : VotorState Hash) slot =>
    acc.setTimeout slot (base + ((slot - first + 1) * cfg.deltaBlock))) acc).clock = acc.clock
    by exact this st
  intro acc
  induction slots generalizing acc with
  | nil =>
      simp [List.foldl]
  | cons slot slots ih =>
      simp only [List.foldl]
      rw [ih]
      rfl

/-
  ## Lemma 33
-/

/-- **Lemma 33 (Timeout scheduling after ParentReady).**

    Handling `ParentReady(s, hash)` schedules `Timeout(k)` for every slot `k`
    in the leader window that begins at `s`, with the timestamp prescribed by
    Definition 17. -/
theorem parentReady_schedules_timeouts
    (cfg : VotorConfig) (st st' : VotorState Hash)
    (hash : Hash) (s : Slot) (logs : List (Broadcast Hash)) :
    handleParentReady cfg st s hash = (st', logs) →
    ∀ {k}, k ∈ cfg.windowSlots s →
      st'.timeouts k =
        some (st'.clock + cfg.deltaTimeout +
          (((k - s) + 1) * cfg.deltaBlock)) := by
  classical
  intro h k hk
  -- Unfold the handler structure.
  let st1 := st.addTag s (SlotTag.parentReady hash)
  let result := checkPendingBlocks cfg st1
  let st2 := result.fst
  let bc := result.snd
  have hcb : checkPendingBlocks cfg st1 = (st2, bc) := by
    simp only [st2, bc, result]
  -- First component equality exposes the call to SETTIMEOUTS.
  have hfst := congrArg Prod.fst h
  simp [handleParentReady, st1, hcb] at hfst
  -- Timeouts produced by SETTIMEOUTS.
  have hTimeouts :
      (setTimeouts cfg s st2).timeouts k =
        some (st2.clock + cfg.deltaTimeout +
          (((k - s) + 1) * cfg.deltaBlock)) :=
    setTimeouts_timeout_of_mem (cfg := cfg) (st := st2)
      (first := s) (slot := k) hk
  -- Translate timeout statement to the final state.
  have hTimeouts' :
      st'.timeouts k =
        some (st2.clock + cfg.deltaTimeout +
          (((k - s) + 1) * cfg.deltaBlock)) := by
    simpa [hfst] using hTimeouts
  -- Convert the clock reference.
  have hclock :
      (setTimeouts cfg s st2).clock = st2.clock :=
    setTimeouts_preserves_clock (cfg := cfg) (st := st2) (first := s)
  have hclock' : st'.clock = st2.clock := by
    have := congrArg VotorState.clock hfst
    -- `this : (setTimeouts cfg s st2).clock = st'.clock`
    have := this.symm
    simpa [hclock] using this
  -- Rewrite the timestamp in terms of `st'.clock`.
  simpa [hclock'] using hTimeouts'

end Lemma33
end Alpenglow
