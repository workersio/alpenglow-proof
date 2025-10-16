/-
  Lemma 22: Finalization and Fallback Vote Mutual Exclusivity

  Whitepaper: Page 29, Lemma 22

  Statement: If a correct node v cast a finalization vote in slot s, then v did
  not cast a notar-fallback or skip-fallback vote in s.

  Whitepaper proof: A correct node adds ItsOver to its state of slot s in line 21
  of Algorithm 2 when casting a finalization vote. Notar-fallback or skip-fallback
  votes can only be cast if ItsOver not in state[s] in lines 18 and 23 of Algorithm 1
  respectively. Therefore, notar-fallback and skip-fallback votes cannot be cast by
  v in slot s after casting a finalization vote in slot s.

  On the other hand, a correct node adds BadWindow to its state of slot s when
  casting a notar-fallback or skip-fallback vote in slot s. A finalization vote
  can only be cast if BadWindow not in state[s] in line 19 of Algorithm 2. Therefore,
  a finalization vote cannot be cast by v in slot s after casting a notar-fallback
  and skip-fallback vote in slot s.
-/

import Basics
import Algorithm1
import Algorithm2
import Lemma20
import Mathlib.Data.Finset.Basic

open Classical

namespace Alpenglow

namespace Lemma22

variable {Hash : Type _} [DecidableEq Hash]
set_option linter.unusedSectionVars false


/-! ## State Invariant Properties -/

-- Corresponds to Algorithm 2, line 21: tryFinal sets ItsOver after casting finalization vote
theorem tryFinal_sets_itsOver
    (st : VotorState Hash) (s : Slot) (h : Hash)
    (h_final : Broadcast.final s ∈ (tryFinal st s h).2) :
    (tryFinal st s h).1.hasTag s SlotTag.itsOver = true := by
  classical
  set blockNotarized := st.hasTag s (SlotTag.blockNotarized h) with hBlock
  set votedNotar := st.hasTag s (SlotTag.votedNotar h) with hVoted
  set badWindow := st.hasTag s SlotTag.badWindow with hBad
  set alreadyFinal := st.hasTag s SlotTag.itsOver with hOver
  simp [tryFinal] at h_final ⊢
  split_ifs at h_final with hguard
  · simp [hguard]
    exact Lemma20.addTag_has_tag st s SlotTag.itsOver
  · simp at h_final

-- Corresponds to Algorithm 2, line 19: finalization requires BadWindow not in state[s]
theorem tryFinal_requires_no_badWindow
    (st : VotorState Hash) (s : Slot) (h : Hash)
    (h_final : Broadcast.final s ∈ (tryFinal st s h).2) :
    st.hasTag s SlotTag.badWindow = false := by
  classical
  simp only [tryFinal] at h_final
  split_ifs at h_final with hguard
  · cases hbad : st.hasTag s SlotTag.badWindow
    · rfl
    · simp [hbad] at hguard
  · simp at h_final

/-! ## Helper lemmas to show trySkipWindow only broadcasts skip votes -/

private def OnlySkips (logs : List (Broadcast Hash)) : Prop :=
  ∀ x ∈ logs, ∃ slot, x = Broadcast.skip slot

private lemma onlySkips_nil : OnlySkips (Hash := Hash) [] := by
  intro x hx
  cases hx

private lemma onlySkips_append_skip {logs : List (Broadcast Hash)} {slot : Slot}
    (hlogs : OnlySkips (Hash := Hash) logs) :
    OnlySkips (Hash := Hash) (logs ++ [Broadcast.skip slot]) := by
  intro x hx
  have hx' := List.mem_append.mp hx
  cases hx' with
  | inl hIn =>
      exact hlogs x hIn
  | inr hIn =>
      have hx'' : x = Broadcast.skip slot := by
        simpa using List.mem_singleton.mp hIn
      exact ⟨slot, hx''⟩

private lemma trySkipWindow_only_skips
    (cfg : VotorConfig) (slot : Slot) (st : VotorState Hash) :
    OnlySkips (Hash := Hash) (trySkipWindow cfg slot st).2 := by
  classical
  let step :
      (VotorState Hash × List (Broadcast Hash)) → Slot →
      (VotorState Hash × List (Broadcast Hash)) :=
    fun acc currentSlot =>
      let (currState, accLogs) := acc
      if currState.hasTag currentSlot SlotTag.voted then
        acc
      else
        let st1 := currState.addTag currentSlot SlotTag.voted
        let st2 := st1.addTag currentSlot SlotTag.badWindow
        let st3 := st2.clearPending currentSlot
        (st3, accLogs ++ [Broadcast.skip currentSlot])
  have hstep :
    ∀ slots acc,
      OnlySkips (Hash := Hash) acc.2 →
      OnlySkips (Hash := Hash) ((List.foldl step acc slots).2) := by
    intro slots
    induction slots with
    | nil =>
        intro acc hacc
        simpa using hacc
    | cons current rest ih =>
        intro acc hacc
        have hacc' :
            OnlySkips (Hash := Hash) ((step acc current).2) := by
          rcases acc with ⟨currState, accLogs⟩
          have haccLogs : OnlySkips (Hash := Hash) accLogs := hacc
          by_cases h : currState.hasTag current SlotTag.voted
          · simpa [step, h] using haccLogs
          ·
            have happend :
                OnlySkips (Hash := Hash) (accLogs ++ [Broadcast.skip current]) :=
              onlySkips_append_skip (Hash := Hash) (logs := accLogs) (slot := current) haccLogs
            simpa [step, h] using happend
        exact ih (step acc current) hacc'
  have hbase :
      OnlySkips (Hash := Hash) (List.nil : List (Broadcast Hash)) :=
    onlySkips_nil (Hash := Hash)
  have := hstep (cfg.windowSlots slot) (st, []) hbase
  simpa [trySkipWindow, step]

private lemma trySkipWindow_no_notarFallback
    (cfg : VotorConfig) (slot : Slot) (st : VotorState Hash)
    (s : Slot) (hash : Hash) :
    Broadcast.notarFallback s hash ∉ (trySkipWindow cfg slot st).2 := by
  classical
  have h := trySkipWindow_only_skips (cfg := cfg) (slot := slot) (st := st)
  intro hmem
  rcases h _ hmem with ⟨k, hk⟩
  cases hk

private lemma trySkipWindow_no_skipFallback
    (cfg : VotorConfig) (slot : Slot) (st : VotorState Hash) (s : Slot) :
    Broadcast.skipFallback s ∉ (trySkipWindow cfg slot st).2 := by
  classical
  have h := trySkipWindow_only_skips (cfg := cfg) (slot := slot) (st := st)
  intro hmem
  rcases h _ hmem with ⟨k, hk⟩
  cases hk

-- Corresponds to Algorithm 1, line 20: casting notar-fallback sets BadWindow
theorem cast_notar_fallback_sets_badWindow
    (cfg : VotorConfig) (st : VotorState Hash) (s : Slot) (h : Hash)
    (h_fb : Broadcast.notarFallback s h ∈ (handleSafeToNotar cfg st s h).2) :
    (handleSafeToNotar cfg st s h).1.hasTag s SlotTag.badWindow = true := by
  classical
  set result := trySkipWindow cfg s st with hResult
  have h_no_notar : Broadcast.notarFallback s h ∉ result.2 := by
    rw [hResult]
    exact trySkipWindow_no_notarFallback (cfg := cfg) (slot := s) (st := st) (s := s) (hash := h)
  simp only [handleSafeToNotar] at h_fb ⊢
  rw [← hResult] at h_fb ⊢
  cases h_over : result.1.hasTag s SlotTag.itsOver
  · have : (result.1.addTag s SlotTag.badWindow).hasTag s SlotTag.badWindow = true :=
      Lemma20.addTag_has_tag result.1 s SlotTag.badWindow
    simp [h_over] at h_fb ⊢
    exact this
  · simp [h_over] at h_fb
    exact False.elim (h_no_notar h_fb)

-- Corresponds to Algorithm 1, line 25: casting skip-fallback sets BadWindow
theorem cast_skip_fallback_sets_badWindow
    (cfg : VotorConfig) (st : VotorState Hash) (s : Slot)
    (h_fb : Broadcast.skipFallback s ∈ (handleSafeToSkip cfg st s).2) :
    (handleSafeToSkip cfg st s).1.hasTag s SlotTag.badWindow = true := by
  classical
  set result := trySkipWindow cfg s st with hResult
  have h_no_skip : Broadcast.skipFallback s ∉ result.2 := by
    rw [hResult]
    exact trySkipWindow_no_skipFallback (cfg := cfg) (slot := s) (st := st) (s := s)
  simp only [handleSafeToSkip] at h_fb ⊢
  rw [← hResult] at h_fb ⊢
  cases h_over : result.1.hasTag s SlotTag.itsOver
  · have : (result.1.addTag s SlotTag.badWindow).hasTag s SlotTag.badWindow = true :=
      Lemma20.addTag_has_tag result.1 s SlotTag.badWindow
    simp [h_over] at h_fb ⊢
    exact this
  · simp [h_over] at h_fb
    exact False.elim (h_no_skip h_fb)

/-! ## Main Lemma 22 Results -/

-- If finalization vote was cast, BadWindow must not have been set
-- (proving no fallback vote was cast before)
theorem lemma22_part_a_final_implies_no_prior_fallback
    (_ : VotorConfig) (st : VotorState Hash) (s : Slot) (h : Hash)
    (h_final : Broadcast.final s ∈ (tryFinal st s h).2) :
    st.hasTag s SlotTag.badWindow = false :=
  tryFinal_requires_no_badWindow st s h h_final

-- After casting fallback vote, BadWindow is set, blocking future finalization
theorem lemma22_part_d_fallback_blocks_future_final
    (cfg : VotorConfig) (st : VotorState Hash) (s : Slot) (h h' : Hash)
    (h_fallback : Broadcast.notarFallback s h ∈ (handleSafeToNotar cfg st s h).2)
    (h_final_attempt : Broadcast.final s ∈ (tryFinal (handleSafeToNotar cfg st s h).1 s h').2) :
    False := by
  have h_badWindow : (handleSafeToNotar cfg st s h).1.hasTag s SlotTag.badWindow = true :=
    cast_notar_fallback_sets_badWindow cfg st s h h_fallback
  have h_no_badWindow : (handleSafeToNotar cfg st s h).1.hasTag s SlotTag.badWindow = false :=
    tryFinal_requires_no_badWindow (handleSafeToNotar cfg st s h).1 s h' h_final_attempt
  rw [h_badWindow] at h_no_badWindow
  exact Bool.noConfusion h_no_badWindow

/-! ## Combined Statement: Full Lemma 22 -/

-- Finalization and fallback votes are mutually exclusive in the same slot
theorem lemma22_finalization_fallback_mutual_exclusion
    (cfg : VotorConfig) (st : VotorState Hash) (s : Slot) (h h' : Hash) :
    (Broadcast.notarFallback s h ∈ (handleSafeToNotar cfg st s h).2 →
     Broadcast.final s ∉ (tryFinal (handleSafeToNotar cfg st s h).1 s h').2) ∧
    (Broadcast.final s ∈ (tryFinal st s h).2 →
     st.hasTag s SlotTag.badWindow = false) := by
  constructor
  · intro h_fb h_final
    exact lemma22_part_d_fallback_blocks_future_final cfg st s h h' h_fb h_final
  · intro h_final
    exact lemma22_part_a_final_implies_no_prior_fallback cfg st s h h_final


#check lemma22_part_a_final_implies_no_prior_fallback
#check lemma22_part_d_fallback_blocks_future_final
#check lemma22_finalization_fallback_mutual_exclusion

end Lemma22

end Alpenglow
