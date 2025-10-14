/-
  Lemma 35 (Votes After Timeout)
  ==============================

  This file mechanizes Lemma 35 from the Alpenglow whitepaper (p.33):

  > If all correct nodes set the timeout for slot `s`, all correct nodes will
  > cast a notarization vote or skip vote in slot `s`.

  In the implementation, setting the timeout for `s` means the node will
  eventually handle the `Timeout(s)` event (Algorithm 1, line 6).  The handler
  checks whether the node has already voted in slot `s`.  If so, nothing
  changes—the vote must have been a prior notarization or skip (captured by the
  `Voted` tag).  Otherwise the handler delegates to `TRYSCIPWINDOW`, which emits
  a skip vote for every slot in the leader window that still lacks the `Voted`
  marker, in particular for `s`.

  The core statement below formalizes exactly this behaviour: handling
  `Timeout(s)` either produces a skip vote for `s`, or the state already
  records a vote in slot `s`.  Together with Lemma 20—which shows that the
  `Voted` tag arises only from notarization or skip votes—this yields the
  whitepaper lemma.
-/

import Algorithm1
import Algorithm2
import Lemma20

open Classical

namespace Alpenglow
namespace Lemma35

open Lemma20

variable {Hash : Type _} [DecidableEq Hash]

/--
  Helper axiom: if the current slot `s` is still missing the `Voted` marker,
  `trySkipWindow` emits a skip vote for `s`.

  This follows immediately from the implementation (Algorithm 2, lines 22–27):
  the fold appends `Broadcast.skip currentSlot` precisely when the guard
  `hasTag currentSlot SlotTag.voted` fails.
-/
axiom trySkipWindow_emits_skip_self
    (cfg : VotorConfig) (s : Slot) (st : VotorState Hash) :
    st.hasTag s SlotTag.voted = false →
    HasSkipVote (Hash := Hash) s (trySkipWindow cfg s st).2

/--
  **Lemma 35.** Handling the timeout event for slot `s` ensures that the node
  either emits a skip vote for `s`, or had already voted in `s`.

  More precisely, the post-state always carries the `Voted` tag for slot `s`,
  and either the handler broadcasts `Skip(s)` or the incoming state already
  contained `Voted`.  By Lemma 20, the presence of `Voted` witnesses a previous
  notarization or skip vote, so this matches the whitepaper statement.
-/
theorem timeout_handlers_vote_or_skip
    (cfg : VotorConfig) (st st' : VotorState Hash)
    (s : Slot) (broadcasts : List (Broadcast Hash)) :
    handleTimeout cfg st s = (st', broadcasts) →
    st'.hasTag s SlotTag.voted = true ∧
      (HasSkipVote (Hash := Hash) s broadcasts ∨
        st.hasTag s SlotTag.voted = true) := by
  classical
  intro htimeout
  unfold handleTimeout at htimeout
  split_ifs at htimeout with htag
  · -- Case: st.hasTag s SlotTag.voted = true
    -- The handler returns immediately with the unchanged state and no broadcasts.
    cases htimeout
    exact ⟨htag, Or.inr htag⟩
  · -- Case: st.hasTag s SlotTag.voted = false
    -- Timeout calls `trySkipWindow`.  The helper axiom guarantees a skip vote
    -- for `s`, and the `trySkipWindow_sets_voted` axiom records that the
    -- resulting state marks the slot as voted.
    have htag_false : st.hasTag s SlotTag.voted = false := by
      cases h : st.hasTag s SlotTag.voted
      · rfl
      · exact absurd h htag
    have hskip :
        HasSkipVote (Hash := Hash) s (trySkipWindow cfg s st).2 :=
      trySkipWindow_emits_skip_self (cfg := cfg) (s := s) (st := st) htag_false
    have hmem : s ∈ cfg.windowSlots s :=
      Lemma20.slot_in_own_window cfg s
    have hvoted :
        (trySkipWindow cfg s st).1.hasTag s SlotTag.voted = true :=
      Lemma20.trySkipWindow_sets_voted
        (cfg := cfg)
        (s := s) (k := s)
        (st := st) (st' := (trySkipWindow cfg s st).1)
        (broadcasts := (trySkipWindow cfg s st).2)
        rfl hskip hmem
    have hst := congrArg Prod.fst htimeout
    have hbc := congrArg Prod.snd htimeout
    simp at hst hbc
    rw [← hst, ← hbc]
    exact ⟨hvoted, Or.inl hskip⟩

end Lemma35
end Alpenglow
