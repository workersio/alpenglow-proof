/-
  Lemma 35 (Votes After Timeout)

  Reference: Alpenglow whitepaper p.33

  Lemma 35: If all correct nodes set the timeout for slot s, all correct nodes
  will cast a notarization vote or skip vote in slot s.

  Whitepaper proof: For any correct node that set the timeout for slot s, the
  handler of event Timeout(s) in line 6 of Algorithm 1 will call the function
  TRYSKIPWINDOW(s), unless Voted is in state[s]. Next, either Voted is not in
  state[s] in line 24 of Algorithm 2 and the node casts a skip vote in slot s,
  or Voted is in state[s]. The object Voted is added to state[s] only when the
  node cast a notarization or skip vote in slot s, and therefore the node must
  have cast either vote.

  Implementation note: Setting the timeout for s means the node handles the
  Timeout(s) event (Algorithm 1, lines 6-8). If the node already voted (Voted
  in state[s]), the handler does nothing. Otherwise it calls TRYSKIPWINDOW,
  which emits a skip vote for every unvoted slot in the leader window
  (Algorithm 2, lines 22-27), including slot s.
-/

import Algorithm1
import Algorithm2
import Lemma20

open Classical

namespace Alpenglow
namespace Lemma35

open Lemma20

variable {Hash : Type _} [DecidableEq Hash]

/-
  Helper axiom: if slot s lacks the Voted marker, trySkipWindow emits a skip
  vote for s.

  From Algorithm 2, lines 22-27: TRYSKIPWINDOW iterates through all slots in
  the window and broadcasts SkipVote(k) when Voted is not in state[k].
-/
axiom trySkipWindow_emits_skip_self
    (cfg : VotorConfig) (s : Slot) (st : VotorState Hash) :
    st.hasTag s SlotTag.voted = false →
    HasSkipVote (Hash := Hash) s (trySkipWindow cfg s st).2

/-
  Lemma 35: Handling Timeout(s) ensures the node either emits a skip vote for
  s, or had already voted in s.

  The post-state always has the Voted tag for slot s, and either the handler
  broadcasts Skip(s) or the pre-state already had Voted. By Lemma 20, Voted
  indicates a prior notarization or skip vote.
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
  · -- Already voted: handler returns unchanged state with no broadcasts
    cases htimeout
    exact ⟨htag, Or.inr htag⟩
  · -- Not yet voted: handler calls trySkipWindow
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
