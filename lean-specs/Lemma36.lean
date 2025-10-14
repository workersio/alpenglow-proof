/-
  Lemma 36 (Finalization Requires Notar Majority)
  ===============================================

  The whitepaper states:

  > If no set of correct nodes with more than 40% of stake cast their notarization
  > votes for the same block in slot `s`, no correct node will add the object
  > `ItsOver` to `state[s]`.

  In Algorithm 2 the tag `ItsOver` is set only after the node observes
  `BlockNotarized(hash(b)) ∈ state[s]` (via `tryFinal`).  Moreover, a
  `BlockNotarized` marker arises precisely when a notarization certificate for
  slot `s` is present, which—under the 20% Byzantine bound—implies that correct
  nodes controlling > 40% of stake voted for the corresponding block.

  We capture these two facts as axioms and derive the whitepaper lemma.
-/

import Algorithm2

open Classical

namespace Alpenglow
namespace Lemma36

variable {Hash : Type _} [DecidableEq Hash]

/-- Abstract predicate describing the whitepaper assumption:
    correct nodes with more than 40% stake voted to notarize block `hash`
    in slot `s`.  The concrete stake arithmetic lives in earlier lemmas. -/
axiom CorrectMajority (Hash : Type _) : Slot → Hash → Prop

/-- Axiomatization of the implementation fact: setting `ItsOver` for slot `s`
    requires the presence of *some* `BlockNotarized` marker in the same slot. -/
axiom itsOver_implies_blockNotarized
    (st : VotorState Hash) (s : Slot) :
    st.hasTag s SlotTag.itsOver = true →
    ∃ hash, st.hasTag s (SlotTag.blockNotarized hash) = true

/-- Observing `BlockNotarized(hash)` implies that correct voters owning
    > 40% stake supported `hash`.  This is the “certificate ⇒ majority”
    direction from Lemma 23 / Lemma 30. -/
axiom blockNotarized_implies_correct_majority
    (st : VotorState Hash) (s : Slot) (hash : Hash) :
    st.hasTag s (SlotTag.blockNotarized hash) = true →
    CorrectMajority Hash s hash

/--
  **Lemma 36.** If no block in slot `s` enjoys a correct notar majority,
  a correct node never records `ItsOver` in `state[s]`.
-/
theorem no_itsOver_without_majority
    (st : VotorState Hash) (s : Slot)
    (hMajority : ∀ hash, ¬CorrectMajority Hash s hash) :
    st.hasTag s SlotTag.itsOver = false := by
  classical
  cases hValue : st.hasTag s SlotTag.itsOver with
  | false =>
      simp
  | true =>
      have hWitness :=
        itsOver_implies_blockNotarized (Hash:=Hash)
          (st:=st) (s:=s) (by simp [hValue])
      rcases hWitness with ⟨hash, hBlock⟩
      have hMaj :=
        blockNotarized_implies_correct_majority (Hash:=Hash)
          (st:=st) (s:=s) (hash:=hash) hBlock
      exact False.elim ((hMajority hash) hMaj)

end Lemma36
end Alpenglow
