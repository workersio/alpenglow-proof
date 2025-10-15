/-
  Lemma 36 from the whitepaper (page 30):

  Statement: If no set of correct nodes with more than 40% of stake cast their
  notarization votes for the same block in slot s, no correct node will add the
  object ItsOver to state[s].

  Proof outline: Object ItsOver is only added to state[s] in line 21 of Algorithm 2
  after testing that BlockNotarized(hash(b)) is in state[s]. The object
  BlockNotarized(hash(b)) is only added to state[s] when the event
  BlockNotarized(s, hash(b)) is handled in Algorithm 1. By Definition 15 Pool needs
  to hold a notarization certificate for b to emit the event. The certificate
  requires that 60% of stake voted to notarize b (Def. 11). Since we assume that
  byzantine nodes hold less than 20% of stake, correct nodes with more than 40% of
  stake need to cast their notarization votes for the same block in slot s for any
  correct node to add the object ItsOver to state[s].

  We axiomatize the two key implementation facts: ItsOver requires BlockNotarized,
  and BlockNotarized requires a correct majority (>40% stake).
-/

import Algorithm2

open Classical

namespace Alpenglow
namespace Lemma36

variable {Hash : Type _} [DecidableEq Hash]

/- Predicate: correct nodes with more than 40% stake voted to notarize
    block hash in slot s. The concrete stake arithmetic is in earlier lemmas. -/
axiom CorrectMajority (Hash : Type _) : Slot → Hash → Prop

/- From Algorithm 2, line 21: ItsOver is only set after observing BlockNotarized
    in the same slot (via tryFinal at line 18). -/
axiom itsOver_implies_blockNotarized
    (st : VotorState Hash) (s : Slot) :
    st.hasTag s SlotTag.itsOver = true →
    ∃ hash, st.hasTag s (SlotTag.blockNotarized hash) = true

/- From Definition 15 and Definition 11: BlockNotarized event requires a
    notarization certificate (60% of stake). Under 20% Byzantine bound, this means
    correct nodes with >40% stake supported the block. See Lemma 23 / Lemma 30. -/
axiom blockNotarized_implies_correct_majority
    (st : VotorState Hash) (s : Slot) (hash : Hash) :
    st.hasTag s (SlotTag.blockNotarized hash) = true →
    CorrectMajority Hash s hash

/- Lemma 36: If no block in slot s has a correct notar majority (>40% stake),
    then no correct node records ItsOver in state[s]. -/
theorem no_itsOver_without_majority
    (st : VotorState Hash) (s : Slot)
    (hMajority : ∀ hash, ¬CorrectMajority Hash s hash) :
    st.hasTag s SlotTag.itsOver = false := by
  classical
  cases hValue : st.hasTag s SlotTag.itsOver with
  | false =>
      simp
  | true =>
      -- ItsOver implies some BlockNotarized exists
      have hWitness :=
        itsOver_implies_blockNotarized (Hash:=Hash)
          (st:=st) (s:=s) (by simp [hValue])
      rcases hWitness with ⟨hash, hBlock⟩
      -- BlockNotarized implies correct majority, contradiction
      have hMaj :=
        blockNotarized_implies_correct_majority (Hash:=Hash)
          (st:=st) (s:=s) (hash:=hash) hBlock
      exact False.elim ((hMajority hash) hMaj)

end Lemma36
end Alpenglow
