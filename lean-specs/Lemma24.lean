/-
  Lemma 24 (Uniqueness of Notarization Per Slot)
  ==============================================

  We mechanize Lemma 24 from the Alpenglow whitepaper (p.29):

  > At most one block can be notarized in a given slot.

  **Whitepaper Proof Sketch:**
  Suppose block b is notarized. By Definition 11, notarization requires
  votes from at least 60% of stake. Since byzantine nodes control less
  than 20% of stake (Assumption 1), correct nodes holding more than 40%
  of stake must have voted for b. By Lemma 23, no other block b' ≠ b
  can be notarized in the same slot.

  **Lean Strategy:**
  We reuse the result established in `Lemma23.at_most_one_notarization_per_slot`,
  which already formalizes the above reasoning. Lemma 24 packages this exclusivity
  as an equality statement: if two blocks in the same slot are both notarized,
  they must share the same hash.
-/

import Lemma23

open Classical

namespace Alpenglow
namespace Lemma24

open Lemma21
open Lemma23

variable {Hash : Type _} [DecidableEq Hash]

/-- **Lemma 24 (Uniqueness of Notarization)** from p.29.

    If two blocks `b₁` and `b₂` in slot `s` are both notarized, then they must be equal.

    This is a direct corollary of `Lemma23.at_most_one_notarization_per_slot`. -/
theorem uniqueness_of_notarization
    (w : StakeWeight) (correct : IsCorrect)
    (byzBound : Lemma21.ByzantineStakeBound w correct)
    (s : Slot) (b₁ b₂ : Hash)
    (votes : Finset (NotarVote Hash))
    (h₁ : IsNotarized w s b₁ votes)
    (h₂ : IsNotarized w s b₂ votes) :
    b₁ = b₂ := by
  classical
  by_contra h_ne
  have h_exclusive :=
    at_most_one_notarization_per_slot w correct byzBound s b₁ b₂ votes h₁ h_ne
  exact h_exclusive h₂

end Lemma24
end Alpenglow
