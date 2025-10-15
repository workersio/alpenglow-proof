/-
  Lemma 24: At most one block can be notarized in a given slot.
  (Alpenglow whitepaper, page 29)

  Whitepaper proof:
  Suppose a block b is notarized. Since 60% of stake holders had to cast
  notarization votes for b (Definition 11) and we assume all byzantine nodes
  hold less than 20% of stake, then correct nodes with more than 40% of stake
  cast notarization votes for b. By Lemma 23, no block b' ≠ b in the same
  slot can be notarized.

  This formalization uses Lemma 23's result directly: if two blocks b₁ and b₂
  in the same slot are both notarized, they must be equal.
-/

import Lemma23

open Classical

namespace Alpenglow
namespace Lemma24

open Lemma21
open Lemma23

variable {Hash : Type _} [DecidableEq Hash]

/-- If two blocks b₁ and b₂ in the same slot are both notarized, they must be equal.
    Follows directly from Lemma 23. -/
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
  -- Lemma 23 says if b₁ is notarized and b₁ ≠ b₂, then b₂ cannot be notarized
  have h_exclusive :=
    at_most_one_notarization_per_slot w correct byzBound s b₁ b₂ votes h₁ h_ne
  exact h_exclusive h₂

end Lemma24
end Alpenglow
