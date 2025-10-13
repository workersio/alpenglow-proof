/-
  Lemma 25 (Finalization Implies Notarization)
  ============================================

  We mechanize Lemma 25 from the Alpenglow whitepaper (p.30):

  > If a block is finalized by a correct node, the block is also notarized.

  **Whitepaper Proof Sketch:**
  - Fast-finalization requires an 80% notarization certificate on the block,
    which directly implies notarization.
  - Slow-finalization requires both a finalization certificate on the slot and
    a notarization certificate for the unique block in that slot (by Lemma 24),
    so the block must already be notarized.

  **Lean Strategy:**
  Definition 14 (finalization) is captured by `Finalized P h`, which splits into:
  - `.fast`: a fast-finalization certificate (80% notar votes) stored in `Pool`
  - `.slow`: a finalization certificate *and* a notarization certificate

  In both constructors the pool already contains a notarization certificate for `h`,
  so the formal proof simply unwraps the definition.
-/

import Basics

namespace Alpenglow
namespace Lemma25

/--
  **Lemma 25 (Finalization implies Notarization)** from p.30 of the whitepaper.

  Whenever a block header `h` is finalized in the pool `P`, the same pool already
  stores a notarization certificate for `h`. This covers both the fast and slow
  finalization paths spelled out in Definition 14.
-/
theorem finalized_block_is_notarized
    {Hash : Type _}
    (P : Pool Hash) (h : Header Hash)
    (h_finalized : Finalized (Hash:=Hash) P h) :
    Notarized (Hash:=Hash) P h := by
  cases h_finalized with
  | fast h_fast =>
      rcases h_fast with ⟨cert, hCert, _⟩
      exact ⟨cert, hCert⟩
  | slow _ h_notar =>
      exact h_notar

end Lemma25
end Alpenglow
