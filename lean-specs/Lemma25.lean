/-
  Lemma 25: Finalization Implies Notarization
  Reference: Alpenglow whitepaper page 30

  Statement: If a block is finalized by a correct node, the block is also notarized.

  Whitepaper proof overview:
  - Fast-finalization: 80% of stake cast notarization votes. Since byzantine nodes
    hold less than 20% of stake, over 60% of correct nodes voted, creating a
    notarization certificate.
  - Slow-finalization: 60% of stake cast finalization votes including correct nodes.
    Correct nodes only cast finalization votes after observing BlockNotarized in
    their state (Algorithm 2 line 19). By Lemma 24, this certificate is for the
    unique notarized block.

  The Lean proof directly follows from Definition 14: both fast and slow finalization
  constructors require a notarization certificate to exist in the pool.
-/

import Basics

namespace Alpenglow
namespace Lemma25

/--
  Lemma 25 from page 30: If a block is finalized, it is also notarized.
  Both fast and slow finalization paths (Definition 14) guarantee a notarization
  certificate exists in the pool.
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
