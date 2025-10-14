import Lake
open Lake DSL

package «alpenglow-specs» where
  -- add package configuration options here

lean_lib «Basics» where
  -- Basic data structures for Alpenglow protocol

lean_lib «Theorem1» where
  -- add library configuration options here

lean_lib «Lemmas» where
  -- Detailed proofs of Lemmas 20, 23, 24, 27-31

lean_lib «Lemma20» where
  -- Formal proof of Lemma 20 (notarization or skip exclusivity)

lean_lib «Lemma21» where
  -- Formal proof of Lemma 21 (fast-finalization property)

lean_lib «Lemma22» where
  -- Formal proof of Lemma 22 (finalization and fallback mutual exclusivity)

lean_lib «Lemma23» where
  -- Formal proof of Lemma 23 (notarization exclusivity with correct majority)

lean_lib «Lemma24» where
  -- Formal proof of Lemma 24 (uniqueness of notarization per slot)

lean_lib «Lemma25» where
  -- Formal proof of Lemma 25

lean_lib «Lemma26» where
  -- Formal proof of Lemma 26 (slow-finalization property)

lean_lib «Lemma27» where
  -- Formal proof of Lemma 27 (correct notar voter exists)

lean_lib «Lemma28» where
  -- Formal proof of Lemma 28 (correct finalizer voter exists)

lean_lib «Lemma29» where
  -- Formal proof of Lemma 29 (parent support for notar-fallback votes)

lean_lib «Lemma30» where
  -- Formal proof of Lemma 30 (window ancestor coverage with support)

lean_lib «Lemma31» where
  -- Formal proof of Lemma 31

lean_lib «Lemma32» where
  -- Formal proof of Lemma 32 (cross-window finalization ancestry)

lean_lib «Lemma33» where
  -- Formal proof of Lemma 33 (timeout scheduling after ParentReady)

lean_lib «Corollary34» where
  -- Formal proof of Corollary 34 (ParentReady witness for scheduled timeouts)

lean_lib «Lemma35» where
  -- Formal proof of Lemma 35 (votes after timeout)

lean_lib «Lemma36» where
  -- Formal proof of Lemma 36 (finalization requires notar majority)

lean_lib «Lemma37» where
  -- Formal proof of Lemma 37 (timeout skip-or-majority)

lean_lib «Lemma38» where
  -- Formal proof of Lemma 38 (notar-fallback certificates from correct majority)

lean_lib «Lemma39» where
  -- Formal proof of Lemma 39 (window certificates after timeouts)

lean_lib «Algorithm1» where
  -- Votor event loop (Algorithm 1 from whitepaper)

lean_lib «Algorithm2» where
  -- Votor helper functions (Algorithm 2 from whitepaper)

lean_lib «Blockstor» where
  -- Blockstor data structures and operations

lean_lib «Theorem1_new» where
  -- Formal proof of Theorem 1 (safety)

@[default_target]
lean_exe «alpenglow-specs» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
