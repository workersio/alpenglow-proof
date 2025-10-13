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

lean_lib «Algorithm1» where
  -- Votor event loop (Algorithm 1 from whitepaper)

lean_lib «Algorithm2» where
  -- Votor helper functions (Algorithm 2 from whitepaper)

lean_lib «Blockstor» where
  -- Blockstor data structures and operations

@[default_target]
lean_exe «alpenglow-specs» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
