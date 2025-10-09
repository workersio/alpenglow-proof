import Lake
open Lake DSL

package «alpenglow-specs» where
  -- add package configuration options here

lean_lib «Theorem1» where
  -- add library configuration options here

lean_lib «Lemmas» where
  -- Detailed proofs of Lemmas 20, 23, 24, 27-31

@[default_target]
lean_exe «alpenglow-specs» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
