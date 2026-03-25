import Lake
open Lake DSL

package «Sostactic» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.25.0"

@[default_target]
lean_lib Sostactic where

lean_lib Tests where
  srcDir := "tests"
