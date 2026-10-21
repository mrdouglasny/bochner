import Lake
open Lake DSL

package «BochnerMinlos» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

-- Local branch only: points at the sibling port of kolmogorov_extension4 (pin-v4.34.1).
require kolmogorov_extension4 from "../kolmogorov_extension4"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.1"

@[default_target]
lean_lib «Bochner» where

lean_lib «Minlos» where
  globs := #[.submodules `Minlos]

lean_lib «Test» where
  globs := #[.submodules `Test]
