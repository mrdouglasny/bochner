import Lake
open Lake DSL

package «BochnerMinlos» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

require kolmogorov_extension4 from git
  "https://github.com/mrdouglasny/kolmogorov_extension4.git" @ "2761d4e"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"

@[default_target]
lean_lib «Bochner» where

lean_lib «Minlos» where

lean_lib «Test» where
