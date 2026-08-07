import Lake
open Lake DSL

package «BochnerMinlos» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

require kolmogorov_extension4 from git
  "https://github.com/RemyDegenne/kolmogorov_extension4.git" @ "7d76e184c3"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0-rc1"

@[default_target]
lean_lib «Bochner» where

lean_lib «Minlos» where

lean_lib «Test» where
