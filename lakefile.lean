import Lake
open Lake DSL

package «BochnerMinlos» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "6dc31c12d6ffdc9a63ebddee67264ea348cc06f8"

require kolmogorov_extension4 from git
  "https://github.com/remydegenne/kolmogorov_extension4.git"

@[default_target]
lean_lib «Bochner» where

lean_lib «Minlos» where

lean_lib «Test» where
