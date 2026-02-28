import Lake
open Lake DSL

package «Bochner» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "9227fd8e4957"

require kolmogorov_extension4 from git
  "https://github.com/remydegenne/kolmogorov_extension4.git"

@[default_target]
lean_lib «Bochner» where
