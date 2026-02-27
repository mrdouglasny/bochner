# Bochner's Theorem — Status

**Total: 3 sorries, 1 axiom**

## PositiveDefinite.lean — 0 sorries

| # | Lemma | Layer | Difficulty | Status |
|---|-------|-------|------------|--------|
| 1 | `IsPositiveDefinite.mul` | 0 | Medium | proved |

## Bochner.lean — 3 sorries, 1 axiom

| # | Lemma | Layer | Difficulty | Status | Depends on |
|---|-------|-------|------------|--------|------------|
| 2 | `gaussian_eq_charFun` | 0 | Medium | proved | — |
| 3 | `pd_l1_fourier_nonneg` | 1 | Hard | sorry (Im=0 proved, Re≥0 remains) | — |
| 4 | `measure_of_pd_l1` | 3 | Medium | proved | 3 |
| 5 | `tightness_from_charfun` | 4 | Medium | sorry | — |
| 6 | `gaussianRegularize_measures_tight` | 4 | Medium | axiom | 4, 5 |
| 7 | `bochner_theorem` (existence) | 4 | Medium | sorry | 4, 6 |

## Proved

| Lemma | Notes |
|-------|-------|
| `conj_symm` | From `.hermitian` field |
| `eval_zero_nonneg` | m=1, c₁=1 specialization |
| `eval_zero_real` | Im(φ(0))=0 from Hermitian symmetry |
| `bounded_by_zero` | 2×2 Cauchy-Schwarz |
| `isPositiveDefinite_precomp_linear` | Composition with linear maps |
| `isPositiveDefinite_charFun` | Forward Bochner: charFun of finite measure is PD |
| `isPositiveDefinite_mul_charFun` | Continuous Schur product: φ · charFun(μ) is PD |
| `isPositiveDefinite_gaussian` | Via `gaussian_eq_charFun` + `isPositiveDefinite_charFun` |
| `gaussianRegularize_pd` | Via `gaussian_eq_charFun` + `isPositiveDefinite_mul_charFun` |
| `gaussianRegularize_integrable` | Bounded × Gaussian decay |
| `gaussianRegularize_tendsto` | exp(-ε‖x‖²) → 1 as ε → 0 |
| `pd_l1_fourier_real_nonneg` | Derived from `pd_l1_fourier_nonneg` |
| `gaussianRegularize_zero` | φ_ε(0) = φ(0) |
| `IsPositiveDefinite.mul` | Schur product via PSD kernel matrices + Kronecker/submatrix |
| `gaussian_eq_charFun` | Gaussian measure via withDensity + integral_cexp_neg_mul_sq_norm_add |
| `measure_of_pd_l1` | Fourier scaling + inversion + withDensity construction |
| `bochner_theorem` (uniqueness) | From Mathlib's `Measure.ext_of_charFun` |

## Recommended work order

**Next** (Layer 1):
3

**Then** (Layer 4, depends on Layers 1+3):
5, 6, 7

## Notes

- Axiom 6 (`gaussianRegularize_measures_tight`) has a **placeholder statement**
  that needs to be corrected — see CLAUDE.md Layer 4 for details
- `pd_l1_fourier_nonneg` Im=0: proved via Hermitian symmetry +
  `integral_conj` + `integral_neg_eq_self` (change of variables v → -v).
  Re≥0 remains: requires Riemann sum convergence from discrete PD condition.
- `IsPositiveDefinite` is a `structure` with two fields:
  `hermitian` (φ(-x) = conj(φ(x))) and `nonneg` (Re ≥ 0 condition)
