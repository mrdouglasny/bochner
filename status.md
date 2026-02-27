# Bochner's Theorem — Status

**Total: 1 sorry, 3 axioms**

## PositiveDefinite.lean — 0 sorries

| # | Lemma | Layer | Difficulty | Status |
|---|-------|-------|------------|--------|
| 1 | `IsPositiveDefinite.mul` | 0 | Medium | proved |

## Bochner.lean — 1 sorry, 3 axioms

| # | Lemma | Layer | Difficulty | Status | Depends on |
|---|-------|-------|------------|--------|------------|
| 2 | `gaussian_eq_charFun` | 0 | Medium | proved | — |
| 3a | `pd_l1_fourier_re_nonneg` | 1 | Hard | axiom | — |
| 3 | `pd_l1_fourier_nonneg` | 1 | Medium | proved | 3a |
| 4 | `measure_of_pd_l1` | 3 | Medium | proved | 3 |
| 5 | `tightness_from_charfun` | 4 | Medium | sorry | — |
| 6a | `gaussianRegularize_ft_integrable` | 3 | Medium | axiom | — |
| 6 | `gaussianRegularize_measures_tight` | 4 | Medium | axiom | 4, 5 |
| 7 | `bochner_theorem` (existence) | 4 | Medium | proved | 4, 6, 6a |
| 7b | `bochner_theorem` (uniqueness) | 5 | Easy | proved | Mathlib |

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
| `pd_l1_fourier_nonneg` | Im=0 proved + Re≥0 from axiom |
| `pd_l1_fourier_real_nonneg` | Derived from `pd_l1_fourier_nonneg` |
| `gaussianRegularize_zero` | φ_ε(0) = φ(0) |
| `IsPositiveDefinite.mul` | Schur product via PSD kernel matrices + Kronecker/submatrix |
| `gaussian_eq_charFun` | Gaussian measure via withDensity + integral_cexp_neg_mul_sq_norm_add |
| `measure_of_pd_l1` | Fourier scaling + inversion + withDensity construction |
| `bochner_theorem` (existence) | Assembly: Prokhorov + weak convergence + charFun limit |
| `bochner_theorem` (uniqueness) | From Mathlib's `Measure.ext_of_charFun` |

## Axioms

| Axiom | Layer | Description |
|-------|-------|-------------|
| `pd_l1_fourier_re_nonneg` | 1 | Re(𝓕φ(ξ)) ≥ 0 for L¹ PD φ. Proof: Cesàro-weighted Riemann sums from discrete PD condition. Ref: Folland §4.2. |
| `gaussianRegularize_ft_integrable` | 3 | 𝓕(φ · g_ε) ∈ L¹. Proof: Parseval-type argument with Gaussian approximate identity shows ∫ 𝓕(φ_ε) = φ_ε(0) = 1. |
| `gaussianRegularize_measures_tight` | 4 | Tightness of {μ_ε}. Proof: `measureReal_abs_inner_gt_le_integral_charFun` (Mathlib) + continuity of φ at 0. |

## Recommended work order

**Next**: Fill the 3 axioms and 1 sorry:
- 3a (`pd_l1_fourier_re_nonneg`): Hardest — requires multi-dimensional Riemann sum convergence
- 6a (`gaussianRegularize_ft_integrable`): Parseval + approximate identity
- 5 (`tightness_from_charfun`): Can use Mathlib's `measureReal_abs_inner_gt_le_integral_charFun`
- 6 (`gaussianRegularize_measures_tight`): Follows from 5 + continuity argument

## Notes

- The main theorem `bochner_theorem` now compiles (modulo axioms/sorry).
  The existence proof uses Prokhorov's theorem (Mathlib) to extract a weakly
  convergent subsequence, then transfers charFun through the weak limit.
- `pd_l1_fourier_nonneg` Im=0: proved via Hermitian symmetry +
  `integral_conj` + `integral_neg_eq_self` (change of variables v → -v).
- `IsPositiveDefinite` is a `structure` with two fields:
  `hermitian` (φ(-x) = conj(φ(x))) and `nonneg` (Re ≥ 0 condition)
