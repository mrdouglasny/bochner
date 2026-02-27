# Bochner's Theorem — Status

**Total: 0 sorries, 1 axiom**

## PositiveDefinite.lean — 0 sorries

| # | Lemma | Layer | Difficulty | Status |
|---|-------|-------|------------|--------|
| 1 | `IsPositiveDefinite.mul` | 0 | Medium | proved |

## Bochner.lean — 0 sorries, 1 axiom

| # | Lemma | Layer | Difficulty | Status | Depends on |
|---|-------|-------|------------|--------|------------|
| 2 | `gaussian_eq_charFun` | 0 | Medium | proved | — |
| 3a | `pd_l1_fourier_re_nonneg` | 1 | Hard | axiom | — |
| 3 | `pd_l1_fourier_nonneg` | 1 | Medium | proved | 3a |
| 4 | `measure_of_pd_l1` | 3 | Medium | proved | 3 |
| 6a | `gaussianRegularize_ft_integrable` | 3 | Medium | proved | 3 |
| 6 | `gaussianRegularize_measures_tight` | 4 | Medium | proved | 4 |
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
| `gaussianRegularize_ft_integrable` | Fatou's lemma + Parseval bound with Gaussian cutoffs |
| `gaussianRegularize_measures_tight` | Tightness via `isTightMeasureSet_of_inner_tendsto` + charFun tail bound |
| `bochner_theorem` (existence) | Assembly: Prokhorov + weak convergence + charFun limit |
| `bochner_theorem` (uniqueness) | From Mathlib's `Measure.ext_of_charFun` |

## Axioms

| Axiom | Layer | Description |
|-------|-------|-------------|
| `pd_l1_fourier_re_nonneg_ax` | 1 | Re(𝓕φ(ξ)) ≥ 0 for continuous L¹ PD φ. Proof: Fejér-weighted Riemann sums from discrete PD condition. Ref: Rudin Thm 1.4.3, Folland §4.2 Lemma 4.8. |

## Recommended work order

**Next**: Eliminate the 1 remaining axiom:
- 3a (`pd_l1_fourier_re_nonneg`): Hardest — requires multi-dimensional Riemann sum convergence

## Notes

- The main theorem `bochner_theorem` now compiles (modulo 1 axiom).
  The existence proof uses Prokhorov's theorem (Mathlib) to extract a weakly
  convergent subsequence, then transfers charFun through the weak limit.
- `gaussianRegularize_ft_integrable` proved via Fatou's lemma: approximate
  ‖𝓕 φ_ε‖ by ‖𝓕 φ_ε * exp(-‖ξ‖²/(n+1))‖, each bounded by (φ 0).re
  via Parseval identity, then take liminf.
- `pd_l1_fourier_nonneg` Im=0: proved via Hermitian symmetry +
  `integral_conj` + `integral_neg_eq_self` (change of variables v → -v).
- `IsPositiveDefinite` is a `structure` with two fields:
  `hermitian` (φ(-x) = conj(φ(x))) and `nonneg` (Re ≥ 0 condition)
- `gaussianRegularize_measures_tight` proved using `isTightMeasureSet_of_inner_tendsto`,
  `measureReal_abs_inner_gt_le_integral_charFun`, and continuity of φ at 0.
  Key helper lemmas: `gaussianRegularize_deviation_bound` (‖1-φ_ε(v)‖ ≤ ‖1-φ(v)‖+‖v‖²)
  and `charFun_measure_inner_bound` (tail bound for individual measures).
