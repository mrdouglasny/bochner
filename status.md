# Bochner's Theorem — Status

**Total: 0 sorries, 0 axioms — FULLY PROVED**

## PositiveDefinite.lean — 0 sorries

| # | Lemma | Layer | Difficulty | Status |
|---|-------|-------|------------|--------|
| 1 | `IsPositiveDefinite.mul` | 0 | Medium | proved |

## FejerPD.lean — 0 sorries, 0 axioms

| # | Lemma | Layer | Difficulty | Status | Depends on |
|---|-------|-------|------------|--------|------------|
| F1 | `isPositiveDefinite_exp_inner` | 0 | Medium | proved | — |
| F2 | `pd_double_integral_re_nonneg` | 1 | Hard | proved | — |
| F3 | `overlapRatio_tendsto_one` | 0 | Medium | proved | — |
| F4 | `fejer_avg_eq_integral` | 1 | Hard | proved | — |
| F5 | `pd_integral_re_nonneg` | 1 | Medium | proved | F2, F3, F4 |
| F6 | `pd_l1_fourier_re_nonneg_theorem` | 1 | Medium | proved | F1, F5 |

## Bochner.lean — 0 sorries, 0 axioms

| # | Lemma | Layer | Difficulty | Status | Depends on |
|---|-------|-------|------------|--------|------------|
| 2 | `gaussian_eq_charFun` | 0 | Medium | proved | — |
| 3a | `pd_l1_fourier_re_nonneg` | 1 | Hard | proved (via FejerPD) | F6 |
| 3 | `pd_l1_fourier_nonneg` | 1 | Medium | proved | 3a |
| 4 | `measure_of_pd_l1` | 3 | Medium | proved | 3 |
| 6a | `gaussianRegularize_ft_integrable` | 3 | Medium | proved | 3 |
| 6 | `gaussianRegularize_measures_tight` | 4 | Medium | proved | 4 |
| 7 | `bochner_theorem` (existence) | 4 | Medium | proved | 4, 6, 6a |
| 7b | `bochner_theorem` (uniqueness) | 5 | Easy | proved | Mathlib |

## Key proofs

| Lemma | Technique |
|-------|-----------|
| `pd_double_integral_re_nonneg` | SimpleFunc approximation of id + double DCT + PD sum with real coefficients |
| `fejer_avg_eq_integral` | Fubini + indicator function manipulation + translation invariance |
| `pd_integral_re_nonneg` | Fejér average + overlap ratio → 1 + DCT + ge_of_tendsto' |
| `pd_l1_fourier_re_nonneg_theorem` | Schur product with exp character + pd_integral_re_nonneg |
| `IsPositiveDefinite.mul` | Schur product via PSD kernel matrices + Kronecker/submatrix |
| `gaussian_eq_charFun` | Gaussian measure via withDensity + integral_cexp_neg_mul_sq_norm_add |
| `measure_of_pd_l1` | Fourier scaling + inversion + withDensity construction |
| `gaussianRegularize_ft_integrable` | Fatou's lemma + Parseval bound with Gaussian cutoffs |
| `gaussianRegularize_measures_tight` | `isTightMeasureSet_of_inner_tendsto` + charFun tail bound |
| `bochner_theorem` (existence) | Prokhorov + weak convergence + charFun limit |
| `bochner_theorem` (uniqueness) | Mathlib's `Measure.ext_of_charFun` |

## Notes

- `#print axioms bochner_theorem` shows only: `propext`, `Classical.choice`, `Quot.sound`.
- The proof is structured through FejerPD.lean which proves `Re(𝓕φ(ξ)) ≥ 0` via
  Fejér-averaged double integrals and overlap-ratio kernels.
- `pd_double_integral_re_nonneg` (formerly an axiom) proved via simple function
  approximation: `StronglyMeasurable.approx` for `id : V → V`, double application
  of dominated convergence, and the discrete PD condition for finite sums with
  real (measure) coefficients.
- `fejer_avg_eq_integral` (formerly an axiom) proved via Fubini
  (`integral_integral_swap`) + indicator function manipulation + `dist_comm`.
