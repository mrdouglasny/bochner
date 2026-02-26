# Bochner's Theorem — Status

**Total: 7 sorries, 0 axioms**

## PositiveDefinite.lean — 1 sorry

| # | Lemma | Layer | Difficulty | Status |
|---|-------|-------|------------|--------|
| 1 | `IsPositiveDefinite.mul` | 0 | Medium | sorry |

## Bochner.lean — 6 sorries

| # | Lemma | Layer | Difficulty | Status | Depends on |
|---|-------|-------|------------|--------|------------|
| 2 | `gaussian_eq_charFun` | 0 | Medium | sorry | — |
| 3 | `pd_l1_fourier_nonneg` | 1 | Medium | sorry | — |
| 4 | `measure_of_pd_l1` | 3 | Medium | sorry | 3 |
| 5 | `tightness_from_charfun` | 4 | Medium | sorry | — |
| 6 | `gaussianRegularize_measures_tight` | 4 | Medium | sorry | 4, 5 |
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
| `bochner_theorem` (uniqueness) | From Mathlib's `Measure.ext_of_charFun` |

## Recommended work order

**Parallel batch 1** (Layer 0, no dependencies):
1, 2

**Then** (Layer 1):
3

**Then** (Layer 3, depends on Layer 1):
4

**Then** (Layer 4, depends on Layer 3):
5, 6, 7

## Notes

- Sorry 6 (`gaussianRegularize_measures_tight`) has a **placeholder statement**
  that needs to be corrected — see CLAUDE.md Layer 4 for details
- Sorry 2 (`gaussian_eq_charFun`) needs constructing a Gaussian measure on V
  with charFun = exp(-ε‖t‖²); approach via product of `gaussianReal` measures
- `IsPositiveDefinite` is a `structure` with two fields:
  `hermitian` (φ(-x) = conj(φ(x))) and `nonneg` (Re ≥ 0 condition)
- Sorry 1 (`mul`) needs Schur product theorem — Mathlib lacks `Hadamard.PosSemidef`,
  so must prove directly via spectral decomposition or tensor trick
