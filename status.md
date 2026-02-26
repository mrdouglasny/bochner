# Bochner's Theorem — Status

**Total: 8 sorries, 0 axioms**

## PositiveDefinite.lean — 2 sorries

| # | Lemma | Layer | Difficulty | Status |
|---|-------|-------|------------|--------|
| 1 | `IsPositiveDefinite.mul` | 0 | Medium | sorry |
| 2 | `isPositiveDefinite_gaussian` | 0 | Medium | sorry |

## Bochner.lean — 6 sorries

| # | Lemma | Layer | Difficulty | Status | Depends on |
|---|-------|-------|------------|--------|------------|
| 3 | `pd_l1_fourier_nonneg` | 1 | Medium | sorry | — |
| 4 | `gaussianRegularize_pd` | 2 | Easy | sorry | 1, 2 |
| 5 | `measure_of_pd_l1` | 3 | Medium | sorry | 3 |
| 6 | `tightness_from_charfun` | 4 | Medium | sorry | — |
| 7 | `gaussianRegularize_measures_tight` | 4 | Medium | sorry | 5, 6 |
| 8 | `bochner_theorem` (existence) | 4 | Medium | sorry | 4, 5, 7 |

## Proved

| Lemma | Notes |
|-------|-------|
| `conj_symm` | From `.hermitian` field |
| `eval_zero_nonneg` | m=1, c₁=1 specialization |
| `eval_zero_real` | Im(φ(0))=0 from Hermitian symmetry |
| `bounded_by_zero` | 2×2 Cauchy-Schwarz |
| `isPositiveDefinite_precomp_linear` | Composition with linear maps |
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

**Then** (Layer 2, depends on Layer 0):
4

**Then** (Layer 3, depends on Layers 1+2):
5

**Then** (Layer 4, depends on Layer 3):
6, 7, 8

## Notes

- Sorry 7 (`gaussianRegularize_measures_tight`) has a **placeholder statement**
  that needs to be corrected — see CLAUDE.md Layer 4 for details
- Sorry 4 (`gaussianRegularize_pd`) has a known **type mismatch** when using
  dot notation — see CLAUDE.md Layer 2 for workaround
- `IsPositiveDefinite` is a `structure` with two fields:
  `hermitian` (φ(-x) = conj(φ(x))) and `nonneg` (Re ≥ 0 condition)
- Sorry 1 (`mul`) needs Schur product theorem — Mathlib lacks `Hadamard.PosSemidef`,
  so must prove directly via spectral decomposition or tensor trick
