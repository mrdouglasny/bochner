# Bochner's Theorem — Status

**Total: 13 sorries, 0 axioms**

## PositiveDefinite.lean — 5 sorries

| # | Lemma | Layer | Difficulty | Status |
|---|-------|-------|------------|--------|
| 1 | `eval_zero_nonneg` | 0 | Easy | sorry |
| 2 | `conj_symm` | 0 | Easy | sorry |
| 3 | `bounded_by_zero` | 0 | Easy-Med | sorry |
| 4 | `IsPositiveDefinite.mul` | 0 | Medium | sorry |
| 5 | `isPositiveDefinite_gaussian` | 0 | Medium | sorry |

## Bochner.lean — 8 sorries

| # | Lemma | Layer | Difficulty | Status | Depends on |
|---|-------|-------|------------|--------|------------|
| 6 | `pd_l1_fourier_nonneg` | 1 | Medium | sorry | — |
| 7 | `gaussianRegularize_pd` | 2 | Easy | sorry | 4, 5 |
| 8 | `gaussianRegularize_integrable` | 2 | Easy-Med | sorry | 3 |
| 9 | `gaussianRegularize_tendsto` | 2 | Easy | sorry | — |
| 10 | `measure_of_pd_l1` | 3 | Medium | sorry | 6 |
| 11 | `tightness_from_charfun` | 4 | Medium | sorry | — |
| 12 | `gaussianRegularize_measures_tight` | 4 | Medium | sorry | 10, 11 |
| 13 | `bochner_theorem` (existence) | 4 | Medium | sorry | 7, 8, 9, 10, 12 |

## Proved

| Lemma | Notes |
|-------|-------|
| `isPositiveDefinite_precomp_linear` | Composition with linear maps |
| `pd_l1_fourier_real_nonneg` | Derived from `pd_l1_fourier_nonneg` |
| `gaussianRegularize_zero` | φ_ε(0) = φ(0) |
| `bochner_theorem` (uniqueness) | From Mathlib's `Measure.ext_of_charFun` |

## Recommended work order

**Parallel batch 1** (Layer 0, no dependencies):
1, 2, 3, 4, 5

**Then** (Layer 1):
6

**Then** (Layer 2, depends on Layer 0):
7, 8, 9

**Then** (Layer 3, depends on Layers 1+2):
10

**Then** (Layer 4, depends on Layer 3):
11, 12, 13

## Notes

- Sorry 12 (`gaussianRegularize_measures_tight`) has a **placeholder statement**
  that needs to be corrected — see CLAUDE.md Layer 4 for details
- Sorry 7 (`gaussianRegularize_pd`) has a known **type mismatch** when using
  dot notation — see CLAUDE.md Layer 2 for workaround
