# CLAUDE.md

## Project Overview

Formal proof of Bochner's theorem in Lean 4: a continuous positive-definite
function φ : V → ℂ with φ(0) = 1 on a finite-dimensional real inner product
space is the characteristic function of a unique probability measure on V.

The proof uses **Gaussian regularization**, avoiding Riesz-Markov-Kakutani.

## Build

```bash
lake build
```

Package name: `BochnerMinlos`. Depends on Mathlib (fetched automatically by lake).

## Status Tracking

After filling sorries or making changes:
1. Run `lake build` to verify
2. Update sorry counts in `status.md`
3. Commit status updates with code changes

## File Structure

```
Bochner/
  PositiveDefinite.lean          -- IsPositiveDefinite definition + Schur product
  FejerPD.lean                   -- Fejér-averaged PD integrals → 𝓕φ ≥ 0
  Bochner.lean                   -- Main Bochner theorem (existence + uniqueness)
  Sazonov.lean                   -- Sazonov topology via trace-class seminorms
  TestFubini.lean                -- Auxiliary Fubini lemmas
Minlos/
  NuclearSpace.lean              -- Nuclear space definitions (Hilbertian, HS embeddings)
  FinDimMarginals.lean           -- Finite-dimensional marginal measures
  ProjectiveFamily.lean          -- Kolmogorov projective family construction
  SazonovTightness.lean          -- Sazonov CF continuity → tightness
  MinlosConcentration.lean       -- Concentration theorem + Gaussian averaging lemmas
  MeasurableModification.lean    -- Measurable modification of cylindrical measure
  Minlos.lean                    -- Main Minlos theorem
  PietschBridge.lean             -- IsNuclear → IsHilbertNuclear bridge
Test/
  WhiteNoise.lean                -- White noise on Schwartz space via Minlos
```

## Proof Architecture (completed)

0 custom axioms. 0 sorries. All theorems fully proved.

### Bochner's Theorem (0 sorries, 0 axioms)

- **Layer 0** (PositiveDefinite.lean): PD basics + Schur product `IsPositiveDefinite.mul`
- **Layer 1** (FejerPD.lean → Bochner.lean): `pd_l1_fourier_nonneg` via Fejér averaging,
  double integral PD, overlap-ratio kernels
- **Layer 2** (Bochner.lean): Gaussian regularization (PD, integrable, tendsto)
- **Layer 3** (Bochner.lean): `measure_of_pd_l1` via Fourier inversion + withDensity
- **Layer 4** (Bochner.lean): `gaussianRegularize_measures_tight` + `bochner_theorem`
  (Prokhorov + weak convergence + charFun limit)
- **Layer 5** (Bochner.lean): Uniqueness via `Measure.ext_of_charFun`

### Minlos' Theorem (0 sorries, 0 axioms)

- **SazonovTightness.lean**: Sazonov CF continuity --> tightness of marginals
  (Chebyshev + Gaussian averaging + spectral decomposition)
- **ProjectiveFamily.lean**: Kolmogorov projective family from cylindrical measure
- **FinDimMarginals.lean**: Finite-dimensional marginal consistency
- **MeasurableModification.lean**: Measurable modification P of cylindrical paths
  (extensionCLM + Q-linearity + boundedness a.e.)
- **Minlos.lean**: Main theorem (Kolmogorov extension + P pushforward + CF verification)
- **MinlosConcentration.lean**: Concentration theorem `nuclear_cylindrical_concentration`
  (Gel'fand-Vilenkin Vol.4, Ch.IV S3.3), fully proved via dimension-free Gaussian
  averaging, Gram matrix construction, Parseval trace bound, and Chebyshev.

### PietschBridge (0 sorries, 0 axioms)

- **PietschBridge.lean**: `IsNuclear E → IsHilbertNuclear E` via double Pietsch
  construction, hilbertianLift, Bessel inequality, WithSeminorms.congr

## Key Mathlib Lemmas

These are the specific Mathlib results needed (search for these names):

- `fourier_gaussian_innerProductSpace'` — Fourier transform of shifted Gaussian
- `fourierIntegral_continuous` — Riemann-Lebesgue: FT of L¹ function is continuous
- `MeasureTheory.Integrable.fourierInv_fourier_eq` — Fourier inversion
- `Measure.ext_of_charFun` — charFun determines the measure uniquely
- `MeasureTheory.charFun` — characteristic function of a measure
- `tendsto_integral_of_dominated_convergence` — DCT
- `Measure.withDensity` — measure with density f · dμ
- `Matrix.PosSemidef` — positive semidefinite matrices (for Schur product)

## Common Lean 4 Patterns

- `starRingEnd ℂ` is complex conjugation; use `starRingEnd_apply` + `star_trivial`
  for real scalars
- `cexp` is `Complex.exp`; `Complex.exp` may not resolve in newer Mathlib
- `𝓕` is the Fourier transform notation (from `open scoped FourierTransform`)
- `𝓕⁻` is the inverse Fourier transform
- For type mismatches between definitionally-equal terms, use `show ... from ...`
  or `convert` with `congr 1` / `ext`

## References

- Folland, *A Course in Abstract Harmonic Analysis*, §4.2 (main proof reference)
- Rudin, *Fourier Analysis on Groups*, Theorem 1.4.3
- Reed-Simon, *Methods of Modern Mathematical Physics I*, §IX.9
