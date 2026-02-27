# Bochner's Theorem in Lean 4

A formal proof of Bochner's theorem in Lean 4 using Mathlib.

**Bochner's Theorem**: A continuous function φ : V → ℂ on a finite-dimensional real inner product space is positive definite with φ(0) = 1 if and only if it is the characteristic function of a unique probability measure on V.

## Current status

**0 sorries, 2 axioms** (both are standard integration theory facts)

The main theorem `bochner_theorem` compiles and depends only on two well-isolated axioms about double integrals:
1. The double integral of a continuous PD function over S × S has nonneg real part (Riemann sum argument)
2. A Fubini identity relating the Fejér average to an overlap-ratio integral

See [status.md](status.md) for details and proof strategies for eliminating these axioms.

## Proof strategy

The hard direction (PD implies measure) uses **Gaussian regularization**, avoiding the Riesz-Markov-Kakutani theorem:

1. **Fourier positivity**: For φ continuous, integrable, and positive-definite, Re(𝓕φ(ξ)) ≥ 0 for all ξ. Proved via Fejér-averaged double integrals: J_R = vol(B_R)⁻¹ ∬_{B_R × B_R} ψ(x-y) dx dy has Re ≥ 0 (from discrete PD condition) and J_R → ∫ψ (by DCT with overlap-ratio kernel).

2. **Gaussian regularization**: Define φ_ε(x) = φ(x) · exp(-ε‖x‖²). By the Schur product theorem (pointwise product of PD is PD), φ_ε is PD with Gaussian decay, hence L¹.

3. **Measure construction**: Apply step 1 to get 𝓕φ_ε ≥ 0, define dμ_ε = 𝓕φ_ε dλ. Since ∫ 𝓕φ_ε = φ_ε(0) = φ(0) = 1, this is a probability measure. Fourier inversion gives charFun(μ_ε) = φ_ε.

4. **Weak limit**: As ε → 0, charFun(μ_ε) → φ pointwise. Tightness of {μ_ε} follows from continuity of φ at 0 via the standard characteristic function tail bound. Prokhorov's theorem (Mathlib) extracts a weakly convergent subsequence, and the limit measure has charFun = φ.

5. **Uniqueness**: From Mathlib's `Measure.ext_of_charFun`.

## File structure

```
Bochner/
  PositiveDefinite.lean   -- IsPositiveDefinite structure, Schur product theorem
  FejerPD.lean            -- Fourier positivity: Re(𝓕φ) ≥ 0 via Fejér averages
  Bochner.lean            -- Main theorem: Gaussian regularization + Prokhorov
```

| File | Lines | Axioms | Sorries |
|------|-------|--------|---------|
| PositiveDefinite.lean | 201 | 0 | 0 |
| FejerPD.lean | 382 | 2 | 0 |
| Bochner.lean | 1290 | 0 | 0 |
| **Total** | **1873** | **2** | **0** |

## Building

```bash
lake update
lake build
```

Requires Lean v4.29.0-rc2 and Mathlib.

## Key Mathlib dependencies

- `Mathlib.Analysis.Fourier.FourierTransform` — Fourier transform on inner product spaces
- `Mathlib.Analysis.Fourier.Inversion` — Fourier inversion theorem
- `Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform` — Gaussian Fourier transform
- `Mathlib.MeasureTheory.Measure.Prokhorov` — Prokhorov's theorem (tightness ↔ sequential compactness)
- `Mathlib.MeasureTheory.Measure.CharacteristicFunction` — Characteristic functions of measures
- `Mathlib.LinearAlgebra.Matrix.PosDef` — Positive semidefinite matrices (for Schur product)

## References

- Rudin, *Fourier Analysis on Groups*, Theorem 1.4.3
- Folland, *A Course in Abstract Harmonic Analysis*, Chapter 4
- Reed and Simon, *Methods of Modern Mathematical Physics I*, Section IX.9
