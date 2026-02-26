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

Depends on Mathlib only (fetched automatically by lake).

## Status Tracking

After filling sorries or making changes:
1. Run `lake build` to verify
2. Update sorry counts in `status.md`
3. Commit status updates with code changes

## File Structure

```
Bochner/
  PositiveDefinite.lean   -- IsPositiveDefinite definition + basic properties
  Bochner.lean            -- Main theorem (Phases 1-5)
```

## Proof Architecture and Dependency Order

Fill sorries in this order — each phase depends on the previous ones.

### Layer 0: PD Basics (PositiveDefinite.lean)

These are independent of each other and can be done in parallel:

1. **`eval_zero_nonneg`** — Easy. Specialize PD definition with m=1, x₁=0, c₁=1.
2. **`conj_symm`** — Easy. Use m=2, compare PD condition for (x,0) vs (0,x).
3. **`bounded_by_zero`** — Easy-Medium. Apply PD to the 2×2 matrix
   [φ(0), φ(x); φ(-x), φ(0)] and use Cauchy-Schwarz (det ≥ 0).
4. **`IsPositiveDefinite.mul`** — Medium. Schur product theorem for functions:
   if A_{ij} = c̄ᵢcⱼφ(xᵢ-xⱼ) and B_{ij} = c̄ᵢcⱼψ(xᵢ-xⱼ) are PSD, then
   their Hadamard product is PSD. Use `Matrix.PosSemidef` from Mathlib.
5. **`isPositiveDefinite_gaussian`** — Medium. Show exp(-ε‖x‖²) is PD.
   Strategy: exp(-ε‖x-y‖²) = exp(-ε‖x‖²)exp(-ε‖y‖²)exp(2ε⟨x,y⟩).
   The matrix exp(2ε⟨xᵢ,xⱼ⟩) is PSD (it's a Gram-like matrix via the
   power series of exp). Alternatively, it's the characteristic function of
   a Gaussian measure (forward direction of Bochner, which is easy).

### Layer 1: Phase 1 — Nonneg Fourier Transform (Bochner.lean)

6. **`pd_l1_fourier_nonneg`** — Medium. Key lemma. Strategy:
   - For each ξ₀, define g_a(x) = exp(-a‖x‖²) exp(-i⟨ξ₀,x⟩)
   - PD condition gives: 0 ≤ ∫∫ ḡ_a(x) g_a(y) φ(x-y) dx dy
   - Rewrite as ∫ |ĝ_a(ξ)|² φ̂(ξ) dξ (convolution theorem)
   - ĝ_a is an explicit Gaussian centered at ξ₀ (use
     `fourier_gaussian_innerProductSpace'` from Mathlib)
   - |ĝ_a|² forms a Dirac sequence as a → 0⁺
   - φ̂ is continuous (Riemann-Lebesgue: `fourierIntegral_continuous`)
   - Therefore ∫ |ĝ_a|² φ̂ → φ̂(ξ₀) · (const) ≥ 0

### Layer 2: Phase 2 — Gaussian Regularization (Bochner.lean)

Depends on Layer 0 (mul, gaussian PD).

7. **`gaussianRegularize_pd`** — Easy once `mul` and `isPositiveDefinite_gaussian`
   are done. NOTE: direct `hpd.mul (isPositiveDefinite_gaussian ε hε)` may fail
   due to definitional mismatch between `gaussianRegularize` and the gaussian PD
   lemma. Use `show` or `convert` to align the types, or unfold `gaussianRegularize`.
8. **`gaussianRegularize_integrable`** — Easy-Medium. φ is bounded by φ(0)
   (from `bounded_by_zero`), so ‖φ_ε(x)‖ ≤ φ(0) · exp(-ε‖x‖²). The Gaussian
   is integrable on ℝⁿ. Use `Integrable.of_norm_le` or similar.
9. **`gaussianRegularize_tendsto`** — Easy. exp(-ε‖x‖²) → 1 as ε → 0⁺,
   so φ(x) · exp(-ε‖x‖²) → φ(x). Use `tendsto_const_mul` or explicit limit.

### Layer 3: Phase 3 — Construct Measures (Bochner.lean)

Depends on Layers 1 and 2.

10. **`measure_of_pd_l1`** — Medium. Given φ ∈ L¹ PD with φ(0) = 1 and φ̂ ∈ L¹:
    - φ̂ ≥ 0 from `pd_l1_fourier_nonneg`
    - Define dμ = φ̂ · dλ (Lebesgue measure with density φ̂)
    - Total mass: ∫ φ̂ = φ(0) = 1 (by Fourier inversion at 0)
    - So μ is a probability measure
    - charFun(μ)(ξ) = ∫ exp(i⟨x,ξ⟩) φ̂(x) dx = 𝓕⁻(φ̂)(ξ) = φ(ξ)
    - Use `Measure.withDensity` from Mathlib for the density construction
    - Use `fourierInv_fourier_eq` for the inversion step

### Layer 4: Phase 4 — Tightness and Weak Limit (Bochner.lean)

Depends on Layer 3. This is the most complex layer.

11. **`tightness_from_charfun`** — Medium. Standard Fourier tightness inequality.
    Proof sketch: 1 - Re(charFun(μ)(ξ)) = ∫ (1 - cos⟨x,ξ⟩) dμ(x).
    Average over ξ in a ball: ∫_ball (1 - cos⟨x,ξ⟩) dξ ≥ c·min(1, R²‖x‖²).
    This gives the tail bound.
12. **`gaussianRegularize_measures_tight`** — Medium. NOTE: the current statement
    is a placeholder (`∀ η > 0, ∃ R > 0, ∀ ε > 0, True`). You need to:
    - First construct the measures μ_ε (from `measure_of_pd_l1` applied to φ_ε)
    - State: for all η > 0, ∃ K compact, ∀ ε > 0, μ_ε(Kᶜ) < η
    - Prove using `tightness_from_charfun` + charFun(μ_ε) = φ_ε → φ
    - φ continuous at 0 with φ(0) = 1 gives the uniform bound
13. **`bochner_theorem` existence** — Medium. Assembly:
    - Apply Prokhorov (`Mathlib.MeasureTheory.Measure.Prokhorov`) to get
      weakly convergent subsequence μ_{ε_k} → μ
    - Show charFun(μ)(ξ) = lim charFun(μ_{ε_k})(ξ) = lim φ_{ε_k}(ξ) = φ(ξ)
    - Testing against bounded continuous x ↦ exp(i⟨ξ,x⟩) transfers charFun
      through the weak limit

### Layer 5: Uniqueness (already done)

The uniqueness half of `bochner_theorem` is proved, delegating to
Mathlib's `Measure.ext_of_charFun`.

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
