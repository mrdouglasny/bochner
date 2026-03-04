import Minlos.Main
import CertificateSchema

/-!
# Export Certificate: minlos_theorem

## Metadata
- **Declaration**: `minlos_theorem`
- **Role**: Export
- **Status**: Verified
- **Method**: LeanProof
- **Date**: 2026-03-04

## Statement
```
theorem minlos_theorem {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [IsHilbertNuclear E] [SeparableSpace E] [Nonempty E] (Φ : E → ℂ)
    (h_continuous : Continuous Φ) (h_positive_definite : IsPositiveDefinite Φ)
    (h_normalized : Φ 0 = 1) :
    ∃! μ : ProbabilityMeasure (WeakDual ℝ E),
      ∀ f : E, Φ f = ∫ ω, exp (I * (ω f)) ∂μ.toMeasure
```

## Proof Summary
Existence via Kolmogorov extension of finite-dimensional marginals (Bochner's
theorem on each ℝⁿ slice), followed by Sazonov tightness to lift from the
algebraic dual to the topological weak dual. Uniqueness via characteristic
functional injectivity on the projective family.

## Migration Targets
- **mathlib4**: expected as `Minlos.minlos_theorem` or similar

## SHA-256
HASH: 3500270934dac553678d495c2584a3fff71233e0fa9236e445f2b0421e27237e
-/

open MeasureTheory Complex TopologicalSpace in
-- Restate the exported type — compilation fails if the declaration changes
set_option checkBinderAnnotations false in
example {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [IsHilbertNuclear E] [SeparableSpace E] [Nonempty E] (Φ : E → ℂ)
    (h_continuous : Continuous Φ) (h_positive_definite : IsPositiveDefinite Φ)
    (h_normalized : Φ 0 = 1) :
    ∃! μ : ProbabilityMeasure (WeakDual ℝ E),
      ∀ f : E, Φ f = ∫ ω, exp (I * (ω f)) ∂μ.toMeasure :=
  minlos_theorem Φ h_continuous h_positive_definite h_normalized

def minlos_theorem_cert : CertificateInfo where
  axiomName    := "minlos_theorem"
  statement    := "∀ {E} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [IsHilbertNuclear E] [SeparableSpace E] [Nonempty E] (Φ : E → ℂ), Continuous Φ → IsPositiveDefinite Φ → Φ 0 = 1 → ∃! μ : ProbabilityMeasure (WeakDual ℝ E), ∀ f, Φ f = ∫ ω, exp (I * (ω f)) ∂μ.toMeasure"
  role         := .Export
  status       := .Verified
  method       := .LeanProof
  sources      := [{
    file     := some "Minlos/Main.lean",
    leanName := some "minlos_theorem"
  }]
  proofSummary := some "Kolmogorov extension of Bochner marginals + Sazonov tightness"
  date         := "2026-03-04"
  migrationTargets := [{
    repo     := "https://github.com/leanprover-community/mathlib4",
    leanName := some "Minlos.minlos_theorem"
  }]
