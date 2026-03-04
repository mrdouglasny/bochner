import Minlos.Main
import CertificateSchema

/-!
# Export Certificate: minlos_uniqueness

## Metadata
- **Declaration**: `minlos_uniqueness`
- **Role**: Export
- **Status**: Verified
- **Method**: LeanProof
- **Date**: 2026-03-04

## Statement
```
theorem minlos_uniqueness {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [IsHilbertNuclear E] [SeparableSpace E] [Nonempty E]
    {Φ : E → ℂ} (hΦ_cont : Continuous Φ)
    (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1)
    {μ₁ μ₂ : ProbabilityMeasure (WeakDual ℝ E)}
    (h₁ : ∀ f : E, ∫ ω, exp (I * (ω f)) ∂μ₁.toMeasure = Φ f)
    (h₂ : ∀ f : E, ∫ ω, exp (I * (ω f)) ∂μ₂.toMeasure = Φ f) :
    μ₁ = μ₂
```

## Proof Summary
Derived from `minlos_theorem` (which proves existence AND uniqueness via `∃!`).
Two measures with the same CF must both equal the unique measure from `minlos_theorem`.

## SHA-256
HASH: 5edcbac6101490370c7469e28321de758f837a2d33111dcefcdb10290b4d92d1
-/

open MeasureTheory Complex TopologicalSpace in
-- Restate the exported type — compilation fails if the declaration changes
set_option checkBinderAnnotations false in
example {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [IsHilbertNuclear E] [SeparableSpace E] [Nonempty E]
    {Φ : E → ℂ} (hΦ_cont : Continuous Φ)
    (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1)
    {μ₁ μ₂ : ProbabilityMeasure (WeakDual ℝ E)}
    (h₁ : ∀ f : E, ∫ ω, exp (I * (ω f)) ∂μ₁.toMeasure = Φ f)
    (h₂ : ∀ f : E, ∫ ω, exp (I * (ω f)) ∂μ₂.toMeasure = Φ f) :
    μ₁ = μ₂ :=
  minlos_uniqueness hΦ_cont hΦ_pd hΦ_norm h₁ h₂

def minlos_uniqueness_cert : CertificateInfo where
  axiomName    := "minlos_uniqueness"
  statement    := "∀ {E} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [IsHilbertNuclear E] [SeparableSpace E] [Nonempty E] {Φ : E → ℂ}, Continuous Φ → IsPositiveDefinite Φ → Φ 0 = 1 → ∀ {μ₁ μ₂}, (∀ f, ∫ ω, exp (I * (ω f)) ∂μ₁.toMeasure = Φ f) → (∀ f, ∫ ω, exp (I * (ω f)) ∂μ₂.toMeasure = Φ f) → μ₁ = μ₂"
  role         := .Export
  status       := .Verified
  method       := .LeanProof
  sources      := [{
    file     := some "Minlos/Main.lean",
    leanName := some "minlos_uniqueness"
  }]
  proofSummary := some "Derived from minlos_theorem (∃! gives uniqueness)"
  date         := "2026-03-04"
