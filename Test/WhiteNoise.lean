/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# White Noise on Schwartz Space via Minlos' Theorem

This test demonstrates that Minlos' theorem (from `Bochner.Minlos.Minlos`) can construct
**white noise** — the canonical Gaussian random generalized function on S'(ℝ) — as a
probability measure on the dual of Schwartz space.

## Comparison with gaussian-field

The `gaussian-field` project constructs the same measure directly:
- `GaussianField.measure T` where `T : S(ℝ) →L[ℝ] L²(ℝ)` is the inclusion
- Both have CF `exp(-½‖f‖²_L²)`: gaussian-field's `GaussianField.charFun T` proves this
- By uniqueness (both theorems prove it), the measures are identical

**Minlos path**: nuclearity → projective limits → measurable modification
**gaussian-field path**: nuclear factorization → product white noise → series limit pushforward

## Axioms

Four domain-specific axioms are used (all provable in gaussian-field):
1. `schwartz_isHilbertNuclear` — Schwartz space is nuclear (Hermite basis proof)
2. `schwartz_separableSpace` — Schwartz space is separable (Hermite basis is countable dense)
3. `schwartzMap_l2Norm_continuous` — L² seminorm continuous on Schwartz topology
4. `whiteNoiseCF_pd` — exp(-½‖f‖²_L²) is positive definite (Gaussian kernel PD)
-/

import Minlos.Minlos
import Bochner.PositiveDefinite
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

open Complex MeasureTheory BigOperators TopologicalSpace

noncomputable section

/-! ## Axioms

These results are proved in the gaussian-field project but axiomatized here
since the two projects do not import each other. -/

/-- Schwartz space S(ℝ) is separable: the Hermite basis provides a countable dense set.
Proved in gaussian-field via `SchwartzMap.instSeparableSpace`. -/
axiom schwartz_separableSpace : SeparableSpace (SchwartzMap ℝ ℝ)

/-- Schwartz space S(ℝ) is nuclear in the Hilbertian sense.
Full proof chain in gaussian-field: Hermite basis → `schwartzRapidDecayEquiv` →
`schwartz_dyninMityaginSpace` → `DyninMityaginSpace.toNuclearSpace` →
`isHilbertNuclear_of_nuclear` (PietschBridge). -/
axiom schwartz_isHilbertNuclear : IsHilbertNuclear (SchwartzMap ℝ ℝ)

/-- The L² seminorm ‖f‖²_L² = ∫ (f x)² dx is continuous on the Schwartz topology.
Dominated by the S_{0,0} Schwartz seminorm. -/
axiom schwartzMap_l2Norm_continuous :
    Continuous (fun f : SchwartzMap ℝ ℝ => ∫ x : ℝ, (f x) ^ 2)

attribute [instance] schwartz_separableSpace schwartz_isHilbertNuclear

/-! ## White Noise Characteristic Functional -/

/-- The white noise characteristic functional Φ(f) = exp(-½‖f‖²_L²).

The covariance is the identity on L²: ⟨Tf, Tg⟩ = ∫ f(x)g(x)dx = ⟨f,g⟩_L².
The associated measure on S'(ℝ) is white noise — the unique probability measure
whose finite-dimensional marginals are standard Gaussians. -/
def whiteNoiseCF : SchwartzMap ℝ ℝ → ℂ :=
  fun f => exp (-(1 / 2 : ℂ) * ↑(∫ x : ℝ, (f x) ^ 2))

/-- Φ(0) = 1: the white noise CF is normalized. -/
theorem whiteNoiseCF_normalized : whiteNoiseCF 0 = 1 := by
  simp only [whiteNoiseCF]
  norm_num [integral_zero]

/-- Φ is continuous: composition of the continuous L² norm, ofReal, scalar multiplication,
and complex exponential. -/
theorem whiteNoiseCF_continuous : Continuous whiteNoiseCF := by
  unfold whiteNoiseCF
  exact continuous_exp.comp
    (continuous_const.mul (continuous_ofReal.comp schwartzMap_l2Norm_continuous))

/-- Φ(f) = exp(-½‖f‖²_L²) is positive definite. This is the Gaussian kernel PD property:
the matrix [exp(-½‖fᵢ-fⱼ‖²_L²)] is positive semidefinite for any finite collection
of Schwartz functions.

**Proof strategy** (implemented in gaussian-field): For f₁,...,fₙ ∈ S(ℝ), their span
in L²(ℝ) is finite-dimensional. On this subspace, exp(-½‖·‖²) is the characteristic
function of a standard Gaussian (Bochner's theorem), hence positive definite.
Use `isPositiveDefinite_precomp_linear` with the projection. -/
axiom whiteNoiseCF_pd : IsPositiveDefinite whiteNoiseCF

/-! ## Main Result -/

/-- **White noise measure exists**: Minlos' theorem gives a unique probability measure μ
on S'(ℝ) = `WeakDual ℝ (SchwartzMap ℝ ℝ)` whose characteristic functional is
`exp(-½‖f‖²_L²)`. This is the **white noise measure**.

The same measure can be constructed directly via `GaussianField.measure` in the
gaussian-field project, using the inclusion `T : S(ℝ) → L²(ℝ)` as the covariance
operator. By uniqueness (proved in both projects), the measures are identical. -/
theorem white_noise_measure_exists :
    ∃! μ : ProbabilityMeasure (WeakDual ℝ (SchwartzMap ℝ ℝ)),
      ∀ f, whiteNoiseCF f = ∫ ω, exp (I * (ω f)) ∂μ.toMeasure :=
  minlos_theorem whiteNoiseCF whiteNoiseCF_continuous whiteNoiseCF_pd whiteNoiseCF_normalized

end
