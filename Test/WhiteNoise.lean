/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# White Noise on Schwartz Space via Minlos' Theorem

This test demonstrates that Minlos' theorem (from `Minlos.Main`) can construct
**white noise** — the canonical Gaussian random generalized function on S'(ℝ) — as a
probability measure on the dual of Schwartz space.

## Bridge with gaussian-field

The `gaussian-field` project (OSforGFF) constructs Gaussian measures on S'(ℝ) via an
axiomatized Minlos theorem using its own `NuclearSpace` class. The CF it produces is
`gaussian_characteristic_functional C f = exp(-½ C(f,f))`, which for the L² covariance
`C(f,f) = ∫ (f x)² dx` is definitionally equal to our `whiteNoiseCF`.

The two nuclear space classes differ only cosmetically:
- **gaussian-field**: `NuclearSpace E` — `∀ n, ∃ m, n < m ∧ HS(p m, p n)`
- **BochnerMinlos**: `IsHilbertNuclear E` — `∀ n, HS(p (n+1), p n)` (consecutive)

Both are axiomatized for `SchwartzMap ℝ ℝ`. The bridge is `white_noise_unique` below:
regardless of *how* a probability measure on S'(ℝ) is constructed — by our proved Minlos
theorem, by gaussian-field's axiomatized Minlos, or by any other method — if it has CF
`exp(-½‖f‖²_L²)`, it must equal the measure from `white_noise_measure_exists`.

This uniqueness comes from our *proved* (0-axiom) `minlos_uniqueness`, not from
gaussian-field's axiomatized version.

## Axioms

Four domain-specific axioms (all provable from Hermite basis theory):
1. `schwartz_isHilbertNuclear` — Schwartz space is nuclear
2. `schwartz_separableSpace` — Schwartz space is separable
3. `schwartzMap_l2Norm_continuous` — L² seminorm continuous on Schwartz topology
4. `whiteNoiseCF_pd` — exp(-½‖f‖²_L²) is positive definite (Gaussian kernel)
-/

import Minlos.Main
import Bochner.PositiveDefinite
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

open Complex MeasureTheory BigOperators TopologicalSpace

noncomputable section

/-! ## Axioms

These results hold for Schwartz space but are axiomatized here since neither
Mathlib nor this project proves them. The gaussian-field project axiomatizes
the same facts under different class names (`NuclearSpace`, `schwartz_nuclear`). -/

/-- Schwartz space S(ℝ) is separable: the Hermite basis provides a countable dense set. -/
axiom schwartz_separableSpace : SeparableSpace (SchwartzMap ℝ ℝ)

/-- Schwartz space S(ℝ) is nuclear in the Hilbertian sense.
Proof: Hermite–Sobolev norms ‖f‖_k² = ∑ (1+n)^{2k} |⟨f,hₙ⟩|² are Hilbertian,
generate the Schwartz topology, and consecutive inclusions are Hilbert-Schmidt
since ∑ (1+n)^{-2} < ∞. -/
axiom schwartz_isHilbertNuclear : IsHilbertNuclear (SchwartzMap ℝ ℝ)

/-- The L² seminorm ‖f‖²_L² = ∫ (f x)² dx is continuous on the Schwartz topology.
Dominated by the S_{0,0} Schwartz seminorm. -/
axiom schwartzMap_l2Norm_continuous :
    Continuous (fun f : SchwartzMap ℝ ℝ => ∫ x : ℝ, (f x) ^ 2)

attribute [instance] schwartz_separableSpace schwartz_isHilbertNuclear

/-! ## White Noise Characteristic Functional -/

/-- The white noise characteristic functional Φ(f) = exp(-½‖f‖²_L²).

This equals gaussian-field's `gaussian_characteristic_functional C` when
`C(f,f) = ∫ (f x)² dx` (the L² covariance form). -/
def whiteNoiseCF : SchwartzMap ℝ ℝ → ℂ :=
  fun f => exp (-(1 / 2 : ℂ) * ↑(∫ x : ℝ, (f x) ^ 2))

/-- Φ(0) = 1: the white noise CF is normalized. -/
theorem whiteNoiseCF_normalized : whiteNoiseCF 0 = 1 := by
  simp only [whiteNoiseCF]
  norm_num [integral_zero]

/-- Φ is continuous: composition of the continuous L² norm, ofReal, and exp. -/
theorem whiteNoiseCF_continuous : Continuous whiteNoiseCF := by
  unfold whiteNoiseCF
  exact continuous_exp.comp
    (continuous_const.mul (continuous_ofReal.comp schwartzMap_l2Norm_continuous))

/-- Φ(f) = exp(-½‖f‖²_L²) is positive definite (Gaussian kernel PD).
Proved in gaussian-field as `gaussian_rbf_pd_innerProduct` composed with
the inclusion S(ℝ) →ₗ[ℝ] L²(ℝ) via `isPositiveDefinite_precomp_linear`. -/
axiom whiteNoiseCF_pd : IsPositiveDefinite whiteNoiseCF

/-! ## Main Results -/

/-- **White noise measure exists and is unique**: Minlos' theorem gives a unique
probability measure μ on S'(ℝ) = `WeakDual ℝ (SchwartzMap ℝ ℝ)` whose
characteristic functional is exp(-½‖f‖²_L²). -/
theorem white_noise_measure_exists :
    ∃! μ : ProbabilityMeasure (WeakDual ℝ (SchwartzMap ℝ ℝ)),
      ∀ f, whiteNoiseCF f = ∫ ω, exp (I * (ω f)) ∂μ.toMeasure :=
  minlos_theorem whiteNoiseCF whiteNoiseCF_continuous whiteNoiseCF_pd whiteNoiseCF_normalized

/-- **Bridge theorem**: Any two probability measures on S'(ℝ) with the white noise
CF are equal. This closes the bridge with gaussian-field: if that project constructs
a measure μ on `WeakDual ℝ (SchwartzMap ℝ ℝ)` and proves
  `∀ f, ∫ ω, exp(i ω(f)) dμ = exp(-½ ∫ (f x)² dx)`
then μ equals our Minlos-constructed measure. The uniqueness comes from our
*proved* `minlos_uniqueness` (0 custom axioms beyond the 4 Schwartz axioms above). -/
theorem white_noise_unique
    (μ₁ μ₂ : ProbabilityMeasure (WeakDual ℝ (SchwartzMap ℝ ℝ)))
    (h₁ : ∀ f, ∫ ω, exp (I * (ω f)) ∂μ₁.toMeasure = whiteNoiseCF f)
    (h₂ : ∀ f, ∫ ω, exp (I * (ω f)) ∂μ₂.toMeasure = whiteNoiseCF f) :
    μ₁ = μ₂ :=
  minlos_uniqueness whiteNoiseCF_continuous whiteNoiseCF_pd whiteNoiseCF_normalized h₁ h₂

end
