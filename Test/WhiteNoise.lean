/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# White Noise on Schwartz Space via Minlos' Theorem

This test demonstrates that Minlos' theorem (from `Minlos.Main`) can construct
**white noise** — the canonical Gaussian random generalized function on S'(ℝ) — as a
probability measure on the dual of Schwartz space.

## Bridge with gaussian-field

The `gaussian-field` project (OSforGFF) constructs Gaussian measures on E' = WeakDual ℝ E
via nuclear factorization and iid Gaussian noise (no Minlos). Its `GaussianField.charFun`
proves `∫ ω, exp(i ω(f)) dμ = exp(-½ ⟨Tf, Tf⟩_H)` for a CLM T : E → H. When T is the
inclusion S(ℝ) → L²(ℝ), this gives `exp(-½ ∫ f²)`, equal to our `whiteNoiseCF`.

The two projects use different characterizations of nuclearity:
- **gaussian-field**: `NuclearSpace E` — Pietsch nuclear dominance
  (`∀ p continuous, ∃ nuclear expansion Σ |fₙ(x)| · cₙ ≥ p(x)`)
- **BochnerMinlos**: `IsNuclear E` — same Pietsch condition (in `PietschBridge.lean`)
- **BochnerMinlos**: `IsHilbertNuclear E` — Hilbertian HS embeddings (used by Minlos)

The bridge chain is: gaussian-field proves `DyninMityaginSpace → NuclearSpace` (Pietsch).
Our `IsNuclear` matches `NuclearSpace`, and `isHilbertNuclear_of_nuclear` (proved,
0 axioms) completes the chain to `IsHilbertNuclear`.

The bridge theorem is `white_noise_unique` below: regardless of *how* a probability
measure on S'(ℝ) is constructed — by our Minlos theorem, by gaussian-field's nuclear
factorization, or by any other method — if it has CF `exp(-½‖f‖²_L²)`, it must equal
the measure from `white_noise_measure_exists`.

This uniqueness comes from our *proved* (0-axiom) `minlos_uniqueness`.

## Axioms

Four domain-specific axioms (all provable from Hermite basis theory):
1. `schwartz_isHilbertNuclear` — Schwartz space is Hilbert-nuclear (derivable from
   gaussian-field's `NuclearSpace` proof via our `isHilbertNuclear_of_nuclear` bridge)
2. `schwartz_separableSpace` — Schwartz space is separable (Hermite functions are dense)
3. `schwartzMap_l2Norm_continuous` — L² seminorm continuous on Schwartz topology
4. `whiteNoiseCF_pd` — exp(-½‖f‖²_L²) is positive definite (derivable from
   gaussian-field's `GaussianField.charFun`: CF of a probability measure is PD)
-/

import Minlos.Main
import Bochner.PositiveDefinite
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

open Complex MeasureTheory BigOperators TopologicalSpace

noncomputable section

/-! ## Axioms

These results hold for Schwartz space but are axiomatized here since neither
Mathlib nor this project proves them. The [gaussian-field](https://github.com/YulinGu-Fly/OSforGFF)
project proves that Schwartz space is nuclear (via Hermite–Sobolev norms and the
Dynin-Mityagin characterization) under its `NuclearSpace` class (Pietsch nuclear
dominance). The bridge `isHilbertNuclear_of_nuclear` in `PietschBridge.lean` connects
this to our `IsHilbertNuclear` used by Minlos' theorem. -/

/-- Schwartz space S(ℝ) is separable: the Hermite basis provides a countable dense set. -/
axiom schwartz_separableSpace : SeparableSpace (SchwartzMap ℝ ℝ)

/-- Schwartz space S(ℝ) is nuclear in the Hilbertian sense.
The gaussian-field project proves `DyninMityaginSpace → NuclearSpace` (Pietsch) using
Hermite–Sobolev norms. Our `IsNuclear` matches gaussian-field's `NuclearSpace`, and
`isHilbertNuclear_of_nuclear` (proved, 0 axioms) bridges Pietsch → Hilbertian HS.
The Hermite–Sobolev norms ‖f‖_k² = ∑ (1+n)^{2k} |⟨f,hₙ⟩|² are Hilbertian, generate
the Schwartz topology, and have HS consecutive inclusions since ∑ (1+n)^{-2} < ∞. -/
axiom schwartz_isHilbertNuclear : IsHilbertNuclear (SchwartzMap ℝ ℝ)

/-- The L² seminorm ‖f‖²_L² = ∫ (f x)² dx is continuous on the Schwartz topology.
Follows from rapid decay: ∫ f² dx ≤ (∫ (1+x²)⁻¹ dx) · sup_x (1+x²)|f(x)|², so the
L² norm is dominated by Schwartz seminorms of the form ‖x^α f‖_∞. -/
axiom schwartzMap_l2Norm_continuous :
    Continuous (fun f : SchwartzMap ℝ ℝ => ∫ x : ℝ, (f x) ^ 2)

-- Register Schwartz space instances so `minlos_theorem` can find them.
attribute [instance] schwartz_separableSpace schwartz_isHilbertNuclear

/-! ## White Noise Characteristic Functional -/

/-- The white noise characteristic functional Φ(f) = exp(-½‖f‖²_L²).

When gaussian-field's `GaussianField.measure` is applied with T = inclusion S(ℝ) → L²(ℝ),
the resulting CF `exp(-½ ⟨Tf, Tf⟩_{L²}) = exp(-½ ∫ f²)` is definitionally equal. -/
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
Derivable from gaussian-field's `GaussianField.charFun`: the CF of any probability
measure is PD, and `charFun` with T = inclusion S(ℝ) → L²(ℝ) gives exactly this CF.
Alternatively, provable directly from Schoenberg's theorem (the Gaussian RBF e^{-½‖x‖²}
is PD on any inner product space) pulled back via `isPositiveDefinite_precomp_linear`. -/
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
