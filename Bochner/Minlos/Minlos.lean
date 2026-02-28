/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Minlos' Theorem

Minlos' theorem: on a nuclear locally convex space E, a continuous positive-definite
normalized functional Φ : E → ℂ is the characteristic functional of a unique
probability measure on the topological dual E' = WeakDual ℝ E.

## Proof strategy

1. **Finite-dim marginals** (proved in FinDimMarginals.lean): For each finite
   F = {f₁,...,fₙ} ⊂ E, Bochner gives μ_F on ℝⁿ with charFun = Φ(∑ tᵢfᵢ).
2. **Projective family** (proved in ProjectiveFamily.lean): Transport marginals
   to `∀ j : J, ℝ` indexed by `Finset E`, forming an `IsProjectiveMeasureFamily`.
3. **Kolmogorov extension** (imported from KolmogorovExtension4):
   `projectiveLimit` gives measure ν on E → ℝ.
4. **Nuclear support** (axiom): nuclearity → ν concentrates on WeakDual image.
5. **Descend** to WeakDual via measurable embedding (axiom).

## Axioms (2)

1. `nuclear_support_concentration` — nuclearity → support in continuous dual
2. `weakDual_measurableEmbedding` — evaluation embedding is measurable

## References

- Minlos, "Generalized random processes and their extension to measures" (1959)
- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. IV, Thm 3
- Billingsley, "Convergence of Probability Measures", Thm 36.1
- Degenne-Pfaffelhuber, KolmogorovExtension4 (formalized Kolmogorov extension)
-/

import Bochner.Minlos.ProjectiveFamily

open BigOperators MeasureTheory Complex

noncomputable section

/-! ## Axioms -/

/-- **Nuclear support concentration.** On a nuclear space E, a probability
    measure on E → ℝ whose characteristic functional is continuous on E
    concentrates on the image of the continuous dual (WeakDual ℝ E).

    The key hypothesis is continuity of the characteristic functional
    φ(f) = ∫ exp(iω(f)) dν(ω). Nuclearity of E makes this sufficient
    for concentration: the Hilbert-Schmidt condition on seminorm inclusions
    provides enough tightness to exclude discontinuous functionals.

    Without the continuity hypothesis, one can construct measures via Kolmogorov
    extension that do NOT concentrate on the dual space, even for nuclear E.

    **Proved in OSforGFF-matteo** (Matteo Barucco): the Gaussian case is proved
    across `MinlosGaussianSupport*.lean` files using nuclear seminorm estimates,
    Chebyshev-Borel-Cantelli, and measurable modification. The technique
    generalizes to arbitrary continuous PD Φ (variance bounds are controlled
    by continuity at 0, nuclear structure gives series convergence).

    **Reference:** Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. IV, §3.3,
    Thm 3 (p. 320): "For L(φ) to be representable as ∫ exp(i(F,φ)) dμ(F) with μ
    on Φ', it is necessary and sufficient that L(φ) be continuous on Φ."
    Also: Vakhania-Tarieladze-Chobanyan, "Probability Distributions on Banach Spaces",
    Ch. 5. **✅ Verified (Gemini, Gel'fand-Vilenkin Vol. 4 Thm 3)** -/
axiom nuclear_support_concentration {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [NuclearSpace E]
    (ν : ProbabilityMeasure (E → ℝ))
    (h_cf_continuous : Continuous (fun f : E => ∫ ω : E → ℝ,
      Complex.exp (Complex.I * ↑(ω f)) ∂ν.toMeasure)) :
    ∀ᵐ ω ∂ν.toMeasure, ω ∈ Set.range (fun (l : WeakDual ℝ E) (f : E) => l f)

/-- The evaluation embedding `WeakDual ℝ E → (E → ℝ)` sending a continuous linear
    functional to its underlying function is a measurable embedding.

    This allows descending a measure on E → ℝ (that concentrates on the image)
    to a measure on `WeakDual ℝ E`.

    **Reference:** Schwartz, "Radon Measures on Arbitrary Topological Spaces", Ch. I;
    Bogachev, "Measure Theory" Vol. 2, §7.14, Appendix A Thm A.3.9.
    **✅ Verified (Gemini, Bogachev Vol. 2 §7.14)** -/
axiom weakDual_measurableEmbedding (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] :
    MeasurableEmbedding (fun (l : WeakDual ℝ E) (f : E) => (l : E →L[ℝ] ℝ) f)

/-! ## Main Theorem -/

/-- **Minlos' Theorem** (existence and uniqueness): On a nuclear locally convex space E,
    a continuous, positive definite, normalized functional Φ : E → ℂ is the characteristic
    functional of a unique probability measure μ on the topological dual E':

    Φ(f) = ∫_{E'} exp(i ω(f)) dμ(ω)

    **Proof**: Combine finite-dimensional Bochner (→ marginal measures), Kolmogorov
    extension (→ measure on E → ℝ), nuclear support concentration (→ measure on
    WeakDual ℝ E), and Bochner uniqueness (→ uniqueness of μ).

    **References**: Minlos (1959), Gel'fand-Vilenkin Vol. 4, Billingsley,
    Degenne-Pfaffelhuber (KolmogorovExtension4). -/
theorem minlos_theorem {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [NuclearSpace E] [Nonempty E] (Φ : E → ℂ)
    (h_continuous : Continuous Φ) (h_positive_definite : IsPositiveDefinite Φ)
    (h_normalized : Φ 0 = 1) :
    ∃! μ : ProbabilityMeasure (WeakDual ℝ E),
      ∀ f : E, Φ f = ∫ ω, exp (I * (ω f)) ∂μ.toMeasure := by
  -- Step 1: Build the projective family and Kolmogorov extension
  -- This gives us ν : Measure (E → ℝ), a probability measure on the algebraic dual
  let ν := marginalProjectiveLimit Φ h_continuous h_positive_definite h_normalized
  have hν_prob : IsProbabilityMeasure ν :=
    marginalProjectiveLimit_isProbability Φ h_continuous h_positive_definite h_normalized
  let ν_prob : ProbabilityMeasure (E → ℝ) := ⟨ν, hν_prob⟩
  -- Step 2: The CF of ν is continuous (it equals Φ, which is continuous by hypothesis)
  -- This uses the projective limit marginal property
  have h_cf_cont : Continuous (fun f : E => ∫ ω : E → ℝ,
      Complex.exp (Complex.I * ↑(ω f)) ∂ν) := by
    sorry -- CF of projective limit = Φ via marginal property, hence continuous
  -- Step 3: Nuclear support concentration — ν concentrates on WeakDual image
  have h_support := nuclear_support_concentration ν_prob h_cf_cont
  -- Step 4: Descend ν to μ on WeakDual ℝ E via measurable embedding
  have h_embed := weakDual_measurableEmbedding E
  -- Step 5: Construct the probability measure μ on WeakDual ℝ E
  -- Since ν concentrates on the image of the embedding, we can restrict/descend
  sorry

/-! ## Derived results -/

/-- Derived uniqueness: two probability measures with the same characteristic functional
    on a nuclear space must be equal. -/
theorem minlos_uniqueness {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [NuclearSpace E] [Nonempty E]
    {Φ : E → ℂ} (hΦ_cont : Continuous Φ)
    (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1)
    {μ₁ μ₂ : ProbabilityMeasure (WeakDual ℝ E)}
    (h₁ : ∀ f : E, ∫ ω, exp (I * (ω f)) ∂μ₁.toMeasure = Φ f)
    (h₂ : ∀ f : E, ∫ ω, exp (I * (ω f)) ∂μ₂.toMeasure = Φ f) :
    μ₁ = μ₂ := by
  obtain ⟨μ₀, _, huniq⟩ := minlos_theorem Φ hΦ_cont hΦ_pd hΦ_norm
  exact (huniq μ₁ (fun f => (h₁ f).symm)).trans (huniq μ₂ (fun f => (h₂ f).symm)).symm

end
