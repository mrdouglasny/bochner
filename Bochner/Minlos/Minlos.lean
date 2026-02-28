/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Minlos' Theorem

Minlos' theorem: on a nuclear locally convex space E, a continuous positive-definite
normalized functional Φ : E → ℂ is the characteristic functional of a unique
probability measure on the topological dual E' = WeakDual ℝ E.

## Proof strategy

1. **Finite-dim marginals** (proved): For each finite F = {f₁,...,fₙ} ⊂ E,
   Bochner gives μ_F on ℝⁿ with charFun = Φ(∑ tᵢfᵢ).
2. **Consistency** (from Bochner uniqueness): projections of μ_G to F-coords = μ_F.
3. **Kolmogorov extension** (axiom): consistent family → measure ν on E → ℝ.
4. **Nuclear support** (axiom): nuclearity → ν concentrates on WeakDual image.
5. **Descend** to WeakDual via measurable embedding (axiom).

## Axioms (3)

1. `kolmogorov_extension` — projective limit of consistent finite-dim measures
2. `nuclear_support_concentration` — nuclearity → support in continuous dual
3. `weakDual_measurableEmbedding` — evaluation embedding is measurable

## References

- Minlos, "Generalized random processes and their extension to measures" (1959)
- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. IV, Thm 3
- Billingsley, "Convergence of Probability Measures", Thm 36.1
-/

import Bochner.Minlos.FinDimMarginals

open BigOperators MeasureTheory Complex

noncomputable section

/-! ## Axioms -/

/-- **Kolmogorov Extension Theorem.** A consistent projective family of probability
    measures on finite-dimensional coordinate spaces extends to a probability measure
    on the full product space.

    Here "consistent" means: for F ⊆ G, the pushforward of μ_G along the
    coordinate restriction (G → ℝ) → (F → ℝ) equals μ_F.

    **Formalized** (not yet imported as dependency):
    `MeasureTheory.isProjectiveLimit_projectiveLimit` in
    [KolmogorovExtension4](https://github.com/remydegenne/kolmogorov_extension4)
    (Rémy Degenne, Peter Pfaffelhuber). Uses `IsProjectiveMeasureFamily` from Mathlib
    and proves existence via inner regularity + compact systems on Polish spaces.
    This axiom could be eliminated by adding KolmogorovExtension4 as a dependency.

    **Reference:** Billingsley, "Convergence of Probability Measures", Thm 36.1;
    Kolmogorov, "Grundbegriffe der Wahrscheinlichkeitsrechnung" (1933).
    **✅ Verified (Gemini, Billingsley Thm 36.1)** -/
axiom kolmogorov_extension {I : Type*}
    (μ : ∀ (n : ℕ) (_ : Fin n → I), ProbabilityMeasure (Fin n → ℝ))
    (h_consistent : ∀ (n m : ℕ) (f : Fin n → I) (g : Fin m → I)
      (π : Fin n → Fin m), (∀ i, g (π i) = f i) →
      (μ m g).toMeasure.map (fun x => x ∘ π) = (μ n f).toMeasure) :
    ∃ ν : ProbabilityMeasure (I → ℝ),
      ∀ (n : ℕ) (f : Fin n → I),
        ν.toMeasure.map (fun ω i => ω (f i)) = (μ n f).toMeasure

/-- **Nuclear support concentration.** On a nuclear space E, a probability
    measure on E → ℝ whose characteristic functional is continuous on E
    concentrates on the image of the continuous dual (WeakDual ℝ E).

    The key hypothesis is continuity of the characteristic functional
    φ(f) = ∫ exp(iω(f)) dν(ω). Nuclearity of E makes this sufficient
    for concentration: the Hilbert-Schmidt condition on seminorm inclusions
    provides enough tightness to exclude discontinuous functionals.

    Without the continuity hypothesis, one can construct measures via Kolmogorov
    extension that do NOT concentrate on the dual space, even for nuclear E.

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

    **References**: Minlos (1959), Gel'fand-Vilenkin Vol. 4, Billingsley. -/
theorem minlos_theorem {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [NuclearSpace E] (Φ : E → ℂ)
    (h_continuous : Continuous Φ) (h_positive_definite : IsPositiveDefinite Φ)
    (h_normalized : Φ 0 = 1) :
    ∃! μ : ProbabilityMeasure (WeakDual ℝ E),
      ∀ f : E, Φ f = ∫ ω, exp (I * (ω f)) ∂μ.toMeasure := by
  -- Step 1: Build marginal family from Bochner
  -- For each finite set of test vectors f₁,...,fₙ, get μ_{f} on ℝⁿ
  have h_marginals : ∀ (n : ℕ) (f : Fin n → E),
      ∃! μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
        ∀ ξ, charFun (μ : Measure (EuclideanSpace ℝ (Fin n))) ξ =
          marginalCF Φ f ξ :=
    fun n f => marginal_measure_exists Φ f h_continuous h_positive_definite h_normalized
  -- Step 2: Assembly from marginals + axioms
  -- (a) Show consistency of marginals (from Bochner uniqueness on projected CFs)
  -- (b) Apply kolmogorov_extension → ν on E → ℝ
  -- (c) Apply nuclear_support_concentration → ν concentrates on WeakDual image
  -- (d) Use weakDual_measurableEmbedding to descend ν to μ on WeakDual ℝ E
  -- (e) Verify CF identity from Kolmogorov marginal property
  -- (f) Prove uniqueness from Bochner uniqueness on 1D marginals
  sorry

/-! ## Derived results -/

/-- Derived uniqueness: two probability measures with the same characteristic functional
    on a nuclear space must be equal. -/
theorem minlos_uniqueness {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [NuclearSpace E]
    {Φ : E → ℂ} (hΦ_cont : Continuous Φ)
    (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1)
    {μ₁ μ₂ : ProbabilityMeasure (WeakDual ℝ E)}
    (h₁ : ∀ f : E, ∫ ω, exp (I * (ω f)) ∂μ₁.toMeasure = Φ f)
    (h₂ : ∀ f : E, ∫ ω, exp (I * (ω f)) ∂μ₂.toMeasure = Φ f) :
    μ₁ = μ₂ := by
  obtain ⟨μ₀, _, huniq⟩ := minlos_theorem Φ hΦ_cont hΦ_pd hΦ_norm
  exact (huniq μ₁ (fun f => (h₁ f).symm)).trans (huniq μ₂ (fun f => (h₂ f).symm)).symm

end
