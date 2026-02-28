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

private lemma trans_symm_apply_eq' {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (e₁ : α ≃ᵐ β) (e₂ : β ≃ᵐ γ) (z : γ) :
    (e₁.trans e₂).symm z = e₁.symm (e₂.symm z) := rfl

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
  -- Step 2: The CF of ν equals Φ (hence is continuous)
  have hν_proj := marginalProjectiveLimit_isProjectiveLimit Φ h_continuous
    h_positive_definite h_normalized
  -- For each f : E, ∫ ω, exp(I * ω f) ∂ν = Φ f, via the singleton marginal
  have h_cf_eq : ∀ f : E, ∫ ω : E → ℝ, Complex.exp (Complex.I * ↑(ω f)) ∂ν = Φ f := by
    intro f
    -- g is the integrand on the singleton Pi type
    let g : (∀ j : ↥({f} : Finset E), ℝ) → ℂ :=
      fun x => Complex.exp (Complex.I * ↑(x ⟨f, Finset.mem_singleton_self f⟩))
    have hg_cont : Continuous g :=
      Complex.continuous_exp.comp
        (continuous_const.mul (continuous_ofReal.comp (continuous_apply _)))
    -- Step 1: Factor integrand through {f}.restrict and change variables
    change ∫ ω, g (({f} : Finset E).restrict ω) ∂ν = Φ f
    rw [← integral_map (Finset.measurable_restrict ({f} : Finset E)).aemeasurable
      hg_cont.aestronglyMeasurable, hν_proj {f}]
    -- Step 2: Unfold marginalFamily and change variables through equiv
    simp only [marginalFamily]
    rw [integral_map (finsetPiMeasEquiv ({f} : Finset E)).symm.measurable.aemeasurable
      hg_cont.aestronglyMeasurable]
    -- Step 3: Simplify the composed integrand
    set idx := ({f} : Finset E).equivFin ⟨f, Finset.mem_singleton_self f⟩ with idx_def
    have h_simp : ∀ y : EuclideanSpace ℝ (Fin ({f} : Finset E).card),
        g ((finsetPiMeasEquiv ({f} : Finset E)).symm y) =
        Complex.exp (Complex.I * ↑(y idx)) := by
      intro y
      simp only [g, finsetPiMeasEquiv, trans_symm_apply_eq',
        MeasurableEquiv.coe_toLp_symm, finsetReindexEquiv,
        MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk]
      rfl
    simp_rw [h_simp, mul_comm Complex.I _]
    -- Step 4: Connect y idx to inner product ⟪y, single idx 1⟫
    have h_inner : ∀ y : EuclideanSpace ℝ (Fin ({f} : Finset E).card),
        (y idx : ℝ) = @inner ℝ _ _ y (EuclideanSpace.single idx 1) := by
      intro y
      simp [PiLp.inner_apply, EuclideanSpace.single_apply,
        RCLike.inner_apply, conj_trivial]
    simp_rw [h_inner, ← charFun_apply, marginalMeasure_charFun]
    -- Step 5: Simplify marginalCF for singleton
    simp [marginalCF, finsetTestVectors, EuclideanSpace.single_apply, idx_def]
  have h_cf_cont : Continuous (fun f : E => ∫ ω : E → ℝ,
      Complex.exp (Complex.I * ↑(ω f)) ∂ν) := by
    have : (fun f : E => ∫ ω : E → ℝ, Complex.exp (Complex.I * ↑(ω f)) ∂ν) = Φ :=
      funext h_cf_eq
    rw [this]; exact h_continuous
  -- Step 3: Nuclear support concentration — ν concentrates on WeakDual image
  have h_support := nuclear_support_concentration ν_prob h_cf_cont
  -- Step 4: Descend ν to μ on WeakDual ℝ E via measurable embedding
  have h_embed := weakDual_measurableEmbedding E
  -- Step 5: Construct μ on WeakDual ℝ E by pulling back ν through the embedding
  let embed := fun (l : WeakDual ℝ E) (f : E) => (l : E →L[ℝ] ℝ) f
  -- ν concentrates on range embed, so comap gives a probability measure
  have h_prob_comap : IsProbabilityMeasure (ν.comap embed) :=
    h_embed.isProbabilityMeasure_comap h_support
  let μ : ProbabilityMeasure (WeakDual ℝ E) := ⟨ν.comap embed, h_prob_comap⟩
  -- Existence: μ has the right characteristic functional
  refine ⟨μ, ?_, ?_⟩
  · -- Show ∀ f, Φ f = ∫ ω, exp(I * ω f) ∂μ
    intro f'
    rw [← h_cf_eq f']
    -- ∫ ω, exp(I * ω f') ∂ν = ∫ l, exp(I * l f') ∂(ν.comap embed)
    -- via: integral_map + map_comap + restrict_eq_self_of_ae_mem
    show ∫ ω : E → ℝ, Complex.exp (Complex.I * ↑(ω f')) ∂ν =
      ∫ l : WeakDual ℝ E, Complex.exp (Complex.I * ↑(l f')) ∂(ν.comap embed)
    have hG_meas : Measurable (fun ω : E → ℝ => Complex.exp (Complex.I * ↑(ω f'))) :=
      Complex.measurable_exp.comp
        (measurable_const.mul (Complex.measurable_ofReal.comp (measurable_pi_apply f')))
    have h_ae : ∀ᵐ ω ∂ν, ω ∈ Set.range embed := h_support
    rw [← integral_map h_embed.measurable.aemeasurable hG_meas.aestronglyMeasurable,
      h_embed.map_comap, Measure.restrict_eq_self_of_ae_mem h_ae]
  · -- Uniqueness: μ' = μ via projective limit uniqueness + embedding injectivity
    intro μ' hμ'
    -- Step 1: μ.toMeasure.map embed = ν
    have h_ae' : ∀ᵐ ω ∂ν, ω ∈ Set.range embed := h_support
    have h_mu_embed : μ.toMeasure.map embed = ν := by
      show (ν.comap embed).map embed = ν
      rw [h_embed.map_comap, Measure.restrict_eq_self_of_ae_mem h_ae']
    -- Step 2: μ'.toMeasure.map embed = ν (via projective limit uniqueness)
    -- μ'.map embed is a projective limit: for each J, (μ'.map embed).map J.restrict = marginalFamily J
    have h_mu'_proj : IsProjectiveLimit (μ'.toMeasure.map embed)
        (marginalFamily Φ h_continuous h_positive_definite h_normalized) := by
      intro J
      simp only [marginalFamily]
      -- Suffice: on EuclideanSpace, the measures agree
      suffices key : ((μ'.toMeasure.map embed).map (Finset.restrict J)).map
          (finsetPiMeasEquiv J) =
          (marginalMeasure Φ h_continuous h_positive_definite h_normalized J :
            Measure _) by
        have := congr_arg (fun μ => μ.map (finsetPiMeasEquiv J).symm) key
        simp only [Measure.map_map (finsetPiMeasEquiv J).symm.measurable
          (finsetPiMeasEquiv J).measurable,
          (finsetPiMeasEquiv J).symm_comp_self, Measure.map_id] at this
        exact this
      -- Prove by charFun uniqueness on EuclideanSpace
      apply Measure.ext_of_charFun
      ext ξ
      rw [marginalMeasure_charFun]
      -- Compose all maps into one
      rw [Measure.map_map (finsetPiMeasEquiv J).measurable (Finset.measurable_restrict J),
        Measure.map_map ((finsetPiMeasEquiv J).measurable.comp
          (Finset.measurable_restrict J)) h_embed.measurable]
      -- charFun of composed map = integral over μ'
      rw [charFun_apply,
        integral_map
          (((finsetPiMeasEquiv J).measurable.comp (Finset.measurable_restrict J)).comp
            h_embed.measurable).aemeasurable
          (by fun_prop : AEStronglyMeasurable _ _)]
      -- Inner product identity: ⟪(e ∘ J.restrict ∘ embed)(l), ξ⟫ = l(∑ k, ξ k • testVec J k)
      have h_inner_eq : ∀ l : WeakDual ℝ E,
          @inner ℝ _ _ (((⇑(finsetPiMeasEquiv J) ∘ Finset.restrict J) ∘ embed) l) ξ =
          l (∑ k : Fin J.card, (ξ k) • finsetTestVectors J k) := by
        intro l
        simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
          finsetPiMeasEquiv, finsetReindexEquiv, finsetTestVectors,
          MeasurableEquiv.trans_apply, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
          MeasurableEquiv.coe_toLp, Function.comp_apply, Finset.restrict, embed]
        rw [map_sum]
        simp_rw [map_smul, smul_eq_mul]
      -- The goal has embed unfolded; rewrite h_inner_eq with embed unfolded too
      have h_inner_eq' : ∀ l : WeakDual ℝ E,
          @inner ℝ _ _ (((⇑(finsetPiMeasEquiv J) ∘ J.restrict) ∘
            fun (l : WeakDual ℝ E) (f : E) => l f) l) ξ =
          l (∑ k : Fin J.card, (ξ k) • finsetTestVectors J k) := h_inner_eq
      simp_rw [h_inner_eq', mul_comm _ Complex.I]
      -- Apply hμ' to get Φ(∑ ...) = marginalCF Φ (testVec J) ξ
      rw [← hμ']
      rfl
    have h_mu'_embed : μ'.toMeasure.map embed = ν :=
      marginalProjectiveLimit_unique Φ h_continuous h_positive_definite h_normalized
        h_mu'_proj
    -- Step 3: μ.map embed = μ'.map embed, so μ = μ' by MeasurableEmbedding.comap_map
    have h_eq : μ.toMeasure = μ'.toMeasure := by
      rw [← h_embed.comap_map μ.toMeasure, ← h_embed.comap_map μ'.toMeasure,
        h_mu_embed, h_mu'_embed]
    exact Subtype.ext h_eq.symm

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
