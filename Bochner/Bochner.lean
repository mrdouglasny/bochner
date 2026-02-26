/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Bochner.PositiveDefinite
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Bochner's Theorem

Bochner's theorem states that a continuous function φ : V → ℂ on a
finite-dimensional real inner product space is positive definite with φ(0) = 1
if and only if it is the characteristic function of a unique probability
measure on V.

## Proof strategy

We prove the hard direction (PD → measure) via **Gaussian regularization**,
avoiding the Riesz-Markov-Kakutani theorem entirely:

1. **Phase 1** (`pd_l1_fourier_nonneg`): An L¹ positive-definite function has
   a nonneg real Fourier transform. Proved by testing the PD double integral
   against explicit shifted Gaussians g(x) = exp(-a‖x‖² - i⟨ξ₀,x⟩). Since
   |ĝ(ξ)|² forms a Dirac sequence as a → 0, continuity of φ̂ (from
   Riemann-Lebesgue) forces φ̂(ξ₀) ≥ 0 at every point.

2. **Phase 2** (`gaussian_regularization`): Define φ_ε(x) = φ(x) · exp(-ε‖x‖²).
   By Schur (pointwise product of PD is PD), φ_ε is PD. Gaussian decay
   guarantees φ_ε ∈ L¹.

3. **Phase 3** (`measure_of_pd_l1`): Apply Phase 1 to get φ̂_ε ≥ 0, then
   define dμ_ε = φ̂_ε dλ. Since ∫ φ̂_ε = φ_ε(0) = 1, this is a probability
   measure. By Fourier inversion, charFun(μ_ε) = φ_ε.

4. **Phase 4** (`tightness_from_charfun`): As ε → 0, charFun(μ_ε)(x) → φ(x)
   pointwise. Tightness of {μ_ε} follows from the standard bound
   μ({‖x‖ > R}) ≤ C ∫_{‖ξ‖≤δ} (1 - Re(φ̂_ε(ξ))) dξ → 0, using continuity
   of φ at 0. Prokhorov's theorem (in Mathlib) extracts a weakly convergent
   subsequence μ_{ε_k} → μ. Testing against x ↦ exp(i⟨ξ,x⟩) shows
   charFun(μ) = φ.

5. **Phase 5** (`Measure.ext_of_charFun`): Uniqueness is already in Mathlib.

## Main results

- `bochner_theorem`: the full theorem
- `pd_l1_fourier_nonneg`: L¹ PD ⟹ nonneg Fourier transform (Phase 1)

## References

- S. Bochner, "Monotone Funktionen, Stieltjessche Integrale und harmonische
  Analyse", Math. Annalen 108 (1933), 378–410
- W. Rudin, *Fourier Analysis on Groups*, Wiley (1962), Theorem 1.4.3
- G.B. Folland, *A Course in Abstract Harmonic Analysis*, CRC Press (2016), §4.2
-/

open MeasureTheory Complex Filter Topology
open scoped Real InnerProductSpace FourierTransform

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-! ## Phase 1: L¹ positive-definite functions have nonneg Fourier transform

The proof uses explicit shifted Gaussians rather than abstract Plancherel.

Given φ ∈ L¹ with φ positive-definite, we want φ̂(ξ₀) ≥ 0 for each ξ₀.

Test the PD condition with g_a(x) = exp(-a‖x‖²) exp(-i⟨ξ₀,x⟩):
  0 ≤ ∫∫ ḡ_a(x) g_a(y) φ(x-y) dx dy = ∫ |ĝ_a(ξ)|² φ̂(ξ) dξ

Since ĝ_a is an explicit Gaussian (Mathlib: `fourier_gaussian_innerProductSpace'`),
|ĝ_a|² is a Gaussian centered at ξ₀ with width ~ 1/√a. As a → 0⁺, this
concentrates at ξ₀. Since φ̂ is continuous (Riemann-Lebesgue), the integral
converges to φ̂(ξ₀) · (const), giving φ̂(ξ₀) ≥ 0. -/

/-- An L¹ positive-definite function has a nonneg real Fourier transform.
    Continuity of φ̂ (from Riemann-Lebesgue) means this holds everywhere,
    not just a.e. -/
lemma pd_l1_fourier_nonneg (φ : V → ℂ) (hpd : IsPositiveDefinite φ)
    (hint : Integrable φ) (ξ : V) :
    0 ≤ (𝓕 φ ξ).re ∧ (𝓕 φ ξ).im = 0 := by
  sorry

/-- The Fourier transform of an L¹ PD function is real and nonneg. -/
lemma pd_l1_fourier_real_nonneg (φ : V → ℂ) (hpd : IsPositiveDefinite φ)
    (hint : Integrable φ) (ξ : V) :
    𝓕 φ ξ = ↑((𝓕 φ ξ).re) ∧ 0 ≤ (𝓕 φ ξ).re := by
  obtain ⟨hre, him⟩ := pd_l1_fourier_nonneg φ hpd hint ξ
  constructor
  · apply Complex.ext <;> simp [him]
  · exact hre

/-! ## Phase 2: Gaussian regularization

φ_ε(x) = φ(x) · exp(-ε‖x‖²) is PD (Schur) and L¹ (bounded × Gaussian). -/

/-- The Gaussian-regularized function. -/
noncomputable def gaussianRegularize (φ : V → ℂ) (ε : ℝ) : V → ℂ :=
  fun x => φ x * cexp (-(ε : ℂ) * ↑(‖x‖ ^ 2))

/-- φ_ε is positive definite (Schur product of PD functions). -/
lemma gaussianRegularize_pd (φ : V → ℂ) (hpd : IsPositiveDefinite φ)
    (ε : ℝ) (hε : 0 < ε) :
    IsPositiveDefinite (gaussianRegularize φ ε) := by
  sorry

/-- φ_ε is integrable (φ is bounded by φ(0), times Gaussian decay). -/
lemma gaussianRegularize_integrable (φ : V → ℂ) (hpd : IsPositiveDefinite φ)
    (hcont : Continuous φ) (ε : ℝ) (hε : 0 < ε) :
    Integrable (gaussianRegularize φ ε) := by
  -- The Gaussian exp(-ε‖x‖²) is integrable
  have hgauss : Integrable (fun x : V => cexp (-(↑ε : ℂ) * ↑(‖x‖ ^ 2))) := by
    have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (show 0 < (↑ε : ℂ).re by simp [hε]) (0 : ℂ) (0 : V)
    simp at this
    convert this using 1; ext x; simp [Complex.ofReal_pow]
  -- φ is bounded: ‖φ(x)‖ ≤ (φ 0).re
  -- So ‖φ(x) * exp(-ε‖x‖²)‖ = ‖φ(x)‖ * ‖exp(-ε‖x‖²)‖ ≤ (φ 0).re * ‖exp(-ε‖x‖²)‖
  -- The bound function (φ 0).re * ‖exp(-ε‖x‖²)‖ is integrable
  refine (hgauss.norm.const_mul (φ 0).re).mono
    ((hcont.mul (by fun_prop : Continuous (fun x : V => cexp (-(↑ε : ℂ) * ↑(‖x‖ ^ 2))))).aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  simp only [gaussianRegularize, norm_mul, Real.norm_eq_abs, abs_of_nonneg hpd.eval_zero_nonneg,
    abs_of_nonneg (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right (hpd.bounded_by_zero x) (norm_nonneg _)

/-- φ_ε(0) = φ(0). -/
lemma gaussianRegularize_zero (φ : V → ℂ) (ε : ℝ) :
    gaussianRegularize φ ε 0 = φ 0 := by
  simp [gaussianRegularize, norm_zero]

/-- φ_ε → φ pointwise as ε → 0⁺. -/
lemma gaussianRegularize_tendsto (φ : V → ℂ) (x : V) :
    Tendsto (fun ε => gaussianRegularize φ ε x) (𝓝[>] 0) (𝓝 (φ x)) := by
  simp only [gaussianRegularize]
  suffices h : Tendsto (fun ε : ℝ => cexp (-(ε : ℂ) * ↑(‖x‖ ^ 2))) (𝓝[>] 0) (𝓝 1) by
    conv_rhs => rw [show φ x = φ x * 1 from (mul_one _).symm]
    exact Filter.Tendsto.mul tendsto_const_nhds h
  have h0 : cexp (-(0 : ℂ) * ↑(‖x‖ ^ 2)) = 1 := by simp
  rw [← h0]
  apply Filter.Tendsto.cexp
  apply Filter.Tendsto.mul _ tendsto_const_nhds
  exact Filter.Tendsto.neg (tendsto_nhdsWithin_of_tendsto_nhds Complex.continuous_ofReal.continuousAt)

/-! ## Phase 3: Construct probability measures from L¹ PD functions

Given φ ∈ L¹ PD with φ(0) = 1, define dμ = φ̂ · dλ. Since φ̂ ≥ 0 (Phase 1)
and ∫ φ̂ = φ(0) = 1 (Fourier inversion at 0), μ is a probability measure.
By Fourier inversion, charFun(μ) = φ. -/

/-- Given an L¹ PD function with φ(0) = 1, there exists a probability measure
    whose characteristic function equals φ. -/
lemma measure_of_pd_l1 (φ : V → ℂ)
    (hpd : IsPositiveDefinite φ) (hint : Integrable φ)
    (hcont : Continuous φ) (hnorm : φ 0 = 1)
    (hint_ft : Integrable (𝓕 φ)) :
    ∃ μ : ProbabilityMeasure V,
      ∀ ξ, MeasureTheory.charFun (μ : Measure V) ξ = φ ξ := by
  sorry

/-! ## Phase 4: Tightness and weak limit

The family {μ_ε} is tight because:
  μ_ε({‖x‖ > R}) ≤ (2/R²) ∫_{‖ξ‖≤δ} (1 - Re(charFun(μ_ε)(ξ))) dξ

Since charFun(μ_ε) = φ_ε → φ and φ is continuous at 0, the right side → 0
uniformly in ε as R → ∞.

Prokhorov's theorem (Mathlib: `isCompact_closure_of_isTightMeasureSet`)
extracts a weakly convergent subsequence. Testing the limit against
x ↦ exp(i⟨ξ,x⟩) identifies charFun(μ) = φ. -/

/-- Tightness bound: tail probability bounded by charFun behavior near 0.
    Standard inequality from Fourier analysis (see Folland §4.2). -/
lemma tightness_from_charfun (μ : ProbabilityMeasure V) (R : ℝ) (hR : 0 < R)
    (δ : ℝ) (hδ : 0 < δ) :
    (μ : Measure V).real {x | R < ‖x‖} ≤
      (2 / R ^ 2) * ∫ ξ in Metric.ball (0 : V) δ,
        (1 - (MeasureTheory.charFun (μ : Measure V) ξ).re) := by
  sorry

/-- The family {μ_ε} constructed from Gaussian regularization is tight. -/
lemma gaussianRegularize_measures_tight (φ : V → ℂ)
    (hpd : IsPositiveDefinite φ) (hcont : Continuous φ) (hnorm : φ 0 = 1) :
    ∀ η > 0, ∃ R > 0, ∀ ε > 0, True := by
  -- Placeholder: the actual statement needs to quantify over the
  -- constructed measures μ_ε from Phase 3
  sorry

/-! ## Phase 5: Uniqueness (from Mathlib)

`MeasureTheory.Measure.ext_of_charFun` already proves that charFun determines
the measure uniquely. -/

/-! ## Main Theorem -/

/-- **Bochner's Theorem.** A continuous positive-definite function φ : V → ℂ
    with φ(0) = 1 on a finite-dimensional real inner product space is the
    characteristic function of a unique probability measure on V.

    This is the finite-dimensional version. The infinite-dimensional
    generalization (Bochner-Minlos) additionally requires nuclearity of the
    domain space. -/
theorem bochner_theorem (φ : V → ℂ)
    (hcont : Continuous φ) (hpd : IsPositiveDefinite φ) (hnorm : φ 0 = 1) :
    ∃! μ : ProbabilityMeasure V,
      ∀ ξ, MeasureTheory.charFun (μ : Measure V) ξ = φ ξ := by
  -- Existence: Gaussian regularization + tightness + Prokhorov
  --
  -- Phase 2: Define φ_ε(x) = φ(x) · exp(-ε‖x‖²)
  --   - gaussianRegularize_pd: φ_ε is PD
  --   - gaussianRegularize_integrable: φ_ε ∈ L¹
  --   - gaussianRegularize_zero + hnorm: φ_ε(0) = 1
  --
  -- Phase 3: Apply pd_l1_fourier_nonneg to get φ̂_ε ≥ 0.
  --   Define dμ_ε = φ̂_ε dλ (probability measure since ∫ φ̂_ε = 1).
  --   By Fourier inversion: charFun(μ_ε) = φ_ε.
  --
  -- Phase 4: charFun(μ_ε) = φ_ε → φ pointwise (gaussianRegularize_tendsto).
  --   Tightness of {μ_ε} via tightness_from_charfun + continuity of φ at 0.
  --   Prokhorov → weakly convergent subsequence μ_{ε_k} → μ.
  --   charFun(μ)(ξ) = lim charFun(μ_{ε_k})(ξ) = lim φ_{ε_k}(ξ) = φ(ξ).
  have hex : ∃ μ : ProbabilityMeasure V,
      ∀ ξ, MeasureTheory.charFun (μ : Measure V) ξ = φ ξ := by
    sorry
  -- Uniqueness: from Mathlib's Measure.ext_of_charFun
  obtain ⟨μ, hμ⟩ := hex
  refine ⟨μ, hμ, fun ν hν => ?_⟩
  have hmeas : (μ : Measure V) = (ν : Measure V) :=
    Measure.ext_of_charFun (by ext ξ; rw [hμ ξ, hν ξ])
  exact Subtype.ext hmeas.symm
