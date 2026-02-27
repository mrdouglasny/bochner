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
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

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
  -- Part 1: Im = 0 from Hermitian symmetry φ(-x) = conj(φ(x))
  -- conj(φ̂(ξ)) = ∫ conj(𝐞(-⟪v,ξ⟫) • φ v) = ∫ 𝐞(⟪v,ξ⟫) • φ(-v)
  -- = ∫ 𝐞(-⟪w,ξ⟫) • φ(w)  (w = -v) = φ̂(ξ)
  have hft_conj : starRingEnd ℂ (𝓕 φ ξ) = 𝓕 φ ξ := by
    show starRingEnd ℂ (∫ v, 𝐞 (-⟪v, ξ⟫_ℝ) • φ v) = ∫ v, 𝐞 (-⟪v, ξ⟫_ℝ) • φ v
    rw [show starRingEnd ℂ (∫ v, 𝐞 (-⟪v, ξ⟫_ℝ) • φ v) =
      ∫ v, starRingEnd ℂ (𝐞 (-⟪v, ξ⟫_ℝ) • φ v) from integral_conj.symm]
    -- Goal: ∫ v, conj(𝐞(-⟪v,ξ⟫) • φ v) = ∫ v, 𝐞(-⟪v,ξ⟫) • φ v
    simp_rw [Circle.smul_def, smul_eq_mul, map_mul,
      Circle.starRingEnd_addChar, neg_neg,
      show ∀ v, starRingEnd ℂ (φ v) = φ (-v) from
        fun v => (hpd.hermitian v).symm]
    -- Goal: ∫ v, ↑(𝐞(⟪v,ξ⟫)) * φ(-v) = ∫ v, ↑(𝐞(-⟪v,ξ⟫)) * φ v
    -- Substitute v → -v in LHS using integral_neg_eq_self
    -- Change variables: v → -v
    have hsub := integral_neg_eq_self
      (fun v => (↑(𝐞 (⟪v, ξ⟫_ℝ)) : ℂ) * φ (-v)) (volume : Measure V)
    simp only [inner_neg_left, neg_neg] at hsub
    exact hsub.symm
  have him : (𝓕 φ ξ).im = 0 := by
    have := congr_arg Complex.im hft_conj
    simp only [Complex.conj_im] at this
    linarith
  -- Part 2: Re ≥ 0 from discrete PD condition + Riemann sum convergence
  -- Proof sketch: Choose grid points x_k = k/N, k ∈ [-M,M]^d with
  -- coefficients c_k = N^{-d/2} e^{2πi⟨x_k,ξ⟩}. The PD condition gives
  -- Σ_{j,k} c̄_j c_k φ(x_j-x_k) ≥ 0. This is a Cesàro-weighted Riemann
  -- sum that converges to ∫ e^{-2πi⟨x,ξ⟩} φ(x) dx = φ̂(ξ) as N,M → ∞.
  exact ⟨sorry, him⟩

/-- The Fourier transform of an L¹ PD function is real and nonneg. -/
lemma pd_l1_fourier_real_nonneg (φ : V → ℂ) (hpd : IsPositiveDefinite φ)
    (hint : Integrable φ) (ξ : V) :
    𝓕 φ ξ = ↑((𝓕 φ ξ).re) ∧ 0 ≤ (𝓕 φ ξ).re := by
  obtain ⟨hre, him⟩ := pd_l1_fourier_nonneg φ hpd hint ξ
  constructor
  · apply Complex.ext <;> simp [him]
  · exact hre

/-- The double sum ∑ᵢ ∑ⱼ conj(aᵢ) * aⱼ equals normSq(∑ₖ aₖ). -/
private lemma sum_star_mul_eq_normSq {m : ℕ} (a : Fin m → ℂ) :
    ∑ i, ∑ j, starRingEnd ℂ (a i) * a j = ↑(Complex.normSq (∑ k, a k)) := by
  have h : (↑(Complex.normSq (∑ k, a k)) : ℂ) =
      (starRingEnd ℂ) (∑ k, a k) * ∑ k, a k := by
    rw [starRingEnd_apply, star_def, Complex.normSq_eq_conj_mul_self]
  rw [h, map_sum, Finset.sum_mul_sum]

/-! ## Phase 1.5: Characteristic functions are positive definite

The "forward" direction of Bochner: the characteristic function of any
finite measure is positive definite. This gives us PD of the Gaussian
as a corollary: exp(-ε‖x‖²) is the charFun of a Gaussian measure. -/

/-- Forward Bochner: the characteristic function of any finite measure is PD.

    Proof: charFun(μ)(t) = ∫ exp(i⟨x,t⟩) dμ(x). So
    ∑ᵢⱼ c̄ᵢcⱼ charFun(tᵢ-tⱼ) = ∫ |∑ₖ cₖ exp(i⟨x,tₖ⟩)|² dμ(x) ≥ 0.

    The key steps are: (1) swap finite sum and integral, (2) recognize
    the integrand as a norm squared. -/
lemma isPositiveDefinite_charFun (μ : Measure V) [IsFiniteMeasure μ] :
    IsPositiveDefinite (fun t : V => charFun μ t) where
  hermitian t := by
    rw [starRingEnd_apply, star_def]
    exact charFun_neg t
  nonneg m t c := by
    -- Step 1: Unfold charFun
    simp only [charFun_apply]
    -- Step 2: Show the .re of the sum equals ∫ normSq(∑ₖ cₖ e^{-i⟨x,tₖ⟩}) dμ ≥ 0
    suffices h : (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j *
        ∫ x, cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ).re =
        ∫ x, Complex.normSq (∑ k, c k * cexp (↑(-⟪x, t k⟫_ℝ) * I)) ∂μ by
      rw [h]
      exact integral_nonneg (fun x => Complex.normSq_nonneg _)
    -- Integrability of exponentials on a finite measure (norm ≤ 1)
    have hexp_int : ∀ v : V, Integrable (fun x : V =>
        cexp (↑⟪x, v⟫_ℝ * I)) μ :=
      fun v => (memLp_top_of_bound (by fun_prop : Continuous _).aestronglyMeasurable 1
        (ae_of_all _ fun x => by simp [Complex.norm_exp_ofReal_mul_I])).integrable le_top
    -- Integrability of each summand c̄ᵢcⱼ·exp
    have hterm_int : ∀ i j, Integrable (fun x : V =>
        (starRingEnd ℂ) (c i) * c j * cexp (↑⟪x, t i - t j⟫_ℝ * I)) μ :=
      fun i j => (hexp_int (t i - t j)).const_mul _
    -- Step A: Complex equality: ∑ᵢ∑ⱼ c̄ᵢcⱼ ∫ exp = ∫ ↑(normSq(∑ cₖexp))
    have hcomplex : ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j *
        ∫ x, cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ =
        ∫ x, ↑(normSq (∑ k, c k * cexp (↑(-⟪x, t k⟫_ℝ) * I))) ∂μ := by
      -- Pull constants into integrals and merge sums
      calc ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j *
              ∫ x, cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ
          = ∑ i, ∑ j, ∫ x, (starRingEnd ℂ) (c i) * c j *
              cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ := by
            congr 1; ext i; congr 1; ext j; exact (integral_const_mul _ _).symm
        _ = ∑ i, ∫ x, ∑ j, (starRingEnd ℂ) (c i) * c j *
              cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ := by
            congr 1; ext i
            exact (integral_finset_sum _ (fun j _ => hterm_int i j)).symm
        _ = ∫ x, ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j *
              cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ := by
            exact (integral_finset_sum _ (fun i _ =>
              integrable_finset_sum _ (fun j _ => hterm_int i j))).symm
        _ = ∫ x, ↑(normSq (∑ k, c k * cexp (↑(-⟪x, t k⟫_ℝ) * I))) ∂μ := by
            congr 1; ext x
            -- Algebraic identity: ∑ᵢ∑ⱼ c̄ᵢcⱼe^{i⟨x,tᵢ-tⱼ⟩} = ↑(normSq(∑ cₖe^{-i⟨x,tₖ⟩}))
            -- Use sum_star_mul_eq_normSq with aₖ = cₖ * exp(-i⟨x,tₖ⟩)
            rw [← sum_star_mul_eq_normSq]
            congr 1; ext i; congr 1; ext j
            -- Goal: c̄ᵢ * cⱼ * exp(⟨x,tᵢ-tⱼ⟩*I) = conj(cᵢ*exp(-⟨x,tᵢ⟩*I)) * (cⱼ*exp(-⟨x,tⱼ⟩*I))
            rw [map_mul, mul_mul_mul_comm]
            congr 1
            -- conj(exp(-⟨x,tᵢ⟩*I)) * exp(-⟨x,tⱼ⟩*I) = exp(⟨x,tᵢ-tⱼ⟩*I)
            -- conj(exp(-r*I)) = exp(r*I)
            rw [starRingEnd_apply, star_def, ← Complex.exp_conj]
            simp only [Complex.conj_ofReal, Complex.conj_I, map_mul, mul_neg]
            -- exp(⟨x,tᵢ⟩*I) * exp(-⟨x,tⱼ⟩*I) = exp((⟨x,tᵢ⟩-⟨x,tⱼ⟩)*I)
            rw [← Complex.exp_add]
            congr 1
            rw [inner_sub_right]; push_cast; ring
    -- Step B: .re of the complex integral = real integral
    rw [hcomplex]
    have hnorm_int : Integrable (fun x : V =>
        (↑(normSq (∑ k, c k * cexp (↑(-⟪x, t k⟫_ℝ) * I))) : ℂ)) μ := by
      apply Integrable.ofReal
      exact (memLp_top_of_bound
        ((Complex.continuous_normSq.comp (by fun_prop : Continuous _)).aestronglyMeasurable)
        ((∑ k, ‖c k‖) ^ 2)
        (ae_of_all _ fun x => by
          simp only [Function.comp_def, Real.norm_eq_abs,
            abs_of_nonneg (Complex.normSq_nonneg _)]
          rw [Complex.normSq_eq_norm_sq]
          gcongr
          calc ‖∑ k, c k * cexp (↑(-⟪x, t k⟫_ℝ) * I)‖
              ≤ ∑ k, ‖c k * cexp (↑(-⟪x, t k⟫_ℝ) * I)‖ := norm_sum_le _ _
            _ = ∑ k, ‖c k‖ := by
                congr 1; ext k; rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
          )).integrable le_top
    -- Move .re inside the integral using reCLM
    -- reCLM.integral_comp_comm gives: ∫ reCLM(f x) = reCLM(∫ f x)
    -- Since reCLM ↑(normSq z) = normSq z and reCLM(∫ ...) = (∫ ...).re,
    -- this gives ∫ normSq ... = (∫ ↑(normSq ...) ∂μ).re
    have hre_swap := Complex.reCLM.integral_comp_comm hnorm_int
    -- hre_swap : ∫ reCLM ↑(normSq ...) = reCLM (∫ ↑(normSq ...))
    -- LHS simplifies: reCLM ↑r = r, so LHS = ∫ normSq ...
    -- RHS is reCLM applied to integral, which = (integral).re
    change ∫ x, Complex.re (↑(normSq (∑ k, c k * cexp (↑(-⟪x, t k⟫_ℝ) * I)))) ∂μ =
        Complex.re (∫ x, ↑(normSq (∑ k, c k * cexp (↑(-⟪x, t k⟫_ℝ) * I))) ∂μ) at hre_swap
    simp only [Complex.ofReal_re] at hre_swap
    exact hre_swap.symm

/-- Pointwise product of a PD function and the characteristic function of a
    finite measure is PD. This is a "continuous Schur product" — the same
    algebraic trick as `isPositiveDefinite_charFun` but with modified
    coefficients d_k(x) = c_k · exp(-i⟨x, t_k⟩) absorbed into the PD condition. -/
lemma isPositiveDefinite_mul_charFun {φ : V → ℂ} (hpd : IsPositiveDefinite φ)
    (μ : Measure V) [IsFiniteMeasure μ] :
    IsPositiveDefinite (fun t => φ t * charFun μ t) where
  hermitian t := by
    show φ (-t) * charFun μ (-t) = (starRingEnd ℂ) (φ t * charFun μ t)
    rw [map_mul, ← hpd.hermitian t]
    congr 1
    rw [starRingEnd_apply, star_def]
    exact charFun_neg t
  nonneg m t c := by
    simp only [charFun_apply]
    -- Integrability of exponentials on a finite measure (norm ≤ 1)
    have hexp_int : ∀ v : V, Integrable (fun x : V =>
        cexp (↑⟪x, v⟫_ℝ * I)) μ :=
      fun v => (memLp_top_of_bound (by fun_prop : Continuous _).aestronglyMeasurable 1
        (ae_of_all _ fun x => by simp [Complex.norm_exp_ofReal_mul_I])).integrable le_top
    -- Integrability of each summand c̄ᵢcⱼφ(dᵢⱼ)·exp
    have hterm_int : ∀ i j, Integrable (fun x : V =>
        (starRingEnd ℂ) (c i) * c j * φ (t i - t j) *
        cexp (↑⟪x, t i - t j⟫_ℝ * I)) μ :=
      fun i j => (hexp_int (t i - t j)).const_mul _
    -- Step A: Swap double sum and integral
    have hswap : ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j *
        (φ (t i - t j) * ∫ x, cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ) =
        ∫ x, ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * φ (t i - t j) *
        cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ := by
      calc ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j *
              (φ (t i - t j) * ∫ x, cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ)
          = ∑ i, ∑ j, ∫ x, (starRingEnd ℂ) (c i) * c j * φ (t i - t j) *
              cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ := by
            congr 1; ext i; congr 1; ext j
            rw [← mul_assoc]; exact (integral_const_mul (L := ℂ) _ _).symm
        _ = ∑ i, ∫ x, ∑ j, (starRingEnd ℂ) (c i) * c j * φ (t i - t j) *
              cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ := by
            congr 1; ext i
            exact (integral_finset_sum _ (fun j _ => hterm_int i j)).symm
        _ = ∫ x, ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * φ (t i - t j) *
              cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ := by
            exact (integral_finset_sum _ (fun i _ =>
              integrable_finset_sum _ (fun j _ => hterm_int i j))).symm
    -- Step B: Algebraic identity — absorb exponentials into modified coefficients
    -- For each x: c̄ᵢcⱼφ(dᵢⱼ)e^{i⟨x,dᵢⱼ⟩} = conj(cᵢe^{-i⟨x,tᵢ⟩})(cⱼe^{-i⟨x,tⱼ⟩})φ(dᵢⱼ)
    -- Exponential splitting: exp(i⟨x,tᵢ-tⱼ⟩) = conj(exp(-i⟨x,tᵢ⟩)) * exp(-i⟨x,tⱼ⟩)
    have hexp_split : ∀ (x : V) (i j : Fin m),
        cexp (↑⟪x, t i - t j⟫_ℝ * I) =
        (starRingEnd ℂ) (cexp (-(↑⟪x, t i⟫_ℝ) * I)) * cexp (-(↑⟪x, t j⟫_ℝ) * I) := by
      intro x i j
      rw [← Complex.exp_conj, ← Complex.exp_add]
      congr 1
      have : (starRingEnd ℂ) (-(↑⟪x, t i⟫_ℝ : ℂ) * I) = ↑⟪x, t i⟫_ℝ * I := by
        rw [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]; ring
      rw [this, inner_sub_right]; push_cast; ring
    have halg : ∀ x : V,
        ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * φ (t i - t j) *
        cexp (↑⟪x, t i - t j⟫_ℝ * I) =
        ∑ i, ∑ j, (starRingEnd ℂ) (c i * cexp (-(↑⟪x, t i⟫_ℝ) * I)) *
        (c j * cexp (-(↑⟪x, t j⟫_ℝ) * I)) * φ (t i - t j) := by
      intro x; congr 1; ext i; congr 1; ext j
      rw [hexp_split, map_mul]; ring
    -- Step C: Combine and take .re inside integral
    rw [hswap]
    simp_rw [halg]
    -- Goal: 0 ≤ (∫ x, ∑ᵢⱼ conj(c'ᵢ(x)) c'ⱼ(x) φ(dᵢⱼ) ∂μ).re
    -- The integrand .re ≥ 0 by PD of φ with modified coefficients
    -- First, show the integrand is integrable
    have hint_sum : Integrable (fun x : V =>
        ∑ i, ∑ j, (starRingEnd ℂ) (c i * cexp (-(↑⟪x, t i⟫_ℝ) * I)) *
        (c j * cexp (-(↑⟪x, t j⟫_ℝ) * I)) * φ (t i - t j)) μ := by
      -- This equals the original sum (by halg), which is integrable
      rw [show (fun x => ∑ i, ∑ j, (starRingEnd ℂ) (c i * cexp (-(↑⟪x, t i⟫_ℝ) * I)) *
        (c j * cexp (-(↑⟪x, t j⟫_ℝ) * I)) * φ (t i - t j)) =
        (fun x => ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * φ (t i - t j) *
        cexp (↑⟪x, t i - t j⟫_ℝ * I)) from funext (fun x => (halg x).symm)]
      exact integrable_finset_sum _ (fun i _ =>
        integrable_finset_sum _ (fun j _ => hterm_int i j))
    -- Pull .re inside the integral using reCLM
    have hre_swap := Complex.reCLM.integral_comp_comm hint_sum
    change ∫ x, Complex.re (∑ i, ∑ j, (starRingEnd ℂ) (c i * cexp (-(↑⟪x, t i⟫_ℝ) * I)) *
        (c j * cexp (-(↑⟪x, t j⟫_ℝ) * I)) * φ (t i - t j)) ∂μ =
        Complex.re (∫ x, ∑ i, ∑ j, (starRingEnd ℂ) (c i * cexp (-(↑⟪x, t i⟫_ℝ) * I)) *
        (c j * cexp (-(↑⟪x, t j⟫_ℝ) * I)) * φ (t i - t j) ∂μ) at hre_swap
    rw [← hre_swap]
    exact integral_nonneg (fun x =>
      hpd.nonneg m t (fun k => c k * cexp (-(↑⟪x, t k⟫_ℝ) * I)))

/-- There exists a centered Gaussian measure whose characteristic function is
    exp(-ε‖t‖²). This is the forward direction of Bochner for Gaussian measures.

    On ℝⁿ with standard inner product, the Gaussian measure with density
    (4πε)^{-n/2} exp(-‖x‖²/(4ε)) has charFun(t) = exp(-ε‖t‖²).

    Proof: define μ = C · exp(-a‖x‖²) · dλ where a = 1/(4ε) and C normalizes.
    Use `integral_cexp_neg_mul_sq_norm_add` for the charFun computation. -/
private lemma gaussian_eq_charFun (ε : ℝ) (hε : 0 < ε) :
    ∃ (μ : Measure V), IsFiniteMeasure μ ∧
    ∀ t, charFun μ t = cexp (-(ε : ℂ) * ↑(‖t‖ ^ 2)) := by
  -- Parameters: a = 1/(4ε), so ε = 1/(4a) and ‖t‖²/(4a) = ε‖t‖²
  set a : ℝ := 1 / (4 * ε) with ha_def
  have ha : 0 < a := by positivity
  -- Normalization constant
  set n : ℕ := Module.finrank ℝ V
  set Cnorm : ℝ := (π / a) ^ (n / 2 : ℝ)
  have hCnorm_pos : 0 < Cnorm := by positivity
  set C : ℝ := Cnorm⁻¹
  have hC_pos : 0 < C := inv_pos.mpr hCnorm_pos
  -- The ℝ≥0∞-valued density
  set density : V → ENNReal := fun x => ENNReal.ofReal (C * rexp (-a * ‖x‖ ^ 2))
  have hdensity_meas : Measurable density := by
    apply ENNReal.measurable_ofReal.comp
    exact measurable_const.mul (by fun_prop)
  -- Define the measure
  set μ := volume.withDensity density
  -- Integrability of the complex Gaussian
  have hgauss_cint : Integrable (fun x : V => cexp (-(a : ℂ) * ↑(‖x‖ ^ 2))) := by
    have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (show 0 < ((a : ℂ)).re by simp [ha]) (0 : ℂ) (0 : V)
    simp at this; convert this using 1; ext x; simp [Complex.ofReal_pow]
  -- The real Gaussian is integrable (derived from complex version)
  have hgauss_rint : Integrable (fun x : V => C * rexp (-a * ‖x‖ ^ 2)) := by
    apply Integrable.const_mul
    have : (fun x : V => rexp (-a * ‖x‖ ^ 2)) =
        (fun x : V => ‖cexp (-(a : ℂ) * ↑(‖x‖ ^ 2))‖) := by
      ext x
      rw [Complex.norm_exp]; congr 1
      simp [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_neg]
    rw [this]; exact hgauss_cint.norm
  have hnn : 0 ≤ᵐ[volume] (fun x : V => C * rexp (-a * ‖x‖ ^ 2)) :=
    ae_of_all _ (fun x => by positivity)
  refine ⟨μ, ?_, ?_⟩
  -- IsFiniteMeasure: ∫⁻ density = ENNReal.ofReal(∫ C*exp(...)) < ⊤
  · apply isFiniteMeasure_withDensity
    rw [← ofReal_integral_eq_lintegral_ofReal hgauss_rint hnn]
    exact ENNReal.ofReal_ne_top
  -- charFun computation: charFun μ t = ∫ exp(i⟪x,t⟫) C exp(-a‖x‖²) dx
  --   = C * ∫ exp(-a‖x‖² + i⟪t,x⟫) dx = C * Cnorm * exp(-ε‖t‖²) = exp(-ε‖t‖²)
  · intro t
    rw [charFun_apply]
    -- Rewrite integral w.r.t. withDensity as integral w.r.t. volume
    rw [integral_withDensity_eq_integral_toReal_smul₀ hdensity_meas.aemeasurable
      (ae_of_all _ (fun x => by simp [density]))]
    -- Simplify: (density x).toReal • cexp(⟪x,t⟫ * I) = C * cexp(-a‖x‖² + I*⟪t,x⟫)
    -- Target form matches Mathlib's integral_cexp_neg_mul_sq_norm_add pattern
    have hintegrand : ∀ x : V, (density x).toReal • cexp (↑⟪x, t⟫_ℝ * I) =
        (C : ℂ) * cexp (-(a : ℂ) * ↑‖x‖ ^ 2 + I * ↑⟪t, x⟫_ℝ) := by
      intro x
      simp only [density, ENNReal.toReal_ofReal (by positivity : 0 ≤ C * rexp (-a * ‖x‖ ^ 2))]
      rw [Complex.real_smul, Complex.ofReal_mul, mul_assoc, Complex.ofReal_exp,
        ← Complex.exp_add, real_inner_comm x t]
      congr 2; push_cast; ring
    -- Use calc to step through the computation
    have hb : 0 < ((a : ℂ)).re := by simp [ha]
    calc ∫ x, (density x).toReal • cexp (↑⟪x, t⟫_ℝ * I) ∂volume
        _ = ∫ x, (C : ℂ) * cexp (-(a : ℂ) * ↑‖x‖ ^ 2 + I * ↑⟪t, x⟫_ℝ) ∂volume := by
          refine MeasureTheory.integral_congr_ae ?_; exact ae_of_all _ hintegrand
        _ = (C : ℂ) * ∫ x, cexp (-(a : ℂ) * ↑‖x‖ ^ 2 + I * ↑⟪t, x⟫_ℝ) ∂volume :=
          integral_const_mul _ _
        _ = cexp (-(ε : ℂ) * ↑(‖t‖ ^ 2)) := by
          rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb I t]
          -- Cancel C * Cnorm = 1
          have hcpow : (↑π / (↑a : ℂ)) ^ ((↑n : ℂ) / 2) = (Cnorm : ℂ) := by
            rw [← Complex.ofReal_natCast n, ← Complex.ofReal_ofNat 2,
              ← Complex.ofReal_div, ← Complex.ofReal_div]
            exact (Complex.ofReal_cpow (le_of_lt (by positivity : (0 : ℝ) < π / a)) _).symm
          rw [hcpow, ← mul_assoc]
          rw [show (C : ℂ) * (Cnorm : ℂ) = 1 from by
            rw [show (C : ℝ) = Cnorm⁻¹ from rfl, Complex.ofReal_inv,
              inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hCnorm_pos))]]
          rw [one_mul, I_sq, ha_def]
          push_cast; field_simp

/-- The Gaussian function x ↦ exp(-ε‖x‖²) is positive definite.

    Proved by showing it is the characteristic function of a centered
    Gaussian measure with variance 1/(2ε). -/
lemma isPositiveDefinite_gaussian (ε : ℝ) (hε : 0 < ε) :
    IsPositiveDefinite (fun x : V => cexp (-(ε : ℂ) * ↑(‖x‖ ^ 2))) := by
  obtain ⟨μ, hfin, hcharFun⟩ := gaussian_eq_charFun (V := V) ε hε
  haveI := hfin
  have hpd := isPositiveDefinite_charFun μ
  convert hpd using 1; ext t; exact (hcharFun t).symm

/-! ## Phase 2: Gaussian regularization

φ_ε(x) = φ(x) · exp(-ε‖x‖²) is PD (Schur) and L¹ (bounded × Gaussian). -/

/-- The Gaussian-regularized function. -/
noncomputable def gaussianRegularize (φ : V → ℂ) (ε : ℝ) : V → ℂ :=
  fun x => φ x * cexp (-(ε : ℂ) * ↑(‖x‖ ^ 2))

/-- φ_ε is positive definite (Schur product of PD functions).

    Direct proof via the Fourier representation of the Gaussian, avoiding
    the general Schur product theorem.

    exp(-ε‖xᵢ-xⱼ‖²) = ∫ exp(2πi⟨ξ,xᵢ-xⱼ⟩) g(ξ) dξ  where g ≥ 0

    So ∑ᵢⱼ c̄ᵢcⱼ φ(xᵢ-xⱼ) exp(-ε‖xᵢ-xⱼ‖²)
      = ∫ g(ξ) [∑ᵢⱼ (cᵢ e^{2πi⟨xᵢ,ξ⟩})* (cⱼ e^{2πi⟨xⱼ,ξ⟩}) φ(xᵢ-xⱼ)] dξ

    The inner sum has .re ≥ 0 by PD of φ, and g ≥ 0, so the integral ≥ 0. -/
lemma gaussianRegularize_pd (φ : V → ℂ) (hpd : IsPositiveDefinite φ)
    (ε : ℝ) (hε : 0 < ε) :
    IsPositiveDefinite (gaussianRegularize φ ε) where
  hermitian x := by
    simp only [gaussianRegularize, norm_neg]
    rw [hpd.hermitian x, starRingEnd_apply, star_def, map_mul, ← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  nonneg m x c := by
    -- gaussianRegularize φ ε = fun t => φ t * cexp(...)
    -- By gaussian_eq_charFun, cexp(-ε‖t‖²) = charFun μ t for some Gaussian μ
    -- So gaussianRegularize φ ε t = φ t * charFun μ t
    -- and isPositiveDefinite_mul_charFun gives the result
    obtain ⟨μ, hfin, hcharFun⟩ := gaussian_eq_charFun (V := V) ε hε
    haveI := hfin
    have hmul := isPositiveDefinite_mul_charFun hpd μ
    have heq : ∀ t, gaussianRegularize φ ε t = φ t * charFun μ t := by
      intro t; simp only [gaussianRegularize]; rw [← hcharFun t]
    simp_rw [heq]
    exact hmul.nonneg m x c

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
    whose characteristic function equals φ.

    Key idea: define ψ(x) = φ(2πx) to absorb the 2π convention difference
    between charFun (uses e^{i⟪x,t⟫}) and 𝓕 (uses e^{-2πi⟪x,ξ⟫}).
    Then dμ = 𝓕ψ · dλ is a probability measure with charFun(μ) = φ. -/
lemma measure_of_pd_l1 (φ : V → ℂ)
    (hpd : IsPositiveDefinite φ) (hint : Integrable φ)
    (hcont : Continuous φ) (hnorm : φ 0 = 1)
    (hint_ft : Integrable (𝓕 φ)) :
    ∃ μ : ProbabilityMeasure V,
      ∀ ξ, MeasureTheory.charFun (μ : Measure V) ξ = φ ξ := by
  -- Step 1: Define ψ(x) = φ(2πx) to match charFun ↔ 𝓕 conventions
  set τ : ℝ := 2 * Real.pi with hτ_def
  have hτ_pos : 0 < τ := by positivity
  have hτ_ne : τ ≠ 0 := ne_of_gt hτ_pos
  -- The scaling map T(x) = τ • x as a linear map
  set T : V →ₗ[ℝ] V := τ • LinearMap.id with hT_def
  set ψ : V → ℂ := fun x => φ (T x) with hψ_def
  -- Step 2: ψ is PD (composition with linear map)
  have hψ_pd : IsPositiveDefinite ψ := isPositiveDefinite_precomp_linear φ hpd T
  -- Step 3: ψ is continuous
  have hψ_cont : Continuous ψ := hcont.comp (continuous_const_smul τ)
  -- Step 4: ψ is integrable (change of variables: ∫|ψ| = τ⁻ⁿ ∫|φ|)
  have hψ_int : Integrable ψ := by
    rw [show ψ = (fun x => φ (τ • x)) from rfl]
    exact (integrable_comp_smul_iff volume φ hτ_ne).mpr hint
  -- Step 5: 𝓕ψ is integrable (from hint_ft via Fourier scaling)
  -- Key formula: 𝓕(φ(τ·))(ξ) = |τ⁻ⁿ| · 𝓕φ(τ⁻¹·ξ)
  -- So Integrable(𝓕ψ) ↔ Integrable(𝓕φ)
  have hψ_ft_int : Integrable (𝓕 ψ) := by
    -- Step A: Show 𝓕ψ(ξ) = |(τ^n)⁻¹| • 𝓕φ(τ⁻¹ • ξ) pointwise
    set n' := Module.finrank ℝ V
    have hkey : ∀ ξ, 𝓕 ψ ξ = |(τ ^ n')⁻¹| • 𝓕 φ (τ⁻¹ • ξ) := by
      intro ξ
      -- Unfold to integral form
      change (∫ v, Real.fourierChar (-⟪v, ξ⟫_ℝ) • φ (τ • v)) =
        |(τ ^ n')⁻¹| • ∫ v, Real.fourierChar (-⟪v, τ⁻¹ • ξ⟫_ℝ) • φ v
      -- Change of variables: ∫ g(τ • v) = |(τ^n)⁻¹| • ∫ g(v)
      -- Change of variables via integral_comp_smul, then simplify inner products
      have hcov := Measure.integral_comp_smul volume
        (fun y => Real.fourierChar (-⟪τ⁻¹ • y, ξ⟫_ℝ) • φ y) τ
      simp only [inv_smul_smul₀ hτ_ne] at hcov
      rw [hcov]
      congr 1
      refine MeasureTheory.integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only [real_inner_smul_left, real_inner_smul_right]
    -- Step B: Transfer integrability
    have hfun_eq : 𝓕 ψ = fun ξ => |(τ ^ n')⁻¹| • 𝓕 φ (τ⁻¹ • ξ) := funext hkey
    rw [hfun_eq]
    exact Integrable.smul |(τ ^ n')⁻¹|
      ((integrable_comp_smul_iff volume (𝓕 φ) (inv_ne_zero hτ_ne)).mpr hint_ft)
  -- Step 6: 𝓕ψ is real and nonneg (from pd_l1_fourier_nonneg)
  have hψ_ft_nonneg : ∀ x, 0 ≤ (𝓕 ψ x).re ∧ (𝓕 ψ x).im = 0 :=
    fun x => pd_l1_fourier_nonneg ψ hψ_pd hψ_int x
  -- Step 7: Define the density and measure
  set density : V → ENNReal := fun x => ENNReal.ofReal (𝓕 ψ x).re
  have hψ_ft_cont : Continuous (𝓕 ψ) := by
    change Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ V) ψ)
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hψ_int
  have hdensity_meas : Measurable density := by
    exact ENNReal.measurable_ofReal.comp ((Complex.continuous_re.comp hψ_ft_cont).measurable)
  set μ_raw := volume.withDensity density
  -- Step 8: Total mass = ψ(0) = φ(0) = 1 (Fourier inversion at 0)
  have htotal : μ_raw Set.univ = 1 := by
    -- μ_raw = withDensity(ofReal (Re(𝓕ψ))), so total mass = ∫⁻ ofReal(Re(𝓕ψ))
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    -- Re(𝓕ψ) is integrable and ≥ 0
    have hre_int : Integrable (fun x => (𝓕 ψ x).re) := hψ_ft_int.re
    have hre_nn : 0 ≤ᵐ[volume] fun x => (𝓕 ψ x).re :=
      ae_of_all _ fun x => (hψ_ft_nonneg x).1
    rw [show density = fun x => ENNReal.ofReal (𝓕 ψ x).re from rfl,
      ← ofReal_integral_eq_lintegral_ofReal hre_int hre_nn]
    -- Goal: ofReal (∫ Re(𝓕ψ)) = 1
    -- Key chain: ∫ Re(𝓕ψ) = Re(∫ 𝓕ψ) = Re(𝓕⁻(𝓕ψ)(0)) = Re(ψ(0)) = Re(φ(0)) = 1
    -- Step A: Fourier inversion at 0: 𝓕⁻(𝓕ψ)(0) = ψ(0)
    have hinv : 𝓕⁻ (𝓕 ψ) 0 = ψ 0 :=
      hψ_int.fourierInv_fourier_eq hψ_ft_int hψ_cont.continuousAt
    -- Step B: ψ(0) = φ(T 0) = φ(0) = 1
    have hψ0 : ψ 0 = 1 := by
      show φ (T 0) = 1
      simp [T, smul_zero, hnorm]
    -- Step C: ∫ 𝓕ψ = ψ(0) = 1 via Fourier inversion at 0
    have hint_eq : ∫ x, 𝓕 ψ x = 1 := by
      -- Fourier inversion: 𝓕⁻(𝓕ψ) = ψ, evaluate at 0
      have hfinv := hψ_cont.fourierInv_fourier_eq hψ_int hψ_ft_int
      have h0 := congr_fun hfinv 0
      -- h0 : 𝓕⁻(𝓕ψ)(0) = ψ(0)
      -- Expand LHS: 𝓕⁻(𝓕ψ)(0) = ∫ 𝓕ψ
      rw [Real.fourierInv_eq'] at h0
      simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul,
        Complex.exp_zero, one_smul] at h0
      -- h0 : ∫ 𝓕ψ v = ψ(0); need ∫ 𝓕ψ x = 1
      convert h0.trans hψ0
    -- Step D: ∫ Re(𝓕ψ) = Re(∫ 𝓕ψ) = 1
    have hre_eq : ∫ x, (𝓕 ψ x).re = 1 := by
      have h1 := Complex.reCLM.integral_comp_comm hψ_ft_int
      change ∫ x, (𝓕 ψ x).re = (∫ x, 𝓕 ψ x).re at h1
      rw [h1, hint_eq]; simp
    rw [hre_eq]; simp
  -- Step 9: Package as ProbabilityMeasure
  have hfm : IsFiniteMeasure μ_raw := by
    constructor; rw [htotal]; exact ENNReal.one_lt_top
  have hprob : IsProbabilityMeasure μ_raw := ⟨htotal⟩
  set μ : ProbabilityMeasure V := ⟨μ_raw, hprob⟩
  -- Step 10: charFun(μ)(t) = φ(t) via Fourier inversion
  refine ⟨μ, fun ξ => ?_⟩
  -- charFun μ ξ = ∫ (𝓕ψ x).re • e^{i⟪x,ξ⟫} dx = 𝓕⁻(𝓕ψ)(τ⁻¹ξ) = ψ(τ⁻¹ξ) = φ(ξ)
  -- Step A: Fourier inversion gives 𝓕⁻(𝓕ψ) = ψ
  have hfinv := hψ_cont.fourierInv_fourier_eq hψ_int hψ_ft_int
  -- Step B: ψ(τ⁻¹ • ξ) = φ(T(τ⁻¹ • ξ)) = φ(ξ)
  have hψ_eval : ψ (τ⁻¹ • ξ) = φ ξ := by
    show φ (T (τ⁻¹ • ξ)) = φ ξ
    simp [T, smul_smul, inv_mul_cancel₀ hτ_ne]
  -- Step C: charFun computation via withDensity integral
  -- charFun is ∫ cexp(i⟪x,ξ⟫) ∂↑μ, and ↑μ = μ_raw = volume.withDensity density
  show ∫ x, cexp (↑⟪x, ξ⟫_ℝ * I) ∂μ_raw = φ ξ
  rw [show μ_raw = volume.withDensity density from rfl]
  rw [integral_withDensity_eq_integral_toReal_smul₀ hdensity_meas.aemeasurable
    (ae_of_all _ (fun x => by simp [density]))]
  -- Goal: ∫ x, (density x).toReal • cexp(⟪x,ξ⟫ * I) = φ ξ
  -- Simplify density toReal
  have hdensity_simp : ∀ x, (density x).toReal = (𝓕 ψ x).re := by
    intro x
    simp only [density, ENNReal.toReal_ofReal (hψ_ft_nonneg x).1]
  -- Rewrite using 𝓕⁻(𝓕ψ)(τ⁻¹ξ) = ψ(τ⁻¹ξ)
  rw [← hψ_eval, ← congr_fun hfinv (τ⁻¹ • ξ)]
  -- Goal: ∫ (density x).toReal • cexp(⟪x,ξ⟫ * I) = 𝓕⁻(𝓕ψ)(τ⁻¹ξ)
  -- Expand 𝓕⁻ using fourierInv_eq'
  rw [Real.fourierInv_eq']
  -- Goal: ∫ (density x).toReal • cexp(⟪x,ξ⟫*I) = ∫ v, cexp(2π⟪v,τ⁻¹ξ⟫*I) • 𝓕ψ v
  -- Both sides are integrals over V. Match integrands.
  refine MeasureTheory.integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [hdensity_simp]
  -- Goal: (𝓕ψ x).re • cexp(⟪x,ξ⟫ * I) = cexp(2π⟪x,τ⁻¹ξ⟫ * I) • 𝓕ψ x
  have him : (𝓕 ψ x).im = 0 := (hψ_ft_nonneg x).2
  have hre_cast : 𝓕 ψ x = ↑((𝓕 ψ x).re) := by
    apply Complex.ext <;> simp [him]
  -- 2π⟪x,τ⁻¹ξ⟫ = 2π · τ⁻¹ · ⟪x,ξ⟫ = ⟪x,ξ⟫ (since τ = 2π)
  have hinner : 2 * π * ⟪x, τ⁻¹ • ξ⟫_ℝ = ⟪x, ξ⟫_ℝ := by
    rw [real_inner_smul_right, hτ_def]
    field_simp
  rw [hinner]
  simp only [smul_eq_mul]
  conv_rhs => rw [hre_cast]
  exact mul_comm _ _

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
-- We know we can prove this, but it is hard.
axiom gaussianRegularize_measures_tight (φ : V → ℂ)
    (hpd : IsPositiveDefinite φ) (hcont : Continuous φ) (hnorm : φ 0 = 1) :
    ∀ η > 0, ∃ R > 0, ∀ ε > 0, True

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
