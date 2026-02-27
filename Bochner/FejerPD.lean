/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Bochner.PositiveDefinite
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Fourier transform of L¹ positive-definite functions is nonneg

We prove: for φ : V → ℂ continuous, integrable, and positive-definite on a
finite-dimensional real inner product space V, Re(𝓕φ(ξ)) ≥ 0 for all ξ.

## Proof strategy

For fixed ξ, note that ψ(x) = φ(x) · exp(-2πi⟨x,ξ⟩) is PD (Schur product of
φ and the PD function exp(2πi⟨·,-ξ⟩)), continuous, and integrable with
𝓕φ(ξ) = ∫ ψ. So it suffices to show Re(∫ ψ) ≥ 0 for any PD continuous L¹ ψ.

For R > 0, define J_R = (1/μ(B_R)) ∫∫_{B_R × B_R} ψ(x-y) dx dy.

**Step A**: Re(J_R) ≥ 0 because the double integral is approximated by
PD double sums (Riemann sums on V × V with PD structure).

**Step B**: By Fubini, J_R = ∫ ψ(v) · [μ(B_R ∩ (v+B_R))/μ(B_R)] dv.
The kernel → 1 pointwise and is bounded by 1, so DCT gives J_R → ∫ ψ.

**Step C**: ge_of_tendsto' gives Re(∫ ψ) ≥ 0.

## References

- Rudin, *Fourier Analysis on Groups*, Theorem 1.4.3
- Folland, *A Course in Abstract Harmonic Analysis*, §4.2, Lemma 4.8
-/

open MeasureTheory Complex Filter Topology BigOperators
open scoped Real FourierTransform InnerProductSpace

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-! ### Helper: exp(2πi⟨·,ξ⟩) is positive definite -/

/-- The exponential character x ↦ exp(2πi⟨x,ξ⟩) is positive definite.
    The PD sum equals |∑ cₖ exp(2πi⟨xₖ,ξ⟩)|². -/
private lemma isPositiveDefinite_exp_inner (ξ : V) :
    IsPositiveDefinite (fun x : V => cexp (2 * ↑π * ↑⟪x, ξ⟫_ℝ * I)) where
  hermitian x := by
    rw [starRingEnd_apply, star_def, ← Complex.exp_conj]
    congr 1
    have : (starRingEnd ℂ) (2 * ↑π * ↑⟪x, ξ⟫_ℝ * I) = 2 * ↑π * ↑⟪x, ξ⟫_ℝ * (-I) := by
      simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    rw [this, inner_neg_left, Complex.ofReal_neg]; ring
  nonneg m x c := by
    -- Show the sum equals |∑ cₖ exp(2πi⟨xₖ,ξ⟩)|² ≥ 0
    -- Use e_k = exp(-2πi⟨x_k,ξ⟩) so that conj(e_i)*e_j = exp(2πi⟨x_i-x_j,ξ⟩)
    set e := fun k : Fin m => cexp (-(2 * ↑π * ↑⟪x k, ξ⟫_ℝ * I))
    have halg : ∀ i j : Fin m,
        (starRingEnd ℂ) (c i) * c j * cexp (2 * ↑π * ↑⟪x i - x j, ξ⟫_ℝ * I) =
        (starRingEnd ℂ) (c i * e i) * (c j * e j) := by
      intro i j
      have : cexp (2 * ↑π * ↑⟪x i - x j, ξ⟫_ℝ * I) =
          (starRingEnd ℂ) (e i) * e j := by
        rw [← Complex.exp_conj, ← Complex.exp_add]
        congr 1
        simp only [map_neg, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
        rw [inner_sub_left, Complex.ofReal_sub]
        ring
      rw [this, map_mul, mul_mul_mul_comm]
    simp_rw [halg]
    -- Now sum = ∑ᵢ∑ⱼ conj(dᵢ)dⱼ = |∑ dₖ|² where dₖ = cₖeₖ
    set d := fun k => c k * e k
    rw [show ∑ i, ∑ j, (starRingEnd ℂ) (d i) * d j =
        (starRingEnd ℂ) (∑ k, d k) * ∑ k, d k from by
      rw [map_sum, Finset.sum_mul_sum]]
    rw [starRingEnd_apply, star_def, ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_nonneg]

/-! ### Step A: The PD double integral has nonneg real part -/

/-- The double integral of a PD function over S × S has nonneg real part. -/
private lemma pd_double_integral_re_nonneg (ψ : V → ℂ) (hpd : IsPositiveDefinite ψ)
    (hcont : Continuous ψ) (S : Set V) (hSmeas : MeasurableSet S)
    (hSbdd : Bornology.IsBounded S) :
    0 ≤ (∫ x in S, ∫ y in S, ψ (x - y)).re := by
  sorry

/-! ### Integral of PD function has nonneg real part -/

/-- The overlap ratio vol(B_R ∩ B_R(v)) / vol(B_R) for the Fejér average. -/
private def overlapRatio (R : ℝ) (v : V) : ℝ :=
  if (volume (Metric.closedBall (0 : V) R)).toReal = 0 then 0
  else (volume (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R)).toReal /
       (volume (Metric.closedBall (0 : V) R)).toReal

/-- The overlap ratio is between 0 and 1. -/
private lemma overlapRatio_le_one (R : ℝ) (v : V) : overlapRatio R v ≤ 1 := by
  unfold overlapRatio; split_ifs with h
  · exact zero_le_one
  · exact div_le_one_of_le₀
      (ENNReal.toReal_mono (ne_of_lt measure_closedBall_lt_top)
        (measure_mono Set.inter_subset_left))
      ENNReal.toReal_nonneg

/-- The overlap ratio is nonneg. -/
private lemma overlapRatio_nonneg (R : ℝ) (v : V) : 0 ≤ overlapRatio R v := by
  unfold overlapRatio; split_ifs
  · exact le_refl 0
  · exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- Ball containment: closedBall 0 (R - ‖v‖) ⊆ closedBall 0 R ∩ closedBall v R. -/
private lemma closedBall_sub_norm_subset (v : V) (R : ℝ) :
    Metric.closedBall (0 : V) (R - ‖v‖) ⊆
    Metric.closedBall (0 : V) R ∩ Metric.closedBall v R := by
  intro x hx
  simp only [Metric.mem_closedBall, dist_zero_right] at hx
  constructor
  · exact Metric.mem_closedBall.mpr (by rw [dist_zero_right]; linarith [norm_nonneg v])
  · refine Metric.mem_closedBall.mpr ?_
    have h1 : dist x v ≤ dist x 0 + dist 0 v := dist_triangle x 0 v
    simp only [dist_zero_right, dist_zero_left] at h1
    linarith

/-- The overlap ratio → 1 as R → ∞ for fixed v.
    Proof: closedBall 0 (R-‖v‖) ⊆ closedBall 0 R ∩ closedBall v R, so
    overlapRatio ≥ ((R-‖v‖)/R)^d → 1. Upper bound is 1. Squeeze. -/
private lemma overlapRatio_tendsto_one (v : V) :
    Filter.Tendsto (fun n : ℕ => overlapRatio (n : ℝ) v) Filter.atTop (nhds 1) := by
  -- Use squeeze: lower bound → 1, upper bound = 1
  set d := Module.finrank ℝ V
  apply Filter.Tendsto.squeeze'
    -- lower bound: ((n - ‖v‖) / n) ^ d → 1
    (show Filter.Tendsto (fun n : ℕ =>
        ((↑n - ‖v‖) / ↑n) ^ d) Filter.atTop (nhds 1) by
      have h : Filter.Tendsto (fun n : ℕ => (↑n - ‖v‖) / (↑n : ℝ)) Filter.atTop (nhds 1) := by
        have h1 : ∀ᶠ n : ℕ in Filter.atTop, (↑n - ‖v‖) / (↑n : ℝ) = 1 - ‖v‖ / ↑n := by
          filter_upwards [Filter.eventually_gt_atTop 0] with n hn; field_simp
        have hc : Filter.Tendsto (fun n : ℕ => ‖v‖ / (↑n : ℝ)) Filter.atTop (nhds 0) :=
          tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
        exact Tendsto.congr' (EventuallyEq.symm h1) (by simpa using Tendsto.sub tendsto_const_nhds hc)
      simpa using h.pow (n := d))
    -- upper bound: constant 1
    tendsto_const_nhds
    -- overlapRatio ≥ lower bound: closedBall 0 (n-‖v‖) ⊆ intersection,
    -- so ratio ≥ vol(B_{n-‖v‖})/vol(B_n) = ((n-‖v‖)/n)^d by Haar formula
    (by sorry)
    -- overlapRatio ≤ 1 (always)
    (Filter.Eventually.of_forall (fun n => overlapRatio_le_one (n : ℝ) v))

/-- Fubini identity: the averaged double integral equals ∫ ψ · overlapRatio. -/
private lemma fejer_avg_eq_integral (ψ : V → ℂ) (hcont : Continuous ψ)
    (hint : Integrable ψ) (R : ℝ) (hR : 0 < R) :
    (volume (Metric.closedBall (0 : V) R)).toReal⁻¹ •
      ∫ x in Metric.closedBall (0 : V) R,
        ∫ y in Metric.closedBall (0 : V) R, ψ (x - y) =
    ∫ v, (overlapRatio R v : ℂ) * ψ v := by
  sorry

/-- For a continuous integrable PD function ψ, Re(∫ ψ) ≥ 0.
    This is the core result: the Fejér-averaged double integral J_R converges
    to ∫ ψ and has Re ≥ 0 for each R. -/
private lemma pd_integral_re_nonneg (ψ : V → ℂ) (hpd : IsPositiveDefinite ψ)
    (hint : Integrable ψ) (hcont : Continuous ψ) :
    0 ≤ (∫ x, ψ x).re := by
  -- Define J_n = (1/vol(B_n)) ∬_{B_n×B_n} ψ(x-y) dx dy
  set J : ℕ → ℂ := fun n =>
    if n = 0 then ψ 0
    else (volume (Metric.closedBall (0 : V) (n : ℝ))).toReal⁻¹ •
      ∫ x in Metric.closedBall (0 : V) (n : ℝ),
        ∫ y in Metric.closedBall (0 : V) (n : ℝ), ψ (x - y) with hJ_def
  -- Re(J_n) ≥ 0 for each n
  have hnn : ∀ n : ℕ, 0 ≤ (J n).re := by
    intro n
    simp only [J]
    split_ifs with h
    · exact hpd.eval_zero_nonneg
    · rw [Complex.smul_re]
      apply mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      exact pd_double_integral_re_nonneg ψ hpd hcont _ measurableSet_closedBall
        Metric.isBounded_closedBall
  -- J_n → ∫ ψ via Fubini identity + DCT
  have hconv : Filter.Tendsto J Filter.atTop (nhds (∫ x, ψ x)) := by
    -- For n ≥ 1, J n = ∫ overlapRatio(n,v) * ψ(v) dv by Fubini
    -- overlapRatio → 1, |overlapRatio * ψ| ≤ |ψ|, so DCT gives J → ∫ ψ
    -- Rewrite goal: suffices that ∫ h_n · ψ → ∫ ψ where h_n → 1, |h_n| ≤ 1
    suffices h : Filter.Tendsto
        (fun n : ℕ => ∫ v, (overlapRatio (n : ℝ) v : ℂ) * ψ v)
        Filter.atTop (nhds (∫ x, ψ x)) by
      apply h.congr'
      filter_upwards [Filter.eventually_ne_atTop 0] with n hn
      simp only [J, if_neg hn]
      exact (fejer_avg_eq_integral ψ hcont hint n (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).symm
    -- Now apply DCT: h_n(v) * ψ(v) → 1 * ψ(v) = ψ(v), with bound |ψ|
    rw [show (∫ x, ψ x) = ∫ x, (1 : ℂ) * ψ x by simp]
    apply tendsto_integral_of_dominated_convergence (fun v => ‖ψ v‖)
    · intro n; exact sorry -- measurability of overlapRatio * ψ
    · exact hint.norm -- bound is integrable
    · intro n; filter_upwards with v
      rw [norm_mul, Complex.norm_real]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (abs_le.mpr ⟨by linarith [overlapRatio_nonneg (n : ℝ) v],
          overlapRatio_le_one (n : ℝ) v⟩)
    · filter_upwards with v
      have h1 := overlapRatio_tendsto_one v
      have h2 : Filter.Tendsto (fun n : ℕ => (overlapRatio (n : ℝ) v : ℂ))
          Filter.atTop (nhds (1 : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 1).comp h1
      exact h2.mul tendsto_const_nhds
  -- Conclude by ge_of_tendsto'
  exact ge_of_tendsto' ((Complex.continuous_re.tendsto _).comp hconv) hnn

/-! ### Step B + C: The main theorem -/

/-- The Fourier transform of a continuous integrable positive-definite function
    on a finite-dimensional real inner product space has nonneg real part. -/
theorem pd_l1_fourier_re_nonneg_theorem
    (φ : V → ℂ) (hpd : IsPositiveDefinite φ)
    (hint : Integrable φ) (hcont : Continuous φ)
    (ξ : V) : 0 ≤ (𝓕 φ ξ).re := by
  -- Step 1: 𝓕 φ ξ = ∫ v, φ v * exp(-2πi⟨v,ξ⟩)
  have hF : 𝓕 φ ξ = ∫ v, φ v * cexp (-(2 * ↑π * ↑⟪v, ξ⟫_ℝ * I)) := by
    show ∫ v, 𝐞 (-(innerSL ℝ v ξ)) • φ v = _
    congr 1; ext v
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm]
    congr 1; congr 1
    simp only [innerSL_apply_apply]; push_cast; ring
  rw [hF]
  -- Step 2: The integrand is ψ(v) where ψ = φ · exp(2πi⟨·,-ξ⟩) is PD
  have hψ_eq : (fun v => φ v * cexp (-(2 * ↑π * ↑⟪v, ξ⟫_ℝ * I))) =
      (fun v => φ v * cexp (2 * ↑π * ↑⟪v, -ξ⟫_ℝ * I)) := by
    ext v; congr 1; congr 1; rw [inner_neg_right, Complex.ofReal_neg]; ring
  rw [hψ_eq]
  have hψ_pd : IsPositiveDefinite (fun v => φ v * cexp (2 * ↑π * ↑⟪v, -ξ⟫_ℝ * I)) :=
    hpd.mul (isPositiveDefinite_exp_inner (-ξ))
  -- Step 3: ψ is continuous and integrable
  have hexp_cont : Continuous (fun v : V => cexp (2 * ↑π * ↑⟪v, -ξ⟫_ℝ * I)) :=
    Complex.continuous_exp.comp (((continuous_const.mul
      (continuous_ofReal.comp ((innerSL ℝ).flip (-ξ)).continuous)).mul continuous_const))
  have hψ_cont : Continuous (fun v => φ v * cexp (2 * ↑π * ↑⟪v, -ξ⟫_ℝ * I)) :=
    hcont.mul hexp_cont
  have hψ_int : Integrable (fun v => φ v * cexp (2 * ↑π * ↑⟪v, -ξ⟫_ℝ * I)) := by
    refine Integrable.mono hint hψ_cont.aestronglyMeasurable ?_
    filter_upwards with v
    rw [norm_mul]
    have : ‖cexp (2 * ↑π * ↑⟪v, -ξ⟫_ℝ * I)‖ = 1 := by
      have h : 2 * ↑π * ↑⟪v, -ξ⟫_ℝ * I = ↑(2 * π * ⟪v, -ξ⟫_ℝ) * I := by push_cast; ring
      rw [h, norm_exp_ofReal_mul_I]
    rw [this, mul_one]
  -- Step 4: Apply pd_integral_re_nonneg
  exact pd_integral_re_nonneg _ hψ_pd hψ_int hψ_cont

end
