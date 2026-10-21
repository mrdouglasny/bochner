/-
Copyright (c) 2026 Axiomatic AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michael R. Douglas
-/
module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.LinearAlgebra.Matrix.Circulant
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Minlos.Mathlib.MeasureTheory.Function.LpSpace.HilbertSchmidtIntegral
public import Bochner.Circulant
public import Minlos.Mathlib.MeasureTheory.Measure.Tight
public import Minlos.Mathlib.MeasureTheory.Measure.TightNormed
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Sazonov's theorem

**Sazonov's theorem** [Sazonov 1958][sazonov1958remark]: on a real Hilbert space `K`, `C : K → ℂ`
is the characteristic function of a Borel probability measure iff it is positive-definite,
`C 0 = 1`, and continuous at `0` for the Sazonov topology, the topology of the seminorms
`x ↦ ‖S x‖` with `S` Hilbert–Schmidt [Bogachev–Smolyanov, Def. 5.10.1][bogachev2017topological].
Such a seminorm is `(∑ₙ ⟪vₙ, x⟫²)^{1/2}` with `∑ₙ ‖vₙ‖² < ∞`
(`ContinuousLinearMap.isHilbertSchmidt_iff_exists_hasSum_norm_sq`), which is the form used here:
`1 - Re C x ≤ ε + ∑ₙ ⟪vₙ, x⟫²`. Norm continuity is not enough: `e^{-‖x‖²/2}` is no characteristic
function when `K` is infinite-dimensional.

Existence (`MeasureTheory.exists_isProbabilityMeasure_charFun_eq_of_sazonov`) needs no
separability and no Hilbert basis. The spans `Fₙ` of the first `n` Sazonov vectors, over the scales
`ε = 1 / (k + 1)`, are nested and finite-dimensional; Bochner's theorem gives on each a probability
measure with characteristic function `C`, whose image in `K` has characteristic function
`C ∘ Pₙ → C`. These measures are tight by flat concentration
(`MeasureTheory.isTightMeasureSet_iff_forall_exists_finiteDimensional`): their mass at distance
`> δ` from `Fₙ₀` is controlled by averaging `1 - Re C` against a Gaussian
(`MeasureTheory.measure_one_le_norm_le_of_charFun`, Gel'fand–Vilenkin's Lemma 4 with Gaussian in
place of spherical averages [Gel'fand–Vilenkin, IV, Ch. IV, §2.3][gelfand1964generalized4];
[Bogachev–Smolyanov, Thm 5.11.4][bogachev2017topological]). A limit point given by Prokhorov's
theorem has characteristic function `C`; it is tight, by the portmanteau theorem, hence Radon, and
so unique (`MeasureTheory.Measure.ext_of_charFun_of_innerRegular`) although `K` need not be
separable. Necessity (`MeasureTheory.exists_one_sub_re_charFun_le`):
outside a ball `1 - cos ≤ 2`, inside `1 - cos t ≤ t²`, and the second-moment form of a measure
with finite second moment is trace class (`MeasureTheory.exists_hasSum_integral_inner_sq`).

## Main results

* `MeasureTheory.exists_isProbabilityMeasure_charFun_eq_iff_sazonov`: Sazonov's theorem
* `MeasureTheory.exists_isProbabilityMeasure_charFun_eq_comp`: Minlos' theorem between Hilbert
  spaces, `φ ∘ T` for `T` Hilbert–Schmidt
* `MeasureTheory.measure_one_le_norm_le_of_charFun`: the Gaussian concentration bound
* `MeasureTheory.exists_hasSum_integral_inner_sq`: second-moment forms are trace class

## Provenance

Ported from or4nge19/QuantumlibCore `pin-v4.34.1` `9a741c08`,
`QuantumlibCore/ToMathlib/MeasureTheory/Measure/CharacteristicFunction/Sazonov.lean` (Lean v4.34.1,
Mathlib `d13f23b7`), with module paths renamed; notices kept.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Filter Topology Matrix Metric
open scoped RealInnerProductSpace ENNReal ComplexOrder

namespace ProbabilityTheory

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-- The standard Gaussian has covariance the inner product: `∫ ⟪w, z⟫² dγ(z) = ‖w‖²`. -/
theorem integral_inner_sq_stdGaussian (w : W) :
    ∫ z, ⟪w, z⟫ ^ 2 ∂stdGaussian W = ‖w‖ ^ 2 := by
  have h := variance_dual_stdGaussian (innerSL ℝ w)
  rw [variance_of_integral_eq_zero (innerSL ℝ w).continuous.aemeasurable
    (integral_strongDual_stdGaussian _), innerSL_apply_norm] at h
  simpa [innerSL_apply_apply] using h

end ProbabilityTheory

namespace MeasureTheory

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-- **Parseval's identity for a Gaussian**: averaging `charFun ν` against the standard Gaussian
pushed forward by `A†` integrates its characteristic function `e^{-‖A t‖²/2}` against `ν`. -/
theorem integral_charFun_adjoint_stdGaussian (ν : Measure V) [IsFiniteMeasure ν] (A : V →L[ℝ] W) :
    ∫ z, charFun ν (ContinuousLinearMap.adjoint A z) ∂stdGaussian W =
      ∫ t, cexp (-‖A t‖ ^ 2 / 2) ∂ν := by
  simp_rw [charFun_apply, ContinuousLinearMap.adjoint_inner_right]
  rw [integral_integral_swap]
  · refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
    dsimp only
    rw [← charFun_stdGaussian, charFun_apply]
    simp_rw [real_inner_comm]
  · refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (ae_of_all _ fun p ↦ ?_)
    · exact (Continuous.aestronglyMeasurable (by fun_prop))
    · exact (Complex.norm_exp_ofReal_mul_I _).le

/-- **The Gaussian concentration bound**: if `1 - Re ν̂ ≤ ε + ∑ₙ ⟪vₙ, ·⟫²`, then
`ν {‖A t‖ ≥ 1} ≤ 3 (ε + ∑ₙ ‖A vₙ‖²)`. By Parseval, `∫ (1 - e^{-‖A t‖²/2}) dν` is the average of
`1 - Re ν̂ ∘ A†` over the standard Gaussian, whose second moments are `‖A vₙ‖²`; then Markov. -/
theorem measure_one_le_norm_le_of_charFun {ν : Measure V} [IsProbabilityMeasure ν] {ε : ℝ}
    {v : ℕ → V} (hv : Summable fun n ↦ ‖v n‖ ^ 2)
    (hν : ∀ t, 1 - (charFun ν t).re ≤ ε + ∑' n, ⟪v n, t⟫ ^ 2) (A : V →L[ℝ] W) :
    ν {t | 1 ≤ ‖A t‖} ≤ ENNReal.ofReal (3 * (ε + ∑' n, ‖A (v n)‖ ^ 2)) := by
  set γ := stdGaussian W
  have hε : 0 ≤ ε := by simpa [charFun_zero] using hν 0
  have hAv : Summable fun n ↦ ‖A (v n)‖ ^ 2 :=
    (hv.mul_left (‖A‖ ^ 2)).of_nonneg_of_le (fun n ↦ by positivity) fun n ↦ by
      rw [← mul_pow]; gcongr; exact A.le_opNorm _
  have hF : Integrable (Function.uncurry fun (z : W) (t : V) ↦ cexp (⟪A t, z⟫ * I)) (γ.prod ν) :=
    Integrable.mono' (integrable_const (1 : ℝ)) (Continuous.aestronglyMeasurable (by fun_prop))
      (ae_of_all _ fun p ↦ (Complex.norm_exp_ofReal_mul_I _).le)
  have hφ : Integrable (fun z ↦ charFun ν (ContinuousLinearMap.adjoint A z)) γ := by
    simp_rw [charFun_apply, ContinuousLinearMap.adjoint_inner_right]
    exact hF.integral_prod_left
  set f : V → ℝ := fun t ↦ 1 - Real.exp (-‖A t‖ ^ 2 / 2) with hf
  set g : W → ℝ := fun z ↦ 1 - (charFun ν (ContinuousLinearMap.adjoint A z)).re with hg
  have hexp_int : Integrable (fun t ↦ Real.exp (-‖A t‖ ^ 2 / 2)) ν :=
    Integrable.mono' (integrable_const (1 : ℝ)) (Continuous.aestronglyMeasurable (by fun_prop))
      (ae_of_all _ fun t ↦ by
        rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
        exact Real.exp_le_one_iff.2 (by nlinarith [norm_nonneg (A t)]))
  have hfi : Integrable f ν := (integrable_const _).sub hexp_int
  have hφre : Integrable (fun z ↦ (charFun ν (ContinuousLinearMap.adjoint A z)).re) γ := hφ.re
  have hgi : Integrable g γ := (integrable_const _).sub hφre
  -- Parseval: `∫ f dν = ∫ g dγ`
  have hfg : ∫ t, f t ∂ν = ∫ z, g z ∂γ := by
    have h := congrArg Complex.re (integral_charFun_adjoint_stdGaussian ν A)
    have hexp : ∀ t, cexp (-(‖A t‖ : ℂ) ^ 2 / 2) = ((Real.exp (-‖A t‖ ^ 2 / 2) : ℝ) : ℂ) :=
      fun t ↦ by rw [Complex.ofReal_exp]; push_cast; ring_nf
    simp_rw [hexp, integral_complex_ofReal, Complex.ofReal_re] at h
    have hre : ∫ z, (charFun ν (ContinuousLinearMap.adjoint A z)).re ∂γ =
        (∫ z, charFun ν (ContinuousLinearMap.adjoint A z) ∂γ).re := by
      simpa only [RCLike.re_to_complex] using integral_re hφ
    simp only [hf, hg]
    rw [integral_sub (integrable_const _) hφre, hre, h, integral_sub (integrable_const _) hexp_int]
    simp
  -- the Sazonov bound, averaged against the Gaussian
  have hg_le : ∫ z, g z ∂γ ≤ ε + ∑' n, ‖A (v n)‖ ^ 2 := by
    have hsq : ∀ n, Integrable (fun z ↦ ⟪A (v n), z⟫ ^ 2) γ := fun n ↦
      ((innerSL ℝ (A (v n))).comp_memLp' IsGaussian.memLp_two_id).integrable_sq
    have hsum : ∀ z : W, Summable fun n ↦ ⟪A (v n), z⟫ ^ 2 := fun z ↦
      (hAv.mul_right (‖z‖ ^ 2)).of_nonneg_of_le (fun n ↦ sq_nonneg _) fun n ↦ by
        rw [← mul_pow, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
    have hg0 : ∀ z, 0 ≤ g z := fun z ↦ sub_nonneg.2 <|
      (Complex.re_le_norm _).trans (norm_charFun_le_one _)
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity),
      ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hg0)]
    calc ∫⁻ z, ENNReal.ofReal (g z) ∂γ
        ≤ ∫⁻ z, (ENNReal.ofReal ε + ∑' n, ENNReal.ofReal (⟪A (v n), z⟫ ^ 2)) ∂γ := by
          refine lintegral_mono fun z ↦ ?_
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ sq_nonneg _) (hsum z),
            ← ENNReal.ofReal_add hε (tsum_nonneg fun n ↦ sq_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h := hν (ContinuousLinearMap.adjoint A z)
          simp_rw [ContinuousLinearMap.adjoint_inner_right] at h
          exact h
      _ = ENNReal.ofReal ε + ∑' n, ∫⁻ z, ENNReal.ofReal (⟪A (v n), z⟫ ^ 2) ∂γ := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_tsum fun n ↦ (Measurable.ennreal_ofReal (by fun_prop)).aemeasurable]
      _ = ENNReal.ofReal ε + ∑' n, ENNReal.ofReal (‖A (v n)‖ ^ 2) := by
          congr 1
          refine tsum_congr fun n ↦ ?_
          rw [← ofReal_integral_eq_lintegral_ofReal (hsq n) (ae_of_all _ fun z ↦ sq_nonneg _),
            integral_inner_sq_stdGaussian]
      _ = ENNReal.ofReal (ε + ∑' n, ‖A (v n)‖ ^ 2) := by
          rw [ENNReal.ofReal_add hε (tsum_nonneg fun n ↦ sq_nonneg _),
            ENNReal.ofReal_tsum_of_nonneg (fun n ↦ sq_nonneg _) hAv]
  -- Markov, with `1 - e^{-1/2} ≥ 1/3`
  set c := 1 - Real.exp (-1 / 2) with hc
  have hc3 : 1 / 3 ≤ c := by
    have h1 := Real.add_one_le_exp (1 / 2)
    have h2 : Real.exp (-1 / 2) * Real.exp (1 / 2) = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-1 / 2)]
  have hsub : {t | 1 ≤ ‖A t‖} ⊆ {t | c ≤ f t} := fun t (ht : 1 ≤ ‖A t‖) ↦ by
    change 1 - Real.exp (-1 / 2) ≤ 1 - Real.exp (-‖A t‖ ^ 2 / 2)
    gcongr
    nlinarith
  have hM := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun t ↦ sub_nonneg.2 <|
    Real.exp_le_one_iff.2 (by nlinarith [norm_nonneg (A t)])) hfi c
  rw [hfg] at hM
  calc ν {t | 1 ≤ ‖A t‖} ≤ ν {t | c ≤ f t} := measure_mono hsub
    _ = ENNReal.ofReal (ν.real {t | c ≤ f t}) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (3 * (ε + ∑' n, ‖A (v n)‖ ^ 2)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have h0 : 0 ≤ ν.real {t | c ≤ f t} := measureReal_nonneg
      nlinarith

section Sazonov

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [MeasurableSpace K] [BorelSpace K]

/-- **Sazonov's theorem, existence**: a positive-definite `C` with `C 0 = 1` and
`1 - Re C ≤ ε + ∑ₙ ⟪vₙ, ·⟫²` for every `ε > 0` (`∑ₙ ‖vₙ‖² < ∞`) is a characteristic function. -/
theorem exists_isProbabilityMeasure_charFun_eq_of_sazonov {C : K → ℂ}
    (hC : (circulant C).PosSemidef) (h0 : C 0 = 1)
    (hS : ∀ ε > 0, ∃ v : ℕ → K, Summable (fun n ↦ ‖v n‖ ^ 2) ∧
      ∀ x, 1 - (C x).re ≤ ε + ∑' n, ⟪v n, x⟫ ^ 2) :
    ∃ μ : Measure K, IsProbabilityMeasure μ ∧ μ.InnerRegular ∧ charFun μ = C := by
  -- Sazonov vectors at the scales `1 / (k + 1)`
  choose v hv hCv using fun k : ℕ ↦ hS (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat
  have hsq : ∀ k x n, ⟪v k n, x⟫ ^ 2 ≤ ‖v k n‖ ^ 2 * ‖x‖ ^ 2 := fun k x n ↦ by
    rw [← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
  have hsum : ∀ k x, Summable fun n ↦ ⟪v k n, x⟫ ^ 2 := fun k x ↦
    ((hv k).mul_right (‖x‖ ^ 2)).of_nonneg_of_le (fun n ↦ sq_nonneg _) (hsq k x)
  have hsumle : ∀ k x, ∑' n, ⟪v k n, x⟫ ^ 2 ≤ (∑' n, ‖v k n‖ ^ 2) * ‖x‖ ^ 2 := fun k x ↦ by
    rw [← tsum_mul_right]
    exact (hsum k x).tsum_le_tsum (hsq k x) ((hv k).mul_right _)
  have hre : ∀ x, (C x).re ≤ 1 := fun x ↦
    (Complex.re_le_norm _).trans (by simpa [h0] using hC.circulant_norm_le x)
  -- `C` is continuous
  have hcont : Continuous C := by
    refine hC.circulant_continuous ?_
    rw [ContinuousAt, h0, Complex.one_re]
    refine tendsto_order.2 ⟨fun a ha ↦ ?_,
      fun a ha ↦ Eventually.of_forall fun x ↦ (hre x).trans_lt ha⟩
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (by linarith : (0 : ℝ) < (1 - a) / 2)
    have hq : Tendsto (fun x : K ↦ (∑' n, ‖v k n‖ ^ 2) * ‖x‖ ^ 2) (𝓝 0) (𝓝 0) := by
      have : Continuous fun x : K ↦ (∑' n, ‖v k n‖ ^ 2) * ‖x‖ ^ 2 := by fun_prop
      simpa using this.tendsto 0
    filter_upwards [hq.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < (1 - a) / 2))] with x hx
    linarith [hCv k x, hsumle k x]
  -- the nested subspaces `F n` spanned by the first `n` Sazonov vectors
  set u : ℕ → K := fun p ↦ v p.unpair.1 p.unpair.2 with hu
  set F : ℕ → Submodule ℝ K := fun n ↦ Submodule.span ℝ (u '' Set.Iio n) with hF
  have hFd : ∀ n, FiniteDimensional ℝ (F n) := fun n ↦
    FiniteDimensional.span_of_finite ℝ ((Set.finite_Iio n).image u)
  have hFmono : Monotone F := fun m n hmn ↦
    Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio hmn))
  have hvF : ∀ k m, ∀ᶠ n in atTop, v k m ∈ F n := fun k m ↦ eventually_atTop.2
    ⟨Nat.pair k m + 1, fun n hn ↦ Submodule.subset_span
      ⟨Nat.pair k m, by simp only [Set.mem_Iio]; omega, by simp [hu]⟩⟩
  -- Bochner's theorem on each `F n`
  have hB : ∀ n, ∃ ν : Measure (F n), IsProbabilityMeasure ν ∧ charFun ν = fun f : F n ↦ C f :=
    fun n ↦ exists_isProbabilityMeasure_charFun_eq_iff.2 ⟨hcont.comp continuous_subtype_val,
      hC.circulant_comp (F n).subtype.toAddMonoidHom, by simpa using h0⟩
  choose ν hνp hνC using hB
  -- their images `μ n` on `K`, with characteristic functions `C ∘ Pₙ`
  set μ : ℕ → Measure K := fun n ↦ (ν n).map Subtype.val with hμ
  have hμp : ∀ n, IsProbabilityMeasure (μ n) := fun n ↦ by
    have := hνp n
    change IsProbabilityMeasure ((ν n).map Subtype.val)
    infer_instance
  have hμC : ∀ n x, charFun (μ n) x = C ((F n).starProjection x) := fun n x ↦ by
    rw [charFun_apply, integral_map measurable_subtype_coe.aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop))]
    simp_rw [← Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    rw [← charFun_apply, hνC n]
    rfl
  -- `C (Pₙ x) → C x`
  have hconv : ∀ x, Tendsto (fun n ↦ C ((F n).starProjection x)) atTop (𝓝 (C x)) := by
    intro x
    have htail : ∀ k, Tendsto (fun n ↦ ∑' m, ⟪v k m, (F n).starProjection x - x⟫ ^ 2) atTop
        (𝓝 0) := by
      intro k
      simpa using tendsto_tsum_of_dominated_convergence (g := fun _ ↦ (0 : ℝ))
        (bound := fun m ↦ ‖v k m‖ ^ 2 * ‖x‖ ^ 2) ((hv k).mul_right _)
        (fun m ↦ tendsto_const_nhds.congr' <| by
          filter_upwards [hvF k m] with n hn
          rw [inner_sub_right, ← Submodule.inner_starProjection_left_eq_right,
            (Submodule.starProjection_eq_self_iff).2 hn, sub_self, zero_pow two_ne_zero])
        (Eventually.of_forall fun n m ↦ by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          refine (hsq k _ m).trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
          have h := Submodule.norm_sq_eq_add_norm_sq_starProjection x (F n)
          rw [Submodule.starProjection_orthogonal_val] at h
          rw [norm_sub_rev]
          nlinarith [sq_nonneg ‖(F n).starProjection x‖])
    refine Metric.tendsto_atTop.2 fun η hη ↦ ?_
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (by positivity : (0 : ℝ) < η ^ 2 / 4)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (htail k) (η ^ 2 / 4) (by positivity)
    refine ⟨N, fun n hn ↦ ?_⟩
    have h1 := hC.circulant_norm_sub_sq_le ((F n).starProjection x) x
    have h2 := hCv k ((F n).starProjection x - x)
    have h3 := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun _ ↦ sq_nonneg _)] at h3
    rw [h0, Complex.one_re, Complex.sub_re, Complex.one_re] at h1
    rw [dist_eq_norm]
    refine lt_of_pow_lt_pow_left₀ 2 hη.le ?_
    nlinarith
  -- the Sazonov bound for `ν n`, with the projected vectors
  have hνS : ∀ (k n : ℕ) (f : F n), 1 - (charFun (ν n) f).re ≤
      1 / ((k : ℝ) + 1) + ∑' m, ⟪(F n).orthogonalProjectionOnto (v k m), f⟫ ^ 2 := by
    intro k n f
    rw [hνC n]
    simp_rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
    exact hCv k f
  have hvP : ∀ k n, Summable fun m ↦ ‖(F n).orthogonalProjectionOnto (v k m)‖ ^ 2 := fun k n ↦
    (hv k).of_nonneg_of_le (fun m ↦ sq_nonneg _) fun m ↦
      pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_orthogonalProjectionOnto_apply_le _ _) 2
  have hreal : ∀ ε : ℝ≥0∞, 0 < ε → ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal η ≤ ε := fun ε hε ↦ by
    obtain ⟨r, -, hr0, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    exact ⟨r, ENNReal.ofReal_pos.1 hr0, hrε.le⟩
  -- tightness, by flat concentration
  have htight : IsTightMeasureSet (Set.range μ) := by
    rw [isTightMeasureSet_iff_forall_exists_finiteDimensional (𝕜 := ℝ)]
    refine ⟨fun ε hε ↦ ?_, fun δ hδ ε hε ↦ ?_⟩
    · obtain ⟨η, hη0, hηε⟩ := hreal ε hε
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (by positivity : (0 : ℝ) < η / 6)
      set τ := ∑' m, ‖v k m‖ ^ 2 with hτ
      have hτ0 : 0 ≤ τ := tsum_nonneg fun _ ↦ sq_nonneg _
      set R := 6 * τ / η + 1 with hR
      have hR1 : 1 ≤ R := by rw [hR]; linarith [div_nonneg (by positivity : 0 ≤ 6 * τ) hη0.le]
      refine ⟨R, ?_⟩
      rintro _ ⟨n, rfl⟩
      rw [Measure.map_apply measurable_subtype_coe
        (measurableSet_lt measurable_const measurable_norm)]
      set A : F n →L[ℝ] F n := R⁻¹ • ContinuousLinearMap.id ℝ (F n)
      have hA : ∀ f : F n, ‖A f‖ = R⁻¹ * ‖f‖ := fun f ↦ by
        rw [_root_.smul_apply, ContinuousLinearMap.id_apply, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.2 (by linarith))]
      calc ν n (Subtype.val ⁻¹' {x | R < ‖x‖}) ≤ ν n {f | 1 ≤ ‖A f‖} := measure_mono fun f hf ↦ by
            simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hf ⊢
            rw [hA, ← Submodule.norm_coe, le_inv_mul_iff₀ (by linarith), mul_one]
            exact hf.le
        _ ≤ ENNReal.ofReal (3 * (1 / ((k : ℝ) + 1) +
            ∑' m, ‖A ((F n).orthogonalProjectionOnto (v k m))‖ ^ 2)) :=
          measure_one_le_norm_le_of_charFun (hvP k n) (hνS k n) A
        _ ≤ ENNReal.ofReal η := by
          refine ENNReal.ofReal_le_ofReal ?_
          simp_rw [hA, mul_pow]
          rw [tsum_mul_left]
          have hle : ∑' m, ‖(F n).orthogonalProjectionOnto (v k m)‖ ^ 2 ≤ τ :=
            (hvP k n).tsum_le_tsum (fun m ↦ pow_le_pow_left₀ (norm_nonneg _)
              (Submodule.norm_orthogonalProjectionOnto_apply_le _ _) 2) (hv k)
          have hRτ : R⁻¹ ^ 2 * τ ≤ η / 6 := by
            rw [inv_pow, inv_mul_le_iff₀ (by positivity)]
            have : 6 * τ / η ≤ R := by rw [hR]; linarith
            rw [div_le_iff₀ hη0] at this
            nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ R⁻¹ ^ 2)]
        _ ≤ ε := hηε
    · obtain ⟨η, hη0, hηε⟩ := hreal ε hε
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (by positivity : (0 : ℝ) < η / 6)
      -- `‖w - P w‖ ≤ ‖w‖`
      have hPle : ∀ (U : Submodule ℝ K) [U.HasOrthogonalProjection] (w : K),
          ‖w - U.starProjection w‖ ≤ ‖w‖ := fun U _ w ↦ by
        have h := Submodule.norm_sq_eq_add_norm_sq_starProjection w U
        rw [Submodule.starProjection_orthogonal_val] at h
        nlinarith [sq_nonneg ‖U.starProjection w‖, norm_nonneg (w - U.starProjection w),
          norm_nonneg w]
      -- the tails of the `k`-th Sazonov vectors vanish
      have hτ : Tendsto (fun n₀ ↦ ∑' m, ‖v k m - (F n₀).starProjection (v k m)‖ ^ 2) atTop
          (𝓝 0) := by
        simpa using tendsto_tsum_of_dominated_convergence (g := fun _ ↦ (0 : ℝ))
          (bound := fun m ↦ ‖v k m‖ ^ 2) (hv k)
          (fun m ↦ tendsto_const_nhds.congr' <| by
            filter_upwards [hvF k m] with n hn
            rw [(Submodule.starProjection_eq_self_iff).2 hn, sub_self, norm_zero,
              zero_pow two_ne_zero])
          (Eventually.of_forall fun n m ↦ by
            rw [Real.norm_of_nonneg (sq_nonneg _)]
            exact pow_le_pow_left₀ (norm_nonneg _) (hPle _ _) 2)
      obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
        (hτ.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < δ ^ 2 * (η / 6))))
      refine ⟨F n₀, hFd n₀, ?_⟩
      rintro _ ⟨n, rfl⟩
      rw [Measure.map_apply measurable_subtype_coe isClosed_cthickening.measurableSet.compl]
      rcases le_total n n₀ with hn | hn
      · -- `F n ≤ F n₀`: no mass outside the thickening
        have : Subtype.val ⁻¹' (cthickening δ (F n₀ : Set K))ᶜ = (∅ : Set (F n)) := by
          ext f
          simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
            not_not]
          exact self_subset_cthickening _ (hFmono hn f.2)
        rw [this, measure_empty]
        exact bot_le
      -- `F n₀ ≤ F n`: the distance to `F n₀` is `‖(1 - Pₙ₀) f‖`, a norm on `F n`
      have hsub : ∀ w ∈ F n, w - (F n₀).starProjection w ∈ F n := fun w hw ↦
        (F n).sub_mem hw (hFmono hn (Submodule.starProjection_apply_mem _ _))
      set A : F n →L[ℝ] F n := δ⁻¹ • ((F n).orthogonalProjectionOnto ∘L
        (ContinuousLinearMap.id ℝ K - (F n₀).starProjection) ∘L (F n).subtypeL)
      have hA : ∀ f : F n, ‖A f‖ = δ⁻¹ * ‖(f : K) - (F n₀).starProjection f‖ := fun f ↦ by
        rw [_root_.smul_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hδ.le)]
        simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
          _root_.sub_apply, ContinuousLinearMap.id_apply]
        rw [Submodule.norm_orthogonalProjectionOnto_apply _ (hsub _ f.2)]
      calc ν n (Subtype.val ⁻¹' (cthickening δ (F n₀ : Set K))ᶜ) ≤ ν n {f | 1 ≤ ‖A f‖} :=
            measure_mono fun f hf ↦ by
              simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq] at hf ⊢
              rw [hA, le_inv_mul_iff₀ hδ, mul_one]
              by_contra! h
              exact hf (mem_cthickening_of_dist_le _ _ _ _
                (Submodule.starProjection_apply_mem _ _) (by rw [dist_eq_norm]; exact h.le))
        _ ≤ ENNReal.ofReal (3 * (1 / ((k : ℝ) + 1) +
            ∑' m, ‖A ((F n).orthogonalProjectionOnto (v k m))‖ ^ 2)) :=
          measure_one_le_norm_le_of_charFun (hvP k n) (hνS k n) A
        _ ≤ ENNReal.ofReal η := by
          refine ENNReal.ofReal_le_ofReal ?_
          -- `‖A (Pₙ v)‖ = δ⁻¹ ‖Pₙ (v - Pₙ₀ v)‖ ≤ δ⁻¹ ‖v - Pₙ₀ v‖`
          have hAv : ∀ m, ‖A ((F n).orthogonalProjectionOnto (v k m))‖ ^ 2 ≤
              δ⁻¹ ^ 2 * ‖v k m - (F n₀).starProjection (v k m)‖ ^ 2 := fun m ↦ by
            rw [hA, mul_pow]
            refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
              (sq_nonneg _)
            have hcomp := congrArg (fun T ↦ T (v k m))
              (Submodule.starProjection_comp_starProjection_of_le (hFmono hn))
            simp only [ContinuousLinearMap.comp_apply] at hcomp
            rw [← Submodule.starProjection_apply, hcomp]
            calc ‖(F n).starProjection (v k m) - (F n₀).starProjection (v k m)‖
                = ‖(F n).starProjection (v k m - (F n₀).starProjection (v k m))‖ := by
                  rw [map_sub, (Submodule.starProjection_eq_self_iff).2
                    (hFmono hn (Submodule.starProjection_apply_mem _ _))]
              _ ≤ _ := Submodule.norm_starProjection_apply_le _ _
          have hsum' : Summable fun m ↦ ‖v k m - (F n₀).starProjection (v k m)‖ ^ 2 :=
            (hv k).of_nonneg_of_le (fun m ↦ sq_nonneg _) fun m ↦
              pow_le_pow_left₀ (norm_nonneg _) (hPle _ _) 2
          have hle : ∑' m, ‖A ((F n).orthogonalProjectionOnto (v k m))‖ ^ 2 ≤
              δ⁻¹ ^ 2 * ∑' m, ‖v k m - (F n₀).starProjection (v k m)‖ ^ 2 := by
            rw [← tsum_mul_left]
            exact ((hsum'.mul_left _).of_nonneg_of_le (fun m ↦ sq_nonneg _) hAv).tsum_le_tsum
              hAv (hsum'.mul_left _)
          have h1 := hn₀ n₀ le_rfl
          have h2 : δ⁻¹ ^ 2 * ∑' m, ‖v k m - (F n₀).starProjection (v k m)‖ ^ 2 ≤ η / 6 := by
            rw [inv_pow, inv_mul_le_iff₀ (by positivity)]
            linarith
          nlinarith
        _ ≤ ε := hηε
  -- Prokhorov: a limit point along an ultrafilter finer than `atTop`
  set P : ℕ → ProbabilityMeasure K := fun n ↦ ⟨μ n, hμp n⟩ with hP
  have hcomp : IsCompact (closure (Set.range P)) := by
    refine isCompact_closure_of_isTightMeasureSet ?_
    convert htight
    ext μ'
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨P n, ⟨n, rfl⟩, rfl⟩
  set U := Ultrafilter.of (atTop : Filter ℕ)
  obtain ⟨μ₀, -, hμ₀ : Tendsto P U (𝓝 μ₀)⟩ := hcomp.ultrafilter_le_nhds (U.map P)
    (.trans (by simp) (monotone_principal subset_closure))
  -- the limit is tight, `Kᶜ` being open (portmanteau), hence Radon
  have hμ₀t : IsTightMeasureSet {(μ₀ : Measure K)} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight ⊢
    intro ε hε
    obtain ⟨L, hL, hLε⟩ := htight ε hε
    refine ⟨L, hL, ?_⟩
    rintro _ rfl
    exact (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ₀ hL.isClosed.isOpen_compl).trans
      (Filter.liminf_le_of_frequently_le' (Eventually.frequently
        (Eventually.of_forall fun n ↦ hLε _ ⟨n, rfl⟩)))
  refine ⟨μ₀, inferInstance, innerRegular_of_isTightMeasureSet_singleton hμ₀t,
    funext fun x ↦ tendsto_nhds_unique ?_
    (((hconv x).mono_left (Ultrafilter.of_le _)).congr fun n ↦ (hμC n x).symm)⟩
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hμ₀
    (BoundedContinuousFunction.innerProbChar x)
  simpa [hP, charFun_eq_integral_innerProbChar] using h

/-- **The second-moment form of a measure with finite second moment is trace class**:
`∫ ⟪y, x⟫² dρ(y) = ∑ₙ ⟪vₙ, x⟫²` with `∑ₙ ‖vₙ‖² < ∞`, the square of the Hilbert–Schmidt operator
`x ↦ ⟪·, x⟫` into `L²(ρ)`. No separability: `id` need not be strongly measurable. -/
theorem exists_hasSum_integral_inner_sq {ρ : Measure K}
    (hρ : Integrable (fun y ↦ ‖y‖ ^ 2) ρ) :
    ∃ v : ℕ → K, Summable (fun n ↦ ‖v n‖ ^ 2) ∧
      ∀ x, HasSum (fun n ↦ ⟪v n, x⟫ ^ 2) (∫ y, ⟪y, x⟫ ^ 2 ∂ρ) := by
  obtain ⟨S, hS, hSk⟩ := ContinuousLinearMap.exists_isHilbertSchmidt_of_kernel (𝕜 := ℝ)
    (κ := id) (μ := ρ) (fun k ↦ (continuous_id.inner continuous_const).aestronglyMeasurable) hρ
  obtain ⟨v, hv, hSv⟩ := S.isHilbertSchmidt_iff_exists_hasSum_norm_sq.1 hS
  refine ⟨v, hv, fun x ↦ ?_⟩
  have h := hSv x
  simp only [Real.norm_eq_abs, sq_abs] at h
  convert h using 1
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ((hSk x).mono fun y hy ↦ ?_)
  simp only [hy, id, RCLike.inner_apply, conj_trivial, sq]

/-- **Sazonov's theorem, necessity**: a characteristic function satisfies
`1 - Re μ̂ ≤ ε + ∑ₙ ⟪vₙ, ·⟫²`, `∑ₙ ‖vₙ‖² < ∞`. Outside a ball of mass `< ε / 2`, `1 - cos ≤ 2`;
inside it, `1 - cos t ≤ t²` integrates to the trace-class second-moment form of the restriction. -/
theorem exists_one_sub_re_charFun_le (μ : Measure K) [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ℕ → K, Summable (fun n ↦ ‖v n‖ ^ 2) ∧
      ∀ x, 1 - (charFun μ x).re ≤ ε + ∑' n, ⟪v n, x⟫ ^ 2 := by
  -- a ball carrying all but `ε / 2` of the mass
  have htend : Tendsto (fun n : ℕ ↦ μ {y | (n : ℝ) < ‖y‖}) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun n : ℕ ↦ {y : K | (n : ℝ) < ‖y‖})
      (fun n ↦ (measurableSet_lt measurable_const measurable_norm).nullMeasurableSet)
      (fun m n hmn y (hy : (n : ℝ) < ‖y‖) ↦ lt_of_le_of_lt (by exact_mod_cast hmn) hy)
      ⟨0, measure_ne_top _ _⟩
    have hempty : ⋂ n : ℕ, {y : K | (n : ℝ) < ‖y‖} = ∅ := by
      ext y
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall,
        not_lt]
      obtain ⟨n, hn⟩ := exists_nat_ge ‖y‖
      exact ⟨n, hn⟩
    rwa [hempty, measure_empty] at h
  obtain ⟨N, hN⟩ := (htend.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (half_pos hε)))).exists
  set R : ℝ := (N : ℝ)
  set B := {y : K | ‖y‖ ≤ R} with hB
  have hBm : MeasurableSet B := measurableSet_le measurable_norm measurable_const
  have hBc : MeasurableSet Bᶜ := hBm.compl
  have hμBc : μ.real Bᶜ < ε / 2 := by
    have : Bᶜ = {y | R < ‖y‖} := by ext; simp [hB]
    rw [this, measureReal_def]
    exact ENNReal.toReal_lt_of_lt_ofReal hN
  -- the restriction to the ball has a trace-class second-moment form
  have hρ : Integrable (fun y ↦ ‖y‖ ^ 2) (μ.restrict B) :=
    Integrable.mono' (integrable_const (R ^ 2)) (by fun_prop)
      ((ae_restrict_iff' hBm).2 (ae_of_all _ fun y (hy : ‖y‖ ≤ R) ↦ by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) hy 2))
  obtain ⟨v, hv, hvx⟩ := exists_hasSum_integral_inner_sq hρ
  refine ⟨v, hv, fun x ↦ ?_⟩
  rw [(hvx x).tsum_eq]
  -- `1 - Re φ̂ = ∫ (1 - cos ⟪y, x⟫)`, split along the ball
  have hre : (charFun μ x).re = ∫ y, Real.cos ⟪y, x⟫ ∂μ := by
    rw [charFun_apply, ← RCLike.re_to_complex, ← integral_re]
    · simp [Complex.exp_ofReal_mul_I_re]
    · exact Integrable.mono' (integrable_const (1 : ℝ))
        (Continuous.aestronglyMeasurable (by fun_prop))
        (ae_of_all _ fun y ↦ (Complex.norm_exp_ofReal_mul_I _).le)
  have hcos : Integrable (fun y ↦ Real.cos ⟪y, x⟫) μ :=
    Integrable.mono' (integrable_const (1 : ℝ)) (Continuous.aestronglyMeasurable (by fun_prop))
      (ae_of_all _ fun y ↦ Real.abs_cos_le_one _)
  have hsq : Integrable (fun y ↦ ⟪y, x⟫ ^ 2) (μ.restrict B) :=
    Integrable.mono' (hρ.mul_const (‖x‖ ^ 2)) (by fun_prop) (ae_of_all _ fun y ↦ by
      rw [Real.norm_of_nonneg (sq_nonneg _), ← mul_pow, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2)
  calc 1 - (charFun μ x).re = ∫ y, (1 - Real.cos ⟪y, x⟫) ∂μ := by
        rw [hre, integral_sub (integrable_const _) hcos, integral_const, probReal_univ, one_smul]
    _ = ∫ y in B, (1 - Real.cos ⟪y, x⟫) ∂μ + ∫ y in Bᶜ, (1 - Real.cos ⟪y, x⟫) ∂μ :=
        (integral_add_compl hBm ((integrable_const _).sub hcos)).symm
    _ ≤ ∫ y in B, ⟪y, x⟫ ^ 2 ∂μ + ∫ y in Bᶜ, (2 : ℝ) ∂μ :=
        add_le_add
          (setIntegral_mono ((integrable_const _).sub hcos).integrableOn hsq fun y ↦ by
            nlinarith [Real.one_sub_sq_div_two_le_cos (x := ⟪y, x⟫), sq_nonneg ⟪y, x⟫])
          (setIntegral_mono ((integrable_const _).sub hcos).integrableOn
            (integrable_const (2 : ℝ)).integrableOn fun y ↦ by
              linarith [Real.neg_one_le_cos ⟪y, x⟫])
    _ ≤ ε + ∫ y in B, ⟪y, x⟫ ^ 2 ∂μ := by
        rw [setIntegral_const, smul_eq_mul]
        linarith

/-- **Sazonov's theorem**: on a real Hilbert space, `C` is the characteristic function of a
probability measure iff it is positive-definite, `C 0 = 1`, and `1 - Re C` is dominated, up to any
`ε > 0`, by a trace-class quadratic form `∑ₙ ⟪vₙ, x⟫²`, `∑ₙ ‖vₙ‖² < ∞`: continuity at `0` for the
Sazonov topology. No separability is assumed. The measure can be taken Radon
(`MeasureTheory.exists_isProbabilityMeasure_charFun_eq_of_sazonov`), and is then unique
(`MeasureTheory.Measure.ext_of_charFun_of_innerRegular`). -/
theorem exists_isProbabilityMeasure_charFun_eq_iff_sazonov {C : K → ℂ} :
    (∃ μ : Measure K, IsProbabilityMeasure μ ∧ charFun μ = C) ↔
      (circulant C).PosSemidef ∧ C 0 = 1 ∧ ∀ ε > 0, ∃ v : ℕ → K,
        Summable (fun n ↦ ‖v n‖ ^ 2) ∧ ∀ x, 1 - (C x).re ≤ ε + ∑' n, ⟪v n, x⟫ ^ 2 :=
  ⟨fun ⟨μ, _, hμ⟩ ↦ hμ ▸ ⟨posSemidef_circulant_charFun μ, by simp [charFun_zero],
    fun _ hε ↦ exists_one_sub_re_charFun_le μ hε⟩,
    fun ⟨hC, h0, hS⟩ ↦
      let ⟨μ, hμ, _, hμC⟩ := exists_isProbabilityMeasure_charFun_eq_of_sazonov hC h0 hS
      ⟨μ, hμ, hμC⟩⟩

/-- **Minlos' theorem between Hilbert spaces** [Gel'fand–Vilenkin, IV, Ch. IV, §2.3,
Thm 4][gelfand1964generalized4]: a positive-definite `φ` with `φ 0 = 1` and real part continuous at
`0`, composed with a Hilbert–Schmidt map `T`, is a characteristic function. Gel'fand–Vilenkin ask
`T` nuclear. -/
theorem exists_isProbabilityMeasure_charFun_eq_comp {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {φ : H → ℂ} (hφ : (circulant φ).PosSemidef)
    (h0 : φ 0 = 1) (hc : ContinuousAt (fun y ↦ (φ y).re) 0) {T : K →L[ℝ] H}
    (hT : T.IsHilbertSchmidt) :
    ∃ μ : Measure K, IsProbabilityMeasure μ ∧ μ.InnerRegular ∧ charFun μ = φ ∘ T := by
  refine exists_isProbabilityMeasure_charFun_eq_of_sazonov
    (hφ.circulant_comp T.toLinearMap.toAddMonoidHom) (by simpa using h0) fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.1 hc ε hε
  obtain ⟨v, hv, hTv⟩ := T.isHilbertSchmidt_iff_exists_hasSum_norm_sq.1 hT
  refine ⟨fun n ↦ (√2 / δ) • v n, ?_, fun x ↦ ?_⟩
  · refine (hv.mul_left ((√2 / δ) ^ 2)).congr fun n ↦ ?_
    rw [norm_smul, mul_pow, Real.norm_of_nonneg (by positivity)]
  have hsum : ∑' n, ⟪(√2 / δ) • v n, x⟫ ^ 2 = 2 / δ ^ 2 * ‖T x‖ ^ 2 := by
    simp_rw [real_inner_smul_left, mul_pow, tsum_mul_left]
    rw [← (hTv x).tsum_eq, div_pow, Real.sq_sqrt zero_le_two]
    simp [Real.norm_eq_abs, sq_abs]
  have hre : 1 - (φ (T x)).re ≤ 2 := by
    have := (Complex.abs_re_le_norm (φ (T x))).trans
      (by simpa [h0] using hφ.circulant_norm_le (T x))
    linarith [abs_le.1 this]
  simp only [Function.comp_apply, hsum]
  rcases lt_or_ge ‖T x‖ δ with hx | hx
  · have := hδε (by rwa [dist_zero_right] : dist (T x) 0 < δ)
    rw [h0, Complex.one_re, Real.dist_eq, abs_sub_comm] at this
    have h2 : 0 ≤ 2 / δ ^ 2 * ‖T x‖ ^ 2 := by positivity
    linarith [(abs_lt.1 this).2]
  · have : 2 ≤ 2 / δ ^ 2 * ‖T x‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    linarith

end Sazonov

end MeasureTheory
