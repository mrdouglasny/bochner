import Bochner.Sazonov
import Bochner.PositiveDefinite
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open MeasureTheory Complex Filter Topology Set InnerProductSpace Function
open scoped Real FourierTransform

/-! # TestFubini

Auxiliary Fubini lemmas for Gaussian regularization, including Fubini identities for
characteristic functions and second moment bounds on quadratic forms.
-/

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V]

private abbrev gaussDensity (σ : ℝ) (x : V) : ℝ :=
  Real.exp (-(1 / (2 * σ ^ 2)) * ‖x‖ ^ 2)

private lemma gaussDensity_nonneg (σ : ℝ) (x : V) : 0 ≤ gaussDensity σ x :=
  Real.exp_nonneg _

private lemma gaussDensity_integrable (σ : ℝ) (hσ : 0 < σ) :
    Integrable (gaussDensity σ) (volume : Measure V) := by
  set b : ℝ := 1 / (2 * σ ^ 2)
  have hb : 0 < b := by positivity
  have hcint : Integrable (fun x : V => cexp (-(b : ℂ) * ↑(‖x‖ ^ 2))) := by
    have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (show 0 < ((b : ℂ)).re by simp [hb]) (0 : ℂ) (0 : V)
    simp at this; convert this using 1; ext x; simp [Complex.ofReal_pow]
  have heq : gaussDensity (V := V) σ = fun x => ‖cexp (-(b : ℂ) * ↑(‖x‖ ^ 2))‖ := by
    ext x; unfold gaussDensity; rw [Complex.norm_exp]; congr 1
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]; ring
  rw [heq]; exact hcint.norm

private lemma gaussDensity_integral_pos (σ : ℝ) (hσ : 0 < σ) :
    0 < ∫ x : V, gaussDensity σ x := by
  apply integral_pos_of_integrable_nonneg_nonzero (x := 0)
    (by unfold gaussDensity; fun_prop : Continuous (gaussDensity (V := V) σ))
    (gaussDensity_integrable σ hσ)
    (fun x => gaussDensity_nonneg σ x)
    (ne_of_gt (Real.exp_pos _))

/-- The Gaussian integral with an exponential phase equals C * exp(-σ²‖y‖²/2). -/
private lemma gaussian_fourier_eq (σ : ℝ) (hσ : 0 < σ) (y : V) :
    ∫ x : V, (gaussDensity σ x : ℂ) * cexp (↑(@inner ℝ V _ y x) * I) =
    ↑(∫ x : V, gaussDensity σ x) * cexp (-(σ ^ 2 * ‖y‖ ^ 2 / 2 : ℝ)) := by
  set b : ℝ := 1 / (2 * σ ^ 2) with hb_def
  have hb : 0 < b := by positivity
  have hb_re : 0 < ((b : ℂ)).re := by simp [hb]
  set n := Module.finrank ℝ V
  have step1 : (∫ x : V, (gaussDensity σ x : ℂ) * cexp (↑(@inner ℝ V _ y x) * I)) =
      ∫ x : V, cexp (-(b : ℂ) * ‖x‖ ^ 2 + I * ↑⟪y, x⟫_ℝ) := by
    congr 1; ext x
    rw [Complex.ofReal_exp, mul_comm (↑⟪y, x⟫_ℝ) I, ← exp_add]
    congr 1
    rw [show (-(1 / (2 * σ ^ 2)) * ‖x‖ ^ 2 : ℝ) = -b * ‖x‖ ^ 2 from by rw [hb_def]]
    push_cast; ring
  rw [step1, GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb_re I y]
  congr 1
  · have hgd : (∫ x : V, gaussDensity σ x) = (π / b) ^ ((n : ℝ) / 2) := by
      rw [show (∫ x : V, gaussDensity σ x) = ∫ x : V, Real.exp (-b * ‖x‖ ^ 2) from by
        congr 1]
      exact GaussianFourier.integral_rexp_neg_mul_sq_norm hb
    rw [hgd, ← Complex.ofReal_natCast n, ← Complex.ofReal_ofNat 2,
      ← Complex.ofReal_div, ← Complex.ofReal_div]
    exact (Complex.ofReal_cpow (le_of_lt (by positivity : (0 : ℝ) < π / b)) _).symm
  · congr 1; rw [I_sq]
    rw [show (b : ℂ) = 1 / (2 * (σ : ℂ) ^ 2) from by rw [hb_def]; push_cast; ring]
    push_cast; field_simp; ring

/-! ## Integrability helpers -/

private lemma exp_neg_sq_integrable_prob (μ : ProbabilityMeasure V) (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun y : V => Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2))) μ.toMeasure := by
  apply (integrable_const (1 : ℝ)).mono'
    (by fun_prop : Continuous (fun y : V =>
      Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2)))).aestronglyMeasurable
  filter_upwards with y
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  rw [← Real.exp_zero]
  exact Real.exp_le_exp_of_le (by nlinarith [sq_nonneg σ, sq_nonneg ‖y‖])

private lemma cexp_neg_sq_integrable_prob (μ : ProbabilityMeasure V) (σ : ℝ) (_hσ : 0 < σ) :
    Integrable (fun y : V => cexp (-(σ ^ 2 * ‖y‖ ^ 2 / 2 : ℝ))) μ.toMeasure := by
  have : (fun y : V => cexp (-(σ ^ 2 * ‖y‖ ^ 2 / 2 : ℝ))) =
      fun y => (Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2)) : ℂ) := by
    ext y; rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
  rw [this]
  exact (exp_neg_sq_integrable_prob μ σ ‹_›).ofReal

private lemma gaussDensity_mul_charFun_re_integrable (μ : ProbabilityMeasure V)
    (φ : V → ℂ) (hφ : ∀ t, charFun μ.toMeasure t = φ t) (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun x : V => gaussDensity σ x * (φ x).re) volume := by
  have heq : (fun x => gaussDensity σ x * (φ x).re) =
      fun x => gaussDensity σ x * (charFun μ.toMeasure x).re := by
    ext x; rw [hφ]
  rw [heq]
  apply Integrable.mono' (gaussDensity_integrable σ hσ)
    (((by fun_prop : Measurable (gaussDensity (V := V) σ)).mul
      (Measurable.re measurable_charFun)).aestronglyMeasurable)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussDensity_nonneg σ x)]
  exact mul_le_of_le_one_right (gaussDensity_nonneg σ x)
    (abs_re_le_norm _ |>.trans (norm_charFun_le_one (μ := μ.toMeasure) x))

private lemma gaussDensity_mul_charFun_integrable (μ : ProbabilityMeasure V)
    (φ : V → ℂ) (hφ : ∀ t, charFun μ.toMeasure t = φ t) (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun x : V => (gaussDensity σ x : ℂ) * φ x) volume := by
  have heq : (fun x => (gaussDensity σ x : ℂ) * φ x) =
      fun x => (gaussDensity σ x : ℂ) * charFun μ.toMeasure x := by
    ext x; rw [hφ]
  rw [heq]
  apply Integrable.mono' (gaussDensity_integrable σ hσ)
    ((Complex.measurable_ofReal.comp (by fun_prop : Measurable (gaussDensity (V := V) σ))
      |>.mul measurable_charFun).aestronglyMeasurable)
  filter_upwards with x
  simp only [Function.comp_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gaussDensity_nonneg σ x)]
  exact mul_le_of_le_one_right (gaussDensity_nonneg σ x)
    (norm_charFun_le_one (μ := μ.toMeasure) x)

/-! ## Fubini identity -/

/-- Fubini identity for Gaussian averaging. -/
private lemma fubini_gaussian_charFun'
    (μ : ProbabilityMeasure V) (φ : V → ℂ)
    (hφ : ∀ t, charFun μ.toMeasure t = φ t) (σ : ℝ) (hσ : 0 < σ) :
    ∫ y, (1 - Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2))) ∂μ.toMeasure =
    (∫ x : V, gaussDensity σ x)⁻¹ *
      ∫ x : V, gaussDensity σ x * (1 - (φ x).re) := by
  set C := ∫ x : V, gaussDensity σ x
  have hC_pos : 0 < C := gaussDensity_integral_pos σ hσ
  have hC_ne : C ≠ 0 := ne_of_gt hC_pos
  have hexp_int := exp_neg_sq_integrable_prob μ σ hσ
  have hcexp_int := cexp_neg_sq_integrable_prob μ σ hσ
  have hgdre_int := gaussDensity_mul_charFun_re_integrable μ φ hφ σ hσ
  have hgdphi_int := gaussDensity_mul_charFun_integrable μ φ hφ σ hσ
  -- Key identity: C * ∫_μ exp(-σ²‖y‖²/2) = ∫ gD(x) * Re(φ(x))
  -- Proved via complex Fubini + taking Re
  suffices key : C * ∫ y, Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2)) ∂μ.toMeasure =
      ∫ x, gaussDensity σ x * (φ x).re by
    -- LHS = 1 - ∫ exp(-) via integral_sub
    rw [integral_sub (integrable_const 1) hexp_int]
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    -- RHS: C⁻¹ * ∫ gD * (1 - Re(φ)) = 1 - C⁻¹ * ∫ gD Re(φ)
    rw [show (fun x : V => gaussDensity σ x * (1 - (φ x).re)) =
      (fun x => gaussDensity σ x - gaussDensity σ x * (φ x).re) from by ext x; ring]
    rw [integral_sub (gaussDensity_integrable σ hσ) hgdre_int,
      mul_sub, inv_mul_cancel₀ hC_ne]
    -- Goal: 1 - ∫ exp(-) = 1 - C⁻¹ * ∫ gD Re(φ)
    congr 1
    rw [← key, ← mul_assoc, inv_mul_cancel₀ hC_ne, one_mul]
  -- Prove key via complex Fubini
  -- Product integrability
  have norm_bound : ∀ y x : V,
      ‖(gaussDensity σ x : ℂ) * cexp (↑⟪y, x⟫_ℝ * I)‖ = gaussDensity σ x := by
    intro y x
    rw [norm_mul, Complex.norm_real, Complex.norm_exp,
      show (↑⟪y, x⟫_ℝ * I : ℂ).re = 0 from by simp [Complex.mul_re], Real.exp_zero,
      mul_one, Real.norm_eq_abs, abs_of_nonneg (gaussDensity_nonneg σ x)]
  have hprod : Integrable (uncurry (fun (y : V) (x : V) =>
      (gaussDensity σ x : ℂ) * cexp (↑⟪y, x⟫_ℝ * I)))
      (μ.toMeasure.prod volume) := by
    rw [integrable_prod_iff
      (by fun_prop : Continuous (uncurry fun (y : V) (x : V) =>
        (↑(gaussDensity σ x) : ℂ) * cexp (↑⟪y, x⟫_ℝ * I))).aestronglyMeasurable]
    constructor
    · filter_upwards with y
      apply Integrable.mono' (gaussDensity_integrable σ hσ)
        (by fun_prop : Continuous (fun x : V =>
          (↑(gaussDensity σ x) : ℂ) * cexp (↑⟪y, x⟫_ℝ * I))).aestronglyMeasurable
      filter_upwards with x
      rw [norm_bound]
    · have : (fun y : V => ∫ x, ‖uncurry (fun (y : V) (x : V) =>
            (gaussDensity σ x : ℂ) * cexp (↑⟪y, x⟫_ℝ * I)) (y, x)‖ ∂volume) =
          fun _ => ∫ x : V, gaussDensity σ x := by
        ext y; congr 1; ext x
        simp only [Function.uncurry_apply_pair, norm_bound]
      rw [this]; exact integrable_const _
  have fubini := integral_integral_swap hprod
  -- LHS of fubini = ↑C * ∫_μ cexp(-(σ²‖y‖²/2))
  have lhs_eq : ∫ y, (∫ x, (gaussDensity σ x : ℂ) * cexp (↑⟪y, x⟫_ℝ * I)) ∂μ.toMeasure =
      ↑C * ∫ y, cexp (-(σ ^ 2 * ‖y‖ ^ 2 / 2 : ℝ)) ∂μ.toMeasure := by
    rw [← integral_const_mul]; congr 1; ext y; exact gaussian_fourier_eq σ hσ y
  -- RHS of fubini = ∫ ↑(gD x) * φ(x)
  have rhs_eq : ∫ x, (∫ y, (gaussDensity σ x : ℂ) * cexp (↑⟪y, x⟫_ℝ * I) ∂μ.toMeasure) =
      ∫ x, (gaussDensity σ x : ℂ) * φ x := by
    congr 1; ext x; rw [integral_const_mul]; congr 1
    show ∫ y, cexp (↑⟪y, x⟫_ℝ * I) ∂μ.toMeasure = φ x
    rw [← hφ x]; rfl
  -- Combine: ↑C * ∫_μ cexp(-) = ∫ ↑(gD) * φ
  have key_complex : ↑C * ∫ y, cexp (-(σ ^ 2 * ‖y‖ ^ 2 / 2 : ℝ)) ∂μ.toMeasure =
      ∫ x, (gaussDensity σ x : ℂ) * φ x := by
    rw [← lhs_eq, fubini, rhs_eq]
  -- Helper: .re commutes with ∫ for ℂ-valued integrable functions
  have integral_re_eq : ∀ {f : V → ℂ} {ν : Measure V}, Integrable f ν →
      (∫ x, f x ∂ν).re = ∫ x, (f x).re ∂ν := by
    intro f ν hf
    exact (Complex.reCLM.integral_comp_comm hf).symm
  -- Take Re of key_complex to get key
  calc C * ∫ y, Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2)) ∂μ.toMeasure
      = (↑C * ∫ y, cexp (-(σ ^ 2 * ‖y‖ ^ 2 / 2 : ℝ)) ∂μ.toMeasure).re := by
        rw [re_ofReal_mul]; congr 1
        rw [integral_re_eq hcexp_int]
        congr 1; ext y
        rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.ofReal_re]
    _ = (∫ x, (gaussDensity σ x : ℂ) * φ x).re := by rw [key_complex]
    _ = ∫ x, gaussDensity σ x * (φ x).re := by
        rw [integral_re_eq hgdphi_int]
        congr 1; ext x; exact re_ofReal_mul _ _

/-! ## Gaussian second moment bound -/

/-- The real Gaussian integral formula as a function of parameter c.
    ∫ exp(-b‖x‖² + c⟪w,x⟫) = C * exp(c²‖w‖²/(4b)) where C = (π/b)^(n/2). -/
private lemma gaussian_real_formula (b : ℝ) (hb : 0 < b) (w : V) (c : ℝ) :
    ∫ x : V, Real.exp (-b * ‖x‖ ^ 2 + c * @inner ℝ V _ w x) =
    (∫ x : V, Real.exp (-b * ‖x‖ ^ 2)) * Real.exp (c ^ 2 * ‖w‖ ^ 2 / (4 * b)) := by
  -- Lift to ℂ via ofReal_inj, use ofRealLI.integral_comp_comm (no integrability needed)
  have hb_re : 0 < ((b : ℂ)).re := by simp [hb]
  rw [← Complex.ofReal_inj, Complex.ofReal_mul, Complex.ofReal_exp]
  -- Convert both real integrals to complex integrals
  have lift1 : (↑(∫ x : V, rexp (-b * ‖x‖ ^ 2 + c * ⟪w, x⟫_ℝ)) : ℂ) =
      ∫ x : V, cexp (-(b : ℂ) * ‖x‖ ^ 2 + ↑c * ↑⟪w, x⟫_ℝ) := by
    change ofRealLI (∫ x, _) = _
    rw [← ofRealLI.integral_comp_comm]
    congr 1; ext x; simp [ofRealLI, Complex.ofReal_exp]
  have lift0 : (↑(∫ x : V, rexp (-b * ‖x‖ ^ 2)) : ℂ) =
      ∫ x : V, cexp (-(b : ℂ) * ‖x‖ ^ 2) := by
    change ofRealLI (∫ x, _) = _
    rw [← ofRealLI.integral_comp_comm]
    congr 1; ext x; simp [ofRealLI, Complex.ofReal_exp]
  rw [lift1, lift0]
  -- Apply complex Gaussian formulas
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb_re (c : ℂ) w,
    GaussianFourier.integral_cexp_neg_mul_sq_norm hb_re]
  congr 1; push_cast; ring

/-! ### Helper: sinh(t) ≥ t for t ≥ 0 -/

private lemma id_le_sinh {t : ℝ} (ht : 0 ≤ t) : t ≤ Real.sinh t := by
  -- sinh(t) - t is nondecreasing on [0,∞) since (sinh - id)' = cosh - 1 ≥ 0
  have hmono : MonotoneOn (fun x => Real.sinh x - x) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (Real.continuous_sinh.sub continuous_id).continuousOn
    · intro x _
      exact ((Real.hasDerivAt_sinh x).sub (hasDerivAt_id x)).differentiableAt.differentiableWithinAt
    · intro x _
      have hd : HasDerivAt (fun y => Real.sinh y - y) (Real.cosh x - 1) x :=
        (Real.hasDerivAt_sinh x).sub (hasDerivAt_id x)
      rw [hd.deriv]
      linarith [Real.one_le_cosh x]
  have h0 : Real.sinh 0 - 0 = 0 := by simp [Real.sinh_zero]
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  linarith [h0]

private lemma half_sq_le_cosh_sub_one (x : ℝ) : x ^ 2 / 2 ≤ Real.cosh x - 1 := by
  -- cosh(x) - 1 = 2 sinh²(x/2) ≥ 2(x/2)² = x²/2
  -- Key identity: cosh(2t) = cosh²(t) + sinh²(t) = 2sinh²(t) + 1
  suffices key : (x / 2) ^ 2 ≤ Real.sinh (x / 2) ^ 2 by
    have h1 := Real.cosh_two_mul (x / 2)
    rw [show 2 * (x / 2) = x from by ring] at h1
    nlinarith [Real.cosh_sq (x / 2)]
  -- sinh(t)² ≥ t²: factor as (sinh t + t)(sinh t - t) ≥ 0
  set t := x / 2
  suffices h : 0 ≤ (Real.sinh t + t) * (Real.sinh t - t) by nlinarith [sq_sub_sq (Real.sinh t) t]
  by_cases ht : 0 ≤ t
  · -- t ≥ 0: both factors nonneg
    have h1 := id_le_sinh ht
    exact mul_nonneg (by linarith) (by linarith)
  · -- t < 0: both factors nonpos, product nonneg
    push_neg at ht
    have h1 : Real.sinh t ≤ t := by
      have := id_le_sinh (by linarith : 0 ≤ -t)
      rw [Real.sinh_neg] at this; linarith
    have h2 : Real.sinh t ≤ 0 := by
      have := id_le_sinh (by linarith : 0 ≤ -t)
      rw [Real.sinh_neg] at this; linarith
    have ha : Real.sinh t + t ≤ 0 := by linarith
    have hb : Real.sinh t - t ≤ 0 := by linarith
    exact mul_nonneg_of_nonpos_of_nonpos ha hb

/-- Integrability of gD * exp(c⟪w,x⟫). -/
private lemma gaussDensity_mul_exp_inner_integrable (σ : ℝ) (hσ : 0 < σ) (w : V) (c : ℝ) :
    Integrable (fun x : V => gaussDensity σ x * rexp (c * @inner ℝ V _ w x)) volume := by
  set b := 1 / (2 * σ ^ 2)
  have hb : 0 < b := by positivity
  have hb_re : 0 < ((b : ℂ)).re := by simp [hb]
  have hci := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb_re (c : ℂ) w
  rw [show (fun x : V => gaussDensity σ x * rexp (c * @inner ℝ V _ w x)) =
    fun x => rexp (-b * ‖x‖ ^ 2 + c * @inner ℝ V _ w x) from by
    ext x; unfold gaussDensity; rw [← Real.exp_add]]
  have : (fun x : V => rexp (-b * ‖x‖ ^ 2 + c * @inner ℝ V _ w x)) =
      fun x => ‖cexp (-(b : ℂ) * ‖x‖ ^ 2 + ↑c * ↑⟪w, x⟫_ℝ)‖ := by
    ext x; rw [Complex.norm_exp]
    congr 1
    have : (-(b : ℂ) * ↑‖x‖ ^ 2 + ↑c * ↑⟪w, x⟫_ℝ) = ↑(-b * ‖x‖ ^ 2 + c * ⟪w, x⟫_ℝ) := by
      push_cast; ring
    rw [this, Complex.ofReal_re]
  rw [this]; exact hci.norm

/-- ∫ gD * exp(c⟪w,x⟫) = C * exp(c²σ²‖w‖²/2). -/
private lemma gaussDensity_exp_inner_integral (σ : ℝ) (hσ : 0 < σ) (w : V) (c : ℝ) :
    ∫ x : V, gaussDensity σ x * rexp (c * @inner ℝ V _ w x) =
    (∫ x : V, gaussDensity σ x) * rexp (c ^ 2 * σ ^ 2 * ‖w‖ ^ 2 / 2) := by
  set b := 1 / (2 * σ ^ 2) with hb_def
  have hb : 0 < b := by positivity
  have h := gaussian_real_formula b hb w c
  have lhs_eq : (fun x : V => gaussDensity σ x * rexp (c * @inner ℝ V _ w x)) =
      fun x => rexp (-b * ‖x‖ ^ 2 + c * @inner ℝ V _ w x) := by
    ext x; unfold gaussDensity; rw [← Real.exp_add]
  have rhs_eq : c ^ 2 * σ ^ 2 * ‖w‖ ^ 2 / 2 = c ^ 2 * ‖w‖ ^ 2 / (4 * b) := by
    rw [hb_def]; field_simp; ring
  rw [lhs_eq, h, rhs_eq]

/-- The slope (exp(tA) - 1)/t → A as t → 0 from the right. -/
private lemma tendsto_exp_slope (A : ℝ) :
    Filter.Tendsto (fun t => (rexp (t * A) - 1) / t) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds A) := by
  have hd : HasDerivAt (fun t => rexp (t * A) - 1) A 0 := by
    have h1 : HasDerivAt (fun t => rexp (t * A)) A 0 := by
      have := (Real.hasDerivAt_exp (0 * A)).comp (0 : ℝ)
        ((hasDerivAt_id (0 : ℝ)).mul_const A)
      simp [zero_mul, Real.exp_zero] at this; exact this
    have h2 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 := hasDerivAt_const 0 1
    convert h1.sub h2 using 1 <;> simp
  have := hd.tendsto_slope_zero_right
  simp only [zero_add, zero_mul, Real.exp_zero, sub_self, sub_zero] at this
  exact this.congr fun t => by rw [smul_eq_mul, ← div_eq_inv_mul]

/-- Integrability of gD * cosh(c⟪w,x⟫). -/
private lemma gaussDensity_mul_cosh_integrable (σ : ℝ) (hσ : 0 < σ) (w : V) (c : ℝ) :
    Integrable (fun x : V => gaussDensity σ x * Real.cosh (c * @inner ℝ V _ w x)) volume := by
  have : (fun x : V => gaussDensity σ x * Real.cosh (c * @inner ℝ V _ w x)) =
      fun x => (gaussDensity σ x * rexp (c * @inner ℝ V _ w x) +
        gaussDensity σ x * rexp (-(c * @inner ℝ V _ w x))) / 2 := by
    ext x; rw [Real.cosh_eq]; ring
  rw [this]
  apply Integrable.div_const
  have : (fun x : V => gaussDensity σ x * rexp (c * @inner ℝ V _ w x) +
      gaussDensity σ x * rexp (-(c * @inner ℝ V _ w x))) =
    fun x => gaussDensity σ x * rexp (c * @inner ℝ V _ w x) +
      gaussDensity σ x * rexp ((-c) * @inner ℝ V _ w x) := by
    ext x; congr 1; congr 1; ring
  rw [this]
  exact (gaussDensity_mul_exp_inner_integrable σ hσ w c).add
    (gaussDensity_mul_exp_inner_integrable σ hσ w (-c))

/-- ∫ gD * cosh(c⟪w,x⟫) = C * exp(c²σ²‖w‖²/2). -/
private lemma gaussDensity_cosh_integral (σ : ℝ) (hσ : 0 < σ) (w : V) (c : ℝ) :
    ∫ x : V, gaussDensity σ x * Real.cosh (c * @inner ℝ V _ w x) =
    (∫ x : V, gaussDensity σ x) * rexp (c ^ 2 * σ ^ 2 * ‖w‖ ^ 2 / 2) := by
  have step1 : (fun x : V => gaussDensity σ x * Real.cosh (c * @inner ℝ V _ w x)) =
      fun x => (gaussDensity σ x * rexp (c * @inner ℝ V _ w x) +
        gaussDensity σ x * rexp (-(c * @inner ℝ V _ w x))) / 2 := by
    ext x; rw [Real.cosh_eq]; ring
  have hint_neg : Integrable (fun x : V => gaussDensity σ x *
      rexp (-(c * @inner ℝ V _ w x))) volume :=
    (gaussDensity_mul_exp_inner_integrable σ hσ w (-c)).congr
      (Eventually.of_forall fun x => by show _ = _; congr 1; ring)
  rw [step1, integral_div, integral_add
    (gaussDensity_mul_exp_inner_integrable σ hσ w c) hint_neg]
  have hrw : ∫ x : V, gaussDensity σ x * rexp (-(c * @inner ℝ V _ w x)) =
      ∫ x : V, gaussDensity σ x * rexp ((-c) * @inner ℝ V _ w x) :=
    integral_congr_ae (Eventually.of_forall fun x => by congr 1; ring)
  rw [gaussDensity_exp_inner_integral σ hσ w c, hrw,
    gaussDensity_exp_inner_integral σ hσ w (-c),
    show (-c) ^ 2 = c ^ 2 from by ring]; ring

/-- Integrability of gD * ⟪w,x⟫². -/
private lemma gaussDensity_mul_inner_sq_integrable (σ : ℝ) (hσ : 0 < σ) (w : V) :
    Integrable (fun x : V => gaussDensity σ x * (@inner ℝ V _ w x) ^ 2) volume := by
  apply ((gaussDensity_mul_cosh_integrable σ hσ w 1).const_mul 2).mono'
    (by fun_prop : AEStronglyMeasurable
      (fun x : V => gaussDensity σ x * (@inner ℝ V _ w x) ^ 2) volume)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussDensity_nonneg σ x)]
  show gaussDensity σ x * |(@inner ℝ V _ w x) ^ 2| ≤
    2 * (gaussDensity σ x * Real.cosh (1 * @inner ℝ V _ w x))
  rw [abs_of_nonneg (sq_nonneg _), one_mul]
  nlinarith [half_sq_le_cosh_sub_one (@inner ℝ V _ w x),
    Real.one_le_cosh (@inner ℝ V _ w x),
    gaussDensity_nonneg σ x, Real.cosh_pos (@inner ℝ V _ w x)]

private lemma gaussian_inner_sq_le (σ : ℝ) (hσ : 0 < σ) (w : V) :
    ∫ x : V, gaussDensity σ x * (@inner ℝ V _ w x) ^ 2 ≤
    (∫ x : V, gaussDensity σ x) * (σ ^ 2 * ‖w‖ ^ 2) := by
  set C := ∫ x : V, gaussDensity σ x
  set I := ∫ x : V, gaussDensity σ x * (@inner ℝ V _ w x) ^ 2
  set A := σ ^ 2 * ‖w‖ ^ 2 / 2 with hA_def
  have hC_pos : 0 < C := gaussDensity_integral_pos σ hσ
  -- Step 1: For all t > 0, I ≤ 2C * (exp(tA) - 1) / t
  have step1 : ∀ t : ℝ, 0 < t → I ≤ 2 * C * (rexp (t * A) - 1) / t := by
    intro t ht
    rw [le_div_iff₀ ht, mul_comm I t]
    set c := Real.sqrt t
    have hc : c ^ 2 = t := Real.sq_sqrt (le_of_lt ht)
    have htI : t * I = ∫ x : V, gaussDensity σ x * (c * @inner ℝ V _ w x) ^ 2 := by
      rw [show t = c ^ 2 from hc.symm, ← integral_const_mul]; congr 1; ext x; ring
    rw [htI]
    calc ∫ x, gaussDensity σ x * (c * @inner ℝ V _ w x) ^ 2
        ≤ ∫ x, gaussDensity σ x * (2 * (Real.cosh (c * @inner ℝ V _ w x) - 1)) := by
          apply integral_mono
            ((gaussDensity_mul_inner_sq_integrable σ hσ w).const_mul (c ^ 2) |>.congr
              (Eventually.of_forall fun x => by show _ = _; ring))
            ((gaussDensity_mul_cosh_integrable σ hσ w c).sub
              (gaussDensity_integrable σ hσ) |>.const_mul 2 |>.congr
              (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring))
            fun x => mul_le_mul_of_nonneg_left
              (by nlinarith [half_sq_le_cosh_sub_one (c * @inner ℝ V _ w x)])
              (gaussDensity_nonneg σ x)
      _ = 2 * C * (rexp (t * A) - 1) := by
          have step_a : ∫ x : V, gaussDensity σ x *
              (2 * (Real.cosh (c * @inner ℝ V _ w x) - 1)) =
              2 * ∫ x : V, (gaussDensity σ x * Real.cosh (c * @inner ℝ V _ w x) -
                gaussDensity σ x) := by
            rw [← integral_const_mul]; congr 1; ext x; ring
          rw [step_a, integral_sub (gaussDensity_mul_cosh_integrable σ hσ w c)
            (gaussDensity_integrable σ hσ), gaussDensity_cosh_integral σ hσ w c, hc]
          have : rexp (t * σ ^ 2 * ‖w‖ ^ 2 / 2) = rexp (t * A) := by
            congr 1; rw [hA_def]; ring
          rw [this]; ring
  -- Step 2: Upper bound → C * σ²‖w‖² = 2CA as t → 0+
  have step2 : Filter.Tendsto (fun t => 2 * C * (rexp (t * A) - 1) / t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (C * (σ ^ 2 * ‖w‖ ^ 2))) := by
    have htarget : C * (σ ^ 2 * ‖w‖ ^ 2) = 2 * C * A := by rw [hA_def]; ring
    rw [htarget]
    have : (fun t => 2 * C * (rexp (t * A) - 1) / t) =
        (fun t => 2 * C * ((rexp (t * A) - 1) / t)) := by ext t; ring
    rw [this]
    exact (tendsto_exp_slope A).const_mul (2 * C)
  -- Step 3: Conclude via le_of_tendsto
  exact ge_of_tendsto step2 (eventually_nhdsWithin_of_forall fun t ht => step1 t ht)

private lemma gaussian_quadForm_integral_le'
    (σ : ℝ) (hσ : 0 < σ)
    (S : V →L[ℝ] V) (hS : S.IsPositive)
    (T : ℝ) (_hT : 0 ≤ T)
    (h_trace : ∀ (ι : Type*) [Fintype ι] (b : OrthonormalBasis ι ℝ V),
      ∑ i, @inner ℝ V _ (b i) (S (b i)) ≤ T) :
    (∫ x : V, gaussDensity σ x)⁻¹ *
      ∫ x : V, gaussDensity σ x * quadForm S x ≤ σ ^ 2 * T := by
  set C := ∫ x : V, gaussDensity σ x
  have hC_pos : 0 < C := gaussDensity_integral_pos σ hσ
  set n := Module.finrank ℝ V
  -- Spectral decomposition
  have hLPos : (S : V →ₗ[ℝ] V).IsPositive := hS.toLinearMap
  have hSym := hLPos.isSymmetric
  set b := hSym.eigenvectorBasis rfl
  set ev := hSym.eigenvalues rfl
  have hevnonneg : ∀ i, 0 ≤ ev i := hLPos.nonneg_eigenvalues rfl
  -- Key: ⟪x, Sx⟫ = ∑ᵢ λᵢ * ⟪b i, x⟫²
  have hinner : ∀ (i : Fin n) (x : V),
      @inner ℝ V _ (b i) ((S : V →ₗ[ℝ] V) x) = ev i * @inner ℝ V _ (b i) x := by
    intro i x
    have := hSym.eigenvectorBasis_apply_self_apply rfl x i
    rwa [b.repr_apply_apply, b.repr_apply_apply] at this
  have hqf : ∀ x : V, quadForm S x = ∑ i, ev i * (@inner ℝ V _ (b i) x) ^ 2 := by
    intro x; show @inner ℝ V _ x (S x) = _
    conv_lhs => rw [show (S : V →L[ℝ] V) x = (S : V →ₗ[ℝ] V) x from rfl]
    rw [← b.sum_inner_mul_inner x ((S : V →ₗ[ℝ] V) x)]
    congr 1; ext i; rw [hinner, real_inner_comm x (b i)]; ring
  -- Integrate: ∫ gD * quadForm S = ∑ᵢ λᵢ * ∫ gD * ⟪b i, ·⟫²
  have hint_eq : ∫ x, gaussDensity σ x * quadForm S x =
      ∑ i, ev i * ∫ x, gaussDensity σ x * (@inner ℝ V _ (b i) x) ^ 2 := by
    simp_rw [hqf, Finset.mul_sum]
    rw [integral_finset_sum]
    · congr 1; ext i; rw [← integral_const_mul]; congr 1; ext x; ring
    · intro i _
      exact (gaussDensity_mul_inner_sq_integrable σ hσ (b i)).const_mul (ev i) |>.congr
        (Eventually.of_forall fun x => by ring)
  -- Bound each term using gaussian_inner_sq_le with ‖b i‖ = 1
  have hbound : ∀ i, ∫ x : V, gaussDensity σ x * (@inner ℝ V _ (b i) x) ^ 2 ≤
      C * (σ ^ 2 * ‖b i‖ ^ 2) :=
    fun i => gaussian_inner_sq_le σ hσ (b i)
  have hnorm : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  -- Eigenvalue = ⟪b i, S(b i)⟫
  have heveq : ∀ i, ev i = @inner ℝ V _ (b i) (S (b i)) := by
    intro i
    have h := hinner i (b i)
    rw [real_inner_self_eq_norm_sq, hnorm i, one_pow, mul_one] at h
    exact h.symm
  -- Put it all together
  rw [hint_eq]
  have hbound' : ∀ i, ∫ x : V, gaussDensity σ x * (@inner ℝ V _ (b i) x) ^ 2 ≤
      C * σ ^ 2 := by
    intro i; have := hbound i; rw [hnorm i, one_pow, mul_one] at this; exact this
  calc C⁻¹ * ∑ i, ev i * ∫ x, gaussDensity σ x * (@inner ℝ V _ (b i) x) ^ 2
      ≤ C⁻¹ * ∑ i, ev i * (C * σ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hC_pos))
        exact Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hbound' i) (hevnonneg i)
    _ = σ ^ 2 * ∑ i, ev i := by
        trans C⁻¹ * ((C * σ ^ 2) * ∑ i, ev i)
        · congr 1; simp_rw [mul_comm (ev _) _]; rw [← Finset.mul_sum]
        · rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hC_pos), one_mul]
    _ = σ ^ 2 * ∑ i, @inner ℝ V _ (b i) (S (b i)) := by
        congr 1; exact Finset.sum_congr rfl fun i _ => heveq i
    _ ≤ σ ^ 2 * T := by
        -- h_trace quantifies over ι : Type*, which lives in universe u_2,
        -- but b is indexed by Fin n : Type 0. Reindex via ULift to bridge.
        have htrace : ∑ i : Fin n, @inner ℝ V _ (b i) (S (b i)) ≤ T := by
          have h := h_trace (ULift (Fin n)) (b.reindex Equiv.ulift.symm)
          simp only [OrthonormalBasis.reindex_apply, Equiv.symm_symm] at h
          rwa [Equiv.sum_comp Equiv.ulift
            (fun i => @inner ℝ V _ (b i) (S (b i)))] at h
        exact mul_le_mul_of_nonneg_left htrace (sq_nonneg σ)

end
