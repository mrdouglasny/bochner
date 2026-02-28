import Bochner.Sazonov
import Bochner.PositiveDefinite
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open MeasureTheory Complex Filter Topology Set InnerProductSpace
open scoped Real FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-! ## Sazonov Continuity -/

/-- Sazonov continuity at 0: for every ε > 0, there exists a positive trace-class
    operator S such that ⟪x, Sx⟫ < 1 implies |1 - φ(x)| < ε. -/
def SazonovContinuousAt (φ : H → ℂ) :=
  ∀ ε > 0, ∃ S : SazonovIndex H,
    ∀ x : H, quadForm S.op x < 1 → ‖1 - φ x‖ < ε

/-! ## Finite-Dimensional Marginals -/

/-- For a family v : Fin n → H, the marginal function
    φ_v(t) = φ(∑ i, t i • v i). -/
def marginalFun (φ : H → ℂ) {n : ℕ} (v : Fin n → H) :
    EuclideanSpace ℝ (Fin n) → ℂ :=
  fun t => φ (∑ i, t i • v i)

omit [CompleteSpace H] in
/-- The marginal function of a PD function is PD. -/
lemma marginalFun_isPositiveDefinite (φ : H → ℂ) (hpd : IsPositiveDefinite φ)
    {n : ℕ} (v : Fin n → H) :
    IsPositiveDefinite (marginalFun φ v) := by
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] H := {
    toFun := fun t => ∑ i, t i • v i
    map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
    map_smul' := fun r x => by
      simp only [RingHom.id_apply]
      rw [Finset.smul_sum]
      congr 1; ext i
      simp [smul_smul, mul_comm r]
  }
  have key : marginalFun φ v = fun t => φ (T t) := by ext t; rfl
  rw [key]
  exact isPositiveDefinite_precomp_linear φ hpd T

/-! ## Tail Bound Algebra -/

/-- 1 - exp(-t) > 0 for t > 0. -/
lemma one_sub_exp_neg_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-t) := by
  have h1 : Real.exp (-t) < 1 := by
    calc Real.exp (-t) < Real.exp 0 := Real.exp_strictMono (by linarith)
      _ = 1 := Real.exp_zero
  linarith

/-- exp(-b) ≤ exp(-a) when a ≤ b. -/
lemma exp_neg_le_exp_neg {a b : ℝ} (hab : a ≤ b) :
    Real.exp (-b) ≤ Real.exp (-a) :=
  Real.exp_le_exp_of_le (neg_le_neg hab)

/-- The denominator 1 - exp(-R²/2) is positive for R > 0. -/
lemma one_sub_exp_half_sq_pos (R : ℝ) (hR : 0 < R) :
    0 < 1 - Real.exp (-(R ^ 2 / 2)) := by
  apply one_sub_exp_neg_pos; positivity

/-- Chebyshev/Markov bound with scaling: if ∫ (1 - exp(-σ²‖y‖²/2)) dμ ≤ C,
    then μ({‖y‖ ≥ R}) ≤ C / (1 - exp(-σ²R²/2)). -/
lemma tail_bound_from_exp_integral {V : Type*} [NormedAddCommGroup V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : ProbabilityMeasure V) (σ : ℝ) (hσ : 0 < σ)
    (C : ℝ) (_hC0 : 0 ≤ C)
    (hC : ∫ y, (1 - Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2))) ∂μ.toMeasure ≤ C)
    (R : ℝ) (hR : 0 < R) :
    (μ.toMeasure {y | R ≤ ‖y‖}).toReal ≤ C / (1 - Real.exp (-(σ ^ 2 * R ^ 2 / 2))) := by
  set δ := 1 - Real.exp (-(σ ^ 2 * R ^ 2 / 2)) with hδ_def
  have hδ_pos : 0 < δ := by
    rw [hδ_def]
    have : Real.exp (-(σ ^ 2 * R ^ 2 / 2)) < 1 := by
      calc Real.exp (-(σ ^ 2 * R ^ 2 / 2)) < Real.exp 0 :=
            Real.exp_strictMono (by linarith [show 0 < σ ^ 2 * R ^ 2 / 2 from by positivity])
        _ = 1 := Real.exp_zero
    linarith
  set A := {y : V | R ≤ ‖y‖}
  set f : V → ℝ := fun y => 1 - Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2))
  have hA_meas : MeasurableSet A :=
    measurableSet_le measurable_const continuous_norm.measurable
  have hf_nn : ∀ y, 0 ≤ f y := by
    intro y; simp only [f]
    have : Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2)) ≤ Real.exp 0 :=
      Real.exp_le_exp_of_le (by linarith [show 0 ≤ σ ^ 2 * ‖y‖ ^ 2 / 2 from by positivity])
    rw [Real.exp_zero] at this; linarith
  have hf_ge_δ : ∀ y ∈ A, δ ≤ f y := by
    intro y hy
    simp only [A, mem_setOf_eq] at hy; simp only [f, hδ_def]
    have : σ ^ 2 * R ^ 2 / 2 ≤ σ ^ 2 * ‖y‖ ^ 2 / 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) ≤ 2)
      exact mul_le_mul_of_nonneg_left (sq_le_sq' (by linarith) hy) (by positivity)
    linarith [Real.exp_le_exp_of_le (neg_le_neg this)]
  have hf_cont : Continuous f := by
    simp only [f]; apply continuous_const.sub
    exact Real.continuous_exp.comp (continuous_neg.comp
      ((continuous_const.mul (continuous_norm.pow 2)).div_const _))
  have hf_int : Integrable f μ.toMeasure := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) hf_cont.aestronglyMeasurable
    exact Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf_nn y)]
      simp only [f]; linarith [Real.exp_nonneg (-(σ ^ 2 * ‖y‖ ^ 2 / 2))]
  have key : δ * (μ.toMeasure A).toReal ≤ C :=
    calc δ * (μ.toMeasure A).toReal
        = ∫ _ in A, δ ∂μ.toMeasure := by
          simp only [setIntegral_const, smul_eq_mul, Measure.real, mul_comm]
      _ ≤ ∫ y in A, f y ∂μ.toMeasure :=
          setIntegral_mono_on (integrable_const δ).integrableOn
            hf_int.integrableOn hA_meas hf_ge_δ
      _ ≤ ∫ y, f y ∂μ.toMeasure :=
          setIntegral_le_integral hf_int (Eventually.of_forall hf_nn)
      _ ≤ C := hC
  exact (le_div_iff₀ hδ_pos).mpr (by linarith)

/-! ## The Gaussian Averaging Bound (with scaling parameter) -/

/-! ## Gaussian Averaging Infrastructure -/

section GaussianAveraging

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V]

private abbrev gaussDensity (σ : ℝ) (x : V) : ℝ :=
  Real.exp (-(1 / (2 * σ ^ 2)) * ‖x‖ ^ 2)

/-- Fubini identity for Gaussian averaging:
    ∫_μ (1-exp(-σ²‖y‖²/2)) = C⁻¹ ∫ exp(-b‖x‖²) Re(1-φ(x)) dx. -/
axiom fubini_gaussian_charFun
    (μ : ProbabilityMeasure V) (φ : V → ℂ)
    (hφ : ∀ t, charFun μ.toMeasure t = φ t) (σ : ℝ) (hσ : 0 < σ) :
    ∫ y, (1 - Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2))) ∂μ.toMeasure =
    (∫ x : V, gaussDensity σ x)⁻¹ *
      ∫ x : V, gaussDensity σ x * (1 - (φ x).re)

/-- Gaussian second moment bound:
    C⁻¹ ∫ exp(-b‖x‖²) ⟪x,Sx⟫ dx ≤ σ²·Tr(S).
    Proof requires computing E_γ[⟪x,Sx⟫] = σ²·∑ᵢ ⟪eᵢ,Seᵢ⟫. -/
axiom gaussian_quadForm_integral_le
    (σ : ℝ) (hσ : 0 < σ)
    (S : V →L[ℝ] V) (hS : S.IsPositive)
    (T : ℝ) (_hT : 0 ≤ T)
    (h_trace : ∀ (ι : Type*) [Fintype ι] (b : OrthonormalBasis ι ℝ V),
      ∑ i, @inner ℝ V _ (b i) (S (b i)) ≤ T) :
    (∫ x : V, gaussDensity σ x)⁻¹ *
      ∫ x : V, gaussDensity σ x * quadForm S x ≤ σ ^ 2 * T

private lemma gaussDensity_nonneg' (σ : ℝ) (x : V) : 0 ≤ gaussDensity σ x :=
  Real.exp_nonneg _

private lemma gaussDensity_continuous' (σ : ℝ) : Continuous (gaussDensity (V := V) σ) := by
  unfold gaussDensity; fun_prop

private lemma gaussDensity_integrable' (σ : ℝ) (hσ : 0 < σ) :
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

private lemma gaussDensity_integral_pos' (σ : ℝ) (hσ : 0 < σ) :
    0 < ∫ x : V, gaussDensity σ x := by
  apply integral_pos_of_integrable_nonneg_nonzero
    (gaussDensity_continuous' σ) (gaussDensity_integrable' σ hσ)
  · exact fun x => gaussDensity_nonneg' σ x
  · exact ne_of_gt (Real.exp_pos (-(1 / (2 * σ ^ 2)) * ‖(0 : V)‖ ^ 2))

private lemma mul_exp_neg_le_one' {t : ℝ} (ht : 0 ≤ t) : t * Real.exp (-t) ≤ 1 := by
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos t)]
  linarith [Real.add_one_le_exp t]

private lemma gaussDensity_mul_quadForm_integrable' (σ : ℝ) (hσ : 0 < σ)
    (S : V →L[ℝ] V) :
    Integrable (fun x => gaussDensity σ x * quadForm S x) volume := by
  set b := 1 / (2 * σ ^ 2) with hb_def
  have hb : 0 < b := by positivity
  set C := ‖S‖ * (2 / b)
  have hC : 0 ≤ C := by positivity
  have hbound_int : Integrable (fun x : V => C * Real.exp (-(b / 2) * ‖x‖ ^ 2)) volume := by
    apply Integrable.const_mul
    have h := gaussDensity_integrable' (V := V) (σ * Real.sqrt 2) (by positivity)
    unfold gaussDensity at h
    convert h using 1; ext x; congr 1
    rw [mul_pow, Real.sq_sqrt (by positivity : (2 : ℝ) ≥ 0)]; ring
  have hqf_cont : Continuous (fun x : V => quadForm S x) := by
    unfold quadForm; fun_prop
  apply hbound_int.mono'
  · exact ((gaussDensity_continuous' σ).mul hqf_cont).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussDensity_nonneg' σ x)]
    have hqf_bound : |quadForm S x| ≤ ‖S‖ * ‖x‖ ^ 2 := by
      unfold quadForm
      calc |@inner ℝ V _ x (S x)| ≤ ‖x‖ * ‖S x‖ := abs_real_inner_le_norm x (S x)
        _ ≤ ‖x‖ * (‖S‖ * ‖x‖) :=
            mul_le_mul_of_nonneg_left (S.le_opNorm x) (norm_nonneg _)
        _ = ‖S‖ * ‖x‖ ^ 2 := by ring
    have hgsq_bound : gaussDensity σ x * ‖x‖ ^ 2 ≤
        (2 / b) * Real.exp (-(b / 2) * ‖x‖ ^ 2) := by
      unfold gaussDensity
      set s := ‖x‖ ^ 2
      have hs : 0 ≤ s := sq_nonneg _
      have h_split : Real.exp (-(1 / (2 * σ ^ 2)) * s) =
          Real.exp (-(b / 2) * s) * Real.exp (-(b / 2) * s) := by
        rw [← Real.exp_add]; congr 1; rw [hb_def]; ring
      rw [h_split]
      have hexp_nn := (Real.exp_pos (-(b / 2) * s)).le
      have key := mul_exp_neg_le_one' (show 0 ≤ b / 2 * s by positivity)
      have hkey2 : b / 2 * (Real.exp (-(b / 2 * s)) * s) ≤ 1 := by
        linarith [show b / 2 * s * Real.exp (-(b / 2 * s)) =
          b / 2 * (Real.exp (-(b / 2 * s)) * s) from by ring]
      have hse : Real.exp (-(b / 2 * s)) * s ≤ 2 / b := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < b)]
        calc Real.exp (-(b / 2 * s)) * s * b
            = 2 * (b / 2 * (Real.exp (-(b / 2 * s)) * s)) := by ring
          _ = 2 * (b / 2 * s * Real.exp (-(b / 2 * s))) := by ring
          _ ≤ 2 * 1 := by linarith
          _ = 2 := by ring
      rw [show -(b / 2) * s = -(b / 2 * s) from by ring] at hexp_nn ⊢
      calc Real.exp (-(b / 2 * s)) * Real.exp (-(b / 2 * s)) * s
          = Real.exp (-(b / 2 * s)) * (Real.exp (-(b / 2 * s)) * s) := by ring
        _ ≤ Real.exp (-(b / 2 * s)) * (2 / b) :=
            mul_le_mul_of_nonneg_left hse hexp_nn
        _ = 2 / b * Real.exp (-(b / 2 * s)) := by ring
    calc gaussDensity σ x * |quadForm S x|
        ≤ gaussDensity σ x * (‖S‖ * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hqf_bound (gaussDensity_nonneg' σ x)
      _ = ‖S‖ * (gaussDensity σ x * ‖x‖ ^ 2) := by ring
      _ ≤ ‖S‖ * ((2 / b) * Real.exp (-(b / 2) * ‖x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hgsq_bound (norm_nonneg S)
      _ = C * Real.exp (-(b / 2) * ‖x‖ ^ 2) := by ring

/-- The Gaussian averaging bound with scaling parameter σ > 0:

    ∫ (1 - exp(-σ²‖y‖²/2)) dμ(y) ≤ ε + 2σ²·T

    Here exp(-σ²‖y‖²/2) is the characteristic function of N(0, σ²I).
    The bound follows from Fubini + pointwise bound Re(1-φ) ≤ ε + 2·qf
    + Gaussian second moment E_γ[⟨x,Sx⟩] ≤ σ²·Tr(S). -/
theorem gaussian_averaging_bound
    (μ : ProbabilityMeasure V) (φ : V → ℂ)
    (hφ : ∀ t, charFun μ.toMeasure t = φ t)
    (ε : ℝ) (hε : 0 < ε)
    (σ : ℝ) (hσ : 0 < σ)
    (S : V →L[ℝ] V) (hS : S.IsPositive)
    (h_bound : ∀ x, quadForm S x < 1 → ‖1 - φ x‖ < ε)
    (T : ℝ) (hT : 0 ≤ T)
    (h_trace : ∀ (ι : Type*) [Fintype ι] (b : OrthonormalBasis ι ℝ V),
      ∑ i, @inner ℝ V _ (b i) (S (b i)) ≤ T) :
    ∫ y, (1 - Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2))) ∂μ.toMeasure ≤ ε + 2 * σ ^ 2 * T := by
  set g := gaussDensity (V := V) σ with hg_def
  set C := ∫ x : V, g x with hC_def
  have hC_pos : 0 < C := gaussDensity_integral_pos' (V := V) σ hσ
  have hCinv_nn : 0 ≤ C⁻¹ := inv_nonneg.mpr hC_pos.le
  have hg_int := gaussDensity_integrable' (V := V) σ hσ
  -- Step 1: Fubini
  rw [fubini_gaussian_charFun μ φ hφ σ hσ]
  -- Step 2: Pointwise bound
  have hpointwise : ∀ x, (1 - (φ x).re) ≤ ε + 2 * quadForm S x := by
    intro x
    by_cases hqf : quadForm S x < 1
    · have hre : (1 - (φ x).re) ≤ ‖1 - φ x‖ := by
        calc (1 - (φ x).re) = (1 - φ x).re := by simp [sub_re]
          _ ≤ |(1 - φ x).re| := le_abs_self _
          _ ≤ ‖1 - φ x‖ := abs_re_le_norm _
      linarith [h_bound x hqf, quadForm_nonneg hS x]
    · push_neg at hqf
      have hre_le : (φ x).re ≤ ‖φ x‖ := le_trans (le_abs_self _) (abs_re_le_norm _)
      have hnorm_le : ‖φ x‖ ≤ 1 := by
        rw [← hφ]; haveI : IsProbabilityMeasure μ.toMeasure := inferInstance
        exact norm_charFun_le_one x
      have hneg_re : -(φ x).re ≤ ‖φ x‖ := le_trans (neg_le_abs _) (abs_re_le_norm _)
      linarith
  -- Step 3: Integrability
  have hgqf_int : Integrable (fun x => g x * quadForm S x) volume :=
    gaussDensity_mul_quadForm_integrable' (V := V) σ hσ S
  have hprod_int : Integrable (fun x => g x * (1 - (φ x).re)) volume := by
    have hφ_eq : φ = charFun μ.toMeasure := funext (fun t => (hφ t).symm)
    rw [hφ_eq]
    have hφ_meas : Measurable (fun x => (charFun μ.toMeasure x).re) :=
      Complex.measurable_re.comp measurable_charFun
    apply Integrable.mono (hg_int.const_mul 2)
      (((gaussDensity_continuous' σ).measurable.mul
        (measurable_const.sub hφ_meas)).aestronglyMeasurable)
    filter_upwards with x
    haveI : IsProbabilityMeasure μ.toMeasure := inferInstance
    have hg_nn := gaussDensity_nonneg' σ x
    have hre := le_trans (le_abs_self (charFun μ.toMeasure x).re) (abs_re_le_norm _)
    have hnre := le_trans (neg_le_abs (charFun μ.toMeasure x).re) (abs_re_le_norm _)
    have hnorm := norm_charFun_le_one (μ := μ.toMeasure) x
    have h1 : |1 - (charFun μ.toMeasure x).re| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    have h2 : ‖g x * (1 - (charFun μ.toMeasure x).re)‖ ≤ g x * 2 := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hg_nn]
      exact mul_le_mul_of_nonneg_left h1 hg_nn
    have h3 : ‖2 * g x‖ = g x * 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hg_nn)]; ring
    linarith
  have hprod2_int : Integrable (fun x => g x * (ε + 2 * quadForm S x)) volume := by
    have : (fun x => g x * (ε + 2 * quadForm S x)) =
        (fun x => ε * g x + 2 * (g x * quadForm S x)) := by ext x; ring
    rw [this]; exact (hg_int.const_mul ε).add (hgqf_int.const_mul 2)
  -- Step 4: Integral inequality + split + combine
  have hint_le : C⁻¹ * ∫ x, g x * (1 - (φ x).re) ≤
      C⁻¹ * ∫ x, g x * (ε + 2 * quadForm S x) :=
    mul_le_mul_of_nonneg_left
      (integral_mono hprod_int hprod2_int fun x =>
        mul_le_mul_of_nonneg_left (hpointwise x) (gaussDensity_nonneg' σ x))
      hCinv_nn
  have hint_split : ∫ x, g x * (ε + 2 * quadForm S x) =
      ε * C + 2 * ∫ x, g x * quadForm S x := by
    have heq : (fun x => g x * (ε + 2 * quadForm S x)) =
        (fun x => ε * g x + 2 * (g x * quadForm S x)) := by ext x; ring
    rw [heq, integral_add (hg_int.const_mul ε) (hgqf_int.const_mul 2),
      integral_const_mul ε, integral_const_mul 2]
  calc C⁻¹ * ∫ x, g x * (1 - (φ x).re)
      ≤ C⁻¹ * ∫ x, g x * (ε + 2 * quadForm S x) := hint_le
    _ = C⁻¹ * (ε * C + 2 * ∫ x, g x * quadForm S x) := by rw [hint_split]
    _ = ε + 2 * (C⁻¹ * ∫ x, g x * quadForm S x) := by
        have hCne : C ≠ 0 := ne_of_gt hC_pos
        rw [mul_add]; congr 1
        · rw [← mul_assoc, mul_comm C⁻¹ ε, mul_assoc, inv_mul_cancel₀ hCne, mul_one]
        · ring
    _ ≤ ε + 2 * (σ ^ 2 * T) := by
        linarith [gaussian_quadForm_integral_le σ hσ S hS T hT h_trace]
    _ = ε + 2 * σ ^ 2 * T := by ring

end GaussianAveraging

/-- Scaled Chebyshev: combining Gaussian averaging with the tail bound. -/
lemma scaled_tail_bound
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V]
    (μ : ProbabilityMeasure V) (φ : V → ℂ)
    (hφ : ∀ t, charFun μ.toMeasure t = φ t)
    (ε : ℝ) (hε : 0 < ε)
    (σ : ℝ) (hσ : 0 < σ)
    (S : V →L[ℝ] V) (hS : S.IsPositive)
    (h_bound : ∀ x, quadForm S x < 1 → ‖1 - φ x‖ < ε)
    (T : ℝ) (hT : 0 ≤ T)
    (h_trace : ∀ (ι : Type*) [Fintype ι] (b : OrthonormalBasis ι ℝ V),
      ∑ i, @inner ℝ V _ (b i) (S (b i)) ≤ T)
    (R : ℝ) (hR : 0 < R) :
    (μ.toMeasure {y | R ≤ ‖y‖}).toReal ≤
      (ε + 2 * σ ^ 2 * T) / (1 - Real.exp (-(σ ^ 2 * R ^ 2 / 2))) := by
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hRσ : 0 < σ ^ 2 * R ^ 2 / 2 := by positivity
  have hC0 : 0 ≤ ε + 2 * σ ^ 2 * T := by nlinarith
  have hgab := gaussian_averaging_bound μ φ hφ ε hε σ hσ S hS h_bound T hT h_trace
  exact tail_bound_from_exp_integral μ σ hσ _ hC0 hgab R hR

/-! ## Restriction of Operators to Marginal Subspaces -/

/-- The embedding t ↦ ∑ tᵢvᵢ from EuclideanSpace to H. -/
private def embedON {n : ℕ} (v : Fin n → H) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] H :=
  { toFun := fun t => ∑ i, t i • v i
    map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
    map_smul' := fun r x => by
      simp only [RingHom.id_apply]; rw [Finset.smul_sum]
      congr 1; ext i; simp [smul_smul, mul_comm r] }

/-- The projection x ↦ (⟪vᵢ, x⟫)ᵢ from H to EuclideanSpace. -/
private def projON {n : ℕ} (v : Fin n → H) : H →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  { toFun := fun x => EuclideanSpace.equiv (Fin n) ℝ |>.symm (fun i => @inner ℝ H _ (v i) x)
    map_add' := fun x y => by ext i; simp [inner_add_right]
    map_smul' := fun r x => by ext i; simp [inner_smul_right] }

/-- Restriction of an operator S on H to a finite-dimensional subspace
    spanned by an orthonormal family v : Fin n → H. Defined as π ∘ S ∘ ι
    where ι embeds and π projects. Matrix: (S_v)_{ij} = ⟪vᵢ, S(vⱼ)⟫. -/
def restrictOp (S : H →L[ℝ] H) {n : ℕ} (v : Fin n → H) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap (projON v ∘ₗ S.toLinearMap ∘ₗ embedON v)

omit [CompleteSpace H] in
/-- Coordinate formula for restrictOp. -/
lemma restrictOp_apply (S : H →L[ℝ] H) {n : ℕ} (v : Fin n → H)
    (t : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (restrictOp S v t) i = @inner ℝ H _ (v i) (S (∑ j, t j • v j)) := by
  unfold restrictOp projON embedON; simp

omit [CompleteSpace H] in
/-- The quadratic form of the restricted operator equals the original. -/
lemma restrictOp_quadForm (S : H →L[ℝ] H) {n : ℕ} (v : Fin n → H)
    (t : EuclideanSpace ℝ (Fin n)) :
    quadForm (restrictOp S v) t = quadForm S (∑ i, t i • v i) := by
  simp only [quadForm]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, RCLike.conj_to_real, restrictOp_apply]
  rw [sum_inner]
  simp only [inner_smul_left, RCLike.conj_to_real]
  congr 1; ext i; ring

/-- Inner product symmetry for self-adjoint operators: ⟪a, Sb⟫ = ⟪b, Sa⟫. -/
private lemma inner_self_adjoint_comm (S : H →L[ℝ] H) (hS : S.IsPositive)
    (a b : H) : @inner ℝ H _ a (S b) = @inner ℝ H _ b (S a) := by
  have h := ContinuousLinearMap.adjoint_inner_left S b a
  rw [hS.isSelfAdjoint.adjoint_eq] at h
  rw [← h, real_inner_comm]

/-- The restriction of a positive operator is positive. -/
lemma restrictOp_isPositive (S : H →L[ℝ] H) (hS : S.IsPositive)
    {n : ℕ} (v : Fin n → H) :
    (restrictOp S v).IsPositive := by
  refine ⟨?_, ?_⟩
  · intro x y
    simp only [ContinuousLinearMap.coe_coe]
    rw [PiLp.inner_apply, PiLp.inner_apply]
    simp only [RCLike.inner_apply, RCLike.conj_to_real, restrictOp_apply]
    trans @inner ℝ H _ (∑ i, y i • v i) (S (∑ j, x j • v j))
    · rw [sum_inner]; congr 1; ext i; rw [inner_smul_left, RCLike.conj_to_real]
    trans @inner ℝ H _ (∑ i, x i • v i) (S (∑ j, y j • v j))
    · exact inner_self_adjoint_comm S hS _ _
    · rw [sum_inner]; congr 1; ext i; rw [inner_smul_left, RCLike.conj_to_real]; ring
  · intro x
    simp only [ContinuousLinearMap.reApplyInnerSelf]
    rw [RCLike.re_to_real, real_inner_comm]
    show 0 ≤ quadForm (restrictOp S v) x
    rw [restrictOp_quadForm]
    exact quadForm_nonneg hS _

/-- For a finite orthonormal set in a Hilbert space, the sum of diagonal
    entries ∑ⱼ ⟪vⱼ, S(vⱼ)⟫ is bounded by the trace ∑' k ⟪bₖ, S(bₖ)⟫.
    Proof: decompose bₖ = P(bₖ) + Q(bₖ) via the projection P onto span(v).
    The cross term ∑' k ⟪Q(bₖ), S(P(bₖ))⟫ vanishes by Parseval + orthonormality,
    so the difference = ∑' k ⟪Q(bₖ), S(Q(bₖ))⟫ ≥ 0 by positivity of S. -/
theorem orthonormal_diag_le_hilbert_trace (S : H →L[ℝ] H) (hS : S.IsPositive)
    {n : ℕ} (v : Fin n → H) (hv : Orthonormal ℝ v)
    {ι : Type} (b : HilbertBasis ι ℝ H)
    (hsum : Summable (fun i => @inner ℝ H _ (b i) (S (b i)))) :
    ∑ j : Fin n, @inner ℝ H _ (v j) (S (v j)) ≤
      ∑' i, @inner ℝ H _ (b i) (S (b i)) := by
  have sa : ∀ a c : H, @inner ℝ H _ a (S c) = @inner ℝ H _ c (S a) := by
    intro a c
    have h := ContinuousLinearMap.adjoint_inner_left S c a
    rw [hS.isSelfAdjoint.adjoint_eq] at h; rw [← h, real_inner_comm]
  have hnn : ∀ x : H, 0 ≤ @inner ℝ H _ x (S x) := by
    intro x; have := hS.re_inner_nonneg_left x
    simp only [RCLike.re_to_real] at this; rwa [real_inner_comm]
  set Pv : H → H := fun x => ∑ j, @inner ℝ H _ (v j) x • v j with hPv_def
  suffices hsuff :
      ∑ j, @inner ℝ H _ (v j) (S (v j)) +
        ∑' k, @inner ℝ H _ (b k - Pv (b k)) (S (b k - Pv (b k))) =
      ∑' k, @inner ℝ H _ (b k) (S (b k)) by
    have h_nn : 0 ≤ ∑' k, @inner ℝ H _ (b k - Pv (b k)) (S (b k - Pv (b k))) :=
      tsum_nonneg fun k => hnn (b k - Pv (b k))
    linarith
  have expand : ∀ k, @inner ℝ H _ (b k - Pv (b k)) (S (b k - Pv (b k))) =
      @inner ℝ H _ (b k) (S (b k)) - 2 * @inner ℝ H _ (Pv (b k)) (S (b k)) +
      @inner ℝ H _ (Pv (b k)) (S (Pv (b k))) := by
    intro k; rw [map_sub]; simp only [inner_sub_left, inner_sub_right, sa (b k) (Pv (b k))]; ring
  have hA_eq : ∀ k, @inner ℝ H _ (Pv (b k)) (S (b k)) =
      ∑ j, @inner ℝ H _ (v j) (b k) * @inner ℝ H _ (b k) (S (v j)) := by
    intro k; simp only [hPv_def, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, RCLike.conj_to_real, sa]
  have hA : HasSum (fun k => @inner ℝ H _ (Pv (b k)) (S (b k)))
      (∑ j, @inner ℝ H _ (v j) (S (v j))) := by
    simp_rw [hA_eq]
    exact hasSum_sum fun j _ => b.hasSum_inner_mul_inner (v j) (S (v j))
  have hB_eq : ∀ k, @inner ℝ H _ (Pv (b k)) (S (Pv (b k))) =
      ∑ j, ∑ i, @inner ℝ H _ (v j) (S (v i)) *
        (@inner ℝ H _ (v j) (b k) * @inner ℝ H _ (v i) (b k)) := by
    intro k; simp only [hPv_def, sum_inner, inner_smul_left, RCLike.conj_to_real]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sa (v j) (∑ i, @inner ℝ H _ (v i) (↑(b k)) • v i)]
    simp only [sum_inner, inner_smul_left, RCLike.conj_to_real]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sa]; ring
  have hB_parseval : ∀ j i : Fin n,
      HasSum (fun k => @inner ℝ H _ (v j) (b k) * @inner ℝ H _ (v i) (b k))
        (@inner ℝ H _ (v j) (v i)) := by
    intro j i
    have h := b.hasSum_inner_mul_inner (v j) (v i)
    simp_rw [real_inner_comm (v i) (b _)] at h; exact h
  have hB_target_eq : ∑ j : Fin n, @inner ℝ H _ (v j) (S (v j)) =
      ∑ j, ∑ i, @inner ℝ H _ (v j) (S (v i)) * @inner ℝ H _ (v j) (v i) := by
    congr 1; ext j
    conv_lhs => rw [show @inner ℝ H _ (v j) (S (v j)) =
      ∑ i, @inner ℝ H _ (v j) (S (v i)) * @inner ℝ H _ (v j) (v i) from by
        simp_rw [orthonormal_iff_ite.mp hv]
        simp [Finset.mem_univ]]
  have hB : HasSum (fun k => @inner ℝ H _ (Pv (b k)) (S (Pv (b k))))
      (∑ j, @inner ℝ H _ (v j) (S (v j))) := by
    rw [hB_target_eq]; simp_rw [hB_eq]
    exact hasSum_sum fun j _ => hasSum_sum fun i _ =>
      (hB_parseval j i).const_smul (@inner ℝ H _ (v j) (S (v i)))
  simp_rw [expand]
  have hQ : HasSum (fun k =>
      @inner ℝ H _ (b k) (S (b k)) - 2 * @inner ℝ H _ (Pv (b k)) (S (b k)) +
      @inner ℝ H _ (Pv (b k)) (S (Pv (b k))))
      (∑' k, @inner ℝ H _ (b k) (S (b k)) -
       ∑ j, @inner ℝ H _ (v j) (S (v j))) := by
    have h := ((hsum.hasSum.sub (hA.add hA)).add hB)
    convert h using 1
    · ext k; ring
    · ring
  linarith [hQ.tsum_eq]

omit [CompleteSpace H] in
/-- The trace of restrictOp in any ONB of EuclideanSpace equals ∑ⱼ ⟪vⱼ, S(vⱼ)⟫.
    Uses `LinearMap.trace_eq_sum_inner` for basis independence on finite-dimensional
    EuclideanSpace, then computes the standard basis entries. -/
lemma restrictOp_trace_eq_diag (S : H →L[ℝ] H) {n : ℕ} (v : Fin n → H)
    (_hv : Orthonormal ℝ v)
    (ι' : Type*) [Fintype ι'] [DecidableEq ι']
    (b' : OrthonormalBasis ι' ℝ (EuclideanSpace ℝ (Fin n))) :
    ∑ i, @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (b' i) (restrictOp S v (b' i)) =
    ∑ j : Fin n, @inner ℝ H _ (v j) (S (v j)) := by
  set T := (restrictOp S v).toLinearMap
  have h1 := LinearMap.trace_eq_sum_inner T b'
  have h2 := LinearMap.trace_eq_sum_inner T (EuclideanSpace.basisFun (Fin n) ℝ)
  have lhs_eq : ∑ i, @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (b' i)
      (restrictOp S v (b' i)) = ∑ i, @inner ℝ _ _ (b' i) (T (b' i)) := by
    congr
  have rhs_eq : ∑ j, @inner ℝ _ _ ((EuclideanSpace.basisFun (Fin n) ℝ) j)
      (T ((EuclideanSpace.basisFun (Fin n) ℝ) j)) =
      ∑ j : Fin n, @inner ℝ H _ (v j) (S (v j)) := by
    congr 1; ext j
    simp only [EuclideanSpace.basisFun_apply]
    change @inner ℝ (EuclideanSpace ℝ (Fin n)) _
      (EuclideanSpace.single j 1) (restrictOp S v (EuclideanSpace.single j 1)) = _
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, RCLike.conj_to_real]
    have h_app : ∀ i, (restrictOp S v (EuclideanSpace.single j 1)) i =
        @inner ℝ H _ (v i) (S (v j)) := by
      intro i; rw [restrictOp_apply]
      congr 1
      simp [EuclideanSpace.single_apply, ite_smul, Finset.sum_ite_eq']
    simp_rw [h_app, EuclideanSpace.single_apply]
    simp [Finset.sum_ite_eq']
  exact lhs_eq.trans ((h1.symm.trans h2).trans rhs_eq)

/-- The trace of the restricted operator is bounded by the trace of the
    original on any Hilbert basis. Combines trace basis independence on
    EuclideanSpace with the diagonal bound. -/
lemma restrictOp_trace_le (S : H →L[ℝ] H) (hS : S.IsPositive)
    {n : ℕ} (v : Fin n → H) (hv : Orthonormal ℝ v)
    {ι : Type} (b : HilbertBasis ι ℝ H)
    (hsum : Summable (fun i => @inner ℝ H _ (b i) (S (b i)))) :
    ∀ (ι' : Type) [Fintype ι'] (b' : OrthonormalBasis ι' ℝ (EuclideanSpace ℝ (Fin n))),
      ∑ i, @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (b' i) (restrictOp S v (b' i)) ≤
        ∑' i, @inner ℝ H _ (b i) (S (b i)) := by
  intro ι' _ b'
  haveI : DecidableEq ι' := Classical.decEq _
  rw [restrictOp_trace_eq_diag S v hv ι' b']
  exact orthonormal_diag_le_hilbert_trace S hS v hv b hsum

/-! ## Main Tightness Theorem -/

/-- For any C < η and σ > 0, there exists R > 0 such that
    C / (1 - exp(-σ²R²/2)) < η. -/
lemma exists_R_for_tail_bound (C η σ : ℝ) (hC : 0 < C) (hCη : C < η) (hσ : 0 < σ) :
    ∃ R > 0, C / (1 - Real.exp (-(σ ^ 2 * R ^ 2 / 2))) < η := by
  have hη : 0 < η := by linarith
  set δ := (1 - C / η) / 2 with hδ_def
  have hCη' : C / η < 1 := by rwa [div_lt_one hη]
  have hδ_pos : 0 < δ := by rw [hδ_def]; linarith
  have hδ_bound : δ < 1 - C / η := by rw [hδ_def]; linarith
  have hδ_lt_one : δ < 1 := by linarith [div_pos hC hη]
  have hlog_neg : Real.log δ < 0 := Real.log_neg hδ_pos hδ_lt_one
  set R := Real.sqrt (2 * (-Real.log δ)) / σ with hR_def
  use R
  constructor
  · rw [hR_def]; apply div_pos (Real.sqrt_pos.mpr (by nlinarith)) hσ
  · have hσ2 : 0 < σ ^ 2 := by positivity
    have hR_sq : R ^ 2 = 2 * (-Real.log δ) / σ ^ 2 := by
      rw [hR_def, div_pow, Real.sq_sqrt (by nlinarith)]
    have h_exp_arg : σ ^ 2 * R ^ 2 / 2 = -Real.log δ := by
      rw [hR_sq]; field_simp
    rw [h_exp_arg, neg_neg, Real.exp_log hδ_pos]
    rw [div_lt_iff₀ (by linarith : 0 < 1 - δ)]
    have : η * (1 - δ) = (η + C) / 2 := by rw [hδ_def]; field_simp; ring
    linarith

/-- **Sazonov Tightness Theorem.** If φ : H → ℂ is positive definite, normalized,
    and Sazonov-continuous at 0, then the family of all finite-dimensional
    marginal measures is uniformly tight. -/
theorem sazonov_tightness (φ : H → ℂ) (_hpd : IsPositiveDefinite φ)
    (_hnorm : φ 0 = 1) (_hcont : Continuous φ)
    (hsaz : SazonovContinuousAt φ) :
    ∀ η > 0, ∃ R > 0, ∀ (n : ℕ) (v : Fin n → H) (_ : Orthonormal ℝ v)
      (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
      (_ : ∀ t, charFun μ.toMeasure t = marginalFun φ v t),
    (μ.toMeasure {y | R ≤ ‖y‖}).toReal < η := by
  intro η hη
  set ε := η / 3 with hε_def
  have hε : 0 < ε := by linarith
  obtain ⟨S, hS_bound⟩ := hsaz ε hε
  obtain ⟨hpos, ι, b, hsum⟩ := S.traceClass
  set T := ∑' i, @inner ℝ H _ (b i) (S.op (b i)) with hT_def
  have hT_nn : 0 ≤ T := by
    apply tsum_nonneg; intro i
    have := hpos.re_inner_nonneg_left (b i)
    simp only [RCLike.re_to_real] at this
    rwa [real_inner_comm]
  set σ := Real.sqrt (η / (6 * (T + 1))) with hσ_def
  have hT1 : 0 < T + 1 := by linarith
  have hσ_sq_pos : 0 < η / (6 * (T + 1)) := by positivity
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hσ_sq_pos
  have hσ_sq : σ ^ 2 = η / (6 * (T + 1)) := by
    rw [hσ_def, sq, Real.mul_self_sqrt hσ_sq_pos.le]
  set C := ε + 2 * σ ^ 2 * T with hC_def
  have hC_bound : C < η := by
    rw [hC_def, hε_def, hσ_sq]
    have h6T1 : (0:ℝ) < 6 * (T + 1) := by positivity
    rw [show 2 * (η / (6 * (T + 1))) * T = η * T / (3 * (T + 1)) by
      field_simp; ring]
    rw [div_add_div _ _ (by positivity : (3:ℝ) ≠ 0) (by positivity : 3 * (T + 1) ≠ 0)]
    rw [div_lt_iff₀ (by positivity : 0 < 3 * (3 * (T + 1)))]
    nlinarith
  have hC_pos : 0 < C := by
    rw [hC_def]; nlinarith [sq_nonneg σ]
  obtain ⟨R, hR, hR_bound⟩ := exists_R_for_tail_bound C η σ hC_pos hC_bound hσ_pos
  use R, hR
  intro n v hv μ hμ
  have h_gauss := gaussian_averaging_bound μ (marginalFun φ v) hμ ε hε σ hσ_pos
      (restrictOp S.op v) (restrictOp_isPositive S.op hpos v)
  have h_bound_v : ∀ t : EuclideanSpace ℝ (Fin n),
      quadForm (restrictOp S.op v) t < 1 → ‖1 - marginalFun φ v t‖ < ε := by
    intro t ht
    rw [restrictOp_quadForm] at ht
    exact hS_bound _ ht
  have h_trace_v := restrictOp_trace_le S.op hpos v hv b hsum
  have h_gauss' := h_gauss h_bound_v T hT_nn (fun ι' _ b' => by
    calc ∑ i, @inner ℝ _ _ (b' i) (restrictOp S.op v (b' i))
        ≤ ∑' i, @inner ℝ H _ (b i) (S.op (b i)) := h_trace_v ι' b'
      _ = T := rfl)
  have h_tail := tail_bound_from_exp_integral μ σ hσ_pos _ (by nlinarith [sq_nonneg σ]) h_gauss' R hR
  calc (μ.toMeasure {y | R ≤ ‖y‖}).toReal
      ≤ C / (1 - Real.exp (-(σ ^ 2 * R ^ 2 / 2))) := h_tail
    _ < η := hR_bound

end
