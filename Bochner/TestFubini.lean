/-
  Prove fubini_gaussian_charFun and gaussian_quadForm_integral_le.
-/
import Bochner.Sazonov
import Bochner.PositiveDefinite
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Complex Filter Topology Set InnerProductSpace
open scoped Real FourierTransform

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
  apply integral_pos_of_integrable_nonneg_nonzero
    (by unfold gaussDensity; fun_prop : Continuous (gaussDensity (V := V) σ))
    (gaussDensity_integrable σ hσ)
  · exact fun x => gaussDensity_nonneg σ x
  · exact ne_of_gt (Real.exp_pos _)

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
        congr 1; ext x; show Real.exp _ = Real.exp _; congr 1; rw [hb_def]]
      exact GaussianFourier.integral_rexp_neg_mul_sq_norm hb
    rw [hgd, ← Complex.ofReal_natCast n, ← Complex.ofReal_ofNat 2,
      ← Complex.ofReal_div, ← Complex.ofReal_div]
    exact (Complex.ofReal_cpow (le_of_lt (by positivity : (0 : ℝ) < π / b)) _).symm
  · congr 1; rw [I_sq]
    rw [show (b : ℂ) = 1 / (2 * (σ : ℂ) ^ 2) from by rw [hb_def]; push_cast; ring]
    push_cast; field_simp; ring

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
  -- Fubini key: ∫_μ ∫_V g(x) cexp(i⟪y,x⟫) dx dμ(y) = ∫_V g(x) ∫_μ cexp(i⟪y,x⟫) dμ(y) dx
  -- Product integrability (sorry for now)
  have hprod : Integrable (uncurry (fun (y : V) (x : V) =>
      (gaussDensity σ x : ℂ) * cexp (↑⟪y, x⟫_ℝ * I)))
      (μ.toMeasure.prod volume) := by sorry
  -- Fubini swap
  have fubini := integral_integral_swap hprod
  -- LHS of fubini: ∫_μ (∫ g cexp(i⟪y,·⟫) dx) dμ(y)
  -- = ∫_μ (C * cexp(-σ²‖y‖²/2)) dμ(y)  by gaussian_fourier_eq
  have lhs_fubini : ∫ y, (∫ x, (gaussDensity σ x : ℂ) * cexp (↑⟪y, x⟫_ℝ * I)) ∂μ.toMeasure =
      ↑C * ∫ y, cexp (-(σ ^ 2 * ‖y‖ ^ 2 / 2 : ℝ)) ∂μ.toMeasure := by
    rw [← integral_const_mul]; congr 1; ext y; exact gaussian_fourier_eq σ hσ y
  -- RHS of fubini: ∫ g(x) (∫_μ cexp(i⟪y,x⟫) dμ(y)) dx = ∫ g(x) φ(x) dx
  have rhs_fubini : ∫ x, (∫ y, (gaussDensity σ x : ℂ) * cexp (↑⟪y, x⟫_ℝ * I) ∂μ.toMeasure) =
      ∫ x, (gaussDensity σ x : ℂ) * φ x := by
    congr 1; ext x
    rw [← integral_const_mul]
    congr 1; ext y
    rw [show ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ from real_inner_comm y x]
    rw [show (charFun μ.toMeasure x = φ x) from hφ x] at *
    rfl
  -- Wait, I need ∫_μ cexp(⟪y,x⟫ * I) = charFun μ x = φ(x)
  -- charFun μ x = ∫ cexp(⟪y,x⟫ * I) dμ(y)
  -- So ∫ g(x) * ∫_μ cexp(⟪y,x⟫ * I) dμ(y) = ∫ g(x) * charFun(μ)(x) dx = ∫ g(x) φ(x) dx
  sorry

/-! ## Gaussian second moment bound -/

/-- The Gaussian second moment of ⟪w,x⟫². -/
private lemma gaussian_inner_sq_integral (σ : ℝ) (hσ : 0 < σ) (w : V) :
    (∫ x : V, gaussDensity σ x)⁻¹ *
      ∫ x : V, gaussDensity σ x * (@inner ℝ V _ w x) ^ 2 = σ ^ 2 * ‖w‖ ^ 2 := by
  sorry

private lemma gaussian_quadForm_integral_le'
    (σ : ℝ) (hσ : 0 < σ)
    (S : V →L[ℝ] V) (hS : S.IsPositive)
    (T : ℝ) (_hT : 0 ≤ T)
    (h_trace : ∀ (ι : Type*) [Fintype ι] (b : OrthonormalBasis ι ℝ V),
      ∑ i, @inner ℝ V _ (b i) (S (b i)) ≤ T) :
    (∫ x : V, gaussDensity σ x)⁻¹ *
      ∫ x : V, gaussDensity σ x * quadForm S x ≤ σ ^ 2 * T := by
  sorry

end
