import Bochner.Sazonov
import Bochner.PositiveDefinite
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.Tight

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

/-- Chebyshev/Markov bound with scaling: if ∫ (1 - exp(-‖y‖²/(2σ²))) dμ ≤ C,
    then μ({‖y‖ ≥ R}) ≤ C / (1 - exp(-R²/(2σ²))).

    Proof: on {‖y‖ ≥ R}, the integrand ≥ 1 - exp(-R²/(2σ²)) > 0, so
    C ≥ ∫ ... ≥ (1 - exp(-R²/(2σ²))) · μ({‖y‖ ≥ R}). -/
axiom tail_bound_from_exp_integral {V : Type*} [NormedAddCommGroup V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : ProbabilityMeasure V) (σ : ℝ) (hσ : 0 < σ)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∫ y, (1 - Real.exp (-(‖y‖ ^ 2 / (2 * σ ^ 2)))) ∂μ.toMeasure ≤ C)
    (R : ℝ) (hR : 0 < R) :
    (μ.toMeasure {y | R ≤ ‖y‖}).toReal ≤ C / (1 - Real.exp (-(R ^ 2 / (2 * σ ^ 2))))

/-! ## The Gaussian Averaging Bound (with scaling parameter) -/

/-- The Gaussian averaging bound with scaling parameter σ > 0:

    ∫ (1 - exp(-‖y‖²/(2σ²))) dμ(y) ≤ ε + 2σ²·T

    When σ = 1, this is the standard bound ε + 2T.
    The scaling freedom is critical for tightness: it lets us balance
    the numerator ε + 2σ²T against the denominator 1 - exp(-R²/(2σ²)). -/
axiom gaussian_averaging_bound
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
      ∑ i, @inner ℝ V _ (b i) (S (b i)) ≤ T) :
    ∫ y, (1 - Real.exp (-(‖y‖ ^ 2 / (2 * σ ^ 2)))) ∂μ.toMeasure ≤ ε + 2 * σ ^ 2 * T

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
      (ε + 2 * σ ^ 2 * T) / (1 - Real.exp (-(R ^ 2 / (2 * σ ^ 2)))) := by
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hRσ : 0 < R ^ 2 / (2 * σ ^ 2) := by positivity
  have hC0 : 0 ≤ ε + 2 * σ ^ 2 * T := by nlinarith
  have hgab := gaussian_averaging_bound μ φ hφ ε hε σ hσ S hS h_bound T hT h_trace
  exact tail_bound_from_exp_integral μ σ hσ _ hC0 hgab R hR

/-! ## Main Tightness Theorem -/

/-- For any C < η and σ > 0, there exists R > 0 such that
    C / (1 - exp(-R²/(2σ²))) < η. -/
lemma exists_R_for_tail_bound (C η σ : ℝ) (hC : 0 < C) (hCη : C < η) (hσ : 0 < σ) :
    ∃ R > 0, C / (1 - Real.exp (-(R ^ 2 / (2 * σ ^ 2)))) < η := by
  -- Need: 1 - exp(-R²/(2σ²)) > C/η, i.e., exp(-R²/(2σ²)) < 1 - C/η
  -- Pick R² = 2σ² · (-log(δ)) where δ = (1 - C/η) / 2 > 0
  -- Then exp(-R²/(2σ²)) = exp(log(δ)) = δ < 1 - C/η ✓
  have hη : 0 < η := by linarith
  set δ := (1 - C / η) / 2 with hδ_def
  have hCη' : C / η < 1 := by rwa [div_lt_one hη]
  have hδ_pos : 0 < δ := by rw [hδ_def]; linarith
  have hδ_bound : δ < 1 - C / η := by rw [hδ_def]; linarith
  -- Use R = σ · √(2 · (-log δ))
  -- Since δ < 1, log δ < 0, so -log δ > 0
  have hδ_lt_one : δ < 1 := by linarith [div_pos hC hη]
  have hlog_neg : Real.log δ < 0 := Real.log_neg hδ_pos hδ_lt_one
  set R := σ * Real.sqrt (2 * (-Real.log δ)) with hR_def
  use R
  constructor
  · rw [hR_def]; apply mul_pos hσ; apply Real.sqrt_pos.mpr; nlinarith
  · -- R²/(2σ²) = (σ²·(2·(-logδ)))/(2σ²) = -logδ
    have hσ2 : 0 < σ ^ 2 := by positivity
    have hR_sq : R ^ 2 = σ ^ 2 * (2 * (-Real.log δ)) := by
      rw [hR_def]; ring_nf; rw [Real.sq_sqrt (by nlinarith)]; ring
    have h_exp_arg : R ^ 2 / (2 * σ ^ 2) = -Real.log δ := by
      rw [hR_sq]; field_simp
    rw [h_exp_arg, neg_neg, Real.exp_log hδ_pos]
    -- Now goal: C / (1 - δ) < η
    -- Since δ < 1 - C/η, we have 1 - δ > C/η, so C/(1-δ) < η
    rw [div_lt_iff₀ (by linarith : 0 < 1 - δ)]
    -- Goal: C < η * (1 - δ). We have δ = (1 - C/η)/2, so 1-δ = 1 - (1-C/η)/2 = (1+C/η)/2
    -- η·(1-δ) = η·(1+C/η)/2 = (η+C)/2 > C (since η > 0)
    have : η * (1 - δ) = (η + C) / 2 := by rw [hδ_def]; field_simp; ring
    linarith

/-- **Sazonov Tightness Theorem.** If φ : H → ℂ is positive definite, normalized,
    and Sazonov-continuous at 0, then the family of all finite-dimensional
    marginal measures is uniformly tight.

    For every η > 0, there exists R > 0 such that for every orthonormal family
    v : Fin n → H and corresponding Bochner measure μ_v, μ_v({‖y‖ ≥ R}) < η. -/
theorem sazonov_tightness (φ : H → ℂ) (hpd : IsPositiveDefinite φ)
    (hnorm : φ 0 = 1) (hcont : Continuous φ)
    (hsaz : SazonovContinuousAt φ) :
    ∀ η > 0, ∃ R > 0, ∀ (n : ℕ) (v : Fin n → H) (hv : Orthonormal ℝ v)
      (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
      (hμ : ∀ t, charFun μ.toMeasure t = marginalFun φ v t),
    (μ.toMeasure {y | R ≤ ‖y‖}).toReal < η := by
  intro η hη
  -- Step 1: Get Sazonov operator S for ε = η/3
  set ε := η / 3 with hε_def
  have hε : 0 < ε := by linarith
  obtain ⟨S, hS_bound⟩ := hsaz ε hε
  obtain ⟨hpos, ι, b, hsum⟩ := S.traceClass
  set T := ∑' i, @inner ℝ H _ (b i) (S.op (b i)) with hT_def
  -- T ≥ 0 since each ⟪eᵢ, Seᵢ⟫ ≥ 0 by positivity of S
  have hT_nn : 0 ≤ T := by
    apply tsum_nonneg; intro i
    have := hpos.re_inner_nonneg_left (b i)
    simp only [RCLike.re_to_real] at this
    rwa [real_inner_comm]
  -- Step 2: Pick σ² = η/(6(T+1)). Then:
  -- 2σ²T = ηT/(3(T+1)) < η/3 = ε, so C = ε + 2σ²T < 2ε = 2η/3 < η
  set σ := Real.sqrt (η / (6 * (T + 1))) with hσ_def
  have hT1 : 0 < T + 1 := by linarith
  have hσ_sq_pos : 0 < η / (6 * (T + 1)) := by positivity
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hσ_sq_pos
  have hσ_sq : σ ^ 2 = η / (6 * (T + 1)) := by
    rw [hσ_def, sq, Real.mul_self_sqrt hσ_sq_pos.le]
  -- The bound constant C = ε + 2σ²T
  set C := ε + 2 * σ ^ 2 * T with hC_def
  have hC_bound : C < η := by
    rw [hC_def, hε_def, hσ_sq]
    -- C = η/3 + 2·(η/(6(T+1)))·T < η
    -- Clear denominators and use nlinarith
    have h6T1 : (0:ℝ) < 6 * (T + 1) := by positivity
    rw [show 2 * (η / (6 * (T + 1))) * T = η * T / (3 * (T + 1)) by
      field_simp; ring]
    -- Need: η/3 + η·T/(3·(T+1)) < η
    -- Equiv: η·(1/3 + T/(3(T+1))) < η
    -- Since T/(T+1) < 1: 1/3 + T/(3(T+1)) < 1/3 + 1/3 = 2/3 < 1
    rw [div_add_div _ _ (by positivity : (3:ℝ) ≠ 0) (by positivity : 3 * (T + 1) ≠ 0)]
    rw [div_lt_iff₀ (by positivity : 0 < 3 * (3 * (T + 1)))]
    nlinarith
  have hC_pos : 0 < C := by
    rw [hC_def]; nlinarith [sq_nonneg σ]
  -- Step 3: Pick R from exists_R_for_tail_bound
  obtain ⟨R, hR, hR_bound⟩ := exists_R_for_tail_bound C η σ hC_pos hC_bound hσ_pos
  use R, hR
  -- Step 4: For each marginal, apply the Gaussian averaging bound + Chebyshev
  intro n v hv μ hμ
  -- Define S_v : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) as
  -- the restriction of S to the span of v. (S_v)_{ij} = ⟪vᵢ, S vⱼ⟫.
  -- Then quadForm S_v t = quadForm S.op (∑ tᵢvᵢ), and Tr(S_v) ≤ T.
  -- The Sazonov bound on H gives: quadForm S_v t < 1 → ‖1 - marginalFun φ v t‖ < ε
  -- Apply gaussian_averaging_bound and tail_bound_from_exp_integral.
  sorry

end
