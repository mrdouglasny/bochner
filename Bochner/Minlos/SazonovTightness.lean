import Bochner.Sazonov
import Bochner.PositiveDefinite
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Trace

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

/-- Chebyshev/Markov bound with scaling: if ∫ (1 - exp(-‖y‖²/(2σ²))) dμ ≤ C,
    then μ({‖y‖ ≥ R}) ≤ C / (1 - exp(-R²/(2σ²))). -/
lemma tail_bound_from_exp_integral {V : Type*} [NormedAddCommGroup V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : ProbabilityMeasure V) (σ : ℝ) (hσ : 0 < σ)
    (C : ℝ) (_hC0 : 0 ≤ C)
    (hC : ∫ y, (1 - Real.exp (-(‖y‖ ^ 2 / (2 * σ ^ 2)))) ∂μ.toMeasure ≤ C)
    (R : ℝ) (hR : 0 < R) :
    (μ.toMeasure {y | R ≤ ‖y‖}).toReal ≤ C / (1 - Real.exp (-(R ^ 2 / (2 * σ ^ 2)))) := by
  set δ := 1 - Real.exp (-(R ^ 2 / (2 * σ ^ 2))) with hδ_def
  have hδ_pos : 0 < δ := by
    rw [hδ_def]
    have : Real.exp (-(R ^ 2 / (2 * σ ^ 2))) < 1 := by
      calc Real.exp (-(R ^ 2 / (2 * σ ^ 2))) < Real.exp 0 :=
            Real.exp_strictMono (by linarith [show 0 < R ^ 2 / (2 * σ ^ 2) from by positivity])
        _ = 1 := Real.exp_zero
    linarith
  set A := {y : V | R ≤ ‖y‖}
  set f : V → ℝ := fun y => 1 - Real.exp (-(‖y‖ ^ 2 / (2 * σ ^ 2)))
  have hA_meas : MeasurableSet A :=
    measurableSet_le measurable_const continuous_norm.measurable
  have hf_nn : ∀ y, 0 ≤ f y := by
    intro y; simp only [f]
    have : Real.exp (-(‖y‖ ^ 2 / (2 * σ ^ 2))) ≤ Real.exp 0 :=
      Real.exp_le_exp_of_le (by linarith [show 0 ≤ ‖y‖ ^ 2 / (2 * σ ^ 2) from by positivity])
    rw [Real.exp_zero] at this; linarith
  have hf_ge_δ : ∀ y ∈ A, δ ≤ f y := by
    intro y hy
    simp only [A, mem_setOf_eq] at hy; simp only [f, hδ_def]
    have : R ^ 2 / (2 * σ ^ 2) ≤ ‖y‖ ^ 2 / (2 * σ ^ 2) :=
      div_le_div_of_nonneg_right (sq_le_sq' (by linarith) hy) (by positivity)
    linarith [Real.exp_le_exp_of_le (neg_le_neg this)]
  have hf_cont : Continuous f := by
    simp only [f]; apply continuous_const.sub
    exact Real.continuous_exp.comp (continuous_neg.comp
      ((continuous_norm.pow 2).mul continuous_const))
  have hf_int : Integrable f μ.toMeasure := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) hf_cont.aestronglyMeasurable
    exact Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf_nn y)]
      simp only [f]; linarith [Real.exp_nonneg (-(‖y‖ ^ 2 / (2 * σ ^ 2)))]
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
axiom orthonormal_diag_le_hilbert_trace (S : H →L[ℝ] H) (hS : S.IsPositive)
    {n : ℕ} (v : Fin n → H) (hv : Orthonormal ℝ v)
    {ι : Type} (b : HilbertBasis ι ℝ H)
    (hsum : Summable (fun i => @inner ℝ H _ (b i) (S (b i)))) :
    ∑ j : Fin n, @inner ℝ H _ (v j) (S (v j)) ≤
      ∑' i, @inner ℝ H _ (b i) (S (b i))

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

omit [CompleteSpace H] in
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
    C / (1 - exp(-R²/(2σ²))) < η. -/
lemma exists_R_for_tail_bound (C η σ : ℝ) (hC : 0 < C) (hCη : C < η) (hσ : 0 < σ) :
    ∃ R > 0, C / (1 - Real.exp (-(R ^ 2 / (2 * σ ^ 2)))) < η := by
  have hη : 0 < η := by linarith
  set δ := (1 - C / η) / 2 with hδ_def
  have hCη' : C / η < 1 := by rwa [div_lt_one hη]
  have hδ_pos : 0 < δ := by rw [hδ_def]; linarith
  have hδ_bound : δ < 1 - C / η := by rw [hδ_def]; linarith
  have hδ_lt_one : δ < 1 := by linarith [div_pos hC hη]
  have hlog_neg : Real.log δ < 0 := Real.log_neg hδ_pos hδ_lt_one
  set R := σ * Real.sqrt (2 * (-Real.log δ)) with hR_def
  use R
  constructor
  · rw [hR_def]; apply mul_pos hσ; apply Real.sqrt_pos.mpr; nlinarith
  · have hσ2 : 0 < σ ^ 2 := by positivity
    have hR_sq : R ^ 2 = σ ^ 2 * (2 * (-Real.log δ)) := by
      rw [hR_def]; ring_nf; rw [Real.sq_sqrt (by nlinarith)]; ring
    have h_exp_arg : R ^ 2 / (2 * σ ^ 2) = -Real.log δ := by
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
      ≤ C / (1 - Real.exp (-(R ^ 2 / (2 * σ ^ 2)))) := h_tail
    _ < η := hR_bound

end
