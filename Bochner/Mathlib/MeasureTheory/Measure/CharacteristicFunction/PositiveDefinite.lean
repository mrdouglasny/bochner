/-
Copyright (c) 2026 Axiomatic AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michael R. Douglas
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.LinearAlgebra.Matrix.Circulant
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Bochner.Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive-definite functions

A function `φ : G → ℂ` on an additive group is *positive-definite* when the matrix
`(x, y) ↦ φ (x - y)`, indexed by `G`, is positive semidefinite, `(Matrix.circulant φ).PosSemidef`:
`∑ᵢⱼ conj cᵢ φ (xᵢ - xⱼ) cⱼ ≥ 0` for finitely many points and coefficients
[Gel'fand–Vilenkin, IV, Ch. II, §3.2, (1)][gelfand1964generalized4]. Then `φ 0 ≥ 0`,
`φ (-x) = conj (φ x)` and `‖φ x‖ ≤ φ 0` (loc. cit.). Fourier transforms `x ↦ ∫ e^{i f x ω} dν(ω)`
of finite measures along additive families `f` — characteristic functions, Fourier transforms on a
weak dual — are positive-definite, and so is the product of a positive-definite function with one;
the converse is Bochner's theorem.

The analytic content is `Matrix.PosSemidef.circulant_integral_integral_sub_nonneg`:
`∫∫ φ (x - y) dν dν ≥ 0` for every finite measure `ν`. Gel'fand–Vilenkin pass from the finite sums
to the integral by Riemann sums, [Douglas 2026][douglas2026bochner] by Fejér averages; here it is
by sampling. For independent points `X₁, …, X_N` of law `ν`, the expectation of
`∑ᵢⱼ φ (Xᵢ - Xⱼ) ≥ 0` is `N φ 0 + N (N - 1) ∫∫ φ (x - y) dν dν`, so the double integral is
nonnegative. On a finite-dimensional inner product space, averaging it over balls gives `∫ φ ≥ 0`
for integrable `φ`, modulating `φ` gives `𝓕 φ ≥ 0`, and testing `𝓕 φ` against Gaussians gives
`𝓕 φ ∈ L¹`: what Bochner's theorem needs.

## Main results

* `Matrix.PosSemidef.circulant_norm_le`: `‖φ x‖ ≤ φ 0`
* `Matrix.PosSemidef.circulant_norm_sub_sq_le`: Krein's inequality
  `‖φ x - φ y‖² ≤ 2 φ 0 · Re (φ 0 - φ (x - y))`, so continuity of `Re φ` at `0` is continuity
  (`Matrix.PosSemidef.circulant_continuous`)
* `Matrix.PosSemidef.circulant_mul_integral_cexp`: the product of a positive-definite function
  with a Fourier transform is positive-definite; `Matrix.PosSemidef.circulant_mul_charFun` is the
  case of a characteristic function
* `posSemidef_circulant_integral_cexp`, `posSemidef_circulant_charFun`: Fourier transforms and
  characteristic functions are positive-definite
* `Matrix.PosSemidef.circulant_integral_integral_sub_nonneg`: `∫∫ φ (x - y) dν dν ≥ 0`
* `Matrix.PosSemidef.circulant_fourier_nonneg`, `Matrix.PosSemidef.circulant_integrable_fourier`:
  a measurable integrable positive-definite function has a nonnegative integrable Fourier
  transform

## Provenance

Ported from or4nge19/QuantumlibCore `pin-v4.34.1` `9a741c08`,
`QuantumlibCore/ToMathlib/MeasureTheory/Measure/CharacteristicFunction/PositiveDefinite.lean` (Lean
v4.34.1, Mathlib `d13f23b7`), with module paths renamed; notices kept.
-/

@[expose] public section

open Matrix MeasureTheory Complex ProbabilityTheory Metric Filter Real
open scoped ComplexOrder RealInnerProductSpace FourierTransform Topology

namespace Matrix.PosSemidef

section Group

variable {G : Type*} [AddGroup G] {φ : G → ℂ} (hφ : (circulant φ).PosSemidef)
include hφ

theorem circulant_zero_nonneg : 0 ≤ φ 0 := by
  simpa [circulant_apply] using hφ.2 (Finsupp.single 0 1)

theorem circulant_neg (x : G) : φ (-x) = star (φ x) := by
  simpa [circulant_apply] using (hφ.1.apply 0 x).symm

theorem circulant_norm_le (x : G) : ‖φ x‖ ≤ (φ 0).re := by
  have hdet := (hφ.submatrix ![0, x]).det_nonneg
  obtain ⟨h0re, h0im⟩ := Complex.nonneg_iff.1 hφ.circulant_zero_nonneg
  rw [det_fin_two] at hdet
  simp only [submatrix_apply, circulant_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_self, sub_zero, zero_sub, hφ.circulant_neg] at hdet
  have hconj : star (φ x) * φ x = ((‖φ x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hφ0 : φ 0 = ((φ 0).re : ℂ) := Complex.ext rfl (by simp [← h0im])
  rw [hconj, hφ0] at hdet
  have h := (Complex.nonneg_iff.1 hdet).1
  simp only [sub_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero] at h
  nlinarith [norm_nonneg (φ x)]

/-- Positive definiteness pulls back along additive maps. -/
theorem circulant_comp {H : Type*} [AddGroup H] (L : H →+ G) :
    (circulant (φ ∘ L)).PosSemidef := by
  refine posSemidef_iff_forall_fin.2 fun k x ↦ ?_
  convert hφ.submatrix (L ∘ x) using 1
  ext i j
  simp [circulant_apply, map_sub]

/-- **Krein's inequality** `‖φ x - φ y‖² ≤ 2 φ 0 · Re (φ 0 - φ (x - y))`, from the `3 × 3` minor at
`0, x, y`: a positive-definite function continuous at `0` is uniformly continuous. -/
theorem circulant_norm_sub_sq_le (x y : G) :
    ‖φ x - φ y‖ ^ 2 ≤ 2 * (φ 0).re * (φ 0 - φ (x - y)).re := by
  obtain ⟨h0re, h0im⟩ := Complex.nonneg_iff.1 hφ.circulant_zero_nonneg
  rcases h0re.eq_or_lt with ha | ha
  · have hx := hφ.circulant_norm_le x
    have hy := hφ.circulant_norm_le y
    rw [← ha] at hx hy
    simp [norm_le_zero_iff.1 hx, norm_le_zero_iff.1 hy, ← ha]
  set a := (φ 0).re with hadef
  set b := φ x - φ y with hbdef
  have hφ0 : φ 0 = (a : ℂ) := Complex.ext rfl (by simp [← h0im])
  have hQ := (posSemidef_iff_dotProduct_mulVec.1 (hφ.submatrix ![0, x, y])).2
    ![-((a⁻¹ : ℝ) : ℂ) * starRingEnd ℂ b, 1, -1]
  simp only [dotProduct, mulVec, Fin.sum_univ_three, submatrix_apply, circulant_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Pi.star_apply, sub_self, sub_zero, zero_sub] at hQ
  rw [hφ.circulant_neg x, hφ.circulant_neg y, ← neg_sub x y, hφ.circulant_neg (x - y), hφ0]
    at hQ
  have key : star (-((a⁻¹ : ℝ) : ℂ) * starRingEnd ℂ b) *
        ((a : ℂ) * (-((a⁻¹ : ℝ) : ℂ) * starRingEnd ℂ b) + star (φ x) * 1 + star (φ y) * -1) +
      star 1 * (φ x * (-((a⁻¹ : ℝ) : ℂ) * starRingEnd ℂ b) + (a : ℂ) * 1 + φ (x - y) * -1) +
      star (-1) * (φ y * (-((a⁻¹ : ℝ) : ℂ) * starRingEnd ℂ b) + star (φ (x - y)) * 1 +
        (a : ℂ) * -1) = ((2 * a - 2 * (φ (x - y)).re - ‖b‖ ^ 2 / a : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp [hbdef, Complex.sq_norm, Complex.normSq_apply] <;>
      field_simp <;> ring
  rw [key] at hQ
  have h := (Complex.nonneg_iff.1 hQ).1
  simp only [ofReal_re] at h
  have h' : ‖b‖ ^ 2 / a ≤ 2 * a - 2 * (φ (x - y)).re := by linarith
  rw [div_le_iff₀ ha] at h'
  have : (φ 0 - φ (x - y)).re = a - (φ (x - y)).re := by simp [hadef]
  rw [this]
  nlinarith

/-- A positive-definite function whose real part is continuous at `0` is continuous, by Krein's
inequality. -/
theorem circulant_continuous [TopologicalSpace G] [IsTopologicalAddGroup G]
    (h : ContinuousAt (fun x ↦ (φ x).re) 0) : Continuous φ := by
  refine continuous_iff_continuousAt.2 fun x ↦ tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have hsub : Tendsto (fun y ↦ y - x) (𝓝 x) (𝓝 0) := by
    simpa using (tendsto_id.sub_const x : Tendsto (fun y ↦ y - x) (𝓝 x) (𝓝 (x - x)))
  have hre : Tendsto (fun y ↦ √(2 * (φ 0).re * (φ 0 - φ (y - x)).re)) (𝓝 x) (𝓝 0) := by
    have := ((tendsto_const_nhds (x := (φ 0).re)).sub (h.tendsto.comp hsub)).const_mul
      (2 * (φ 0).re)
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto _).comp this
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun y ↦ ?_) hre
  rw [← Real.sqrt_sq (norm_nonneg _)]
  exact Real.sqrt_le_sqrt (hφ.circulant_norm_sub_sq_le y x)

/-- **Positivity passes to integrals**: `∫∫ φ (x - y) dν dν ≥ 0` for every finite measure `ν`
[Gel'fand–Vilenkin, IV, Ch. II, §3.2, (4)][gelfand1964generalized4], without their bounded support.
For independent points `X₁, …, X_N` of law `ν`, `0 ≤ 𝔼 ∑ᵢⱼ φ (Xᵢ - Xⱼ) = N φ 0 + N (N - 1) J`. -/
theorem circulant_integral_integral_sub_nonneg {mG : MeasurableSpace G} [MeasurableSub₂ G]
    (hm : Measurable φ) (ν : Measure G) [IsFiniteMeasure ν] :
    0 ≤ ∫ x, ∫ y, φ (x - y) ∂ν ∂ν := by
  -- reduce to a probability measure
  rcases eq_zero_or_neZero ν with rfl | hν
  · simp
  set ν₁ : Measure G := (ν Set.univ)⁻¹ • ν with hν₁
  have : IsProbabilityMeasure ν₁ := by
    constructor
    rw [hν₁, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel
      (NeZero.ne (ν Set.univ)) (measure_ne_top ν _)]
  have hscale : ∫ x, ∫ y, φ (x - y) ∂ν ∂ν =
      ((ν.real Set.univ) ^ 2 : ℝ) • ∫ x, ∫ y, φ (x - y) ∂ν₁ ∂ν₁ := by
    have hν' : ν = (ν Set.univ) • ν₁ := by
      rw [hν₁, smul_smul, ENNReal.mul_inv_cancel (NeZero.ne (ν Set.univ)) (measure_ne_top ν _),
        one_smul]
    conv_lhs => rw [hν']
    simp only [integral_smul_measure, integral_smul, smul_smul, measureReal_def, sq]
  rw [hscale]
  refine smul_nonneg (sq_nonneg _) ?_
  -- the sampling argument for the probability measure `ν₁`
  set J := ∫ x, ∫ y, φ (x - y) ∂ν₁ ∂ν₁ with hJdef
  have hf : Measurable fun p : G × G ↦ φ (p.1 - p.2) := hm.comp measurable_sub
  have hfi : Integrable (fun p : G × G ↦ φ (p.1 - p.2)) (ν₁.prod ν₁) :=
    (integrable_const (φ 0).re).mono' hf.aestronglyMeasurable
      (ae_of_all _ fun p ↦ hφ.circulant_norm_le _)
  have hJ : ∫ p, φ (p.1 - p.2) ∂(ν₁.prod ν₁) = J := integral_prod _ hfi
  have hN (N : ℕ) : 0 ≤ (N : ℂ) * φ 0 + ((N : ℂ) * N - N) * J := by
    set P : Measure (Fin N → G) := Measure.pi fun _ ↦ ν₁ with hP
    have hpair (i j : Fin N) (hij : i ≠ j) : ∫ ω, φ (ω i - ω j) ∂P = J := by
      have hind : IndepFun (fun ω : Fin N → G ↦ ω i) (fun ω ↦ ω j) P :=
        (iIndepFun_pi (X := fun _ ↦ id) fun _ ↦ aemeasurable_id).indepFun hij
      have hmap : P.map (fun ω ↦ (ω i, ω j)) = ν₁.prod ν₁ := by
        rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
          (measurable_pi_apply j).aemeasurable).1 hind,
          (measurePreserving_eval (fun _ ↦ ν₁) i).map_eq,
          (measurePreserving_eval (fun _ ↦ ν₁) j).map_eq]
      rw [← hJ, ← hmap, integral_map ((measurable_pi_apply i).prodMk
        (measurable_pi_apply j)).aemeasurable hf.aestronglyMeasurable]
    have hint (i j : Fin N) : Integrable (fun ω : Fin N → G ↦ φ (ω i - ω j)) P :=
      (integrable_const (φ 0).re).mono'
        (hm.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))).aestronglyMeasurable
        (ae_of_all _ fun ω ↦ hφ.circulant_norm_le _)
    have hsum : ∫ ω, ∑ i, ∑ j, φ (ω i - ω j) ∂P = (N : ℂ) * φ 0 + ((N : ℂ) * N - N) * J := by
      rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
      have hrow (i : Fin N) : ∫ ω, ∑ j, φ (ω i - ω j) ∂P = φ 0 + ((N : ℂ) - 1) * J := by
        rw [integral_finsetSum _ fun j _ ↦ hint i j]
        have : ∀ j, ∫ ω, φ (ω i - ω j) ∂P = J + if j = i then φ 0 - J else 0 := fun j ↦ by
          by_cases hji : j = i
          · subst hji
            simp [integral_const]
          · rw [ite_eq_right hji, add_zero, hpair i j (Ne.symm hji)]
        simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [← hsum]
    refine integral_nonneg fun ω ↦ ?_
    simpa [dotProduct, mulVec, submatrix_apply, circulant_apply] using
      (posSemidef_iff_dotProduct_mulVec.1 (hφ.submatrix ω)).2 1
  -- `0 ≤ N φ 0 + N (N - 1) J` for all `N` forces `0 ≤ J`
  obtain ⟨h0re, h0im⟩ := Complex.nonneg_iff.1 hφ.circulant_zero_nonneg
  have him : J.im = 0 := by
    have h2 := (Complex.nonneg_iff.1 (hN 2)).2
    simp only [add_im, mul_im, natCast_re, natCast_im, sub_im, sub_re, mul_re, zero_mul,
      mul_zero, sub_zero, add_zero, ← h0im] at h2
    norm_num at h2
    linarith
  refine Complex.nonneg_iff.2 ⟨?_, him.symm⟩
  by_contra! hneg
  obtain ⟨N, hN'⟩ := exists_nat_gt ((φ 0).re / -J.re + 1)
  have h := (Complex.nonneg_iff.1 (hN N)).1
  simp only [add_re, mul_re, natCast_re, natCast_im, sub_re, sub_im, mul_im, zero_mul,
    mul_zero, sub_zero, him] at h
  have hJ0 : 0 < -J.re := neg_pos.2 hneg
  have hN1 : (1 : ℝ) < N := by
    have := div_nonneg h0re hJ0.le
    linarith
  have h1 : (φ 0).re < ((N : ℝ) - 1) * -J.re :=
    (div_lt_iff₀ hJ0).1 (by linarith)
  nlinarith

end Group

section Fourier

variable {G Ω : Type*} [AddGroup G] {mΩ : MeasurableSpace Ω}

/-- **The product of a positive-definite function with a Fourier transform is positive-definite**:
for a finite measure `ν` and an additive family `f` of measurable real functions, the quadratic
form of `φ · ∫ e^{i f(·) ω} dν(ω)` is the `ν`-integral of those of `φ` against the modulated
coefficients `ω ↦ e^{-i f xⱼ ω} cⱼ`. -/
theorem circulant_mul_integral_cexp {φ : G → ℂ} (hφ : (circulant φ).PosSemidef) (ν : Measure Ω)
    [IsFiniteMeasure ν] (f : G →+ Ω → ℝ) (hf : ∀ x, Measurable (f x)) :
    (circulant (φ * fun x ↦ ∫ ω, exp (f x ω * I) ∂ν)).PosSemidef := by
  have hint (t : G) : Integrable (fun ω ↦ exp (f t ω * I)) ν :=
    Integrable.of_bound ((measurable_ofReal.comp (hf t)).mul_const I).cexp.aestronglyMeasurable 1
      (Eventually.of_forall fun ω ↦ by rw [norm_exp_ofReal_mul_I])
  refine posSemidef_iff_forall_fin.2 fun k x ↦ posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun c ↦ ?_⟩
  · refine IsHermitian.ext fun i j ↦ ?_
    simp only [submatrix_apply, circulant_apply, Pi.mul_apply]
    rw [← neg_sub (x j) (x i), hφ.circulant_neg, star_mul', Complex.star_def,
      ← integral_conj]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)
    simp only [map_neg, Pi.neg_apply, ofReal_neg, neg_mul, ← Complex.exp_conj, map_mul,
      conj_ofReal, conj_I, mul_neg]
  · have hB := posSemidef_iff_dotProduct_mulVec.1 (hφ.submatrix x)
    set d : Ω → Fin k → ℂ := fun ω j ↦ exp (-(f (x j) ω : ℂ) * I) * c j with hd
    have hpt (ω : Ω) : star (d ω) ⬝ᵥ ((circulant φ).submatrix x x *ᵥ d ω) =
        ∑ i, ∑ j, star (c i) * φ (x i - x j) * c j * exp (f (x i - x j) ω * I) := by
      simp only [dotProduct, mulVec, submatrix_apply, circulant_apply, Finset.mul_sum, hd,
        Pi.star_apply, star_mul', Complex.star_def, ← Complex.exp_conj, map_mul, map_neg,
        Complex.conj_ofReal, Complex.conj_I]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_sub, Pi.sub_apply, ofReal_sub, sub_mul, Complex.exp_sub, div_eq_mul_inv,
        ← Complex.exp_neg]
      ring_nf
    have hform : star c ⬝ᵥ ((circulant (φ * fun x ↦ ∫ ω, exp (f x ω * I) ∂ν)).submatrix x x *ᵥ c) =
        ∫ ω, star (d ω) ⬝ᵥ ((circulant φ).submatrix x x *ᵥ d ω) ∂ν := by
      simp_rw [hpt]
      rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
        (hint _).const_mul _]
      simp_rw [integral_finsetSum _ fun j _ ↦ (hint _).const_mul _, integral_const_mul]
      simp only [dotProduct, mulVec, submatrix_apply, circulant_apply, Pi.mul_apply,
        Finset.mul_sum, Pi.star_apply]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    rw [hform]
    exact integral_nonneg fun ω ↦ hB.2 (d ω)

end Fourier

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {mE : MeasurableSpace E}
  [OpensMeasurableSpace E]

/-- The product of a positive-definite function with a characteristic function is
positive-definite. -/
theorem circulant_mul_charFun {φ : E → ℂ} (hφ : (circulant φ).PosSemidef) (ν : Measure E)
    [IsFiniteMeasure ν] : (circulant (φ * charFun ν)).PosSemidef := by
  let f : E →+ E → ℝ :=
    { toFun := fun x v ↦ ⟪v, x⟫
      map_zero' := funext fun v ↦ inner_zero_right v
      map_add' := fun x y ↦ funext fun v ↦ inner_add_right v x y }
  have h := hφ.circulant_mul_integral_cexp ν f fun x ↦
    (continuous_id.inner continuous_const).measurable
  convert h using 3
  exact funext fun t ↦ charFun_apply (μ := ν) t

end InnerProductSpace

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {φ : E → ℂ} (hφ : (circulant φ).PosSemidef)
include hφ

/-- **A continuous integrable positive-definite function has nonnegative integral**: over a ball
`B_R`, `∫∫ φ (x - y) = ∫ φ z · vol (B_R ∩ B_R(z)) dz ≥ 0`, and the overlap ratio
`vol (B_R ∩ B_R(z)) / vol B_R` tends to `1`. -/
theorem circulant_integral_nonneg (hφm : Measurable φ) (hi : Integrable φ) :
    0 ≤ ∫ x, φ x := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : (fun x : E ↦ φ x) = fun _ ↦ φ 0 := funext fun x ↦ by rw [Subsingleton.elim x 0]
    rw [this, integral_const]
    exact smul_nonneg measureReal_nonneg hφ.circulant_zero_nonneg
  set d := Module.finrank ℝ E
  set v₁ := (volume : Measure E).real (ball 0 1) with hv₁
  have hv₁pos : 0 < v₁ :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hvol (c : E) {r : ℝ} (hr : 0 ≤ r) : (volume : Measure E).real (ball c r) = r ^ d * v₁ := by
    rw [measureReal_def, Measure.addHaar_ball volume c hr, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hr d), ← measureReal_def]
  -- the overlap of two balls of radius `R`, at distance `‖z‖`
  set m : ℝ → E → ℝ := fun R z ↦ (volume : Measure E).real (ball 0 R ∩ ball z R) with hm
  -- (i) the double integral over `B_R` is `∫ φ z · m R z`
  have hinner (R : ℝ) (x : E) :
      ∫ y in ball (0 : E) R, φ (x - y) = ∫ z in ball x R, φ z := by
    rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball,
      ← integral_sub_left_eq_self _ volume x]
    congr 1
    funext z
    simp only [Set.indicator, mem_ball, sub_sub_cancel, dist_eq_norm, sub_zero, norm_sub_rev]
  have hdouble (R : ℝ) :
      ∫ x in ball (0 : E) R, ∫ y in ball (0 : E) R, φ (x - y) = ∫ z, φ z * m R z := by
    simp_rw [hinner]
    set S : Set (E × E) := {p | p.1 ∈ ball (0 : E) R ∧ p.2 ∈ ball p.1 R} with hS
    have hSm : MeasurableSet S :=
      (measurableSet_ball.preimage measurable_fst).inter
        (measurableSet_lt (measurable_snd.dist measurable_fst) measurable_const)
    have h1 : Integrable ((ball (0 : E) R).indicator fun _ ↦ (1 : ℝ)) :=
      (integrableOn_const (C := (1 : ℝ))
        (measure_ball_lt_top (x := (0 : E)) (r := R)).ne).integrable_indicator measurableSet_ball
    have hG : Integrable (S.indicator fun p ↦ φ p.2) (volume.prod volume) := by
      refine (h1.mul_prod hi.norm).mono'
        ((hφm.comp measurable_snd).aestronglyMeasurable.indicator hSm) (ae_of_all _ fun p ↦ ?_)
      by_cases hp : p ∈ S
      · have hp1 : p.1 ∈ ball (0 : E) R := hp.1
        rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp1, one_mul]
      · rw [Set.indicator_of_notMem hp, norm_zero]
        exact mul_nonneg (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _) (norm_nonneg _)
    have hswap := integral_integral_swap (f := fun x z ↦ S.indicator (fun p ↦ φ p.2) (x, z)) hG
    calc ∫ x in ball (0 : E) R, ∫ z in ball x R, φ z
        = ∫ x, ∫ z, S.indicator (fun p ↦ φ p.2) (x, z) := by
          rw [← integral_indicator measurableSet_ball]
          congr 1
          funext x
          by_cases hx : x ∈ ball (0 : E) R
          · rw [Set.indicator_of_mem hx, ← integral_indicator measurableSet_ball]
            congr 1
            funext z
            by_cases hz : z ∈ ball x R
            · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (s := S) ⟨hx, hz⟩]
            · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (s := S) fun h ↦ hz h.2]
          · rw [Set.indicator_of_notMem hx]
            have : (fun z ↦ S.indicator (fun p ↦ φ p.2) (x, z)) = fun _ ↦ 0 :=
              funext fun z ↦ Set.indicator_of_notMem (s := S) (fun h ↦ hx h.1) _
            rw [this, integral_zero]
      _ = ∫ z, ∫ x, S.indicator (fun p ↦ φ p.2) (x, z) := hswap
      _ = ∫ z, φ z * m R z := by
          simp only [hm]
          congr 1
          funext z
          have : (fun x ↦ S.indicator (fun p ↦ φ p.2) (x, z)) =
              (ball (0 : E) R ∩ ball z R).indicator fun _ ↦ φ z := by
            funext x
            by_cases hx : x ∈ ball (0 : E) R ∩ ball z R
            · rw [Set.indicator_of_mem hx, Set.indicator_of_mem]
              exact ⟨hx.1, by simpa [dist_comm] using hx.2⟩
            · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
              exact fun h ↦ hx ⟨h.1, by simpa [dist_comm] using h.2⟩
          rw [this, integral_indicator (measurableSet_ball.inter measurableSet_ball),
            setIntegral_const, Complex.real_smul, mul_comm]
  have hpos (R : ℝ) : 0 ≤ ∫ z, φ z * m R z := by
    have : IsFiniteMeasure (volume.restrict (ball (0 : E) R)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    rw [← hdouble]
    exact hφ.circulant_integral_integral_sub_nonneg hφm _
  -- (ii) the overlap ratio tends to `1`
  have hle (R : ℝ) (z : E) : m R z ≤ (volume : Measure E).real (ball 0 R) :=
    measureReal_mono Set.inter_subset_left measure_ball_lt_top.ne
  have hge (R : ℝ) (z : E) :
      (volume : Measure E).real (ball ((2 : ℝ)⁻¹ • z) (R - ‖z‖ / 2)) ≤ m R z := by
    have hz2 : ‖(2 : ℝ)⁻¹ • z‖ = ‖z‖ / 2 := by
      rw [norm_smul]
      norm_num
      ring
    refine measureReal_mono (fun x hx ↦ ⟨?_, ?_⟩)
      ((measure_mono Set.inter_subset_left).trans_lt measure_ball_lt_top).ne
    · rw [mem_ball, dist_eq_norm] at hx
      rw [mem_ball, dist_zero_right]
      calc ‖x‖ = ‖(x - (2 : ℝ)⁻¹ • z) + (2 : ℝ)⁻¹ • z‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - (2 : ℝ)⁻¹ • z‖ + ‖(2 : ℝ)⁻¹ • z‖ := norm_add_le _ _
        _ < R := by linarith
    · rw [mem_ball, dist_eq_norm] at hx
      rw [mem_ball, dist_eq_norm]
      have h : x - z = (x - (2 : ℝ)⁻¹ • z) - (2 : ℝ)⁻¹ • z := by
        rw [sub_sub, ← add_smul]
        norm_num
      calc ‖x - z‖ = ‖(x - (2 : ℝ)⁻¹ • z) - (2 : ℝ)⁻¹ • z‖ := by rw [h]
        _ ≤ ‖x - (2 : ℝ)⁻¹ • z‖ + ‖(2 : ℝ)⁻¹ • z‖ := norm_sub_le _ _
        _ < R := by linarith
  have hratio (z : E) : Tendsto (fun R ↦ m R z / (R ^ d * v₁)) atTop (𝓝 1) := by
    have hlow : Tendsto (fun R : ℝ ↦ (1 - ‖z‖ / 2 / R) ^ d) atTop (𝓝 1) := by
      simpa using (((tendsto_const_nhds (x := ‖z‖ / 2)).div_atTop
        (tendsto_id (α := ℝ) (x := atTop))).const_sub 1).pow d
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop (‖z‖ / 2)] with R hR
      have hR0 : 0 < R := (div_nonneg (norm_nonneg z) zero_le_two).trans_lt hR
      rw [le_div_iff₀ (by positivity)]
      calc (1 - ‖z‖ / 2 / R) ^ d * (R ^ d * v₁) = (R - ‖z‖ / 2) ^ d * v₁ := by
            rw [← mul_assoc, ← mul_pow, sub_mul, one_mul, div_mul_cancel₀ _ hR0.ne']
        _ = (volume : Measure E).real (ball ((2 : ℝ)⁻¹ • z) (R - ‖z‖ / 2)) :=
            (hvol _ (by linarith)).symm
        _ ≤ m R z := hge R z
    · filter_upwards [eventually_gt_atTop 0] with R hR
      rw [div_le_one (by positivity), ← hvol 0 hR.le]
      exact hle R z
  -- (iii) dominated convergence
  have hmeas (R : ℝ) : Measurable (m R) := by
    have hS : MeasurableSet {p : E × E | p.1 ∈ ball (0 : E) R ∧ p.1 ∈ ball p.2 R} :=
      (measurableSet_ball.preimage measurable_fst).inter
        (measurableSet_lt (measurable_fst.dist measurable_snd) measurable_const)
    exact (measurable_measure_prodMk_right hS).ennreal_toReal
  have hlim : Tendsto (fun R ↦ ∫ z, φ z * ((m R z / (R ^ d * v₁) : ℝ) : ℂ)) atTop
      (𝓝 (∫ z, φ z)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z ↦ ‖φ z‖) (.of_forall fun R ↦
      hφm.aestronglyMeasurable.mul ((hmeas R).div_const _).complex_ofReal.aestronglyMeasurable)
      ?_ hi.norm (.of_forall fun z ↦ ?_)
    · filter_upwards [eventually_gt_atTop 0] with R hR
      refine .of_forall fun z ↦ ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_nonneg measureReal_nonneg,
        abs_of_pos (by positivity)]
      refine mul_le_of_le_one_right (norm_nonneg _) ((div_le_one (by positivity)).2 ?_)
      rw [← hvol 0 hR.le]
      exact hle R z
    · simpa using tendsto_const_nhds.mul ((continuous_ofReal.tendsto 1).comp (hratio z))
  refine ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨1, fun R hR ↦ ?_⟩)
  have heq : ∫ z, φ z * ((m R z / (R ^ d * v₁) : ℝ) : ℂ) =
      ((R ^ d * v₁)⁻¹ : ℝ) • ∫ z, φ z * m R z := by
    rw [← integral_smul]
    congr 1
    funext z
    rw [Complex.real_smul]
    push_cast
    ring
  rw [heq]
  exact smul_nonneg (inv_nonneg.2 (by positivity)) (hpos R)

/-- **A continuous integrable positive-definite function has a nonnegative Fourier transform**:
`𝓕 φ ξ` is the integral of `v ↦ e^{-2πi⟪v, ξ⟫} φ v`, positive-definite as the product of `φ` with
the characteristic function of a Dirac mass. -/
theorem circulant_fourier_nonneg (hφm : Measurable φ) (hi : Integrable φ) (ξ : E) :
    0 ≤ 𝓕 φ ξ := by
  have hψ := hφ.circulant_mul_charFun (Measure.dirac (-(2 * π) • ξ))
  have heq : φ * charFun (Measure.dirac (-(2 * π) • ξ)) = fun v ↦ 𝐞 (-⟪v, ξ⟫) • φ v := by
    funext v
    rw [Pi.mul_apply, charFun_dirac, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul,
      mul_comm, real_inner_smul_left, real_inner_comm]
    congr 2
    push_cast
    ring
  rw [heq] at hψ
  rw [Real.fourier_eq]
  have hmeas : Measurable fun v ↦ 𝐞 (-⟪v, ξ⟫) • φ v := by
    simp_rw [Circle.smul_def, Real.fourierChar_apply]
    exact (by fun_prop : Continuous fun v : E ↦ cexp (↑(2 * π * -⟪v, ξ⟫) * I)).measurable.mul hφm
  exact hψ.circulant_integral_nonneg hmeas
    ((Real.fourierIntegral_convergent_iff ξ).2 hi)

/-- **A continuous integrable positive-definite function has an integrable Fourier transform**:
against the Gaussians `Gₙ ξ = e^{-π ‖ξ‖² / (n + 1)}`, whose Fourier transforms are nonnegative of
integral `1`, `∫ 𝓕 φ · Gₙ = ∫ φ · 𝓕 Gₙ ≤ φ 0`, and `Gₙ → 1`; Fatou's lemma concludes. -/
theorem circulant_integrable_fourier (hφm : Measurable φ) (hi : Integrable φ) :
    Integrable (𝓕 φ) := by
  have hpos := hφ.circulant_fourier_nonneg hφm hi
  have hcont : Continuous (𝓕 φ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hi
  set d := Module.finrank ℝ E
  -- the Gaussians and their Fourier transforms
  set g : ℕ → E → ℝ := fun n ξ ↦ rexp (-(π / (n + 1)) * ‖ξ‖ ^ 2) with hg
  have hb (n : ℕ) : 0 < (((π / (n + 1) : ℝ)) : ℂ).re := by
    simp only [ofReal_re]
    positivity
  have hb' (n : ℕ) : 0 < (((π * (n + 1) : ℝ)) : ℂ).re := by
    simp only [ofReal_re]
    positivity
  have hG (n : ℕ) : (fun ξ ↦ ((g n ξ : ℝ) : ℂ)) =
      fun ξ ↦ cexp (-((π / (n + 1) : ℝ) : ℂ) * ‖ξ‖ ^ 2) := by
    funext ξ
    simp [hg, Complex.ofReal_exp]
  have hGi (n : ℕ) : Integrable (fun ξ ↦ ((g n ξ : ℝ) : ℂ)) := by
    rw [hG]
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (hb n) 0 (0 : E)
  have hFG (n : ℕ) (x : E) : 𝓕 (fun ξ ↦ ((g n ξ : ℝ) : ℂ)) x =
      (((n + 1 : ℝ) ^ ((d : ℝ) / 2) : ℝ) : ℂ) * cexp (-((π * (n + 1) : ℝ) : ℂ) * ‖x‖ ^ 2) := by
    rw [hG, fourier_gaussian_innerProductSpace (hb n), Complex.ofReal_cpow (by positivity)]
    congr 1
    · congr 1
      · push_cast
        field_simp
      · push_cast
        ring
    · congr 1
      push_cast
      field_simp
  have hFGi (n : ℕ) : Integrable (𝓕 (fun ξ ↦ ((g n ξ : ℝ) : ℂ))) := by
    rw [funext (hFG n)]
    exact (by simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (hb' n) 0 (0 : E) :
      Integrable fun x : E ↦ cexp (-((π * (n + 1) : ℝ) : ℂ) * ‖x‖ ^ 2)).const_mul _
  have hFGreal (n : ℕ) (x : E) : 𝓕 (fun ξ ↦ ((g n ξ : ℝ) : ℂ)) x =
      (((n + 1 : ℝ) ^ ((d : ℝ) / 2) * rexp (-(π * (n + 1)) * ‖x‖ ^ 2) : ℝ) : ℂ) := by
    rw [hFG]
    push_cast
    ring_nf
  have hFG1 (n : ℕ) : ∫ x, 𝓕 (fun ξ ↦ ((g n ξ : ℝ) : ℂ)) x = 1 := by
    have hGc : Continuous fun ξ ↦ ((g n ξ : ℝ) : ℂ) := by
      simp only [hg]
      fun_prop
    have h := congrFun (hGc.fourierInv_fourier_eq (hGi n) (hFGi n)) 0
    rw [Real.fourierInv_eq] at h
    simpa [hg] using h
  have hnorm1 (n : ℕ) : ∫ x, ‖𝓕 (fun ξ ↦ ((g n ξ : ℝ) : ℂ)) x‖ = 1 := by
    have : (fun x ↦ ‖𝓕 (fun ξ ↦ ((g n ξ : ℝ) : ℂ)) x‖) =
        fun x ↦ (𝓕 (fun ξ ↦ ((g n ξ : ℝ) : ℂ)) x).re := funext fun x ↦ by
      rw [hFGreal, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    have h := integral_re (hFGi n)
    simp only [RCLike.re_to_complex] at h
    rw [this, h, hFG1 n, one_re]
  -- the pairing `∫ 𝓕 φ · Gₙ = ∫ φ · 𝓕 Gₙ`, bounded by `φ 0`
  have hflip : (innerₗ E).flip = innerₗ E := LinearMap.ext₂ fun x y ↦ real_inner_comm x y
  have hpair (n : ℕ) :
      ∫ ξ, 𝓕 φ ξ * (g n ξ : ℂ) = ∫ x, φ x * 𝓕 (fun ξ ↦ ((g n ξ : ℝ) : ℂ)) x := by
    have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := 𝐞)
      (μ := (volume : Measure E)) (ν := volume) (L := innerₗ E) Real.continuous_fourierChar
      continuous_inner hi (hGi n)
    rw [hflip] at h
    simp only [smul_eq_mul] at h
    exact h
  have hbound (n : ℕ) : ‖∫ x, φ x * 𝓕 (fun ξ ↦ ((g n ξ : ℝ) : ℂ)) x‖ ≤ (φ 0).re := by
    calc ‖∫ x, φ x * 𝓕 (fun ξ ↦ ((g n ξ : ℝ) : ℂ)) x‖
        ≤ ∫ x, ‖φ x * 𝓕 (fun ξ ↦ ((g n ξ : ℝ) : ℂ)) x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, (φ 0).re * ‖𝓕 (fun ξ ↦ ((g n ξ : ℝ) : ℂ)) x‖ := by
          refine integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _)
            ((hFGi n).norm.const_mul _) (.of_forall fun x ↦ ?_)
          simp only [norm_mul]
          exact mul_le_mul_of_nonneg_right (hφ.circulant_norm_le x) (norm_nonneg _)
      _ = (φ 0).re := by rw [integral_const_mul, hnorm1, mul_one]
  -- `𝓕 φ` is real and nonnegative; Fatou's lemma bounds its integral by `φ 0`
  set f : E → ℝ := fun ξ ↦ (𝓕 φ ξ).re with hf
  have hf0 (ξ : E) : 0 ≤ f ξ := (Complex.nonneg_iff.1 (hpos ξ)).1
  have hfeq (ξ : E) : 𝓕 φ ξ = (f ξ : ℂ) :=
    Complex.ext rfl (by simp [hf, (Complex.nonneg_iff.1 (hpos ξ)).2.symm])
  have hgi (n : ℕ) : Integrable (g n) := by simpa using (hGi n).re
  have hlin (n : ℕ) : ∫⁻ ξ, ENNReal.ofReal (f ξ * g n ξ) ≤ ENNReal.ofReal (φ 0).re := by
    have hint : Integrable fun ξ ↦ f ξ * g n ξ :=
      (hgi n).bdd_mul (c := ∫ x, ‖φ x‖) (Complex.continuous_re.comp hcont).aestronglyMeasurable
        (ae_of_all _ fun ξ ↦ (Complex.abs_re_le_norm _).trans
          (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _))
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (.of_forall fun ξ ↦ mul_nonneg (hf0 ξ) (Real.exp_pos _).le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : ∫ ξ, f ξ * g n ξ = (∫ ξ, 𝓕 φ ξ * (g n ξ : ℂ)).re := by
      have h : (fun ξ ↦ 𝓕 φ ξ * (g n ξ : ℂ)) = fun ξ ↦ ((f ξ * g n ξ : ℝ) : ℂ) := by
        funext ξ
        rw [hfeq, ofReal_mul]
      rw [h, integral_complex_ofReal, ofReal_re]
    rw [this, hpair n]
    exact (Complex.re_le_norm _).trans (hbound n)
  have hfatou : ∫⁻ ξ, ENNReal.ofReal (f ξ) ≤ ENNReal.ofReal (φ 0).re := by
    calc ∫⁻ ξ, ENNReal.ofReal (f ξ)
        = ∫⁻ ξ, liminf (fun n ↦ ENNReal.ofReal (f ξ * g n ξ)) atTop := by
          congr 1
          funext ξ
          refine (Tendsto.liminf_eq ?_).symm
          have h0 : Tendsto (fun n : ℕ ↦ -(π / (n + 1)) * ‖ξ‖ ^ 2) atTop (𝓝 0) := by
            have h := ((tendsto_one_div_add_atTop_nhds_zero_nat.const_mul π).neg).mul_const
              (‖ξ‖ ^ 2)
            rw [mul_zero, neg_zero, zero_mul] at h
            exact h.congr fun n ↦ by ring
          have h1 : Tendsto (fun n ↦ g n ξ) atTop (𝓝 1) := by
            have h := (Real.continuous_exp.tendsto 0).comp h0
            rw [Real.exp_zero] at h
            exact h
          have h := (ENNReal.continuous_ofReal.tendsto _).comp
            ((tendsto_const_nhds (x := f ξ)).mul h1)
          rw [mul_one] at h
          exact h
      _ ≤ liminf (fun n ↦ ∫⁻ ξ, ENNReal.ofReal (f ξ * g n ξ)) atTop :=
          lintegral_liminf_le fun n ↦ ENNReal.measurable_ofReal.comp
            ((Complex.continuous_re.comp hcont).measurable.mul (by simp only [hg]; fun_prop))
      _ ≤ ENNReal.ofReal (φ 0).re := Filter.liminf_le_of_frequently_le' (.of_forall hlin)
  have hfi : Integrable f := ⟨(Complex.continuous_re.comp hcont).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (.of_forall hf0)).2 (hfatou.trans_lt ENNReal.ofReal_lt_top)⟩
  rw [funext hfeq]
  exact hfi.ofReal

end FiniteDimensional

end Matrix.PosSemidef

/-- The constant `1` is positive-definite: `∑ᵢⱼ conj cᵢ cⱼ = |∑ᵢ cᵢ|²`. -/
theorem Matrix.posSemidef_circulant_one {G : Type*} [AddGroup G] :
    (circulant (1 : G → ℂ)).PosSemidef :=
  posSemidef_iff_forall_fin.2 fun k x ↦
    posSemidef_iff_dotProduct_mulVec.2 ⟨IsHermitian.ext fun _ _ ↦ by simp [circulant_apply],
      fun c ↦ by
        simpa [dotProduct, mulVec, circulant_apply, ← Finset.mul_sum, ← Finset.sum_mul, star_sum]
          using star_mul_self_nonneg (∑ i, c i)⟩

/-- **Fourier transforms of finite measures are positive-definite**: for an additive family `f` of
measurable real functions, `∑ᵢⱼ conj cᵢ cⱼ ∫ e^{i f (xᵢ - xⱼ)} dν = ∫ |∑ᵢ cᵢ e^{-i f xᵢ}|² dν`. -/
theorem posSemidef_circulant_integral_cexp {G Ω : Type*} [AddGroup G] {mΩ : MeasurableSpace Ω}
    (ν : Measure Ω) [IsFiniteMeasure ν] (f : G →+ Ω → ℝ) (hf : ∀ x, Measurable (f x)) :
    (circulant fun x ↦ ∫ ω, exp (f x ω * I) ∂ν).PosSemidef := by
  simpa using posSemidef_circulant_one.circulant_mul_integral_cexp ν f hf

/-- **Characteristic functions are positive-definite** [Gel'fand–Vilenkin, IV, Ch. II, §3.2,
Thm 2][gelfand1964generalized4]:
`∑ᵢⱼ conj cᵢ cⱼ charFun ν (xᵢ - xⱼ) = ∫ |∑ᵢ conj cᵢ e^{i⟪v, xᵢ⟫}|² dν`. -/
theorem posSemidef_circulant_charFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {mE : MeasurableSpace E} [OpensMeasurableSpace E] (ν : Measure E) [IsFiniteMeasure ν] :
    (circulant (charFun ν)).PosSemidef := by
  simpa using posSemidef_circulant_one.circulant_mul_charFun ν
