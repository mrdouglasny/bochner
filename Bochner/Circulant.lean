/-
Copyright (c) 2026 Axiomatic AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michael R. Douglas
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Matrix.Circulant
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Bochner.Mathlib.MeasureTheory.Measure.CharacteristicFunction.PositiveDefinite
public import Bochner.Mathlib.LinearAlgebra.Matrix.PosDef
public import Bochner.Main

/-!
# Bochner's theorem for circulant positive-definite functions

`IsPositiveDefinite φ` is Mathlib's positive semidefiniteness of the matrix `(x, y) ↦ φ (x - y)`
indexed by the whole group, `(Matrix.circulant φ).PosSemidef`
(`isPositiveDefinite_iff_posSemidef_circulant`): both ask the finite kernel matrices
`φ (xᵢ - xⱼ)` to be Hermitian positive semidefinite (`Matrix.posSemidef_iff_forall_fin`).

In that vocabulary `bochner_theorem` reads: on a finite-dimensional real inner product space, the
characteristic functions of probability measures are exactly the continuous positive-definite `φ`
with `φ 0 = 1` [Gel'fand–Vilenkin, IV, Ch. II, §3.2, Thm 2][gelfand1964generalized4]; scaling by
`φ 0` gives the finite measures, of mass `φ 0`.

## Main results

* `isPositiveDefinite_iff_posSemidef_circulant`: the two definitions of positive-definite functions
  agree
* `MeasureTheory.exists_isProbabilityMeasure_charFun_eq_iff`: Bochner's theorem for probability
  measures, from `bochner_theorem`
* `MeasureTheory.exists_charFun_eq_iff`: Bochner's theorem for finite measures

## Provenance

The statements are those of or4nge19/QuantumlibCore `pin-v4.34.1` `9a741c08`,
`QuantumlibCore/ToMathlib/MeasureTheory/Measure/CharacteristicFunction/Bochner.lean`, whose own
proof of the probability case (Gaussian regularization, with the positivity of the regularized
Fourier transforms by sampling) is replaced by `bochner_theorem`: one Bochner theorem.
-/

@[expose] public section

open MeasureTheory Matrix Complex Filter Topology ProbabilityTheory Real
open scoped ComplexOrder FourierTransform RealInnerProductSpace NNReal ENNReal

/-- **Two definitions of positive-definite functions agree**: `IsPositiveDefinite φ` (Hermitian
symmetry and nonnegative real parts of the finite quadratic forms) is positive semidefiniteness of
the circulant matrix `(x, y) ↦ φ (x - y)` indexed by the group. -/
theorem isPositiveDefinite_iff_posSemidef_circulant {α : Type*} [AddGroup α] {φ : α → ℂ} :
    IsPositiveDefinite φ ↔ (circulant φ).PosSemidef := by
  rw [posSemidef_iff_forall_fin]
  refine ⟨fun hpd m x ↦ ?_, fun h ↦ ⟨fun x ↦ ?_, fun m x c ↦ ?_⟩⟩
  · have hM : ((circulant φ).submatrix x x).IsHermitian := by
      refine Matrix.IsHermitian.ext fun i j ↦ ?_
      simp only [submatrix_apply, circulant_apply]
      rw [← neg_sub, hpd.hermitian, RCLike.star_def, Complex.conj_conj]
    refine posSemidef_iff_dotProduct_mulVec.2 ⟨hM, fun c ↦ ?_⟩
    have hre : 0 ≤ (star c ⬝ᵥ ((circulant φ).submatrix x x *ᵥ c)).re := by
      simpa [dotProduct, mulVec, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
        using hpd.nonneg m x c
    have him : (star c ⬝ᵥ ((circulant φ).submatrix x x *ᵥ c)).im = 0 := by
      simpa using hM.im_star_dotProduct_mulVec_self c
    exact Complex.nonneg_iff.2 ⟨hre, him.symm⟩
  · have h1 := (h 2 ![x, 0]).isHermitian.apply 0 1
    simp only [submatrix_apply, circulant_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      sub_zero, zero_sub] at h1
    rw [← h1, RCLike.star_def, Complex.conj_conj]
  · have h2 := (posSemidef_iff_dotProduct_mulVec.1 (h m x)).2 c
    have := (Complex.nonneg_iff.1 h2).1
    simpa [dotProduct, mulVec, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using this

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Bochner's theorem** for probability measures [Gel'fand–Vilenkin, IV, Ch. II, §3.2,
Thm 2][gelfand1964generalized4]: `φ` is the characteristic function of a probability measure on a
finite-dimensional real inner product space iff it is continuous, positive-definite, and
`φ 0 = 1`. The converse direction is `bochner_theorem`. -/
theorem exists_isProbabilityMeasure_charFun_eq_iff {φ : E → ℂ} :
    (∃ μ : Measure E, IsProbabilityMeasure μ ∧ charFun μ = φ) ↔
      Continuous φ ∧ (circulant φ).PosSemidef ∧ φ 0 = 1 := by
  refine ⟨fun ⟨μ, _, hμ⟩ ↦ hμ ▸ ⟨continuous_charFun, posSemidef_circulant_charFun μ,
    by simp [charFun_zero]⟩, fun ⟨hc, hφ, h0⟩ ↦ ?_⟩
  obtain ⟨μ, hμ, -⟩ := bochner_theorem φ hc (isPositiveDefinite_iff_posSemidef_circulant.2 hφ) h0
  exact ⟨μ, inferInstance, funext hμ⟩

/-- **Bochner's theorem** [Gel'fand–Vilenkin, IV, Ch. II, §3.2, Thm 2][gelfand1964generalized4]:
the characteristic functions of finite measures on a finite-dimensional real inner product space are
exactly the continuous positive-definite functions. -/
theorem exists_charFun_eq_iff {φ : E → ℂ} :
    (∃ μ : Measure E, IsFiniteMeasure μ ∧ charFun μ = φ) ↔
      Continuous φ ∧ (circulant φ).PosSemidef := by
  refine ⟨fun ⟨μ, _, hμ⟩ ↦ hμ ▸ ⟨continuous_charFun, posSemidef_circulant_charFun μ⟩,
    fun ⟨hc, hφ⟩ ↦ ?_⟩
  obtain ⟨h0re, h0im⟩ := Complex.nonneg_iff.1 hφ.circulant_zero_nonneg
  rcases h0re.eq_or_lt with h0 | h0
  · refine ⟨0, inferInstance, funext fun t ↦ ?_⟩
    have h := hφ.circulant_norm_le t
    rw [← h0] at h
    simp [charFun_zero_measure, norm_le_zero_iff.1 h]
  set a := (φ 0).re with ha
  have hφ0 : φ 0 = (a : ℂ) := Complex.ext rfl (by simp [← h0im])
  have hψ : (circulant fun t ↦ (a⁻¹ : ℝ) • φ t).PosSemidef := by
    have h := hφ.smul (inv_nonneg.2 h0.le)
    rw [← circulant_smul] at h
    exact h
  obtain ⟨μ, hμ, hμφ⟩ :=
    (exists_isProbabilityMeasure_charFun_eq_iff (φ := fun t ↦ (a⁻¹ : ℝ) • φ t)).2
      ⟨hc.const_smul (a⁻¹ : ℝ), hψ, by
        rw [hφ0, Complex.real_smul, ← ofReal_mul, inv_mul_cancel₀ h0.ne', ofReal_one]⟩
  refine ⟨ENNReal.ofReal a • μ, ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩, funext fun t ↦ ?_⟩
  rw [charFun_apply, integral_smul_measure, ← charFun_apply, hμφ, ENNReal.toReal_ofReal h0.le,
    smul_smul, mul_inv_cancel₀ h0.ne', one_smul]

end MeasureTheory
