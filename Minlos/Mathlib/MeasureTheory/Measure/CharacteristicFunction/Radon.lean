/-
Copyright (c) 2026 Axiomatic AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Minlos.Mathlib.MeasureTheory.Constructions.Projective

/-!
# Fourier uniqueness for Radon measures

A finite Radon measure on a Hausdorff space `X` is determined by its Fourier transform along a
separating linear family: if `f : X → V →ₗ[ℝ] ℝ` is continuous and injective, finite inner
regular measures with the same `L ↦ ∫ e^{i f x L}` are equal. Their marginals along finitely many
`L` agree by the finite-dimensional uniqueness theorem, hence the measures do, by Prokhorov's
uniqueness theorem (`MeasureTheory.ext_of_map_restrict_eq`) [Bourbaki, *INT*, IX, §6, no. 3,
Prop. 3 and §4, no. 2, Thm 1][bourbaki2004integration2].

Nothing countable is assumed. Mathlib's `MeasureTheory.Measure.ext_of_charFunDual` and
`MeasureTheory.Measure.ext_of_charFun` ask for a complete second-countable space, on which every
finite measure is Radon; here the space is arbitrary and the measures Radon, which covers
non-separable Hilbert spaces and weak duals.

## Main results

* `MeasureTheory.ext_of_forall_integral_cexp_eq`: uniqueness along a separating linear family
* `MeasureTheory.Measure.ext_of_charFunDual_of_innerRegular`: on a real normed space
* `MeasureTheory.Measure.ext_of_charFun_of_innerRegular`: on a real inner product space

## Provenance

Ported from or4nge19/QuantumlibCore `pin-v4.34.1` `9a741c08`,
`QuantumlibCore/ToMathlib/MeasureTheory/Measure/CharacteristicFunction/Radon.lean` (Lean v4.34.1,
Mathlib `d13f23b7`), with module paths renamed; notices kept.
-/

@[expose] public section

open Complex

namespace MeasureTheory

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A linear form on `ℝ^J` evaluated on the restriction of a linear form `ω` to `J`:
`L (ω|_J) = ω (∑ⱼ L eⱼ • j)`. -/
lemma apply_restrict_eq_apply_sum [DecidableEq V] (J : Finset V) (L : (J → ℝ) →ₗ[ℝ] ℝ)
    (ω : V →ₗ[ℝ] ℝ) :
    L (fun j : J ↦ ω j) = ω (∑ j : J, L (Pi.single j 1) • (j : V)) := by
  rw [LinearMap.pi_apply_eq_sum_univ L, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
  congr 2
  ext i
  simp [Pi.single_apply, eq_comm]

variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

/-- **A Radon measure is determined by its Fourier transform along a separating linear family**
[Bourbaki, *INT*, IX, §6, no. 3, Prop. 3 and §4, no. 2, Thm 1][bourbaki2004integration2]: for
`f : X → V →ₗ[ℝ] ℝ` continuous (into `V → ℝ`) and injective, finite inner regular measures with
the same `L ↦ ∫ e^{i f x L}` are equal. -/
theorem ext_of_forall_integral_cexp_eq {f : X → V →ₗ[ℝ] ℝ} (hf : Continuous fun x L ↦ f x L)
    (hinj : Function.Injective f) {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [μ.InnerRegular] [ν.InnerRegular]
    (h : ∀ L, ∫ x, cexp (f x L * I) ∂μ = ∫ x, cexp (f x L * I) ∂ν) :
    μ = ν := by
  classical
  refine ext_of_map_restrict_eq (α := fun _ : V ↦ ℝ) (f := fun x L ↦ f x L) hf
    (fun x y hxy ↦ hinj (LinearMap.ext fun L ↦ congrFun hxy L)) fun J ↦ ?_
  have hm : Measurable fun x ↦ J.restrict fun L ↦ f x L :=
    ((Finset.continuous_restrict J).comp hf).measurable
  refine Measure.ext_of_charFunDual (funext fun M ↦ ?_)
  rw [charFunDual_apply, charFunDual_apply,
    integral_map hm.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop)),
    integral_map hm.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
  have hM : ∀ x, M (J.restrict fun L ↦ f x L) = f x (∑ j : J, M (Pi.single j 1) • (j : V)) :=
    fun x ↦ apply_restrict_eq_apply_sum J M.toLinearMap (f x)
  simp_rw [hM]
  exact h _

/-- **Finite Radon measures on a real normed space are determined by `charFunDual`**, without
completeness or separability. -/
theorem Measure.ext_of_charFunDual_of_innerRegular {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] {μ ν : Measure E} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] [μ.InnerRegular] [ν.InnerRegular] (h : charFunDual μ = charFunDual ν) :
    μ = ν :=
  ext_of_forall_integral_cexp_eq (V := StrongDual ℝ E)
    (f := fun x ↦ (ContinuousLinearMap.apply ℝ ℝ x).toLinearMap)
    (continuous_pi fun L ↦ L.continuous)
    (fun _ _ hxy ↦ SeparatingDual.eq_iff_forall_dual_eq.2 fun L ↦ LinearMap.congr_fun hxy L)
    fun L ↦ congrFun h L

/-- **Finite Radon measures on a real inner product space are determined by `charFun`**, without
completeness or separability: Sazonov's measures on a non-separable Hilbert space are unique. -/
theorem Measure.ext_of_charFun_of_innerRegular {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] {μ ν : Measure E}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [μ.InnerRegular] [ν.InnerRegular]
    (h : charFun μ = charFun ν) :
    μ = ν :=
  ext_of_forall_integral_cexp_eq (f := innerₗ E)
    (continuous_pi fun _ ↦ continuous_id.inner continuous_const)
    (fun _ _ hxy ↦ ext_inner_right ℝ fun t ↦ LinearMap.congr_fun hxy t)
    fun t ↦ congrFun h t

end MeasureTheory
