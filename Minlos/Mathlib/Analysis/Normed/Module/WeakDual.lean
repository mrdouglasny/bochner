/-
Copyright (c) 2026 Axiomatic AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.LocallyConvex.Basic
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# The Alaoglu–Bourbaki theorem

In the dual of a topological vector space over a proper field, the polar of a neighbourhood of `0`
is weak-* compact [Bourbaki, *EVT*, III, §3, no. 4, Cor. 2][bourbaki2023evt]: a neighbourhood is
absorbent, so the polar is pointwise bounded, and it is closed in `E → 𝕜`, a linear form bounded on
a neighbourhood of `0` being continuous; Tychonoff concludes. Mathlib's
`WeakDual.isCompact_polar` is the case of a normed space.

For a continuous positive quadratic form `H`, the ellipsoid `{ω | ω² ≤ r² H}` is therefore
weak-* compact, and by Hahn–Banach its image in `ℝ^J` is the finite-dimensional ellipsoid
`{t | (∑ aⱼ tⱼ)² ≤ r² H (∑ aⱼ j)}` — the two facts behind Minlos' theorem
[Bourbaki, *INT*, IX, §6, no. 10, Thm 2][bourbaki2004integration2].

## Provenance

Ported from or4nge19/QuantumlibCore `pin-v4.34.1` `9a741c08`,
`QuantumlibCore/ToMathlib/Analysis/Normed/Module/WeakDual.lean` (Lean v4.34.1, Mathlib `d13f23b7`),
with module paths renamed; notices kept.
-/

@[expose] public section

open Filter Topology Pointwise

namespace WeakDual

variable {𝕜 M : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [Module 𝕜 M]
  [ContinuousSMul 𝕜 M]

/-- **The Alaoglu–Bourbaki theorem** [Bourbaki, *EVT*, III, §3, no. 4, Cor. 2][bourbaki2023evt]:
the polar of a neighbourhood of `0` in a topological vector space is weak-* compact. -/
theorem isCompact_polar_of_mem_nhds {s : Set M} (hs : s ∈ 𝓝 (0 : M)) :
    IsCompact (polar 𝕜 s) := by
  -- pointwise bounds, from absorbency
  have hb : ∀ x : M, ∃ r : ℝ, ∀ f ∈ polar 𝕜 s, ‖f x‖ ≤ r := fun x ↦ by
    obtain ⟨c, hc⟩ := ((absorbent_nhds_zero (𝕜 := 𝕜) hs) x).exists
    obtain ⟨y, hy, rfl⟩ := hc rfl
    refine ⟨‖c‖, fun f hf ↦ ?_⟩
    rw [map_smul, smul_eq_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hf y hy)
  choose r hr using hb
  -- the image in `M → 𝕜` is the set of linear forms bounded by `1` on `s`
  set A : Set (M → 𝕜) := {g | (∀ x y, g (x + y) = g x + g y) ∧
    (∀ (c : 𝕜) x, g (c • x) = c * g x) ∧ ∀ y ∈ s, ‖g y‖ ≤ 1} with hAdef
  have himage : ((↑) : WeakDual 𝕜 M → M → 𝕜) '' polar 𝕜 s = A := by
    ext g
    refine ⟨?_, fun ⟨hadd, hsmul, hg⟩ ↦ ?_⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨map_add f, fun c x ↦ by simp, hf⟩
    -- a linear form bounded by `1` on `s` is `≤ ‖c‖` on `c • s`, so continuous
    set L : M →ₗ[𝕜] 𝕜 := ⟨⟨g, hadd⟩, fun c x ↦ by simpa using hsmul c x⟩
    have hL : Continuous L := by
      refine continuous_of_tendsto_nhds_zero L (Metric.tendsto_nhds.2 fun ε hε ↦ ?_)
      obtain ⟨c, hc0, hcε⟩ := NormedField.exists_norm_lt 𝕜 hε
      filter_upwards [(set_smul_mem_nhds_zero_iff (norm_pos_iff.1 hc0)).2 hs] with z hz
      obtain ⟨y, hy, rfl⟩ := hz
      rw [dist_zero_right, map_smul, smul_eq_mul, norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hg y hy)).trans_lt hcε
    exact ⟨⟨L, hL⟩, hg, rfl⟩
  -- `A` is closed and pointwise bounded: compact by Tychonoff
  have hA : IsCompact A := by
    refine (isCompact_univ_pi fun x ↦ ProperSpace.isCompact_closedBall (0 : 𝕜) (r x))
      |>.of_isClosed_subset ?_ fun g hg x _ ↦ ?_
    · simp only [hAdef, Set.ofPred_and, Set.ofPred_forall]
      refine ((isClosed_iInter fun x : M ↦ isClosed_iInter fun y : M ↦ isClosed_eq
        (continuous_apply (x + y)) ((continuous_apply x).add (continuous_apply y))).inter
        ((isClosed_iInter fun c : 𝕜 ↦ isClosed_iInter fun x : M ↦ isClosed_eq
          (continuous_apply (c • x)) (continuous_const.mul (continuous_apply x))).inter
        (isClosed_iInter fun y : M ↦ isClosed_iInter fun _ : y ∈ s ↦
          isClosed_le (continuous_apply y).norm continuous_const)))
    · rw [← himage] at hg
      obtain ⟨f, hf, rfl⟩ := hg
      simpa using hr x f hf
  rw [← himage] at hA
  exact DFunLike.coe_injective.isEmbedding_induced.isCompact_iff.2 hA

section Ellipsoid

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E]

/-- The ellipsoid `{ω | ω x² ≤ r² H x}` of a continuous quadratic form is weak-* compact
(Alaoglu–Bourbaki). -/
theorem isCompact_setOf_forall_sq_le {H : QuadraticForm ℝ E} (hH : Continuous H) (r : ℝ) :
    IsCompact {ω : WeakDual ℝ E | ∀ x, ω x ^ 2 ≤ r ^ 2 * H x} := by
  have hs : {x : E | r ^ 2 * H x < 1} ∈ 𝓝 (0 : E) :=
    (isOpen_lt (continuous_const.mul hH) continuous_const).mem_nhds (by simp)
  refine (isCompact_polar_of_mem_nhds (𝕜 := ℝ) hs).of_isClosed_subset ?_ fun ω hω x hx ↦ ?_
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x ↦ isClosed_le ((eval_continuous x).pow 2) continuous_const
  · have h1 : ω x ^ 2 ≤ r ^ 2 * H x := hω x
    have h2 : r ^ 2 * H x < 1 := hx
    change ‖ω x‖ ≤ 1
    rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one]
    linarith

omit [ContinuousSMul ℝ E] in
/-- **Hahn–Banach for ellipsoids**: a vector `t` of `ℝ^J` with `(∑ aⱼ tⱼ)² ≤ r² H (∑ aⱼ j)` is the
restriction to `J` of some `ω` with `ω² ≤ r² H`, as `r √H` is a continuous seminorm. -/
theorem exists_forall_sq_le_and_apply_eq {H : QuadraticForm ℝ E} (hH : Continuous H)
    (hpos : ∀ x, 0 ≤ H x) {r : ℝ} (hr : 0 ≤ r) {J : Finset E} {t : J → ℝ}
    (ht : ∀ a : J → ℝ, (∑ j, a j * t j) ^ 2 ≤ r ^ 2 * H (∑ j, a j • (j : E))) :
    ∃ ω : WeakDual ℝ E, (∀ x, ω x ^ 2 ≤ r ^ 2 * H x) ∧ ∀ j : J, ω j = t j := by
  classical
  -- `r √H` is sublinear, by Cauchy–Schwarz for the associated form
  set B := QuadraticMap.associated H with hBdef
  have hBH : ∀ x, B x x = H x := QuadraticMap.associated_eq_self_apply ℝ H
  have hCS : ∀ x y, B x y ^ 2 ≤ H x * H y := fun x y ↦ by
    have := LinearMap.BilinForm.apply_sq_le_of_symm B (fun x ↦ (hBH x).symm ▸ hpos x)
      (QuadraticForm.associated_isSymm ℝ H) x y
    rwa [hBH, hBH] at this
  have hadd : ∀ x y, H (x + y) = H x + H y + 2 * B x y := fun x y ↦ by
    have := congrArg (fun F ↦ F x y) (QuadraticMap.two_nsmul_associated ℝ H)
    simp only [LinearMap.smul_apply, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      nsmul_eq_mul, Nat.cast_ofNat] at this
    linarith
  set N : E → ℝ := fun x ↦ r * √(H x) with hN
  have hN_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x := fun c hc x ↦ by
    simp only [hN, QuadraticMap.map_smul, smul_eq_mul]
    rw [Real.sqrt_mul (mul_self_nonneg c), Real.sqrt_mul_self hc.le]
    ring
  have hN_add : ∀ x y, N (x + y) ≤ N x + N y := fun x y ↦ by
    simp only [hN, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ hr
    rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg (H x)) (Real.sqrt_nonneg (H y)))]
    refine Real.sqrt_le_sqrt ?_
    have hB : B x y ≤ √(H x) * √(H y) := by
      rw [← Real.sqrt_mul (hpos x)]
      exact (le_abs_self _).trans (Real.abs_le_sqrt (hCS x y))
    rw [hadd, add_sq, Real.sq_sqrt (hpos x), Real.sq_sqrt (hpos y)]
    linarith
  have hN_neg : ∀ x, N (-x) = N x := fun x ↦ by simp [hN, QuadraticMap.map_neg]
  -- the linear form `∑ aⱼ j ↦ ∑ aⱼ tⱼ` on the span of `J`, well defined by `ht`
  set L : (J → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ fun j : J ↦ (j : E) with hL
  set g₀ : (J → ℝ) →ₗ[ℝ] ℝ := Fintype.linearCombination ℝ t with hg₀
  have hLa : ∀ a, L a = ∑ j, a j • (j : E) := fun a ↦ Fintype.linearCombination_apply ℝ _ a
  have hg₀a : ∀ a, g₀ a = ∑ j, a j * t j := fun a ↦ by
    rw [hg₀, Fintype.linearCombination_apply]
    rfl
  have hle : ∀ a, |g₀ a| ≤ N (L a) := fun a ↦ by
    have hNL : N (L a) = √(r ^ 2 * H (L a)) := by
      rw [hN]
      dsimp only
      rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr]
    rw [hNL, hg₀a, hLa]
    exact Real.abs_le_sqrt (ht a)
  have hker : LinearMap.ker L ≤ LinearMap.ker g₀ := fun a ha ↦ by
    have := hle a
    rw [LinearMap.mem_ker.1 ha] at this
    simpa [hN, abs_nonpos_iff] using this
  set f : LinearMap.range L →ₗ[ℝ] ℝ :=
    (LinearMap.ker L).liftQ g₀ hker ∘ₗ L.quotKerEquivRange.symm.toLinearMap with hf
  have hfa : ∀ a, f ⟨L a, LinearMap.mem_range_self L a⟩ = g₀ a := fun a ↦ by
    simp [hf, LinearMap.quotKerEquivRange_symm_apply_image]
  obtain ⟨g, hgf, hgN⟩ := exists_extension_of_le_sublinear ⟨LinearMap.range L, f⟩ N hN_hom
    hN_add (by
      rintro ⟨y, a, rfl⟩
      change f ⟨L a, _⟩ ≤ N (L a)
      exact (le_abs_self _).trans ((congrArg abs (hfa a)).trans_le (hle a)))
  -- `|g| ≤ r √H`, so `g` is continuous
  have habs : ∀ x, |g x| ≤ N x := fun x ↦ abs_le.2
    ⟨by have := hgN (-x); rw [map_neg, hN_neg] at this; linarith, hgN x⟩
  have hgc : Continuous g := by
    refine continuous_of_tendsto_nhds_zero g ?_
    have hN0 : Tendsto N (𝓝 0) (𝓝 0) := by
      have := ((Real.continuous_sqrt.comp hH).tendsto 0).const_mul r
      simpa [hN, Function.comp_def] using this
    exact squeeze_zero_norm (fun x ↦ (Real.norm_eq_abs _).trans_le (habs x)) hN0
  refine ⟨StrongDual.toWeakDual ⟨g, hgc⟩, fun x ↦ ?_, fun j ↦ ?_⟩
  · change g x ^ 2 ≤ r ^ 2 * H x
    calc g x ^ 2 = |g x| ^ 2 := (sq_abs _).symm
      _ ≤ N x ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (habs x) 2
      _ = r ^ 2 * H x := by rw [hN, mul_pow, Real.sq_sqrt (hpos x)]
  · change g j = t j
    have h1 : g (L (Pi.single j 1)) = f ⟨L (Pi.single j 1), LinearMap.mem_range_self L _⟩ :=
      hgf ⟨_, LinearMap.mem_range_self L _⟩
    rw [hfa, hg₀a] at h1
    have h2 : L (Pi.single j 1) = (j : E) := by
      rw [hL, Fintype.linearCombination_apply_single, one_smul]
    rw [h2] at h1
    rw [h1]
    simp [Pi.single_apply]

end Ellipsoid

end WeakDual
