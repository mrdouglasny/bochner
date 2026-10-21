/-
Copyright (c) 2026 Axiomatic AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michael R. Douglas, Sarah Hoback
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Minlos.Mathlib.Analysis.LocallyConvex.NuclearMap
public import Minlos.Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Nuclear spaces

A topological vector space `E` is *nuclear* when every continuous seminorm `p` is dominated by an
absolutely convergent series of linear forms bounded by one continuous seminorm `q`:

  `p x ≤ ∑ₙ aₙ ‖fₙ x‖`,   `‖fₙ x‖ ≤ q x`,   `aₙ ≥ 0`,   `∑ₙ aₙ < ∞`.

This is Pietsch's condition — `p` is majorized by an integral seminorm, here of a measure on `ℕ`
[Bourbaki, *EVT*, VII, §4, no. 3, Thm 1 (ii)][bourbaki2023evt]. Bourbaki's definition, that every
continuous linear map into a Banach space be nuclear (loc. cit., no. 1, déf. 1), implies it
(`NuclearSpace.of_isNuclear`): the domination is what the applications consume, and it is stated
without quantifying over Banach spaces.

Over `ℝ`, Cauchy–Schwarz turns the domination into one by a nuclear quadratic form,
`p² ≤ ∑ₙ ωₙ²` with `ωₙ² ≤ cₙ² H`, `∑ₙ cₙ² < ∞` and `H` a continuous positive quadratic form
(`NuclearSpace.exists_sq_le_tsum_sq`): every continuous seminorm is continuous for the Sazonov
topology, which is the definition of nuclear spaces in [Bourbaki, *INT*, IX, §6,
no. 10][bourbaki2004integration2] and the form in which nuclearity enters Minlos' theorem. A real
space dominated through a continuous linear map by the seminorms of a nuclear space over `ℝ` or
`ℂ` is nuclear (`NuclearSpace.of_le_comp`): the complex forms split into real and imaginary parts.
After the Pietsch bridge of [Douglas–Hoback][douglas2026bochner].

## Main definitions and results

* `NuclearSpace`: Pietsch's condition
* `NuclearSpace.of_isNuclear`: a space whose continuous linear maps into normed spaces are nuclear
  is nuclear
* `NuclearSpace.exists_sq_le_tsum_sq`: the Sazonov domination of a continuous seminorm
* `NuclearSpace.of_le_comp`: pulling nuclearity back to a real space

## Provenance

Ported from or4nge19/QuantumlibCore `pin-v4.34.1` `9a741c08`,
`QuantumlibCore/ToMathlib/Analysis/LocallyConvex/NuclearSpace.lean` (Lean v4.34.1, Mathlib
`d13f23b7`), with module paths renamed; notices kept.
-/

@[expose] public section

open Filter Topology
open scoped ENNReal lp RealInnerProductSpace

universe u v

/-- A topological vector space is **nuclear** if every continuous seminorm `p` is dominated by an
absolutely convergent series of linear forms bounded by one continuous seminorm,
`p x ≤ ∑ₙ aₙ ‖fₙ x‖` [Bourbaki, *EVT*, VII, §4, no. 3, Thm 1][bourbaki2023evt]. -/
class NuclearSpace (𝕜 E : Type*) [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] : Prop where
  /-- Every continuous seminorm is dominated by a nuclear one. -/
  exists_le_tsum (p : Seminorm 𝕜 E) (hp : Continuous p) :
    ∃ (q : Seminorm 𝕜 E) (f : ℕ → StrongDual 𝕜 E) (a : ℕ → ℝ), Continuous q ∧
      (∀ n x, ‖f n x‖ ≤ q x) ∧ (∀ n, 0 ≤ a n) ∧ Summable a ∧ ∀ x, p x ≤ ∑' n, a n * ‖f n x‖

namespace NuclearSpace

section IsNuclear

variable {𝕜 : Type v} {E : Type u} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E]

/-- **Bourbaki's nuclear spaces are nuclear** [Bourbaki, *EVT*, VII, §4, no. 3, Thm 1,
(i) ⇒ (ii)][bourbaki2023evt]: if every continuous linear map into a normed space is nuclear, then
so is `x ↦ (g_y x)_y ∈ ℓ^∞(E)` for Hahn–Banach forms `g_y` with `g_y y = p y` and `‖g_y‖ ≤ p`,
whose norm is `p`. -/
theorem of_isNuclear
    (h : ∀ (F : Type (max u v)) [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : E →L[𝕜] F),
      f.IsNuclear) :
    NuclearSpace 𝕜 E := by
  refine ⟨fun p hp ↦ ?_⟩
  -- Hahn–Banach: `g y y = p y` and `‖g y x‖ ≤ p x`
  have hg : ∀ y : E, ∃ g : Module.Dual 𝕜 E, g y = p y ∧ ∀ x, ‖g x‖ ≤ p x := fun y ↦ by
    have H : ∀ c : 𝕜, c • y = 0 → RingHom.id 𝕜 c • (p y : 𝕜) = 0 := fun c hc ↦ by
      rcases smul_eq_zero.1 hc with rfl | rfl
      · rw [map_zero, zero_smul]
      · rw [map_zero, RCLike.ofReal_zero, smul_zero]
    set f := LinearPMap.mkSpanSingleton' y (p y : 𝕜) H with hf
    obtain ⟨g, hgf, hgp⟩ := Module.Dual.exists_extension_of_le_seminorm f.domain f.toFun
      (p := p) fun z ↦ by
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 z.2
        have hz : z = ⟨c • y, hc ▸ z.2⟩ := Subtype.ext hc.symm
        rw [hz]
        change ‖f ⟨c • y, _⟩‖ ≤ p (c • y)
        rw [LinearPMap.mkSpanSingleton'_apply, RingHom.id_apply, smul_eq_mul, norm_mul,
          map_smul_eq_mul, RCLike.norm_ofReal, abs_of_nonneg (apply_nonneg p y)]
    refine ⟨g, ?_, hgp⟩
    have := hgf ⟨y, Submodule.mem_span_singleton_self y⟩
    rw [this]
    exact LinearPMap.mkSpanSingleton'_apply_self y (p y : 𝕜) H _
  choose g hgy hgp using hg
  -- `j x = (g y x)_y ∈ ℓ^∞(E)`, of norm `p x`
  have hmem : ∀ x, Memℓp (fun y ↦ g y x) ∞ := fun x ↦
    memℓp_infty ⟨p x, by rintro _ ⟨y, rfl⟩; exact hgp y x⟩
  let jₗ : E →ₗ[𝕜] ℓ^∞(E, 𝕜) :=
    { toFun := fun x ↦ ⟨fun y ↦ g y x, hmem x⟩
      map_add' := fun x x' ↦ lp.ext <| funext fun y ↦ map_add (g y) x x'
      map_smul' := fun c x ↦ lp.ext <| funext fun y ↦ map_smul (g y) c x }
  have hj : ∀ x, ‖jₗ x‖ ≤ p x := fun x ↦
    lp.norm_le_of_forall_le (apply_nonneg p x) fun y ↦ hgp y x
  let j : E →L[𝕜] ℓ^∞(E, 𝕜) := ⟨jₗ, jₗ.continuous_of_le_seminorm p hp hj⟩
  obtain ⟨R⟩ := h _ j
  refine ⟨R.seminorm, R.func, fun n ↦ ‖R.vec n‖, R.continuous_seminorm, R.norm_func_le,
    fun n ↦ norm_nonneg _, R.summable_norm_vec, fun x ↦ ?_⟩
  calc p x = ‖j x x‖ := by
        change p x = ‖g x x‖
        rw [hgy, RCLike.norm_ofReal, abs_of_nonneg (apply_nonneg p x)]
    _ ≤ ‖j x‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero _ x
    _ = ‖∑' n, R.func n x • R.vec n‖ := by rw [(R.hasSum x).tsum_eq]
    _ ≤ ∑' n, ‖R.func n x • R.vec n‖ := norm_tsum_le_tsum_norm (R.summable_norm_smul x)
    _ = ∑' n, ‖R.vec n‖ * ‖R.func n x‖ := tsum_congr fun n ↦ by rw [norm_smul, mul_comm]

end IsNuclear

/-- **Cauchy–Schwarz for a weighted series**: `(∑ₙ aₙ |yₙ|)² ≤ (∑ₙ aₙ) ∑ₙ aₙ yₙ²`. -/
lemma sq_tsum_mul_abs_le {a y : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hy : Summable fun n ↦ a n * y n ^ 2) :
    Summable (fun n ↦ a n * |y n|) ∧
      (∑' n, a n * |y n|) ^ 2 ≤ (∑' n, a n) * ∑' n, a n * y n ^ 2 := by
  have hay : Summable fun n ↦ a n * |y n| :=
    ((hs.add hy).div_const 2).of_nonneg_of_le (fun n ↦ mul_nonneg (ha n) (abs_nonneg _))
      fun n ↦ by nlinarith [ha n, sq_nonneg (|y n| - 1), sq_abs (y n)]
  refine ⟨hay, le_of_tendsto_of_tendsto' ((hay.hasSum.tendsto_sum_nat).pow 2)
    (hs.hasSum.tendsto_sum_nat.mul hy.hasSum.tendsto_sum_nat) fun N ↦ ?_⟩
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun n _ ↦ ha n)
    (fun n _ ↦ mul_nonneg (ha n) (sq_nonneg _)) fun n _ ↦ le_of_eq (by rw [mul_pow, sq_abs]; ring)

section Real

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]

/-- **Continuous seminorms of a nuclear space are Sazonov-continuous** [Bourbaki, *INT*, IX, §6,
no. 10][bourbaki2004integration2]: `p² ≤ ∑ₙ ωₙ²` with `ωₙ² ≤ cₙ² H`, `∑ₙ cₙ² < ∞`, for a continuous
positive quadratic form `H`. From `p ≤ ∑ₙ aₙ |fₙ|` and `q ≤ ∑ₘ bₘ |gₘ|` with `|fₙ| ≤ q`,
Cauchy–Schwarz gives `p² ≤ A ∑ₙ aₙ fₙ²` and `q² ≤ B ∑ₘ bₘ gₘ² = H`. -/
theorem exists_sq_le_tsum_sq [NuclearSpace ℝ E] {p : Seminorm ℝ E} (hp : Continuous p) :
    ∃ (H : QuadraticForm ℝ E) (ω : ℕ → StrongDual ℝ E) (c : ℕ → ℝ), Continuous H ∧
      (∀ x, 0 ≤ H x) ∧ Summable (fun n ↦ c n ^ 2) ∧ (∀ n x, ω n x ^ 2 ≤ c n ^ 2 * H x) ∧
      ∀ x, p x ^ 2 ≤ ∑' n, ω n x ^ 2 := by
  obtain ⟨q, f, a, hq, hfq, ha0, ha, hpf⟩ := exists_le_tsum p hp
  obtain ⟨r, g, b, hr, hgr, hb0, hb, hqg⟩ := exists_le_tsum q hq
  set A := ∑' n, a n with hA
  set B := ∑' m, b m with hB
  have hA0 : 0 ≤ A := tsum_nonneg ha0
  have hB0 : 0 ≤ B := tsum_nonneg hb0
  -- `J x = (√(B bₘ) gₘ x)ₘ ∈ ℓ²`, so that `H x = ‖J x‖²`
  have hJle : ∀ x m, ‖√(B * b m) * g m x‖ ^ 2 ≤ B * b m * r x ^ 2 := fun x m ↦ by
    rw [norm_mul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (mul_nonneg hB0 (hb0 m))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hgr m x) 2)
      (mul_nonneg hB0 (hb0 m))
  have hJsum : ∀ x, Summable fun m ↦ ‖√(B * b m) * g m x‖ ^ 2 := fun x ↦
    ((hb.mul_left B).mul_right (r x ^ 2)).of_nonneg_of_le (fun _ ↦ sq_nonneg _) (hJle x)
  have hJmem : ∀ x, Memℓp (fun m ↦ √(B * b m) * g m x) 2 := fun x ↦ memℓp_gen <| by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hJsum x
  let Jₗ : E →ₗ[ℝ] ℓ²(ℕ, ℝ) :=
    { toFun := fun x ↦ ⟨fun m ↦ √(B * b m) * g m x, hJmem x⟩
      map_add' := fun x x' ↦ lp.ext <| funext fun m ↦
        (congrArg (_ * ·) (map_add (g m) x x')).trans (mul_add _ _ _)
      map_smul' := fun c x ↦ lp.ext <| funext fun m ↦
        (congrArg (_ * ·) (map_smul (g m) c x)).trans (mul_left_comm _ _ _) }
  have hJnorm : ∀ x, ‖Jₗ x‖ ^ 2 = ∑' m, ‖√(B * b m) * g m x‖ ^ 2 := fun x ↦ by
    have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (Jₗ x)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at this
    exact this
  have hJ : Continuous Jₗ := Jₗ.continuous_of_le_mul_seminorm hB0 r hr fun x ↦ by
    rw [← abs_of_nonneg (norm_nonneg (Jₗ x)), ← abs_of_nonneg (mul_nonneg hB0 (apply_nonneg r x)),
      ← sq_le_sq, hJnorm]
    calc ∑' m, ‖√(B * b m) * g m x‖ ^ 2 ≤ ∑' m, B * b m * r x ^ 2 :=
          (hJsum x).tsum_le_tsum (hJle x) ((hb.mul_left B).mul_right _)
      _ = (B * r x) ^ 2 := by rw [tsum_mul_right, tsum_mul_left, ← hB]; ring
  let H : QuadraticForm ℝ E :=
    LinearMap.BilinMap.toQuadraticMap ((innerₗ (ℓ²(ℕ, ℝ))).compl₁₂ Jₗ Jₗ)
  have hH : ∀ x, H x = ‖Jₗ x‖ ^ 2 := fun x ↦ by
    rw [LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.compl₁₂_apply, innerₗ_apply_apply,
      real_inner_self_eq_norm_sq]
  -- `q² ≤ H` and `p² ≤ A ∑ₙ aₙ fₙ²`
  have hqH : ∀ x, q x ^ 2 ≤ H x := fun x ↦ by
    have hgs : Summable fun m ↦ b m * g m x ^ 2 :=
      (hb.mul_right (r x ^ 2)).of_nonneg_of_le (fun m ↦ mul_nonneg (hb0 m) (sq_nonneg _))
        fun m ↦ mul_le_mul_of_nonneg_left (by
          rw [← sq_abs, ← Real.norm_eq_abs]
          exact pow_le_pow_left₀ (norm_nonneg _) (hgr m x) 2) (hb0 m)
    obtain ⟨-, hcs⟩ := sq_tsum_mul_abs_le hb0 hb hgs
    rw [hH, hJnorm]
    calc q x ^ 2 ≤ (∑' m, b m * |g m x|) ^ 2 := by
          simp only [Real.norm_eq_abs] at hqg
          exact pow_le_pow_left₀ (apply_nonneg q x) (hqg x) 2
      _ ≤ B * ∑' m, b m * g m x ^ 2 := hcs
      _ = ∑' m, ‖√(B * b m) * g m x‖ ^ 2 := by
          rw [← tsum_mul_left]
          refine tsum_congr fun m ↦ ?_
          rw [norm_mul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _),
            Real.sq_sqrt (mul_nonneg hB0 (hb0 m)), Real.norm_eq_abs, sq_abs]
          ring
  refine ⟨H, fun n ↦ √(A * a n) • f n, fun n ↦ √(A * a n), ?_, fun x ↦ by rw [hH]; positivity,
    ?_, fun n x ↦ ?_, fun x ↦ ?_⟩
  · rw [show ⇑H = fun x ↦ ‖Jₗ x‖ ^ 2 from funext hH]
    exact (continuous_norm.comp hJ).pow 2
  · simpa only [Real.sq_sqrt (mul_nonneg hA0 (ha0 _))] using ha.mul_left A
  · rw [_root_.smul_apply, smul_eq_mul, mul_pow, Real.sq_sqrt (mul_nonneg hA0 (ha0 n))]
    refine mul_le_mul_of_nonneg_left ((?_ : f n x ^ 2 ≤ q x ^ 2).trans (hqH x))
      (mul_nonneg hA0 (ha0 n))
    rw [← sq_abs, ← Real.norm_eq_abs]
    exact pow_le_pow_left₀ (norm_nonneg _) (hfq n x) 2
  · have hfs : Summable fun n ↦ a n * f n x ^ 2 :=
      (ha.mul_right (q x ^ 2)).of_nonneg_of_le (fun n ↦ mul_nonneg (ha0 n) (sq_nonneg _))
        fun n ↦ mul_le_mul_of_nonneg_left (by
          rw [← sq_abs, ← Real.norm_eq_abs]
          exact pow_le_pow_left₀ (norm_nonneg _) (hfq n x) 2) (ha0 n)
    obtain ⟨-, hcs⟩ := sq_tsum_mul_abs_le ha0 ha hfs
    calc p x ^ 2 ≤ (∑' n, a n * |f n x|) ^ 2 := by
          simp only [Real.norm_eq_abs] at hpf
          exact pow_le_pow_left₀ (apply_nonneg p x) (hpf x) 2
      _ ≤ A * ∑' n, a n * f n x ^ 2 := hcs
      _ = ∑' n, ((√(A * a n) • f n) x) ^ 2 := by
          rw [← tsum_mul_left]
          refine tsum_congr fun n ↦ ?_
          rw [_root_.smul_apply, smul_eq_mul, mul_pow,
            Real.sq_sqrt (mul_nonneg hA0 (ha0 n))]
          ring

omit [IsTopologicalAddGroup E] in
/-- **Nuclearity pulls back to a real space** [Bourbaki, *EVT*, VII, §4, no. 2, Prop. 3 and no. 4,
Prop. 5][bourbaki2023evt]: if every continuous seminorm of `E` is dominated through a continuous
real-linear `ι` by a continuous seminorm of a nuclear space `F` over `ℝ` or `ℂ`, then `E` is
nuclear — the forms of `F`, composed with `ι`, split into their real and imaginary parts. -/
theorem of_le_comp {𝕜 F : Type*} [RCLike 𝕜] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [NuclearSpace 𝕜 F] (ι : E →L[ℝ] F)
    (h : ∀ p : Seminorm ℝ E, Continuous p → ∃ P : Seminorm 𝕜 F, Continuous P ∧ ∀ x, p x ≤ P (ι x)) :
    NuclearSpace ℝ E := by
  refine ⟨fun p hp ↦ ?_⟩
  obtain ⟨P, hP, hpP⟩ := h p hp
  obtain ⟨q, φ, a, hq, hφq, ha0, ha, hPφ⟩ := exists_le_tsum P hP
  set re : ℕ → StrongDual ℝ E := fun n ↦ RCLike.reCLM ∘L (φ n).restrictScalars ℝ ∘L ι
  set im : ℕ → StrongDual ℝ E := fun n ↦ RCLike.imCLM ∘L (φ n).restrictScalars ℝ ∘L ι
  have hre : ∀ n x, re n x = RCLike.re (φ n (ι x)) := fun _ _ ↦ rfl
  have him : ∀ n x, im n x = RCLike.im (φ n (ι x)) := fun _ _ ↦ rfl
  have hsplit : ∀ z : 𝕜, ‖z‖ ≤ |RCLike.re z| + |RCLike.im z| := fun z ↦ by
    rw [← Real.sqrt_sq (norm_nonneg z), ← Real.sqrt_sq (add_nonneg (abs_nonneg _) (abs_nonneg _))]
    refine Real.sqrt_le_sqrt ?_
    rw [RCLike.norm_sq_eq_def, add_sq, sq_abs, sq_abs]
    nlinarith [abs_nonneg (RCLike.re z), abs_nonneg (RCLike.im z)]
  set f : ℕ → StrongDual ℝ E := fun k ↦ if Even k then re (k / 2) else im (k / 2) with hf
  set a' : ℕ → ℝ := fun k ↦ a (k / 2) with ha'
  have h2 : ∀ k : ℕ, (2 * k + 1) / 2 = k := fun k ↦ by omega
  have h2' : ∀ k : ℕ, 2 * k / 2 = k := fun k ↦ by omega
  have hqι : Continuous fun x ↦ q (ι x) := hq.comp ι.continuous
  refine ⟨(q.restrictScalars ℝ).comp ι.toLinearMap, f, a', hqι, fun k x ↦ ?_,
    fun k ↦ ha0 _, ?_, fun x ↦ ?_⟩
  · change ‖f k x‖ ≤ q (ι x)
    simp only [hf]
    split_ifs
    · rw [hre, Real.norm_eq_abs]
      exact (RCLike.abs_re_le_norm _).trans (hφq _ _)
    · rw [him, Real.norm_eq_abs]
      exact (RCLike.abs_im_le_norm _).trans (hφq _ _)
  · refine Summable.even_add_odd ?_ ?_
    · simpa [ha', h2'] using ha
    · simpa [ha', h2] using ha
  · have hbound : ∀ n, a n * ‖φ n (ι x)‖ ≤ a n * q (ι x) := fun n ↦
      mul_le_mul_of_nonneg_left (hφq n _) (ha0 n)
    have hsre : Summable fun n ↦ a n * |re n x| :=
      (ha.mul_right (q (ι x))).of_nonneg_of_le (fun n ↦ mul_nonneg (ha0 n) (abs_nonneg _))
        fun n ↦ mul_le_mul_of_nonneg_left ((RCLike.abs_re_le_norm _).trans (hφq _ _)) (ha0 n)
    have hsim : Summable fun n ↦ a n * |im n x| :=
      (ha.mul_right (q (ι x))).of_nonneg_of_le (fun n ↦ mul_nonneg (ha0 n) (abs_nonneg _))
        fun n ↦ mul_le_mul_of_nonneg_left ((RCLike.abs_im_le_norm _).trans (hφq _ _)) (ha0 n)
    have hsφ : Summable fun n ↦ a n * ‖φ n (ι x)‖ :=
      (ha.mul_right (q (ι x))).of_nonneg_of_le (fun n ↦ mul_nonneg (ha0 n) (norm_nonneg _))
        hbound
    have heven : (fun k ↦ a' (2 * k) * ‖f (2 * k) x‖) = fun n ↦ a n * |re n x| := by
      funext n
      simp [hf, ha', h2', Real.norm_eq_abs]
    have hodd : (fun k ↦ a' (2 * k + 1) * ‖f (2 * k + 1) x‖) = fun n ↦ a n * |im n x| := by
      funext n
      simp [hf, ha', h2, Real.norm_eq_abs]
    calc p x ≤ P (ι x) := hpP x
      _ ≤ ∑' n, a n * ‖φ n (ι x)‖ := hPφ (ι x)
      _ ≤ ∑' n, (a n * |re n x| + a n * |im n x|) :=
          hsφ.tsum_le_tsum (fun n ↦ by
            rw [← mul_add, hre, him]
            exact mul_le_mul_of_nonneg_left (hsplit _) (ha0 n)) (hsre.add hsim)
      _ = ∑' k, a' k * ‖f k x‖ := by
          have hse : Summable fun k ↦ a' (2 * k) * ‖f (2 * k) x‖ := by rw [heven]; exact hsre
          have hso : Summable fun k ↦ a' (2 * k + 1) * ‖f (2 * k + 1) x‖ := by
            rw [hodd]; exact hsim
          rw [← tsum_even_add_odd (f := fun k ↦ a' k * ‖f k x‖) hse hso, heven, hodd,
            hsre.tsum_add hsim]

end Real

end NuclearSpace
