/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Minlos Concentration Bound

States `nuclear_cylindrical_concentration` as a textbook axiom and provides
`minlos_concentration` as a convenience wrapper.

## Architecture

1. **Helper lemmas** (proved): pointwise CF estimates (`cf_norm_le_one`,
   `cf_nhds_ball`, `one_sub_re_nonneg`, `quadratic_bound_outside`).

2. **Monotonicity lemmas** (proved): `seminorm_mono_of_le`, `finset_sup_le_of_mono`
   derive seminorm monotonicity from consecutive HS embeddings.

3. **Textbook axiom** `nuclear_cylindrical_concentration`: for Hilbertian
   seminorms with consecutive Hilbert-Schmidt embeddings, the concentration
   bound holds. This is the analytical core of Gel'fand-Vilenkin Vol.4,
   Ch.IV §3.3.

4. **Theorem** `minlos_concentration`: trivial wrapper applying the axiom.

## References

- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. IV, §3.3
- Bogachev, "Gaussian Measures", Ch. 2-3
- Trèves, "Topological Vector Spaces", Ch. 50-51
-/

import Bochner.Minlos.SazonovTightness
import Bochner.Minlos.NuclearSpace
import Bochner.Minlos.PietschBridge
import Mathlib.Data.Finsupp.Encodable

open BigOperators MeasureTheory Complex TopologicalSpace Classical Finsupp

noncomputable section

/-! ## CF constantly 1 implies random variable is 0 a.e. -/

/-- If X : Ω → ℝ is measurable and ∫ exp(I * ↑(t * X(ω))) dν = 1 for all t ∈ ℝ,
    then X = 0 ν-a.e.

    Proof sketch: Re(1 - ∫ exp(itX)) = ∫ (1 - cos(tX)) = 0. Since 1 - cos ≥ 0,
    cos(tX) = 1 a.e. for each t. Over countably many t ∈ ℚ simultaneously,
    this forces X = 0. -/
lemma ae_eq_zero_of_charfun_eq_one {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν]
    {X : Ω → ℝ} (hX : Measurable X)
    (hcf : ∀ t : ℝ, ∫ ω, exp (I * ↑(t * X ω)) ∂ν = 1) :
    ∀ᵐ ω ∂ν, X ω = 0 := by
  -- Step 1: Show ν.map X = dirac 0 via charFun equality
  have h_eq : ν.map X = Measure.dirac (0 : ℝ) := by
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_dirac]
    simp only [inner_zero_left]
    rw [charFun_apply, integral_map hX.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x => cexp (@inner ℝ ℝ _ x t * I)) _)]
    have h_inner : ∀ ω, cexp (@inner ℝ ℝ _ (X ω) t * I) = exp (I * ↑(t * X ω)) := by
      intro ω; congr 1
      simp [RCLike.inner_apply, mul_comm I]
    simp_rw [h_inner]
    rw [hcf t]
    simp [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  -- Step 2: Deduce X = 0 a.e.
  have h_ae : ∀ᵐ y ∂(ν.map X), y = 0 := by
    rw [h_eq]; exact ae_dirac_iff (measurableSet_singleton 0) |>.mpr rfl
  rw [show (∀ᵐ ω ∂ν, X ω = 0) ↔ ∀ᵐ y ∂(ν.map X), y = 0 from
    (ae_map_iff hX.aemeasurable (measurableSet_singleton 0)).symm]
  exact h_ae

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-! ## Helper lemmas -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The characteristic functional satisfies `‖Φ(x)‖ ≤ 1`, as the integral
    of a unit-modulus function against a probability measure. -/
lemma cf_norm_le_one
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (x : E) : ‖Φ x‖ ≤ 1 := by
  have h := h_cf_joint 1 (fun _ => 1) (fun _ => x)
  simp only [Fin.sum_univ_one, one_smul, one_mul] at h
  rw [← h]
  calc ‖∫ ω, exp (I * ↑(ω x)) ∂ν‖
      ≤ ∫ ω, ‖exp (I * ↑(ω x))‖ ∂ν := norm_integral_le_integral_norm _
    _ = ∫ ω, 1 ∂ν := by
        congr 1; ext ω; rw [Complex.norm_exp]
        simp [Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
    _ = 1 := by simp

/-- `1 - Re(z) ≤ 2` when `‖z‖ ≤ 1`. -/
lemma one_sub_re_le_two_of_norm_le (z : ℂ) (hz : ‖z‖ ≤ 1) : 1 - z.re ≤ 2 := by
  have h1 : |z.re| ≤ ‖z‖ := abs_re_le_norm z
  have h2 : -1 ≤ z.re := by linarith [abs_le.mp (h1.trans hz)]
  linarith

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- Quadratic bound outside a seminorm ball: if `q(x) ≥ δ > 0` and `‖Φ(x)‖ ≤ 1`,
    then `1 - Re(Φ(x)) ≤ (2/δ²) · q(x)²`. -/
lemma quadratic_bound_outside
    (Φ : E → ℂ) (h_norm_le : ∀ x : E, ‖Φ x‖ ≤ 1)
    (q : Seminorm ℝ E) (δ : ℝ) (hδ : 0 < δ)
    (x : E) (hx : δ ≤ q x) :
    1 - (Φ x).re ≤ (2 / δ ^ 2) * q x ^ 2 := by
  have h_re : 1 - (Φ x).re ≤ 2 := one_sub_re_le_two_of_norm_le _ (h_norm_le x)
  calc 1 - (Φ x).re ≤ 2 := h_re
    _ = (2 / δ ^ 2) * δ ^ 2 := by field_simp
    _ ≤ (2 / δ ^ 2) * q x ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sq_le_sq' (by linarith) hx

omit [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- CF norm bound gives `1 - Re(Φ(x)) ≥ 0`. -/
lemma one_sub_re_nonneg
    (Φ : E → ℂ) (h_norm_le : ∀ x : E, ‖Φ x‖ ≤ 1) (x : E) :
    0 ≤ 1 - (Φ x).re := by
  have h1 : |Complex.re (Φ x)| ≤ ‖Φ x‖ := abs_re_le_norm _
  have h2 : (Φ x).re ≤ 1 := by linarith [abs_le.mp (h1.trans (h_norm_le x))]
  linarith

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- From `Continuous Φ`, `Φ 0 = 1`, and `WithSeminorms p`: extract a finite set
    of seminorm indices s and radius r > 0 such that `(s.sup p)(x) < r`
    implies `‖1 - Φ(x)‖ < ε`. -/
lemma cf_nhds_ball
    (Φ : E → ℂ) (h_cf_cont : Continuous Φ) (h_normalized : Φ 0 = 1)
    (p : ℕ → Seminorm ℝ E) (hp_top : WithSeminorms (fun n => p n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : Finset ℕ) (r : ℝ), 0 < r ∧
      ∀ x, (s.sup p) x < r → ‖1 - Φ x‖ < ε := by
  have h_cont_at : ContinuousAt Φ 0 := h_cf_cont.continuousAt
  rw [ContinuousAt, h_normalized] at h_cont_at
  have h_nhds : {x | ‖1 - Φ x‖ < ε} ∈ nhds (0 : E) := by
    have hsub : Φ ⁻¹' Metric.ball 1 ε ⊆ {x : E | ‖1 - Φ x‖ < ε} := by
      intro x hx; simp only [Set.mem_preimage, Metric.mem_ball] at hx
      simp only [Set.mem_setOf_eq]; rwa [norm_sub_rev]
    exact Filter.mem_of_superset
      (h_cont_at (Metric.isOpen_ball.mem_nhds (by simp [Metric.mem_ball, dist_self, hε]))) hsub
  rw [hp_top.hasBasis_zero_ball.mem_iff] at h_nhds
  obtain ⟨⟨s, r⟩, hr, h_sub⟩ := h_nhds
  refine ⟨s, r, hr, fun x hx => h_sub ?_⟩
  rw [Seminorm.ball_zero_eq]; exact hx


/-! ## Monotonicity from consecutive HS embeddings -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- From consecutive HS embeddings, `p n ≤ p m` whenever `n ≤ m`. -/
lemma seminorm_mono_of_le (p : ℕ → Seminorm ℝ E)
    (hp_hs : ∀ n, (p (n + 1)).IsHilbertSchmidtEmbedding (p n))
    {n m : ℕ} (h : n ≤ m) : p n ≤ p m := by
  induction m with
  | zero => simp [Nat.le_zero.mp h]
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact le_refl _
    · exact le_trans (ih (Nat.lt_succ_iff.mp hlt)) (hp_hs k).1

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- For a finite set of indices, `s.sup p ≤ p m` when `m` dominates every index in `s`
    (which holds when `m ≥ max s`, given monotonicity). -/
lemma finset_sup_le_of_mono (p : ℕ → Seminorm ℝ E)
    (hp_hs : ∀ n, (p (n + 1)).IsHilbertSchmidtEmbedding (p n))
    (s : Finset ℕ) (m : ℕ) (hm : ∀ n ∈ s, n ≤ m) :
    s.sup p ≤ p m := by
  apply Finset.sup_le
  intro n hn
  exact seminorm_mono_of_le p hp_hs (hm n hn)


/-! ## Combined quadratic bound -/

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- **Combined quadratic bound** from CF continuity: for any ε > 0, there exist m₀ : ℕ
    and K ≥ 0 such that `1 - Re(Φ(x)) ≤ ε + K · (p m₀)(x)²` for all x. -/
lemma combined_quadratic_bound
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_cont : Continuous Φ) (h_normalized : Φ 0 = 1)
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (p : ℕ → Seminorm ℝ E) (hp_top : WithSeminorms (fun n => p n))
    (hp_hs : ∀ n, (p (n + 1)).IsHilbertSchmidtEmbedding (p n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (m₀ : ℕ) (K : ℝ), 0 ≤ K ∧
      ∀ x : E, 1 - (Φ x).re ≤ ε + K * (p m₀) x ^ 2 := by
  obtain ⟨s, r, hr, h_ball⟩ := cf_nhds_ball Φ h_cf_cont h_normalized p hp_top ε hε
  have h_norm_le : ∀ x : E, ‖Φ x‖ ≤ 1 := cf_norm_le_one Φ ν h_cf_joint
  set m₀ := s.sup id
  have hm₀ : ∀ n ∈ s, n ≤ m₀ := fun n hn => Finset.le_sup (f := id) hn
  have h_mono : s.sup p ≤ p m₀ := finset_sup_le_of_mono p hp_hs s m₀ hm₀
  refine ⟨m₀, 2 / r ^ 2, by positivity, fun x => ?_⟩
  by_cases hx : (s.sup p) x < r
  · -- Inside ball: ‖1 - Φ(x)‖ < ε, so 1 - Re(Φ(x)) < ε
    have h1 : 1 - (Φ x).re ≤ ‖1 - Φ x‖ := by
      have := abs_re_le_norm (1 - Φ x)
      simp only [Complex.sub_re, Complex.one_re] at this
      linarith [abs_le.mp this]
    have h3 : (0 : ℝ) ≤ 2 / r ^ 2 * (p m₀) x ^ 2 := by positivity
    linarith [h_ball x hx]
  · -- Outside ball: use quadratic_bound_outside with q = p m₀
    push_neg at hx
    have hx' : r ≤ (p m₀) x := le_trans hx (h_mono x)
    have := quadratic_bound_outside Φ h_norm_le (p m₀) r hr x hx'
    linarith


/-! ## CF vanishes on seminorm kernel -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- If `q(z) = 0` and `q` dominates the CF near 0 (i.e., for any ε > 0, there's a q-ball
    where `‖1 - Φ‖ < ε`), then `Φ(t • z) = 1` for all `t`.

    Proof: `q(t•z) = |t| · q(z) = 0 < r` for any `r > 0`, so `‖1 - Φ(t•z)‖ < ε`
    for all `ε > 0`. -/
lemma cf_kernel_of_ball_bound
    (Φ : E → ℂ)
    (q : Seminorm ℝ E) (z : E) (hz : q z = 0)
    (h_dom : ∀ ε > 0, ∃ r > 0, ∀ x, q x < r → ‖1 - Φ x‖ < ε) (t : ℝ) :
    Φ (t • z) = 1 := by
  by_contra h_ne
  have h_pos : 0 < ‖1 - Φ (t • z)‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm h_ne))
  obtain ⟨r, hr, h_bound⟩ := h_dom _ h_pos
  have h_qtz : q (t • z) < r := by
    calc q (t • z) = ‖t‖ * q z := map_smul_eq_mul q t z
      _ = ‖t‖ * 0 := by rw [hz]
      _ = 0 := mul_zero _
      _ < r := hr
  linarith [h_bound (t • z) h_qtz]

/-! ## Linear combination a.e. from joint CF -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- If `x = ∑ j, β j • e j` in E (real coefficients), then `ω(x) = ∑ j, β j * ω(e j)`
    for ν-a.e. ω. Uses `h_cf_joint` directly — no linearity of ω assumed.

    This is the key trick: the joint CF condition forces the "linear decomposition"
    to hold a.e. even for real (not just rational) coefficients. -/
lemma linear_combination_ae
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_normalized : Φ 0 = 1)
    {k : ℕ} (e : Fin k → E) (β : Fin k → ℝ) :
    ∀ᵐ ω ∂ν, ω (∑ j, β j • e j) = ∑ j, β j * ω (e j) := by
  set x := ∑ j, β j • e j with x_def
  set X : (E → ℝ) → ℝ := fun ω => ω x - ∑ j, β j * ω (e j)
  have hX_meas : Measurable X := by
    apply Measurable.sub (measurable_pi_apply x)
    exact Finset.measurable_sum _ (fun j _ => (measurable_pi_apply (e j)).const_mul _)
  have hX_cf : ∀ t : ℝ, ∫ ω, exp (I * ↑(t * X ω)) ∂ν = 1 := by
    intro t
    let s' : Fin (k + 1) → ℝ := Fin.cons t (fun j => -t * β j)
    let x' : Fin (k + 1) → E := Fin.cons x e
    have h := h_cf_joint (k + 1) s' x'
    have h_sum_x : ∑ i : Fin (k + 1), s' i • x' i = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, s', x']
      rw [show ∑ j : Fin k, (-t * β j) • e j = -(t • ∑ j, β j • e j) from by
        rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
        congr 1; ext j; simp [neg_smul, neg_mul, smul_smul]]
      simp [x_def]
    have h_sum_ω : ∀ ω', (∑ i : Fin (k + 1), s' i * ω' (x' i)) = t * X ω' := by
      intro ω'
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, s', x', X, mul_sub]
      congr 1
      rw [show ∑ j : Fin k, -t * β j * ω' (e j) =
          -(t * ∑ j, β j * ω' (e j)) from by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]; congr 1; ext j; ring]
    rw [h_sum_x, h_normalized] at h
    rw [show (fun ω' => exp (I * ↑(t * X ω'))) =
      (fun ω' => exp (I * ↑(∑ i : Fin (k + 1), s' i * ω' (x' i)))) from by
      funext ω'; congr 2; exact_mod_cast (h_sum_ω ω').symm]
    exact h
  have := ae_eq_zero_of_charfun_eq_one hX_meas hX_cf
  filter_upwards [this] with ω hω
  linarith [show X ω = 0 from hω]


/-! ## Pushforward CF for finite evaluation maps -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The pushforward of ν to `Fin k → ℝ` via evaluation at vectors `e₀,...,e_{k-1}`
    has characteristic function `v ↦ Φ(∑ vⱼ • eⱼ)`. This is a direct consequence
    of `h_cf_joint` and `integral_map`. -/
lemma pushforward_charfun_eq
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    {k : ℕ} (e : Fin k → E) (v : Fin k → ℝ) :
    ∫ y : Fin k → ℝ, exp (I * ↑(∑ j, v j * y j))
      ∂(ν.map (fun ω j => ω (e j))) = Φ (∑ j, v j • e j) := by
  have hg : Measurable (fun ω : E → ℝ => (fun j => ω (e j) : Fin k → ℝ)) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply (e j))
  rw [integral_map hg.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
  exact h_cf_joint k v e


/-! ## Concentration on good set via Cauchy-Schwarz + Parseval -/

/-- **Cauchy-Schwarz + Parseval concentration bound**: if ω is linear on combinations of
    a p-orthonormal sequence `{eⱼ}` and `∑ ω(eⱼ)² ≤ R²`, then for any linear combination
    `x = ∑ βⱼ eⱼ`, we have `|ω(x)| ≤ R · p(x)`.

    This is the pointwise bound at the heart of the concentration argument:
    ω in the "good set" (bounded evaluation norm) respects the seminorm. -/
lemma bound_on_good_set
    (p : Seminorm ℝ E) (hp : p.IsHilbertian)
    {k : ℕ} (e : Fin k → E) (he : p.IsOrthonormalSeq e)
    (R : ℝ) (hR : 0 < R)
    (ω : E → ℝ)
    (h_linear : ∀ (β : Fin k → ℝ), ω (∑ j, β j • e j) = ∑ j, β j * ω (e j))
    (h_norm : ∑ j : Fin k, (ω (e j)) ^ 2 ≤ R ^ 2)
    (β : Fin k → ℝ) :
    |ω (∑ j, β j • e j)| ≤ R * p (∑ j, β j • e j) := by
  rw [h_linear]
  -- Parseval: p(∑ βⱼ eⱼ)² = ∑ βⱼ²
  have h_parseval := Seminorm.sq_sum_orthonormal p hp e he β
  -- Cauchy-Schwarz: (∑ βⱼ ω(eⱼ))² ≤ (∑ βⱼ²)(∑ ω(eⱼ)²)
  have h_cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ β (fun j => ω (e j))
  -- Combined: (∑ βⱼ ω(eⱼ))² ≤ (R · p(x))²
  have h_sq : (∑ j : Fin k, β j * ω (e j)) ^ 2 ≤ (R * p (∑ j, β j • e j)) ^ 2 := by
    calc (∑ j : Fin k, β j * ω (e j)) ^ 2
        ≤ (∑ j, β j ^ 2) * (∑ j, (ω (e j)) ^ 2) := h_cs
      _ = p (∑ j, β j • e j) ^ 2 * (∑ j, (ω (e j)) ^ 2) := by rw [h_parseval]
      _ ≤ p (∑ j, β j • e j) ^ 2 * R ^ 2 :=
          mul_le_mul_of_nonneg_left h_norm (sq_nonneg _)
      _ = (R * p (∑ j, β j • e j)) ^ 2 := by ring
  exact abs_le_of_sq_le_sq h_sq (by positivity)


/-! ## Kernel elements vanish a.e. -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- If `p(z) = 0` and `p` dominates the CF (i.e., the CF at multiples of z
    is always 1), then `ω(z) = 0` for ν-a.e. ω. Proof: the CF of ω(z)
    is constantly 1, so ω(z) = 0 a.e. by `ae_eq_zero_of_charfun_eq_one`. -/
lemma kernel_eval_ae_zero
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_normalized : Φ 0 = 1)
    (p : Seminorm ℝ E) (z : E) (hz : p z = 0)
    (h_cf_kernel : ∀ t : ℝ, Φ (t • z) = 1) :
    ∀ᵐ ω ∂ν, ω z = 0 := by
  apply ae_eq_zero_of_charfun_eq_one (measurable_pi_apply z)
  intro t
  have h := h_cf_joint 1 (fun _ => t) (fun _ => z)
  simp only [Fin.sum_univ_one] at h
  rw [h_cf_kernel t] at h; exact h


/-! ## ℚ-linearity for all Finsupp simultaneously -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- For ν-a.e. ω, the evaluation `ω(x_c)` equals the ℚ-linear combination
    `∑ cᵢ ω(dᵢ)` for **all** `c : ℕ →₀ ℚ` simultaneously.

    Uses countable intersection (`eventually_countable_forall`) since `ℕ →₀ ℚ`
    is countable, plus `linear_combination_ae` for each individual `c`. -/
lemma q_linear_ae_all
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_normalized : Φ 0 = 1)
    (d : ℕ → E) :
    ∀ᵐ ω ∂ν, ∀ c : ℕ →₀ ℚ,
      ω (c.sum fun i a => (a : ℝ) • d i) = c.sum fun i a => (a : ℝ) * ω (d i) := by
  rw [eventually_countable_forall]
  intro c
  -- Enumerate support: Fin-indexed vectors and coefficients
  let e : Fin c.support.card → E := fun j => d (c.support.equivFin.symm j)
  let β : Fin c.support.card → ℝ := fun j => (c (c.support.equivFin.symm j) : ℝ)
  -- Apply linear_combination_ae with the Fin-indexed data
  have := linear_combination_ae Φ ν h_cf_joint h_normalized e β
  filter_upwards [this] with ω hω
  -- Both sides equal the Fin-indexed sum, via sum_coe_sort + Equiv.sum_comp
  show ω (∑ a ∈ c.support, (↑(c a) : ℝ) • d a) =
    ∑ a ∈ c.support, (↑(c a) : ℝ) * ω (d a)
  have h1 : (∑ a ∈ c.support, (↑(c a) : ℝ) • d a : E) = ∑ j, β j • e j := by
    rw [← c.support.sum_coe_sort]; exact (Equiv.sum_comp c.support.equivFin.symm _).symm
  have h2 : (∑ a ∈ c.support, (↑(c a) : ℝ) * ω (d a) : ℝ) = ∑ j, β j * ω (e j) := by
    rw [← c.support.sum_coe_sort]; exact (Equiv.sum_comp c.support.equivFin.symm _).symm
  rw [h1, h2]; exact hω


/-! ## Bad set definitions for continuity from below -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The "bad set" for the concentration bound: the set of ω where some
    ℚ-linear combination of dense vectors violates the seminorm bound. -/
def concentrationBadSet (d : ℕ → E) (p : Seminorm ℝ E) (C : ℝ) :
    Set (E → ℝ) :=
  {ω | ∃ c : ℕ →₀ ℚ,
    ¬ (|ω (c.sum fun i a => (a : ℝ) • d i)| ≤
      C * p (c.sum fun i a => (a : ℝ) • d i))}

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The "restricted bad set" B_N: bad set restricted to ℚ-linear combinations
    with support in `{0, ..., N-1}`. -/
def concentrationBadSetN (d : ℕ → E) (p : Seminorm ℝ E) (C : ℝ) (N : ℕ) :
    Set (E → ℝ) :=
  {ω | ∃ c : ℕ →₀ ℚ, c.support ⊆ Finset.range N ∧
    ¬ (|ω (c.sum fun i a => (a : ℝ) • d i)| ≤
      C * p (c.sum fun i a => (a : ℝ) • d i))}

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- B_N ⊆ B_M when N ≤ M. -/
lemma concentrationBadSetN_mono (d : ℕ → E) (p : Seminorm ℝ E) (C : ℝ)
    {N M : ℕ} (h : N ≤ M) :
    concentrationBadSetN d p C N ⊆ concentrationBadSetN d p C M := by
  intro ω hω
  obtain ⟨c, hc_supp, hc_bad⟩ := hω
  exact ⟨c, hc_supp.trans (Finset.range_mono h), hc_bad⟩

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The full bad set equals the union of the restricted bad sets.
    Every `c : ℕ →₀ ℚ` has finite support contained in some `Finset.range N`. -/
lemma concentrationBadSet_eq_iUnion (d : ℕ → E) (p : Seminorm ℝ E) (C : ℝ) :
    concentrationBadSet d p C = ⋃ N, concentrationBadSetN d p C N := by
  ext ω
  simp only [concentrationBadSet, concentrationBadSetN, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c.support.sup id + 1, c, ?_, hc⟩
    intro i hi
    exact Finset.mem_range.mpr (by
      have : i ≤ c.support.sup id := Finset.le_sup (f := id) hi
      omega)
  · rintro ⟨_, c, _, hc⟩
    exact ⟨c, hc⟩

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- If `ν(B_N) ≤ δ` for all N, then `ν(full bad set) ≤ δ`.
    Uses continuity of measure from below (`tendsto_measure_iUnion`). -/
lemma concentrationBadSet_measure_le (d : ℕ → E) (p : Seminorm ℝ E) (C : ℝ)
    (ν : Measure (E → ℝ)) (δ : ENNReal)
    (h_bound : ∀ N, ν (concentrationBadSetN d p C N) ≤ δ) :
    ν (concentrationBadSet d p C) ≤ δ := by
  rw [concentrationBadSet_eq_iUnion]
  exact le_of_tendsto' (tendsto_measure_iUnion_atTop
    (fun _ _ h => concentrationBadSetN_mono d p C h)) h_bound


/-! ## Seminorm Gram-Schmidt (sorry'd) -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- **Gram-Schmidt for Hilbertian seminorms**: given N vectors in E and a Hilbertian
    seminorm p, there exist k ≤ N p-orthonormal vectors such that every element of
    the span of the original vectors decomposes as a p-ONB combination plus a kernel
    element (where p vanishes).

    This is Gram-Schmidt applied to the positive semidefinite inner product
    `p.innerProd`. The kernel elements arise from the semidefinite (vs definite) case.

    **TODO**: Prove via explicit Gram-Schmidt construction using
    `Seminorm.innerProd_add_left`, `Seminorm.innerProd_smul_left` from PietschBridge. -/
lemma gram_schmidt_seminorm (p : Seminorm ℝ E) (hp : p.IsHilbertian)
    (N : ℕ) (d : Fin N → E) :
    ∃ (k : ℕ) (e : Fin k → E),
      p.IsOrthonormalSeq e ∧
      (∀ (β : Fin N → ℝ), ∃ (α : Fin k → ℝ),
        p (∑ i, β i • d i - ∑ j, α j • e j) = 0 ∧
        p (∑ i, β i • d i) ^ 2 = ∑ j, α j ^ 2) := by
  sorry


/-! ## Per-N concentration bound -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- For each N, the restricted bad set B_N has measure bounded by the tail probability
    of the squared evaluation norm on a p-ONB.

    Key argument: on the a.e. set where all decompositions hold,
    Cauchy-Schwarz + Parseval gives |ω(x_c)| ≤ R · p(x_c) whenever Σ ω(eⱼ)² ≤ R².
    So B_N ⊆ {Σ ω(eⱼ)² > R²} ∪ (null set). -/
lemma concentrationBadSetN_measure_bound
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_normalized : Φ 0 = 1)
    (d : ℕ → E) (p : Seminorm ℝ E) (hp : p.IsHilbertian)
    (h_cf_kernel : ∀ z, p z = 0 → ∀ t : ℝ, Φ (t • z) = 1)
    {k : ℕ} (e : Fin k → E) (he : p.IsOrthonormalSeq e)
    (h_decomp : ∀ c : ℕ →₀ ℚ, ∃ (α : Fin k → ℝ),
      p (c.sum (fun i a => (a : ℝ) • d i) - ∑ j, α j • e j) = 0 ∧
      p (c.sum (fun i a => (a : ℝ) • d i)) ^ 2 = ∑ j, α j ^ 2)
    (R : ℝ) (hR : 0 < R) (N : ℕ) :
    ν (concentrationBadSetN d p R N) ≤
      ν {ω : E → ℝ | R ^ 2 < ∑ j : Fin k, (ω (e j)) ^ 2} := by
  -- Choose decomposition coefficients for each c
  choose α hα_ker hα_parseval using h_decomp
  -- Step 1: For a.e. ω, for all c, ω(x_c) = Σ α(c)_j ω(e_j)
  have h_ae_decomp : ∀ᵐ ω ∂ν, ∀ c : ℕ →₀ ℚ,
      ω (c.sum (fun i a => (a : ℝ) • d i)) = ∑ j, (α c) j * ω (e j) := by
    rw [eventually_countable_forall]; intro c
    -- z_c = x_c - Σ α_j e_j is in the kernel of p
    set z_c := c.sum (fun i a => (a : ℝ) • d i) - ∑ j, (α c) j • e j
    -- ω(z_c) = 0 a.e. via kernel_eval_ae_zero + h_cf_kernel
    have h_z_zero := kernel_eval_ae_zero Φ ν h_cf_joint h_normalized p z_c
      (hα_ker c) (h_cf_kernel z_c (hα_ker c))
    -- x_c = z_c + Σ α_j e_j, so linear_combination_ae with (z_c, e₁,...,eₖ)
    -- and coefficients (1, α₁,...,αₖ) gives ω(x_c) = ω(z_c) + Σ α_j ω(e_j) a.e.
    let e' : Fin (k + 1) → E := Fin.cons z_c e
    let β' : Fin (k + 1) → ℝ := Fin.cons 1 (α c)
    have h_sum_eq : (∑ j, β' j • e' j) = c.sum (fun i a => (a : ℝ) • d i) := by
      rw [Fin.sum_univ_succ]
      simp only [e', β', Fin.cons_zero, Fin.cons_succ, one_smul]
      exact sub_add_cancel _ _
    have h_lin := linear_combination_ae Φ ν h_cf_joint h_normalized e' β'
    filter_upwards [h_z_zero, h_lin] with ω h_z h_xc
    -- h_xc: ω(Σ β'_j • e'_j) = Σ β'_j * ω(e'_j)
    rw [h_sum_eq] at h_xc; rw [h_xc, Fin.sum_univ_succ]
    simp only [e', β', Fin.cons_zero, Fin.cons_succ, one_mul, h_z, zero_add]
  -- Step 2: concentrationBadSetN ⊆ {R² < Σ ω(e_j)²} ∪ (null set)
  set tail := {ω : E → ℝ | R ^ 2 < ∑ j : Fin k, (ω (e j)) ^ 2}
  set null_set := {ω : E → ℝ | ¬∀ c : ℕ →₀ ℚ,
    ω (c.sum (fun i a => (a : ℝ) • d i)) = ∑ j, (α c) j * ω (e j)}
  have h_null : ν null_set = 0 := ae_iff.mp h_ae_decomp
  have h_sub : concentrationBadSetN d p R N ⊆ tail ∪ null_set := by
    intro ω hω
    by_contra h_not
    simp only [Set.mem_union, not_or] at h_not
    obtain ⟨h_not_tail, h_not_null⟩ := h_not
    simp only [tail, null_set, Set.mem_setOf_eq, not_lt, not_not] at h_not_tail h_not_null
    -- h_not_tail: Σ ω(e_j)² ≤ R²
    -- h_not_null: ∀ c, ω(x_c) = Σ α(c)_j ω(e_j)
    obtain ⟨c, _, hc_bad⟩ := hω
    apply hc_bad
    rw [h_not_null c]
    -- |Σ α(c)_j ω(e_j)| ≤ R · p(x_c) by Cauchy-Schwarz + Parseval
    have h_cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (α c) (fun j => ω (e j))
    have h_sq : (∑ j, (α c) j * ω (e j)) ^ 2 ≤
        (R * p (c.sum fun i a => (a : ℝ) • d i)) ^ 2 := by
      calc (∑ j, (α c) j * ω (e j)) ^ 2
          ≤ (∑ j, (α c) j ^ 2) * (∑ j, ω (e j) ^ 2) := h_cs
        _ = p (c.sum fun i a => (a : ℝ) • d i) ^ 2 * (∑ j, ω (e j) ^ 2) := by
            rw [hα_parseval c]
        _ ≤ p (c.sum fun i a => (a : ℝ) • d i) ^ 2 * R ^ 2 :=
            mul_le_mul_of_nonneg_left h_not_tail (sq_nonneg _)
        _ = (R * p (c.sum fun i a => (a : ℝ) • d i)) ^ 2 := by ring
    exact abs_le_of_sq_le_sq h_sq (by positivity)
  calc ν (concentrationBadSetN d p R N)
      ≤ ν (tail ∪ null_set) := measure_mono h_sub
    _ ≤ ν tail + ν null_set := measure_union_le _ _
    _ = ν tail := by rw [h_null, add_zero]


/-! ## Textbook axiom -/

/-- **Nuclear cylindrical concentration** (Gel'fand-Vilenkin Vol.4, Ch.IV §3.3).

Given:
- A separable, nonempty locally convex space `E`,
- Hilbertian seminorms `p` with consecutive Hilbert-Schmidt embeddings
  (`(p (n+1)).IsHilbertSchmidtEmbedding (p n)`) generating the topology,
- A cylindrical probability measure `ν` with continuous characteristic
  functional `Φ` satisfying `Φ(0) = 1` and the joint CF condition
  `∫ exp(i ∑ sⱼ ω(xⱼ)) dν = Φ(∑ sⱼ xⱼ)`,
- A dense sequence `d : ℕ → E`,

the conclusion is: for any `ε > 0`, there exist `m, C : ℕ` such that
  `ν {ω | ∃ c : ℕ →₀ ℚ, |ω(x_c)| > C · (p m)(x_c)} < ε`.

**Proof outline** (not yet formalized):
1. CF continuity at 0 → seminorm ball where `‖1 - Φ‖ < ε/2`.
2. Quadratic bound: `1 - Re Φ(x) ≤ ε/2 + (2/r²) · (p m₀)(x)²`.
3. Gaussian averaging on `(p m₁)`-orthonormal `{eⱼ}`:
   `𝔼[1 - exp(-σ² ω(eⱼ)²/2)] ≤ ε/2 + 2σ²(2/r²)(p m₀)(eⱼ)²`.
4. Sum over `j` using HS bound `∑ (p m₀)(eⱼ)² ≤ C_HS` → tail control.
5. Chebyshev + Bessel inequality for ℚ-linear combinations.

**References:**
- Gel'fand & Vilenkin, *Generalized Functions* Vol. 4, Ch. IV, §3.3
- Bogachev, *Gaussian Measures*, Ch. 2–3
- Minlos, *Generalized Random Processes*, Theorems 2.1–2.3 -/
axiom nuclear_cylindrical_concentration
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [SeparableSpace E] [Nonempty E]
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_cont : Continuous Φ)
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_normalized : Φ 0 = 1)
    (d : ℕ → E) (p : ℕ → Seminorm ℝ E) (hp_top : WithSeminorms (fun n => p n))
    (hp_hilb : ∀ n, (p n).IsHilbertian)
    (hp_hs : ∀ n, (p (n + 1)).IsHilbertSchmidtEmbedding (p n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (m C : ℕ),
      ν {ω | ∃ c : ℕ →₀ ℚ,
        ¬ (|ω (c.sum fun i a => (a : ℝ) • d i)| ≤
          (C : ℝ) * (p m) (c.sum fun i a => (a : ℝ) • d i))} < ENNReal.ofReal ε


/-! ## Main theorem -/

/-- **Minlos concentration bound** — wrapper around
`nuclear_cylindrical_concentration`. -/
theorem minlos_concentration [SeparableSpace E] [Nonempty E]
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_cont : Continuous Φ)
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_normalized : Φ 0 = 1)
    (d : ℕ → E) (p : ℕ → Seminorm ℝ E) (hp_top : WithSeminorms (fun n => p n))
    (hp_hilb : ∀ n, (p n).IsHilbertian)
    (hp_hs : ∀ n, (p (n + 1)).IsHilbertSchmidtEmbedding (p n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (m C : ℕ),
      ν {ω | ∃ c : ℕ →₀ ℚ,
        ¬ (|ω (c.sum fun i a => (a : ℝ) • d i)| ≤
          (C : ℝ) * (p m) (c.sum fun i a => (a : ℝ) • d i))} < ENNReal.ofReal ε :=
  nuclear_cylindrical_concentration (E := E) Φ ν h_cf_cont h_cf_joint h_normalized d p hp_top
    hp_hilb hp_hs ε hε

end
