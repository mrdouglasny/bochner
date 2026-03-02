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

open BigOperators MeasureTheory Complex TopologicalSpace Classical Finsupp

noncomputable section

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
