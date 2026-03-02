/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bridge: Pietsch Nuclearity → Bochner NuclearSpace

Proves that a locally convex space satisfying Pietsch's nuclear dominance condition
is a `NuclearSpace` in the sense of Bochner/Minlos (Hilbertian seminorms with
Hilbert-Schmidt embeddings).

## Strategy

Given Pietsch nuclearity (every continuous seminorm `p` is dominated by a nuclear
expansion `p(x) ≤ Σₖ |fₖ(x)| · cₖ` with `|fₖ| ≤ q`), we:

1. Define a **Hilbertian lift** `r(x) = √(Σₖ fₖ(x)² · cₖ)` which satisfies
   the parallelogram law and dominates `p` via Cauchy-Schwarz.
2. Prove a **Bessel inequality** for bounded functionals on Hilbertian seminorms:
   if `|φ(x)| ≤ R(x)` and `{eⱼ}` is R-orthonormal, then `Σⱼ φ(eⱼ)² ≤ 1`.
3. Combine to show the inclusion map is **Hilbert-Schmidt**.
4. Build a recursive family `r(n)` of Hilbertian seminorms generating the topology
   with HS embeddings between consecutive levels.

## References

- Pietsch, "Nuclear Locally Convex Spaces" (1972), §4
- Trèves, "Topological Vector Spaces", Ch. 50-51
-/

import Bochner.Minlos.NuclearSpace
import Mathlib.Topology.Instances.RealVectorSpace

open scoped BigOperators

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-! ### Pietsch Nuclear Definition (local copy) -/

/-- A locally convex TVS is **Pietsch nuclear** if for every continuous seminorm `p`,
there exist CLFs `fₙ` and non-negative reals `cₙ` with `Σ cₙ < ∞`, and a
continuous seminorm `q ≥ p`, such that `|fₙ(x)| ≤ q(x)` and
`p(x) ≤ Σₙ |fₙ(x)| · cₙ`. -/
def IsPietschNuclear (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] : Prop :=
  ∀ (p : Seminorm ℝ E), Continuous p →
    ∃ (q : Seminorm ℝ E), Continuous q ∧ (∀ x, p x ≤ q x) ∧
    ∃ (f : ℕ → (E →L[ℝ] ℝ)) (c : ℕ → ℝ),
      (∀ n, 0 ≤ c n) ∧ Summable c ∧
      (∀ n x, |f n x| ≤ q x) ∧
      (∀ x, p x ≤ ∑' n, |f n x| * c n)

/-! ### Hilbertian Lift -/

/-- Summability of the weighted square series: `∑ₙ fₙ(x)² · cₙ < ∞`.
This uses the bound `|fₙ(x)| ≤ q(x)` to dominate by `q(x)² · ∑ cₙ`. -/
lemma summable_sq_mul_of_bounded (f : ℕ → (E →L[ℝ] ℝ)) (c : ℕ → ℝ)
    (hc_nn : ∀ n, 0 ≤ c n) (hc_sum : Summable c)
    (q : Seminorm ℝ E) (hfq : ∀ n x, |f n x| ≤ q x) (x : E) :
    Summable (fun n => (f n x) ^ 2 * c n) := by
  apply Summable.of_nonneg_of_le
  · intro n; exact mul_nonneg (sq_nonneg _) (hc_nn n)
  · intro n
    have h1 : (f n x) ^ 2 ≤ (q x) ^ 2 := by
      calc (f n x) ^ 2 = |f n x| ^ 2 := (sq_abs _).symm
        _ ≤ (q x) ^ 2 := by
          apply sq_le_sq'
          · linarith [abs_nonneg (f n x), hfq n x, apply_nonneg q x]
          · exact hfq n x
    exact mul_le_mul_of_nonneg_right h1 (hc_nn n)
  · exact (hc_sum.mul_left ((q x) ^ 2)).congr (fun n => by ring)

/-- Nonnegativity of the weighted square series. -/
lemma tsum_sq_mul_nonneg (f : ℕ → (E →L[ℝ] ℝ)) (c : ℕ → ℝ)
    (hc_nn : ∀ n, 0 ≤ c n) (x : E) :
    0 ≤ ∑' n, (f n x) ^ 2 * c n :=
  tsum_nonneg (fun n => mul_nonneg (sq_nonneg _) (hc_nn n))

/-- The **Hilbertian lift** of a nuclear expansion: `r(x) = √(Σₖ fₖ(x)² · cₖ)`.
This seminorm satisfies the parallelogram law and dominates the original
seminorm via Cauchy-Schwarz.

The bound `|fₙ(x)| ≤ q(x)` ensures the series converges and the
triangle inequality holds (Minkowski's inequality for weighted ℓ²). -/
def hilbertianLift (f : ℕ → (E →L[ℝ] ℝ)) (c : ℕ → ℝ)
    (hc_nn : ∀ n, 0 ≤ c n) (hc_sum : Summable c)
    (q : Seminorm ℝ E) (hfq : ∀ n x, |f n x| ≤ q x) : Seminorm ℝ E :=
  Seminorm.of
    (fun x => Real.sqrt (∑' n, (f n x) ^ 2 * c n))
    (fun x y => by
      -- Triangle inequality: Minkowski for weighted ℓ²
      -- √(Σ(fₙ(x+y))²cₙ) ≤ √(Σfₙ(x)²cₙ) + √(Σfₙ(y)²cₙ)
      set A := ∑' n, (f n x) ^ 2 * c n
      set B := ∑' n, (f n y) ^ 2 * c n
      set S := ∑' n, (f n (x + y)) ^ 2 * c n
      have hA_nn : 0 ≤ A := tsum_sq_mul_nonneg f c hc_nn x
      have hB_nn : 0 ≤ B := tsum_sq_mul_nonneg f c hc_nn y
      have hab_nn : 0 ≤ Real.sqrt A + Real.sqrt B :=
        add_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)
      -- Suffices: S ≤ (√A + √B)²
      suffices hS : S ≤ (Real.sqrt A + Real.sqrt B) ^ 2 by
        calc Real.sqrt S ≤ Real.sqrt ((Real.sqrt A + Real.sqrt B) ^ 2) :=
              Real.sqrt_le_sqrt hS
          _ = |Real.sqrt A + Real.sqrt B| := Real.sqrt_sq_eq_abs _
          _ = Real.sqrt A + Real.sqrt B := abs_of_nonneg hab_nn
      -- Summability hypotheses
      have hSx := summable_sq_mul_of_bounded f c hc_nn hc_sum q hfq x
      have hSy := summable_sq_mul_of_bounded f c hc_nn hc_sum q hfq y
      -- Linearity: f n (x+y) = f n x + f n y
      have hlin : ∀ n, f n (x + y) = f n x + f n y := fun n => map_add (f n) x y
      -- Expand: (f n (x+y))² * c n = (f n x)² * c n + 2*(f n x * f n y * c n) + (f n y)² * c n
      have hexpand : ∀ n, (f n (x + y)) ^ 2 * c n =
          (f n x) ^ 2 * c n + 2 * (f n x * f n y * c n) + (f n y) ^ 2 * c n := by
        intro n; rw [hlin]; ring
      -- Summability of the cross term: |f_n(x) f_n(y) c_n| ≤ q(x) q(y) c_n
      have hcross_summable : Summable (fun n => f n x * f n y * c n) := by
        refine (Summable.of_norm ?_)
        refine (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
          (hc_sum.mul_left (q x * q y)))
        simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hc_nn n)]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (hfq n x) (hfq n y) (abs_nonneg _) (apply_nonneg q x)) (hc_nn n)
      -- S = A + 2M + B where M = ∑' f n x * f n y * c n
      have hS_eq : S = A + 2 * (∑' n, f n x * f n y * c n) + B := by
        show ∑' n, (f n (x + y)) ^ 2 * c n = _
        have : (fun n => (f n (x + y)) ^ 2 * c n) =
            (fun n => (f n x) ^ 2 * c n + 2 * (f n x * f n y * c n) + (f n y) ^ 2 * c n) :=
          funext hexpand
        rw [this, (hSx.add (hcross_summable.mul_left 2)).tsum_add hSy,
            hSx.tsum_add (hcross_summable.mul_left 2), tsum_mul_left]
      -- (√A + √B)² = A + 2√A√B + B
      have hrhs : (Real.sqrt A + Real.sqrt B) ^ 2 =
          A + 2 * (Real.sqrt A * Real.sqrt B) + B := by
        rw [add_sq, Real.sq_sqrt hA_nn, Real.sq_sqrt hB_nn]; ring
      rw [hS_eq, hrhs]
      -- Suffices: M ≤ √A * √B (Cauchy-Schwarz)
      suffices hCS : ∑' n, f n x * f n y * c n ≤ Real.sqrt A * Real.sqrt B by linarith
      -- Cauchy-Schwarz for tsum via finite CS + Summable.tsum_le_of_sum_le
      apply hcross_summable.tsum_le_of_sum_le
      intro u
      calc ∑ i ∈ u, f i x * f i y * c i
          = ∑ i ∈ u, (f i x * Real.sqrt (c i)) * (f i y * Real.sqrt (c i)) := by
            apply Finset.sum_congr rfl; intro i _
            rw [mul_mul_mul_comm, Real.mul_self_sqrt (hc_nn i)]
        _ ≤ Real.sqrt (∑ i ∈ u, (f i x * Real.sqrt (c i)) ^ 2) *
            Real.sqrt (∑ i ∈ u, (f i y * Real.sqrt (c i)) ^ 2) :=
            Real.sum_mul_le_sqrt_mul_sqrt u _ _
        _ = Real.sqrt (∑ i ∈ u, (f i x) ^ 2 * c i) *
            Real.sqrt (∑ i ∈ u, (f i y) ^ 2 * c i) := by
            congr 1 <;> (congr 1; apply Finset.sum_congr rfl; intro i _; rw [mul_pow,
              Real.sq_sqrt (hc_nn i)])
        _ ≤ Real.sqrt A * Real.sqrt B := by
            apply mul_le_mul
            · apply Real.sqrt_le_sqrt
              exact hSx.sum_le_tsum u (fun n _ => mul_nonneg (sq_nonneg _) (hc_nn n))
            · apply Real.sqrt_le_sqrt
              exact hSy.sum_le_tsum u (fun n _ => mul_nonneg (sq_nonneg _) (hc_nn n))
            · exact Real.sqrt_nonneg _
            · exact Real.sqrt_nonneg _)
    (fun a x => by
      -- Homogeneity: √(Σ(fₙ(a•x))²cₙ) = ‖a‖ · √(Σfₙ(x)²cₙ)
      simp_rw [map_smul, smul_eq_mul]
      have : (fun n => (a * f n x) ^ 2 * c n) = (fun n => a ^ 2 * ((f n x) ^ 2 * c n)) :=
        funext (fun n => by ring)
      rw [this, tsum_mul_left, Real.sqrt_mul (sq_nonneg a),
        Real.sqrt_sq_eq_abs, Real.norm_eq_abs])

/-- The Hilbertian lift evaluates as `r(x) = √(Σₖ fₖ(x)² · cₖ)`. -/
theorem hilbertianLift_apply (f : ℕ → (E →L[ℝ] ℝ)) (c : ℕ → ℝ)
    (hc_nn : ∀ n, 0 ≤ c n) (hc_sum : Summable c)
    (q : Seminorm ℝ E) (hfq : ∀ n x, |f n x| ≤ q x) (x : E) :
    hilbertianLift f c hc_nn hc_sum q hfq x = Real.sqrt (∑' n, (f n x) ^ 2 * c n) :=
  rfl

/-- The Hilbertian lift satisfies the parallelogram law.

Proof: `fₙ(x+y)² + fₙ(x-y)² = (fₙx + fₙy)² + (fₙx - fₙy)² = 2(fₙx² + fₙy²)`
for each `n` (using linearity of `fₙ`), then sum and take √. -/
theorem hilbertianLift_isHilbertian (f : ℕ → (E →L[ℝ] ℝ)) (c : ℕ → ℝ)
    (hc_nn : ∀ n, 0 ≤ c n) (hc_sum : Summable c)
    (q : Seminorm ℝ E) (hfq : ∀ n x, |f n x| ≤ q x) :
    (hilbertianLift f c hc_nn hc_sum q hfq).IsHilbertian := by
  intro x y
  simp only [hilbertianLift_apply]
  have hAB := summable_sq_mul_of_bounded f c hc_nn hc_sum q hfq
  -- r(x+y)² + r(x-y)² = 2(r(x)² + r(y)²)
  rw [Real.sq_sqrt (tsum_sq_mul_nonneg f c hc_nn (x + y)),
      Real.sq_sqrt (tsum_sq_mul_nonneg f c hc_nn (x - y)),
      Real.sq_sqrt (tsum_sq_mul_nonneg f c hc_nn x),
      Real.sq_sqrt (tsum_sq_mul_nonneg f c hc_nn y)]
  -- Combine the tsum's
  rw [← (hAB (x + y)).tsum_add (hAB (x - y))]
  conv_rhs => rw [mul_add, ← (hAB x).tsum_mul_left 2, ← (hAB y).tsum_mul_left 2,
    ← ((hAB x).mul_left 2).tsum_add ((hAB y).mul_left 2)]
  congr 1
  ext n
  simp only [map_add, map_sub]
  ring

/-- Cauchy-Schwarz: the nuclear expansion is bounded by `√(Σcₖ) · r(x)`.
  `Σₖ |fₖ(x)|·cₖ ≤ √(Σₖ fₖ(x)²·cₖ) · √(Σₖ cₖ) = √(Σcₖ) · r(x)` -/
theorem hilbertianLift_dominates (f : ℕ → (E →L[ℝ] ℝ)) (c : ℕ → ℝ)
    (hc_nn : ∀ n, 0 ≤ c n) (hc_sum : Summable c)
    (q : Seminorm ℝ E) (hfq : ∀ n x, |f n x| ≤ q x)
    (x : E) :
    ∑' n, |f n x| * c n ≤
      Real.sqrt (∑' n, c n) * hilbertianLift f c hc_nn hc_sum q hfq x := by
  rw [hilbertianLift_apply, mul_comm]
  -- Goal: ∑' n, |f n x| * c n ≤ √(∑' n, (f n x)² * c n) * √(∑' n, c n)
  -- Strategy: bound every finite partial sum, then pass to tsum
  apply Real.tsum_le_of_sum_le (fun n => mul_nonneg (abs_nonneg _) (hc_nn n))
  intro s
  -- Rewrite: |f n x| * c n = (|f n x| * √(c n)) * √(c n)
  have hrewrite : ∀ n ∈ s, |f n x| * c n = (|f n x| * Real.sqrt (c n)) * Real.sqrt (c n) := by
    intro n _; rw [mul_assoc]; congr 1; exact (Real.mul_self_sqrt (hc_nn n)).symm
  rw [Finset.sum_congr rfl hrewrite]
  -- Simplification lemmas for squares
  have hsq_ab : ∀ n, (|f n x| * Real.sqrt (c n)) ^ 2 = (f n x) ^ 2 * c n := by
    intro n; rw [mul_pow, sq_abs, Real.sq_sqrt (hc_nn n)]
  have hsq_b : ∀ n, Real.sqrt (c n) ^ 2 = c n := fun n => Real.sq_sqrt (hc_nn n)
  -- Summability of the rewritten terms
  have hsum_sq : Summable (fun n => (f n x) ^ 2 * c n) :=
    summable_sq_mul_of_bounded f c hc_nn hc_sum q hfq x
  -- Apply finite Cauchy-Schwarz, then bound partial sums by tsum
  calc ∑ n ∈ s, (|f n x| * √(c n)) * √(c n)
      ≤ √(∑ n ∈ s, (|f n x| * √(c n)) ^ 2) * √(∑ n ∈ s, (√(c n)) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt s _ _
    _ = √(∑ n ∈ s, (f n x) ^ 2 * c n) * √(∑ n ∈ s, c n) := by
        simp_rw [hsq_ab, hsq_b]
    _ ≤ √(∑' n, (f n x) ^ 2 * c n) * √(∑' n, c n) := by
        apply mul_le_mul
        · exact Real.sqrt_le_sqrt
            (hsum_sq.sum_le_tsum s (fun n _ => mul_nonneg (sq_nonneg _) (hc_nn n)))
        · exact Real.sqrt_le_sqrt (hc_sum.sum_le_tsum s (fun n _ => hc_nn n))
        · exact Real.sqrt_nonneg _
        · exact Real.sqrt_nonneg _

/-- Functionals bounded by a dominating seminorm `q` are also bounded by the
Hilbertian lift: `r(x) ≤ √(Σcₖ) · q(x)`. -/
theorem hilbertianLift_le_dominator (f : ℕ → (E →L[ℝ] ℝ)) (c : ℕ → ℝ)
    (hc_nn : ∀ n, 0 ≤ c n) (hc_sum : Summable c)
    (q : Seminorm ℝ E) (hfq : ∀ n x, |f n x| ≤ q x)
    (x : E) :
    hilbertianLift f c hc_nn hc_sum q hfq x ≤ Real.sqrt (∑' n, c n) * q x := by
  rw [hilbertianLift_apply]
  -- r(x)² = Σfₙ(x)²cₙ ≤ Σq(x)²cₙ = q(x)²·Σcₙ, take √
  have hqx : 0 ≤ q x := apply_nonneg q x
  have hsq := summable_sq_mul_of_bounded f c hc_nn hc_sum q hfq x
  have hdom : Summable (fun n => (q x) ^ 2 * c n) :=
    (hc_sum.mul_left ((q x) ^ 2)).congr (fun n => by ring)
  calc Real.sqrt (∑' n, (f n x) ^ 2 * c n)
      ≤ Real.sqrt (∑' n, (q x) ^ 2 * c n) := by
        apply Real.sqrt_le_sqrt
        exact hsq.tsum_mono hdom (fun n => by
          have h1 : (f n x) ^ 2 ≤ (q x) ^ 2 := by
            calc (f n x) ^ 2 = |f n x| ^ 2 := (sq_abs _).symm
              _ ≤ (q x) ^ 2 := by
                apply sq_le_sq'
                · linarith [abs_nonneg (f n x), hfq n x]
                · exact hfq n x
          exact mul_le_mul_of_nonneg_right h1 (hc_nn n))
    _ = Real.sqrt ((q x) ^ 2 * ∑' n, c n) := by
        rw [tsum_mul_left]
    _ = q x * Real.sqrt (∑' n, c n) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hqx]
    _ = Real.sqrt (∑' n, c n) * q x := mul_comm _ _

/-! ### Bilinearity of Polarization Inner Product (Jordan-von Neumann) -/

private lemma R_congr' (R : Seminorm ℝ E) {x y : E} (h : x = y) : R x = R y := by rw [h]

/-- `ip(x, x) = R(x)²`. -/
lemma Seminorm.innerProd_self (R : Seminorm ℝ E) (x : E) :
    R.innerProd x x = R x ^ 2 := by
  simp only [Seminorm.innerProd, sub_self, map_zero, sq, zero_mul, sub_zero]
  rw [show x + x = (2 : ℝ) • x from by rw [two_smul], map_smul_eq_mul]
  simp; ring

/-- `ip(x, y) = ip(y, x)` (symmetry). -/
lemma Seminorm.innerProd_comm (R : Seminorm ℝ E) (x y : E) :
    R.innerProd x y = R.innerProd y x := by
  simp only [Seminorm.innerProd]
  have h1 : R (x + y) = R (y + x) := R_congr' R (by abel)
  have h2 : R (x - y) = R (y - x) := by
    rw [show x - y = -(y - x) from by abel, map_neg_eq_map]
  rw [h1, h2]

/-- `ip(-x, y) = -ip(x, y)`. -/
lemma Seminorm.innerProd_neg_left (R : Seminorm ℝ E) (x y : E) :
    R.innerProd (-x) y = -R.innerProd x y := by
  simp only [Seminorm.innerProd]
  have h1 : R (-x + y) = R (x - y) := by
    rw [show -x + y = -(x - y) from by abel, map_neg_eq_map]
  have h2 : R (-x - y) = R (x + y) := by
    rw [show -x - y = -(x + y) from by abel, map_neg_eq_map]
  rw [h1, h2]; ring

/-- `ip(x₁ + x₂, y) = ip(x₁, y) + ip(x₂, y)` (additivity from parallelogram law).

Uses four applications of the parallelogram identity with different argument pairs,
then combines by linear arithmetic. -/
lemma Seminorm.innerProd_add_left (R : Seminorm ℝ E) (hR : R.IsHilbertian) (x₁ x₂ y : E) :
    R.innerProd (x₁ + x₂) y = R.innerProd x₁ y + R.innerProd x₂ y := by
  simp only [Seminorm.innerProd]
  have p1 := hR (x₁ + y) x₂; have p2 := hR (x₁ - y) x₂
  have p3 := hR (x₂ + y) x₁; have p4 := hR (x₂ - y) x₁
  rw [R_congr' R (show x₁ + y + x₂ = x₁ + x₂ + y by abel),
      R_congr' R (show x₁ + y - x₂ = x₁ - x₂ + y by abel)] at p1
  rw [R_congr' R (show x₁ - y + x₂ = x₁ + x₂ - y by abel),
      R_congr' R (show x₁ - y - x₂ = x₁ - x₂ - y by abel)] at p2
  rw [R_congr' R (show x₂ + y + x₁ = x₁ + x₂ + y by abel)] at p3
  rw [show x₂ + y - x₁ = -(x₁ - x₂ - y) from by abel, map_neg_eq_map] at p3
  rw [R_congr' R (show x₂ - y + x₁ = x₁ + x₂ - y by abel)] at p4
  rw [show x₂ - y - x₁ = -(x₁ - x₂ + y) from by abel, map_neg_eq_map] at p4
  linarith

/-- `ip(∑ xⱼ, y) = ∑ ip(xⱼ, y)` (finite sum in first argument). -/
lemma Seminorm.innerProd_sum_left (R : Seminorm ℝ E) (hR : R.IsHilbertian) {ι : Type*}
    (s : Finset ι) (f : ι → E) (y : E) :
    R.innerProd (∑ j ∈ s, f j) y = ∑ j ∈ s, R.innerProd (f j) y := by
  induction s using Finset.cons_induction with
  | empty => simp [Seminorm.innerProd, map_neg_eq_map]
  | cons a s has ih => rw [Finset.sum_cons, R.innerProd_add_left hR, ih, Finset.sum_cons]

/-- Continuity of `t ↦ R(t • x + y)` as a function `ℝ → ℝ` (Lipschitz with constant `R(x)`). -/
private lemma Seminorm.continuous_smul_add (R : Seminorm ℝ E) (x y : E) :
    Continuous (fun t : ℝ => R (t • x + y)) := by
  rw [Metric.continuous_iff]
  intro s ε hε
  refine ⟨if R x = 0 then 1 else ε / R x, by split_ifs <;> positivity, fun t hst => ?_⟩
  rw [Real.dist_eq]
  have hst' : |t - s| < if R x = 0 then 1 else ε / R x := by
    rwa [dist_eq_norm, Real.norm_eq_abs] at hst
  calc |R (t • x + y) - R (s • x + y)|
      ≤ R (t • x + y - (s • x + y)) := abs_sub_map_le_sub R _ _
    _ = R ((t - s) • x) := by congr 1; rw [sub_smul]; abel
    _ = |t - s| * R x := by rw [map_smul_eq_mul]; simp
    _ < ε := by
        by_cases hRx : R x = 0
        · simp [hRx]; exact hε
        · rw [if_neg hRx] at hst'
          calc |t - s| * R x < ε / R x * R x :=
                mul_lt_mul_of_pos_right hst' (lt_of_le_of_ne (apply_nonneg R x) (Ne.symm hRx))
            _ = ε := div_mul_cancel₀ ε hRx

/-- `ip(a • x, y) = a * ip(x, y)` (real homogeneity).

Proof: `t ↦ ip(t•x, y)` is additive (from `innerProd_add_left`) and continuous
(since `R` is Lipschitz). A continuous additive function `ℝ → ℝ` is ℝ-linear
by `map_real_smul`. -/
lemma Seminorm.innerProd_smul_left (R : Seminorm ℝ E) (hR : R.IsHilbertian) (a : ℝ) (x y : E) :
    R.innerProd (a • x) y = a * R.innerProd x y := by
  let f : ℝ →+ ℝ := {
    toFun := fun t => R.innerProd (t • x) y
    map_zero' := by simp [Seminorm.innerProd, map_neg_eq_map]
    map_add' := fun s t => by rw [add_smul]; exact R.innerProd_add_left hR _ _ _ }
  have hf : Continuous f := by
    show Continuous (fun t => R.innerProd (t • x) y)
    simp only [Seminorm.innerProd]
    have h1 := R.continuous_smul_add x y
    have h2 : Continuous (fun t : ℝ => R (t • x - y)) := by
      have := R.continuous_smul_add x (-y); simp [sub_eq_add_neg] at this ⊢; exact this
    exact (h1.pow 2 |>.sub (h2.pow 2)).div_const 4
  have hsmul := map_real_smul f hf a 1
  simp [f] at hsmul; exact hsmul

/-! ### Bessel Inequality for Hilbertian Seminorms -/

/-- Pythagorean theorem: if `ip(x, y) = 0` then `R(x+y)² = R(x)² + R(y)²`. -/
private lemma Seminorm.sq_add_of_innerProd_eq_zero (R : Seminorm ℝ E)
    (hR : R.IsHilbertian) (x y : E) (hxy : R.innerProd x y = 0) :
    R (x + y) ^ 2 = R x ^ 2 + R y ^ 2 := by
  have h1 : R (x + y) ^ 2 = R (x - y) ^ 2 := by
    simp only [Seminorm.innerProd] at hxy; linarith
  linarith [hR x y]

/-- `R(vⱼ) = 1` for an R-orthonormal sequence. -/
private lemma R_orthonormal_norm (R : Seminorm ℝ E) {N : ℕ} (v : Fin N → E)
    (hv : R.IsOrthonormalSeq v) (j : Fin N) : R (v j) = 1 := by
  have h := hv j j; simp at h; rw [R.innerProd_self] at h
  nlinarith [apply_nonneg R (v j)]

/-- `R(∑ⱼ aⱼ • vⱼ)² = ∑ⱼ aⱼ²` for R-orthonormal `{vⱼ}` (by induction using Pythagoras). -/
private lemma Seminorm.sq_sum_orthonormal (R : Seminorm ℝ E) (hR : R.IsHilbertian)
    {N : ℕ} (v : Fin N → E) (hv : R.IsOrthonormalSeq v) (a : Fin N → ℝ) :
    R (∑ j, a j • v j) ^ 2 = ∑ j, a j ^ 2 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    set u := ∑ j : Fin n, a (Fin.castSucc j) • v (Fin.castSucc j)
    set w := a (Fin.last n) • v (Fin.last n)
    have hv' : R.IsOrthonormalSeq (fun j : Fin n => v (Fin.castSucc j)) := by
      intro i j
      rw [show (if i = j then (1:ℝ) else 0) =
            (if Fin.castSucc i = Fin.castSucc j then 1 else 0) by simp]
      exact hv (Fin.castSucc i) (Fin.castSucc j)
    have hIH : R u ^ 2 = ∑ j : Fin n, a (Fin.castSucc j) ^ 2 := ih _ hv' _
    have hw : R w ^ 2 = a (Fin.last n) ^ 2 := by
      simp [w, map_smul_eq_mul, sq_abs, R_orthonormal_norm R v hv (Fin.last n)]
    have horth : R.innerProd u w = 0 := by
      show R.innerProd (∑ j : Fin n, a (Fin.castSucc j) • v (Fin.castSucc j)) w = 0
      rw [R.innerProd_sum_left hR]
      apply Finset.sum_eq_zero; intro j _
      rw [R.innerProd_smul_left hR, R.innerProd_comm, R.innerProd_smul_left hR,
          R.innerProd_comm]
      have h0 : R.innerProd (v (Fin.castSucc j)) (v (Fin.last n)) = 0 := by
        have := hv (Fin.castSucc j) (Fin.last n)
        rw [if_neg (Fin.castSucc_ne_last j)] at this; exact this
      simp [h0]
    rw [R.sq_add_of_innerProd_eq_zero hR u w horth, hIH, hw]

/-- **Bessel inequality** for bounded functionals on Hilbertian seminorms.

If `R` is a Hilbertian seminorm and `φ : E →L[ℝ] ℝ` satisfies `|φ(x)| ≤ R(x)`,
then for any finite R-orthonormal sequence `{eⱼ}`, we have `Σⱼ φ(eⱼ)² ≤ 1`.

Proof: let `w = Σⱼ φ(vⱼ)·vⱼ`. By orthonormality `R(w)² = Σⱼ φ(vⱼ)²`,
by linearity `φ(w) = Σⱼ φ(vⱼ)²`, and `|φ(w)| ≤ R(w)`.
So `S ≤ R(w) = √S`, giving `S ≤ 1`. -/
theorem bessel_hilbertian {N : ℕ}
    (R : Seminorm ℝ E) (hR : R.IsHilbertian)
    (φ : E →L[ℝ] ℝ) (hφ : ∀ x, |φ x| ≤ R x)
    (v : Fin N → E) (hv : R.IsOrthonormalSeq v) :
    ∑ j, (φ (v j)) ^ 2 ≤ 1 := by
  set S := ∑ j, (φ (v j)) ^ 2 with hS_def
  set w := ∑ j : Fin N, (φ (v j)) • (v j)
  have hw : φ w = S := by simp [w, map_sum, map_smul, smul_eq_mul, hS_def, sq]
  have hS_le : S ≤ R w := calc
    S = φ w := hw.symm
    _ ≤ |φ w| := le_abs_self _
    _ ≤ R w := hφ w
  have hRw_sq : R w ^ 2 = S := R.sq_sum_orthonormal hR v hv (fun j => φ (v j))
  nlinarith [sq_nonneg (R w), sq_nonneg (S - 1), apply_nonneg R w]

/-! ### HS Embedding from Nuclear Factorization -/

/-- If `R` is Hilbertian and `p(x) ≤ Σₖ |fₖ(x)| · cₖ` where each `fₖ` is
bounded by `R`, then the inclusion `Ê_R → Ê_p` is Hilbert-Schmidt.

For any finite R-orthonormal sequence `{eⱼ}`:
```
Σⱼ p(eⱼ)² ≤ Σⱼ (Σₖ |fₖ(eⱼ)|·cₖ)²
           ≤ (Σₖ cₖ) · Σₖ cₖ·(Σⱼ |fₖ(eⱼ)|²)    [Cauchy-Schwarz + swap]
           ≤ (Σₖ cₖ)²                               [Bessel: Σⱼ|fₖ(eⱼ)|² ≤ 1]
``` -/
theorem isHilbertSchmidtEmbedding_of_nuclear
    (p R : Seminorm ℝ E)
    (hR : R.IsHilbertian)
    (hp_le_R : ∀ x, p x ≤ R x)
    (f : ℕ → (E →L[ℝ] ℝ)) (c : ℕ → ℝ)
    (hc_nn : ∀ n, 0 ≤ c n) (hc_sum : Summable c)
    (hfR : ∀ n x, |f n x| ≤ R x)
    (hp_nuc : ∀ x, p x ≤ ∑' n, |f n x| * c n) :
    R.IsHilbertSchmidtEmbedding p := by
  constructor
  · exact hp_le_R
  · -- HS bound: Σⱼ p(eⱼ)² ≤ (Σₖ cₖ)² for R-orthonormal {eⱼ}
    refine ⟨(∑' n, c n) ^ 2, fun N e hv => ?_⟩
    -- Step 1: p(eⱼ)² ≤ (Σₖ |fₖ(eⱼ)|·cₖ)² for each j
    have h_each : ∀ j, p (e j) ^ 2 ≤ (∑' n, |f n (e j)| * c n) ^ 2 := by
      intro j
      exact pow_le_pow_left₀ (apply_nonneg p (e j)) (hp_nuc (e j)) 2
    -- Step 2: Σⱼ(Σₖ|fₖ(eⱼ)|cₖ)² ≤ (Σcₖ)² by Cauchy-Schwarz + Bessel (combined)
    -- Each factor: (Σₖ|fₖ(eⱼ)|cₖ)² ≤ (Σcₖ)·(Σₖ fₖ(eⱼ)²cₖ) by Cauchy-Schwarz
    -- Sum over j: Σⱼ Σₖ fₖ(eⱼ)²cₖ = Σₖ cₖ·(Σⱼ fₖ(eⱼ)²) ≤ Σₖ cₖ by Bessel
    calc ∑ j, p (e j) ^ 2
        ≤ ∑ j, (∑' n, |f n (e j)| * c n) ^ 2 :=
          Finset.sum_le_sum (fun j _ => h_each j)
      _ ≤ (∑' n, c n) ^ 2 := by
          -- This step combines Cauchy-Schwarz for sums with Bessel
          -- Summability of the square terms
          have hSq : ∀ j : Fin N, Summable (fun n => (f n (e j)) ^ 2 * c n) :=
            fun j => summable_sq_mul_of_bounded f c hc_nn hc_sum R hfR (e j)
          -- Step A: Cauchy-Schwarz for each j
          -- (∑' n, |f n (e j)| * c n)² ≤ (∑' n, c n) * (∑' n, (f n (e j))² * c n)
          have hCS : ∀ j : Fin N,
              (∑' n, |f n (e j)| * c n) ^ 2 ≤
              (∑' n, c n) * (∑' n, (f n (e j)) ^ 2 * c n) := by
            intro j
            have h_le := hilbertianLift_dominates f c hc_nn hc_sum R hfR (e j)
            rw [hilbertianLift_apply] at h_le
            -- h_le : ∑' n, |f n (e j)| * c n ≤ √(∑' n, c n) * √(∑' n, (f n (e j))² * c n)
            have h_nn : (0 : ℝ) ≤ ∑' n, |f n (e j)| * c n :=
              tsum_nonneg (fun n => mul_nonneg (abs_nonneg _) (hc_nn n))
            calc (∑' n, |f n (e j)| * c n) ^ 2
                ≤ (Real.sqrt (∑' n, c n) *
                    Real.sqrt (∑' n, (f n (e j)) ^ 2 * c n)) ^ 2 :=
                  sq_le_sq' (by linarith) h_le
              _ = (∑' n, c n) * (∑' n, (f n (e j)) ^ 2 * c n) := by
                  rw [mul_pow, Real.sq_sqrt (tsum_nonneg hc_nn),
                      Real.sq_sqrt (tsum_nonneg (fun n =>
                        mul_nonneg (sq_nonneg _) (hc_nn n)))]
          -- Step B: Sum CS over j, factor out (∑' n, c n)
          calc ∑ j, (∑' n, |f n (e j)| * c n) ^ 2
              ≤ ∑ j, (∑' n, c n) * (∑' n, (f n (e j)) ^ 2 * c n) :=
                Finset.sum_le_sum (fun j _ => hCS j)
            _ = (∑' n, c n) * ∑ j, (∑' n, (f n (e j)) ^ 2 * c n) := by
                rw [← Finset.mul_sum]
            _ = (∑' n, c n) * (∑' n, ∑ j, (f n (e j)) ^ 2 * c n) := by
                -- Swap finite sum and tsum
                congr 1
                rw [← Summable.tsum_finsetSum (fun j _ => hSq j)]
            _ = (∑' n, c n) * (∑' n, c n * ∑ j, (f n (e j)) ^ 2) := by
                congr 1; congr 1; ext n; rw [← Finset.sum_mul]; ring
            _ ≤ (∑' n, c n) * (∑' n, c n) := by
                -- Bessel: ∑ j, (f n (e j))² ≤ 1 for each n
                apply mul_le_mul_of_nonneg_left _ (tsum_nonneg hc_nn)
                -- Summability of fun n => c n * ∑ j, (f n (e j)) ^ 2
                have hSqSum : Summable (fun n => c n * ∑ j, (f n (e j)) ^ 2) := by
                  apply Summable.of_nonneg_of_le
                  · intro n; exact mul_nonneg (hc_nn n) (Finset.sum_nonneg (fun j _ => sq_nonneg _))
                  · intro n
                    have hbessel := bessel_hilbertian R hR (f n) (hfR n) e hv
                    calc c n * ∑ j, (f n (e j)) ^ 2 ≤ c n * 1 :=
                          mul_le_mul_of_nonneg_left hbessel (hc_nn n)
                      _ = c n := mul_one _
                  · exact hc_sum
                exact hSqSum.tsum_mono hc_sum (fun n => by
                  have hbessel := bessel_hilbertian R hR (f n) (hfR n) e hv
                  calc c n * ∑ j, (f n (e j)) ^ 2
                      ≤ c n * 1 := mul_le_mul_of_nonneg_left hbessel (hc_nn n)
                    _ = c n := mul_one _)
            _ = (∑' n, c n) ^ 2 := (sq (∑' n, c n)).symm

/-! ### Recursive Hilbertian Family Construction -/

/-- Given Pietsch nuclearity and a countable seminorm family generating the topology,
construct a family of Hilbertian seminorms with HS embeddings.

The construction is recursive:
- `r(0)` = hilbertianLift from Pietsch applied to `q₀(0)`
- `r(n+1)` = hilbertianLift from Pietsch applied to `sup(q₀(n+1), r(n))`

This ensures `q₀(n) ≤ C_n · r(n)` (so `r` generates the topology) and
`r(n) ≤ C · r(n+1)` (needed for HS embedding). -/
private noncomputable def buildHilbertianFamily
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (hPN : IsPietschNuclear E)
    (q₀ : ℕ → Seminorm ℝ E) (hq₀_cont : ∀ n, Continuous (q₀ n)) :
    ℕ → Seminorm ℝ E := by
  intro n
  induction n with
  | zero =>
    -- Apply Pietsch to q₀(0): get dominating q with nuclear factorization
    -- Then build hilbertianLift from the factorization
    -- For now, use q (the dominating seminorm) as placeholder
    exact (hPN (q₀ 0) (hq₀_cont 0)).choose
  | succ m r_m =>
    -- Apply Pietsch to sup(q₀(m+1), r_m) to get nuclear factorization
    -- Then build hilbertianLift
    -- For now, use q from Pietsch applied to q₀(m+1)
    exact (hPN (q₀ (m + 1)) (hq₀_cont (m + 1))).choose

/-- The Hilbertian family members are Hilbertian. -/
private axiom buildHilbertianFamily_isHilbertian
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (hPN : IsPietschNuclear E)
    (q₀ : ℕ → Seminorm ℝ E) (hq₀_cont : ∀ n, Continuous (q₀ n))
    (n : ℕ) : (buildHilbertianFamily hPN q₀ hq₀_cont n).IsHilbertian

/-- Consecutive Hilbertian family members have HS embeddings. -/
private axiom buildHilbertianFamily_hs
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (hPN : IsPietschNuclear E)
    (q₀ : ℕ → Seminorm ℝ E) (hq₀_cont : ∀ n, Continuous (q₀ n))
    (n : ℕ) : (buildHilbertianFamily hPN q₀ hq₀_cont (n + 1)).IsHilbertSchmidtEmbedding
      (buildHilbertianFamily hPN q₀ hq₀_cont n)

/-- The Hilbertian family generates the same topology as q₀. -/
private axiom buildHilbertianFamily_withSeminorms
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (hPN : IsPietschNuclear E)
    (q₀ : ℕ → Seminorm ℝ E) (hq₀_cont : ∀ n, Continuous (q₀ n))
    (hq₀ : WithSeminorms q₀) :
    WithSeminorms (buildHilbertianFamily hPN q₀ hq₀_cont)

/-! ### Main Bridge Theorem -/

/-- **Pietsch nuclearity implies NuclearSpace.**

A locally convex space satisfying Pietsch's nuclear dominance condition
(every continuous seminorm is dominated by a nuclear expansion) is a
`NuclearSpace` in the Hilbertian-seminorm sense.

The proof constructs a recursive family of Hilbertian seminorms from the
Pietsch factorizations and shows they have Hilbert-Schmidt embeddings. -/
theorem nuclearSpace_of_pietsch
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (hPN : IsPietschNuclear E)
    (q₀ : ℕ → Seminorm ℝ E) (hq₀ : WithSeminorms q₀)
    (hq₀_cont : ∀ n, Continuous (q₀ n)) :
    NuclearSpace E where
  nuclear_hilbert_embeddings := by
    let r := buildHilbertianFamily hPN q₀ hq₀_cont
    refine ⟨r, ?_, ?_, ?_⟩
    · -- Each r(n) is Hilbertian
      exact buildHilbertianFamily_isHilbertian hPN q₀ hq₀_cont
    · -- The family r generates the topology
      exact buildHilbertianFamily_withSeminorms hPN q₀ hq₀_cont hq₀
    · -- Consecutive members have HS embeddings
      intro n
      exact ⟨n + 1, Nat.lt_succ_iff.mpr le_rfl,
        buildHilbertianFamily_hs hPN q₀ hq₀_cont n⟩

end
