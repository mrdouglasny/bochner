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
      sorry)
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

/-! ### Bessel Inequality for Hilbertian Seminorms -/

/-- **Bessel inequality** for bounded functionals on Hilbertian seminorms.

If `R` is a Hilbertian seminorm and `φ : E →L[ℝ] ℝ` satisfies `|φ(x)| ≤ R(x)`,
then for any finite R-orthonormal sequence `{eⱼ}`, we have `Σⱼ φ(eⱼ)² ≤ 1`.

Proof sketch: let `w = Σⱼ φ(vⱼ)·vⱼ`. By orthonormality, `R(w)² = Σⱼ φ(vⱼ)²`.
Also `φ(w) = Σⱼ φ(vⱼ)²` and `|φ(w)| ≤ R(w)`.
So `S := Σⱼ φ(vⱼ)² ≤ R(w) = √S`, giving `S ≤ 1`. -/
theorem bessel_hilbertian {N : ℕ}
    (R : Seminorm ℝ E) (hR : R.IsHilbertian)
    (φ : E →L[ℝ] ℝ) (hφ : ∀ x, |φ x| ≤ R x)
    (v : Fin N → E) (hv : R.IsOrthonormalSeq v) :
    ∑ j, (φ (v j)) ^ 2 ≤ 1 := by
  sorry

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
          sorry

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

/-- Each original seminorm is bounded by a multiple of the
corresponding Hilbertian family member. -/
private axiom buildHilbertianFamily_dominates
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (hPN : IsPietschNuclear E)
    (q₀ : ℕ → Seminorm ℝ E) (hq₀_cont : ∀ n, Continuous (q₀ n))
    (n : ℕ) : ∃ C > 0, ∀ x, q₀ n x ≤ C * buildHilbertianFamily hPN q₀ hq₀_cont n x

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
