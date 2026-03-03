# `PietschBridge.lean` — Informal Summary

> **Source**: [`Bochner/Minlos/PietschBridge.lean`](../../Bochner/Minlos/PietschBridge.lean)
> **Generated**: 2026-03-03

## Overview

This file proves the **main bridge theorem**: a locally convex space satisfying Pietsch's nuclear dominance condition is a `IsHilbertNuclear` in the Hilbertian-seminorm sense (Hilbert-Schmidt embeddings between consecutive Hilbertian seminorms).

The proof uses **double Pietsch construction** to bootstrap a single Pietsch nuclear factorization into a Hilbertian lift, then recursively builds a family of Hilbertian seminorms with Hilbert-Schmidt embeddings by repeatedly applying this double construction. Key techniques include Cauchy–Schwarz inequalities, Bessel inequality for bounded functionals on Hilbertian seminorms, and the parallelogram law.

## Status

**Main result**: Fully proven (0 sorries)
**Length**: 811 lines, 18 def(s) + 27 theorem(s)/lemma(s)

---

## Definitions

### `IsNuclear`

**Definition** (lines 45–52):
```lean
def IsNuclear (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] : Prop :=
  ∀ (p : Seminorm ℝ E), Continuous p →
    ∃ (q : Seminorm ℝ E), Continuous q ∧ (∀ x, p x ≤ q x) ∧
    ∃ (f : ℕ → (E →L[ℝ] ℝ)) (c : ℕ → ℝ),
      (∀ n, 0 ≤ c n) ∧ Summable c ∧
      (∀ n x, |f n x| ≤ q x) ∧
      (∀ x, p x ≤ ∑' n, |f n x| * c n)
```

A locally convex TVS is **Pietsch nuclear** if for every continuous seminorm $p$, there exist a continuous seminorm $q \geq p$, continuous linear functionals $f_n$, and non-negative coefficients $c_n \in \ell^1$ such that $|f_n(x)| \leq q(x)$ and $p(x) \leq \sum_n |f_n(x)| \cdot c_n$.

### `hilbertianLift`

**Definition** (lines 86–167):
```lean
def hilbertianLift (f : ℕ → (E →L[ℝ] ℝ)) (c : ℕ → ℝ)
    (hc_nn : ∀ n, 0 ≤ c n) (hc_sum : Summable c)
    (q : Seminorm ℝ E) (hfq : ∀ n x, |f n x| ≤ q x) : Seminorm ℝ E
```

The **Hilbertian lift** of a nuclear expansion: $r(x) = \sqrt{\sum_n f_n(x)^2 \cdot c_n}$. This seminorm satisfies the parallelogram law and dominates the original seminorm via Cauchy–Schwarz.

### `buildHilbertianBundle`

**Definition** (lines 634–646):
```lean
noncomputable def buildHilbertianBundle
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (hPN : IsNuclear E)
    (q₀ : ℕ → Seminorm ℝ E) (hq₀_cont : ∀ n, Continuous (q₀ n)) :
    (n : ℕ) → { r : Seminorm ℝ E // Continuous r }
```

Bundled recursive construction carrying continuity for the next step in the Hilbertian family building process.

### `buildHilbertianFamily`

**Definition** (lines 649–654):
```lean
noncomputable def buildHilbertianFamily
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (hPN : IsNuclear E)
    (q₀ : ℕ → Seminorm ℝ E) (hq₀_cont : ∀ n, Continuous (q₀ n)) :
    ℕ → Seminorm ℝ E
```

The recursive family of Hilbertian seminorms extracting the underlying value from the bundle.

### `buildInput`

**Definition** (lines 657–662):
```lean
noncomputable abbrev buildInput
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (hPN : IsNuclear E)
    (q₀ : ℕ → Seminorm ℝ E) (hq₀_cont : ∀ n, Continuous (q₀ n))
    (n : ℕ) : Seminorm ℝ E :=
  buildHilbertianFamily hPN q₀ hq₀_cont n ⊔ q₀ (n + 1)
```

Helper abbreviation: the supremum of the previous Hilbertian family member and the next original seminorm, used as input to the next double Pietsch step.

---

## Lemmas and Theorems

### `summable_sq_mul_of_bounded`

**Lemma** (lines 58–72): Summability of the weighted square series $\sum_n f_n(x)^2 \cdot c_n < \infty$.

Uses the bound $|f_n(x)| \leq q(x)$ to dominate by $q(x)^2 \cdot \sum c_n$.
Proof uses: `Summable.of_nonneg_of_le`

### `tsum_sq_mul_nonneg`

**Lemma** (lines 75–78): Nonnegativity of the weighted square series $\sum' n, (f_n x)^2 \cdot c_n \geq 0$.

Proof uses: `tsum_nonneg`

### `hilbertianLift_apply`

**Theorem** (lines 170–174): The Hilbertian lift evaluates as $r(x) = \sqrt{\sum_k f_k(x)^2 \cdot c_k}$.

Proof uses: reflexivity (definitional)

### `hilbertianLift_isHilbertian`

**Theorem** (lines 180–199): The Hilbertian lift satisfies the parallelogram law: $r(x+y)^2 + r(x-y)^2 = 2(r(x)^2 + r(y)^2)$.

For each $n$: $(f_n(x+y))^2 + (f_n(x-y))^2 = 2(f_n(x)^2 + f_n(y)^2)$ (using linearity of $f_n$), then sum and take $\sqrt{}$.
Proof uses: `Real.sq_sqrt`, `map_add`, `map_sub`

### `hilbertianLift_dominates`

**Theorem** (lines 203–237): Cauchy–Schwarz bound: the nuclear expansion is bounded by $\sqrt{\sum c_k} \cdot r(x)$.

$\sum_k |f_k(x)| \cdot c_k \leq \sqrt{\sum_k f_k(x)^2 \cdot c_k} \cdot \sqrt{\sum_k c_k} = \sqrt{\sum c_k} \cdot r(x)$
Proof uses: `Real.tsum_le_of_sum_le`, `Real.sum_mul_le_sqrt_mul_sqrt`, `Finset.sum_le_sum`

### `hilbertianLift_le_dominator`

**Theorem** (lines 241–267): Functionals bounded by a dominating seminorm $q$ are also bounded by the Hilbertian lift: $r(x) \leq \sqrt{\sum c_k} \cdot q(x)$.

Proof uses: `Real.sqrt_le_sqrt`, `tsum_mul_left`, `Real.sqrt_mul`, `Real.sqrt_sq`

### `Seminorm.innerProd_self`

**Lemma** (lines 274–278): Jordan–von Neumann polarization identity: $\text{ip}(x, x) = r(x)^2$.

Where $\text{ip}(x, y) = \frac{1}{4}(r(x+y)^2 - r(x-y)^2)$.
Proof uses: `map_zero`, `map_smul_eq_mul`

### `Seminorm.innerProd_comm`

**Lemma** (lines 281–287): Symmetry of the polarization inner product: $\text{ip}(x, y) = \text{ip}(y, x)$.

Proof uses: `R_congr'`, `map_neg_eq_map`

### `Seminorm.innerProd_neg_left`

**Lemma** (lines 290–297): $\text{ip}(-x, y) = -\text{ip}(x, y)$.

Proof uses: `map_neg_eq_map`

### `Seminorm.innerProd_add_left`

**Lemma** (lines 303–316): Additivity in the first argument: $\text{ip}(x_1 + x_2, y) = \text{ip}(x_1, y) + \text{ip}(x_2, y)$ (from the parallelogram law).

Uses four applications of the parallelogram identity with different argument pairs, then combines by linear arithmetic.
Proof uses: `R_congr'`, `map_neg_eq_map`

### `Seminorm.innerProd_sum_left`

**Lemma** (lines 319–324): Finite sum in first argument: $\text{ip}(\sum_j x_j, y) = \sum_j \text{ip}(x_j, y)$.

Proof uses: `Finset.cons_induction`, `innerProd_add_left`, `map_neg_eq_map`

### `Seminorm.continuous_smul_add`

**Lemma** (lines 327–345): Continuity of $t \mapsto r(t \cdot x + y)$ as a function $\mathbb{R} \to \mathbb{R}$ (Lipschitz with constant $r(x)$).

Proof uses: `Metric.continuous_iff`, `Real.dist_eq`, `abs_sub_map_le_sub`, `map_smul_eq_mul`

### `Seminorm.innerProd_smul_left`

**Lemma** (lines 352–366): Real homogeneity: $\text{ip}(a \cdot x, y) = a \cdot \text{ip}(x, y)$.

The function $t \mapsto \text{ip}(t \cdot x, y)$ is additive (from `innerProd_add_left`) and continuous (since $r$ is Lipschitz). A continuous additive function $\mathbb{R} \to \mathbb{R}$ is $\mathbb{R}$-linear by `map_real_smul`.
Proof uses: `Continuous`, `innerProd_add_left`, `map_real_smul`, `continuous_smul_add`

### `Seminorm.sq_add_of_innerProd_eq_zero`

**Lemma** (lines 371–376): Pythagorean theorem: if $\text{ip}(x, y) = 0$ then $r(x+y)^2 = r(x)^2 + r(y)^2$.

Proof uses: `innerProd` definition

### `R_orthonormal_norm`

**Lemma** (lines 379–382): $r(v_j) = 1$ for an $r$-orthonormal sequence.

Proof uses: `innerProd_self`

### `Seminorm.sq_sum_orthonormal`

**Lemma** (lines 385–412): Pythagoras for orthonormal sums: $r(\sum_j a_j \cdot v_j)^2 = \sum_j a_j^2$ for $r$-orthonormal $\{v_j\}$.

Proved by induction using the Pythagorean theorem.
Proof uses: `Fin.sum_univ_castSucc`, `sq_add_of_innerProd_eq_zero`, `innerProd_sum_left`, `innerProd_smul_left`, `innerProd_comm`, `map_smul_eq_mul`, `Fin.castSucc_ne_last`

### `bessel_hilbertian`

**Theorem** (lines 422–435): **Bessel inequality** for bounded functionals on Hilbertian seminorms.

If $r$ is a Hilbertian seminorm and $\varphi : E \to_L[\mathbb{R}] \mathbb{R}$ satisfies $|\varphi(x)| \leq r(x)$, then for any finite $r$-orthonormal sequence $\{e_j\}$: $\sum_j \varphi(e_j)^2 \leq 1$.

Let $w = \sum_j \varphi(v_j) \cdot v_j$. By orthonormality $r(w)^2 = \sum_j \varphi(v_j)^2$; by linearity $\varphi(w) = \sum_j \varphi(v_j)^2$; and $|\varphi(w)| \leq r(w)$. So $S \leq r(w) = \sqrt{S}$, giving $S \leq 1$.
Proof uses: `sq_sum_orthonormal`, `map_sum`, `map_smul`, `le_abs_self`, `sq_nonneg`

### `isHilbertSchmidtEmbedding_of_nuclear`

**Theorem** (lines 448–525): If $r$ is Hilbertian and $p(x) \leq \sum_k |f_k(x)| \cdot c_k$ where each $f_k$ is bounded by $r$, then the inclusion $\hat{E}_r \to \hat{E}_p$ is Hilbert–Schmidt.

For any finite $r$-orthonormal sequence $\{e_j\}$:
$$\sum_j p(e_j)^2 \leq \sum_j (\sum_k |f_k(e_j)| \cdot c_k)^2 \leq (\sum_k c_k)^2$$
(via Cauchy–Schwarz + Bessel: $\sum_j |f_k(e_j)|^2 \leq 1$).

Proof uses: `pow_le_pow_left₀`, `Finset.sum_le_sum`, `hilbertianLift_dominates`, `bessel_hilbertian`, `Summable.tsum_finsetSum`, `mul_le_mul_of_nonneg_left`, `sq`

### `nuclear_le_sumC_mul_Q`

**Lemma** (lines 530–539): Bound a nuclear sum by $(\sum c_k) \cdot q(x)$ when each functional is dominated by $q$.

Proof uses: `Summable.of_nonneg_of_le`, `tsum_mul_left`

### `hilbertian_smul`

**Lemma** (lines 542–551): Scaling a Hilbertian seminorm by $K : \mathbb{R}_{\geq 0}$ preserves the parallelogram law.

Proof uses: `IsHilbertian` definition, `mul_pow`, `add_mul`

### `doublePietsch_step`

**Lemma** (lines 559–624): **Double Pietsch step**: Apply `IsNuclear` twice to produce a Hilbertian seminorm $r \geq p$ with a nuclear expansion whose functionals are bounded by $r$.

A single Pietsch application gives $|f_k| \leq q$ but we need $|f_k| \leq r$ for the Hilbertian lift. Applying Pietsch twice and scaling by $K = \max(\sum c_k, 1) \cdot \sqrt{\sum d_k}$ achieves both $p \leq r$ and $|f_k| \leq r$.

Proof uses: `hilbertianLift`, `hilbertianLift_isHilbertian`, `le_trans`, `hilbertianLift_dominates`, `hilbertianLift_le_dominator`, `Seminorm.continuous_of_le`, `continuous_const.mul`, `mul_nonneg`, `le_max_left`, `le_max_right`, `mul_le_mul_of_nonneg_left`, `mul_le_mul_of_nonneg_right`

### `seminorm_continuous_sup`

**Theorem** (lines 627–631): Continuity of the sup of two continuous seminorms.

Proof uses: `Seminorm.sup_apply`, `Continuous.sup`

### `buildInput_continuous`

**Theorem** (lines 664–669): Continuity of the `buildInput` at step $n$.

Proof uses: `seminorm_continuous_sup`, `buildHilbertianBundle.property`

### `buildHilbertianFamily_isHilbertian`

**Theorem** (lines 672–681): Each family member $r(n)$ is Hilbertian.

Proof uses: `doublePietsch_step.choose_spec`, `buildInput_continuous`

### `buildHilbertianFamily_continuous`

**Theorem** (lines 684–689): Each family member $r(n)$ is continuous.

Proof uses: `buildHilbertianBundle.property`

### `buildFamily_stepSucc_spec`

**Theorem** (lines 692–705): Extract the `doublePietsch_step` specification at step $n+1$.

Returns continuity, Hilbertian property, dominance, and nuclear factorization data for $r(n+1)$ over input $p(n) = r(n) \sqcup q_0(n+1)$.

Proof uses: `doublePietsch_step.choose_spec`

### `buildHilbertianFamily_dominates_q₀`

**Theorem** (lines 708–720): Pointwise dominance: $q_0(n) \leq r(n)$.

Proof uses: `doublePietsch_step.choose_spec`, `buildFamily_stepSucc_spec`, `le_max_right`, `le_trans`, `Seminorm.sup_apply`

### `buildHilbertianFamily_monotone`

**Theorem** (lines 723–734): Monotonicity: $r(n) \leq r(n+1)$ pointwise (previous level is dominated by next).

Proof uses: `le_max_left`, `le_trans`, `buildFamily_stepSucc_spec`, `Seminorm.sup_apply`

### `buildHilbertianFamily_hs`

**Theorem** (lines 737–758): Consecutive family members have Hilbert–Schmidt embeddings: $r(n+1) \overset{\text{HS}}{\to} r(n)$.

Proof uses: `buildFamily_stepSucc_spec`, `isHilbertSchmidtEmbedding_of_nuclear`, `buildHilbertianFamily_monotone`

### `buildHilbertianFamily_withSeminorms`

**Theorem** (lines 764–782): The Hilbertian family generates the same topology as $q_0$.

Uses `WithSeminorms.congr`: the two families are mutually bounded because $q_0(n) \leq r(n)$ and each $r(n)$ is continuous in the $q_0$-topology.

Proof uses: `WithSeminorms.congr`, `Seminorm.bound_of_continuous`, `buildHilbertianFamily_continuous`, `buildHilbertianFamily_dominates_q₀`, `Finset.sup_singleton`, `Seminorm.sup_apply`, `le_max_right`

### `isHilbertNuclear_of_nuclear`

**Theorem** (lines 794–808): **Pietsch nuclearity implies IsHilbertNuclear.**

A locally convex space satisfying Pietsch's nuclear dominance condition (every continuous seminorm is dominated by a nuclear expansion) is an `IsHilbertNuclear` in the Hilbertian-seminorm sense (Hilbert-Schmidt embeddings between consecutive levels).

The proof constructs a recursive family of Hilbertian seminorms from the Pietsch factorizations and shows they have Hilbert–Schmidt embeddings.

Proof uses: `buildHilbertianFamily_isHilbertian`, `buildHilbertianFamily_withSeminorms`, `buildHilbertianFamily_hs`

---

*This file has **5** definitions and **27** theorems/lemmas.*
