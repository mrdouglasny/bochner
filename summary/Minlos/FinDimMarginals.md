# `FinDimMarginals.lean` — Informal Summary

> **Source**: [`Minlos/FinDimMarginals.lean`](../../../Minlos/FinDimMarginals.lean)
> **Generated**: 2026-03-03

## Overview

For a continuous positive-definite normalized functional $\Phi : E \to \mathbb{C}$ on a TVS, this file constructs finite-dimensional marginal measures via Bochner's theorem. Given test vectors $f_1, \ldots, f_n \in E$, the marginal characteristic function $\Phi_F(t) = \Phi\left(\sum t_i f_i\right)$ is continuous and PD on $\mathbb{R}^n$, so Bochner gives a unique probability measure $\mu_F$ on $\mathbb{R}^n$. This is the core step connecting the infinite-dimensional Minlos problem to the finite-dimensional Bochner theorem.

## Status

**Main result**: Fully proven
**Length**: 97 lines, 1 def + 4 theorems/lemmas

---

### [marginalCF](../../../Minlos/FinDimMarginals.lean#L36)

```lean
def marginalCF {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Φ : E → ℂ) {n : ℕ} (f : Fin n → E) :
    EuclideanSpace ℝ (Fin n) → ℂ
```

The finite-dimensional marginal CF: $\Phi_F(t) = \Phi\left(\sum_{i} t_i \cdot f_i\right)$, defined on `EuclideanSpace ℝ (Fin n)` so that Bochner's theorem applies.

### [marginalCF_continuous](../../../Minlos/FinDimMarginals.lean#L46)

```lean
theorem marginalCF_continuous {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (Φ : E → ℂ) {n : ℕ} (f : Fin n → E)
    (hΦ : Continuous Φ) : Continuous (marginalCF Φ f)
```

The marginal CF is continuous. Proof uses: finite sum of continuous scalar multiplications, composed with continuous $\Phi$.

### [marginalCF_pd](../../../Minlos/FinDimMarginals.lean#L68)

```lean
theorem marginalCF_pd {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Φ : E → ℂ) {n : ℕ} (f : Fin n → E)
    (hPD : IsPositiveDefinite Φ) : IsPositiveDefinite (marginalCF Φ f)
```

The marginal CF is positive definite. Proof uses: [`isPositiveDefinite_precomp_linear`](../../../Minlos/FinDimMarginals.lean#L71) — if $\Phi$ is PD and $T : V \to E$ is linear, then $\Phi \circ T$ is PD.

### [marginalCF_normalized](../../../Minlos/FinDimMarginals.lean#L74)

```lean
theorem marginalCF_normalized {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Φ : E → ℂ) {n : ℕ} (f : Fin n → E)
    (h_norm : Φ 0 = 1) : marginalCF Φ f 0 = 1
```

The marginal CF is normalized: $\Phi_F(0) = \Phi(0) = 1$.

### [marginal_measure_exists](../../../Minlos/FinDimMarginals.lean#L84)

```lean
theorem marginal_measure_exists {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (Φ : E → ℂ) {n : ℕ} (f : Fin n → E)
    (hΦ_cont : Continuous Φ) (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1) :
    ∃! μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
      ∀ ξ, charFun (μ : Measure (EuclideanSpace ℝ (Fin n))) ξ =
        marginalCF Φ f ξ
```

For each finite set of test vectors, Bochner's theorem gives a unique probability measure on $\mathbb{R}^n$ whose characteristic function equals the marginal CF. Proof uses: [`bochner_theorem`](../../../Minlos/FinDimMarginals.lean#L91) applied to `marginalCF_continuous`, `marginalCF_pd`, and `marginalCF_normalized`.

---

*This file has **1** definition and **4** theorems/lemmas.*
