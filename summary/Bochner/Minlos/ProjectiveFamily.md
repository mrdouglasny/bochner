# `ProjectiveFamily.lean` — Informal Summary

> **Source**: [`Bochner/Minlos/ProjectiveFamily.lean`](../../../Bochner/Minlos/ProjectiveFamily.lean)
> **Generated**: 2026-03-03

## Overview

This file bridges finite-dimensional Bochner marginals (measures on `EuclideanSpace ℝ (Fin n)`) to the `IsProjectiveMeasureFamily` API from Mathlib, enabling application of the Kolmogorov extension theorem. The key result is that the family of marginal measures indexed by finsets is projective (consistent under coordinate restriction), with characteristic functions determined by a fixed positive-definite function Φ. The file constructs a projective limit measure on the full space `E → ℝ` from these marginals.

## Status

**Main result**: Fully proven
**Length**: 262 lines, 3 def(s) + 6 theorem(s)/lemma(s)

---

### Transport Equivalence

#### [finsetReindexEquiv](../../../Bochner/Minlos/ProjectiveFamily.lean#L30)

**Signature**: `finsetReindexEquiv (J : Finset E) : (↥J → ℝ) ≃ᵐ (Fin J.card → ℝ)`

Measurable equivalence between `∀ j : J, ℝ` and `Fin |J| → ℝ` via reindexing with `J.equivFin`.

#### [finsetPiMeasEquiv](../../../Bochner/Minlos/ProjectiveFamily.lean#L42)

**Signature**: `finsetPiMeasEquiv (J : Finset E) : (↥J → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin J.card)`

Measurable equivalence between `∀ j : J, ℝ` and `EuclideanSpace ℝ (Fin |J|)` via composition of reindexing and the `WithLp` transport to PiLp structures.

### Marginal Family

#### [finsetTestVectors](../../../Bochner/Minlos/ProjectiveFamily.lean#L49)

**Signature**: `finsetTestVectors (J : Finset E) : Fin J.card → E`

The test vectors for a finset `J`, selecting from `J` in order via `J.equivFin.symm`.

#### [marginalMeasure](../../../Bochner/Minlos/ProjectiveFamily.lean#L53)

**Signature**: `marginalMeasure (Φ : E → ℂ) (hΦ_cont : Continuous Φ) (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1) (J : Finset E) : ProbabilityMeasure (EuclideanSpace ℝ (Fin J.card))`

The unique Bochner marginal measure on `EuclideanSpace ℝ (Fin |J|)` for test vectors from finset `J`, obtained by applying the existence theorem from `FinDimMarginals` and extracting the witness.

#### [marginalMeasure_charFun](../../../Bochner/Minlos/ProjectiveFamily.lean#L58)

**Theorem**: For each test vector finset $J \subseteq E$ and spatial frequency $\xi$ on the finite-dimensional space, the characteristic function of the marginal measure equals $\Phi$ applied to the linear combination $\sum_{j \in J} \xi_j \cdot v_j$ where $v_j$ are the test vectors.

**Proof uses**: `marginal_measure_exists`, characteristic function definition.

#### [marginalFamily](../../../Bochner/Minlos/ProjectiveFamily.lean#L67)

**Signature**: `marginalFamily (Φ : E → ℂ) (hΦ_cont : Continuous Φ) (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1) : ∀ J : Finset E, Measure (∀ j : ↥J, (fun (_ : E) => ℝ) ↑j)`

The projective family of probability measures indexed by `Finset E`. For each `J`, we take the Bochner marginal on `EuclideanSpace ℝ (Fin |J|)` and transport it to the Pi-type `∀ j : J, ℝ` via `finsetPiMeasEquiv`.

#### [marginalFamily_isFiniteMeasure](../../../Bochner/Minlos/ProjectiveFamily.lean#L73)

**Instance**: The marginal family carries a finite measure instance on each `J` via pushforward of the finite Bochner marginal.

#### [marginalFamily_isProbabilityMeasure](../../../Bochner/Minlos/ProjectiveFamily.lean#L78)

**Instance**: Each marginal in the family is a probability measure (weight 1) by preservation under measurable pushforward.

### Projectivity

#### [marginalFamily_isProjective](../../../Bochner/Minlos/ProjectiveFamily.lean#L136)

**Theorem**: For $J \subseteq I$, the restriction of the marginal measure on $I$ to $J$-coordinates (via `Finset.restrict₂`) equals the marginal measure on $J$. In other words, $\pi_J^\#(P_I) = P_J$.

**Proof uses**:
- Characteristic function uniqueness (`Measure.ext_of_charFun`)
- Zero-extension of test frequencies to handle coordinate mismatch
- Inner product identity relating EuclideanSpace projection to Pi-type restriction
- Test vector compatibility under index injection
- Finset summation manipulation with zero-dropping

The key insight is proving the inner product identity $\langle \text{euclideanProject}(y), \xi \rangle = \langle y, \xi_{\text{ext}} \rangle$ where $\xi_{\text{ext}}$ zero-extends frequencies outside $J$.

### Application of Kolmogorov Extension

#### [marginalProjectiveLimit](../../../Bochner/Minlos/ProjectiveFamily.lean#L232)

**Signature**: `marginalProjectiveLimit (Φ : E → ℂ) (hΦ_cont : Continuous Φ) (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1) [Nonempty E] : Measure (E → ℝ)`

The Kolmogorov projective limit of the marginal family, a measure on the full space `E → ℝ` constructed via the Kolmogorov extension theorem applied to the projective family.

#### [marginalProjectiveLimit_isProbability](../../../Bochner/Minlos/ProjectiveFamily.lean#L239)

**Instance**: The projective limit is a probability measure, following from general projectivity of probability measures under Kolmogorov extension.

#### [marginalProjectiveLimit_isProjectiveLimit](../../../Bochner/Minlos/ProjectiveFamily.lean#L247)

**Theorem**: The projective limit satisfies the universal property: it projects correctly onto each finite-dimensional marginal, i.e., $\pi_J^\#(\mu_{\text{limit}}) = P_J$.

**Proof uses**: `isProjectiveLimit_projectiveLimit` from Kolmogorov extension API.

#### [marginalProjectiveLimit_unique](../../../Bochner/Minlos/ProjectiveFamily.lean#L255)

**Theorem**: If a measure $\nu$ on `E → ℝ` satisfies the projective limit property, then $\nu = \mu_{\text{limit}}$ (uniqueness of the Kolmogorov extension).

**Proof uses**: Uniqueness clause from the Kolmogorov extension API applied to `marginalProjectiveLimit_isProjectiveLimit`.

---

*This file has **3** definitions and **6** theorems/lemmas.*
