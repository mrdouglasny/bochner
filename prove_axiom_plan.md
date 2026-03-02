# Plan: Prove `nuclear_cylindrical_concentration`

## Goal

Eliminate the last custom axiom from `minlos_theorem`. Replace the `axiom` declaration
in `MinlosConcentration.lean` with a `theorem` + proof.

## The Axiom Statement

```lean
axiom nuclear_cylindrical_concentration
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_cont : Continuous Φ) (h_cf_joint : ...) (h_normalized : Φ 0 = 1)
    (d : ℕ → E) (p : ℕ → Seminorm ℝ E) (hp_top : WithSeminorms p)
    (hp_hilb : ∀ n, (p n).IsHilbertian)
    (hp_hs : ∀ n, (p (n + 1)).IsHilbertSchmidtEmbedding (p n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (m C : ℕ),
      ν {ω | ∃ c : ℕ →₀ ℚ,
        ¬ (|ω (c.sum fun i a => (a : ℝ) • d i)| ≤
          (C : ℝ) * (p m) (c.sum fun i a => (a : ℝ) • d i))} < ENNReal.ofReal ε
```

## Architecture

### File structure

```
Bochner/Minlos/
  CharFunZero.lean          -- NEW: ae_eq_zero_of_charfun_eq_one (extracted)
  MinlosConcentration.lean  -- REWRITE: theorem replacing axiom
  MeasurableModification.lean -- MODIFIED: import CharFunZero instead
```

### Avoiding circular imports

Extract `ae_eq_zero_of_charfun_eq_one` from MeasurableModification.lean into a new
foundational file `CharFunZero.lean`. Both MinlosConcentration and
MeasurableModification import it.

## Proof Strategy

### Key Insight: h_cf_joint bypass

We do NOT need ω to be linear. For any x = Σ βⱼ eⱼ in E (real coefficients), h_cf_joint
gives directly:

```
CF of (ω(x) - Σ βⱼ ω(eⱼ)) at t
  = ∫ exp(i·(t·ω(x) + Σ(-t·βⱼ)·ω(eⱼ))) dν
  = Φ(t·x - t·Σ βⱼ eⱼ)           [by h_cf_joint]
  = Φ(0) = 1                       [since x = Σ βⱼ eⱼ]
```

So ω(x) = Σ βⱼ ω(eⱼ) a.e., even with real βⱼ. Then Cauchy-Schwarz + Gaussian tail
bound on Σ ω(eⱼ)² gives the result.

### Trap 1: Gram-Schmidt on a Seminorm — The Quotient Trick

**Problem**: Mathlib's `GramSchmidt` and `OrthonormalBasis` require `[InnerProductSpace ℝ V]`
with strictly positive definite inner product (‖x‖ = 0 ↔ x = 0). A Hilbertian seminorm
p_{m₁} is only positive semidefinite, so Lean refuses to synthesize the instance.

**Solution**: For fixed N, work on the quotient W_N = ℝ^N / ker(⟨·,·⟩_{m₁}).

1. Equip ℝ^N with the pseudo-inner product ⟨u,v⟩ = p_{m₁}.innerProd(Σ uᵢ dᵢ, Σ vⱼ dⱼ).
2. Quotient by ker to get W_N with a strict inner product → genuine InnerProductSpace.
3. Use Mathlib's `stdOrthonormalBasis` on W_N.
4. Lift basis vectors back to ℝ^N via `Quotient.out`, map to E via Eⱼ = Σ (eⱼ)ᵢ dᵢ.
5. For c ∈ ℚ^N, its image in W_N decomposes as c = Σ βⱼ eⱼ + z where z ∈ ker.
6. Since z ∈ ker: p_{m₁}(Tz) = 0, hence p_{m₀}(Tz) = 0 (monotonicity), hence Φ(t·Tz) = 1,
   hence ω(Tz) = 0 a.e. The kernel residual is handled perfectly by h_cf_joint!

### Trap 2: Infinite ONB — Continuity from Below

**Problem**: Building a consistent infinite growing ONB and using MCT on expectations
requires ℝ → ENNReal conversion and is extremely tedious in Lean.

**Solution**: Use continuity of measure from below. No infinite ONB needed.

1. Define B_N = {ω | ∃ c : ℕ →₀ ℚ with supp ⊆ {0,...,N-1}, |ω(x_c)| > R · p_{m₁}(x_c)}.
2. For each finite N, use the quotient-trick ONB to prove ν(B_N) ≤ δ.
3. The bound δ = (ε/4 + 2σ²C_HS) / (1 - exp(-σ²R²/2)) depends only on C_HS and R,
   NOT on N or the specific ONB. Uniform in N!
4. B_N ⊆ B_{N+1} (monotone increasing).
5. The full bad set = ⋃_N B_N (any finitely-supported c has support ⊆ some {0,...,N-1}).
6. By `measure_iUnion_eq_iSup`: ν(⋃ B_N) = lim ν(B_N) ≤ δ.

No MCT on integrals, no ENNReal gymnastics, no infinite sequences of ONB vectors.
The ONB for N+1 does NOT need to extend the ONB for N!

## Proof Outline (Revised)

### Step 1: Extract parameters
- From `cf_nhds_ball`: get s₀, r₀ with (s₀.sup p)(x) < r₀ ⟹ ‖1-Φ(x)‖ < ε/4.
- Choose m₀ ≥ max(s₀) so p_{m₀} ≥ s₀.sup p (by `finset_sup_le_of_mono`).
- Set m₁ = m₀ + 1. Get C_HS from hp_hs m₀.
- Choose σ, R so that (ε/4 + 2σ²C_HS) / (1 - exp(-σ²R²/2)) < ε
  (from `exists_R_for_tail_bound`).
- Set C = ⌈R⌉, m = m₁.

### Step 2: For each N, build finite ONB via quotient trick
- Define pseudo-inner product on ℝ^N from p_{m₁}.
- Quotient by kernel → InnerProductSpace W_N.
- `stdOrthonormalBasis` on W_N → lift to E₁,...,Eₖ ∈ E (with k ≤ N).
- These are p_{m₁}-orthonormal by construction.

### Step 3: For each N, prove ν(B_N) ≤ δ
**Step 3a**: Push ν to ℝ^k via ω ↦ (ω(E₁),...,ω(Eₖ)).
  CF = v ↦ Φ(Σ vⱼ Eⱼ) by h_cf_joint.

**Step 3b**: Apply `gaussian_averaging_bound` on EuclideanSpace ℝ (Fin k).
  - Positive operator S: the identity (since Eⱼ are p_{m₁}-orthonormal,
    the relevant operator is diagonal with entries p_{m₀}(Eⱼ)²).
  - Actually: need S such that quadForm S v < 1 ⟹ ‖1-Φ(Σ vⱼ Eⱼ)‖ < ε/4.
    Use S = (1/r₀²) · G where Gᵢⱼ = p_{m₀}.innerProd(Eᵢ, Eⱼ).
  - Trace of S ≤ (1/r₀²) · Σⱼ p_{m₀}(Eⱼ)² ≤ (1/r₀²) · C_HS (HS bound!).

**Step 3c**: Chebyshev: P(Σ ω(Eⱼ)² ≥ R²) ≤ δ.

**Step 3d**: For each c with supp ⊆ {0,...,N-1}:
  - Map c to W_N, decompose: image(c) = Σ βⱼ bⱼ (ONB decomposition in W_N).
  - Lift: x_c = Σ βⱼ Eⱼ + Tz where z ∈ ker.
  - h_cf_joint: ω(x_c) = Σ βⱼ ω(Eⱼ) + ω(Tz) a.e.
  - h_cf_joint: ω(Tz) = 0 a.e. (since p_{m₁}(Tz) = 0 ⟹ Φ(t·Tz) = 1).
  - So ω(x_c) = Σ βⱼ ω(Eⱼ) a.e.
  - Cauchy-Schwarz: |ω(x_c)| = |Σ βⱼ ω(Eⱼ)| ≤ (Σ βⱼ²)^{1/2} · (Σ ω(Eⱼ)²)^{1/2}.
  - Parseval (in W_N): Σ βⱼ² = p_{m₁}(x_c)².
  - On good event: |ω(x_c)| ≤ p_{m₁}(x_c) · R ≤ C · p_{m₁}(x_c).

**Step 3e**: Countable intersection over all c with supp ⊆ {0,...,N-1}: still a.e.
  So ν(B_N) ≤ δ.

### Step 4: Continuity from below
- B_N ↑ ⋃ B_N = {ω | ∃ c, |ω(x_c)| > C · p_{m₁}(x_c)}.
- `measure_iUnion_eq_iSup`: ν(⋃ B_N) = sup ν(B_N) ≤ δ < ε.
- Done!

## Lemma Roadmap

| # | Lemma | Difficulty | Strategy |
|---|-------|-----------|----------|
| L1 | `combined_quadratic_bound` | Easy | linarith from cf_nhds_ball + quadratic_bound_outside |
| L2 | `finite_onb_lift` | Easy | Quotient ℝ^N/ker, stdOrthonormalBasis, Quotient.out |
| L3 | `parseval_seminorm` | Easy | Native Parseval on the IPS quotient |
| L4 | `decomposition_ae` | Medium | h_cf_joint on x_c, Eⱼ, and kernel residual Tz |
| L5 | `marginal_cf_onb` | Easy | Standard h_cf_joint application on lifts Eⱼ |
| L6 | `gaussian_avg_onb_bound` | Medium | Pushforward ω ↦ (ω(E₁),...) to EuclideanSpace, apply existing gaussian_averaging_bound. Trace bounded by C_HS natively |
| L7 | `measure_iUnion_bound` | Easy | measure_iUnion_eq_iSup on nested B_N. No integrals, no ENNReal, no infinite limits |
| L8 | `concentration_assembly` | Medium | Combine all pieces |

## Key Risks

1. **Quotient construction in Lean**: Building `InnerProductSpace ℝ (ℝ^N / ker)` from
   a positive semidefinite bilinear form. Mathlib has `Submodule.Quotient` and
   `InnerProductSpace` but connecting them may require manual work.

2. **Pushforward measure + CF verification**: Constructing `ProbabilityMeasure (EuclideanSpace ℝ (Fin k))`
   from ν and verifying its charFun matches marginalFun. Type coercions between
   `EuclideanSpace ℝ (Fin k)` and `Fin k → ℝ` can be painful.

3. **Operator S construction**: Building a `ContinuousLinearMap` on EuclideanSpace
   from the p_{m₀}-Gram matrix and proving it's positive with the right trace bound.

## Estimated Size

~400-600 lines across:
- `CharFunZero.lean`: ~80 lines (extract from MeasurableModification)
- `MinlosConcentration.lean`: ~400-500 lines (existing helpers + new proof)
