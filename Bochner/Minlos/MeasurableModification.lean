/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Measurable Modification for Minlos' Theorem

Replaces the false axioms `nuclear_support_concentration` and
`weakDual_measurableEmbedding` with a measurable **pushforward** construction.

The key idea: instead of pulling back ν (a measure on E → ℝ) through the
embedding E' ↪ (E → ℝ), we push forward ν through a measurable projection
P : (E → ℝ) → WeakDual ℝ E that agrees with the identity on "good paths"
(ω that are ℚ-linear and bounded on a countable dense subset).

## Main definitions

- `qLinearPaths` — set of ω that are ℚ-linear on the dense sequence (Finsupp version)
- `boundedPaths` — set of ω bounded by a NuclearSpace seminorm (Finsupp version)
- `goodPaths` — intersection (measurable, full measure under ν)
- `measurableProjection` — P : (E → ℝ) → WeakDual ℝ E
- `weakDualEmbed` — the embedding WeakDual ℝ E → (E → ℝ)

## Axioms (6 textbook results)

1. `extensionCLM` — BLT: construct ContinuousLinearMap from good path
2. `extensionCLM_eq_on_dense` — extension agrees with ω on dense sequence
3. `measurable_measurableProjection` — P is measurable
4. `qLinearPaths_ae` — ℚ-linearity a.e. (joint CF → X = 0 a.s.)
5. `boundedPaths_ae` — boundedness a.e. (Markov + CF continuity)
6. `projection_ae_eq` — P(ω)(f) = ω(f) ν-a.e.

## References

- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. IV, §3.3
- Minlos, "Generalized random processes and their extension to measures" (1959)
-/

import Bochner.Minlos.ProjectiveFamily
import Mathlib.Topology.Bases
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Encodable

open BigOperators MeasureTheory Complex TopologicalSpace Classical Finsupp

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-! ## Embedding: WeakDual ℝ E → (E → ℝ) -/

/-- The evaluation embedding sending a continuous linear functional to its
    underlying function. This is measurable (but NOT a MeasurableEmbedding
    when E is uncountable-dimensional). -/
def weakDualEmbed (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] :
    WeakDual ℝ E → (E → ℝ) :=
  fun l f => (l : E →L[ℝ] ℝ) f

lemma weakDualEmbed_apply (l : WeakDual ℝ E) (f : E) :
    weakDualEmbed E l f = l f := rfl

lemma weakDualEmbed_injective : Function.Injective (weakDualEmbed E) := by
  intro l₁ l₂ h
  have : ∀ f, (l₁ : E →L[ℝ] ℝ) f = (l₂ : E →L[ℝ] ℝ) f := congr_fun h
  exact ContinuousLinearMap.ext this

/-- The embedding is measurable: each coordinate l ↦ l(f) is continuous
    in the weak-* topology, hence measurable. -/
lemma measurable_weakDualEmbed : Measurable (weakDualEmbed E) := by
  apply measurable_pi_lambda
  intro f
  exact (WeakDual.eval_continuous f).measurable

/-! ## Good Paths (Finsupp version) -/

/-- The set of "ℚ-linear paths" on a sequence d : ℕ → E.
    ω respects all finite ℚ-linear combinations:
    ω(∑ cᵢ • d(i)) = ∑ cᵢ * ω(d(i)) for every c : ℕ →₀ ℚ.

    This is a countable intersection (ℕ →₀ ℚ is countable) of measurable sets. -/
def qLinearPaths (d : ℕ → E) : Set (E → ℝ) :=
  ⋂ (c : ℕ →₀ ℚ),
    { ω | ω (c.sum fun i a => (a : ℝ) • d i) =
      c.sum fun i a => (a : ℝ) * ω (d i) }

lemma qLinearPaths_measurableSet (d : ℕ → E) :
    MeasurableSet (qLinearPaths d) := by
  apply MeasurableSet.iInter; intro c
  apply measurableSet_eq_fun
  · exact measurable_pi_apply _
  · simp only [Finsupp.sum]
    apply Finset.measurable_sum
    intro i _
    exact (measurable_pi_apply (d i)).const_mul _

/-- The set of "bounded paths" on a sequence d : ℕ → E with respect to
    seminorms p : ℕ → Seminorm ℝ E.
    ω is bounded on all finite ℚ-linear combinations:
    ∃ s : Finset ℕ, ∃ C : ℕ, ∀ c : ℕ →₀ ℚ,
    |ω(∑ cᵢ • d(i))| ≤ C * (s.sup p)(∑ cᵢ • d(i)).

    Combined with ℚ-linearity, this gives uniform continuity of ω on
    the ℚ-span of range(d).

    This is measurable (countable ⋃/⋂ over ℕ × ℕ × (ℕ →₀ ℚ)). -/
def boundedPaths (d : ℕ → E) (p : ℕ → Seminorm ℝ E) : Set (E → ℝ) :=
  ⋃ (s : Finset ℕ) (C : ℕ), ⋂ (c : ℕ →₀ ℚ),
    { ω | |ω (c.sum fun i a => (a : ℝ) • d i)| ≤
        (C : ℝ) * (s.sup p) (c.sum fun i a => (a : ℝ) • d i) }

lemma boundedPaths_measurableSet (d : ℕ → E) (p : ℕ → Seminorm ℝ E) :
    MeasurableSet (boundedPaths d p) := by
  apply MeasurableSet.iUnion; intro s
  apply MeasurableSet.iUnion; intro C
  apply MeasurableSet.iInter; intro c
  exact measurableSet_le
    ((measurable_pi_apply (c.sum fun i a => (a : ℝ) • d i)).norm) measurable_const

/-- The "good paths" set: ω that are ℚ-linear and bounded on the dense sequence.
    This is measurable (countable Boolean operations on measurable sets). -/
def goodPaths (d : ℕ → E) (p : ℕ → Seminorm ℝ E) : Set (E → ℝ) :=
  qLinearPaths d ∩ boundedPaths d p

lemma goodPaths_measurableSet (d : ℕ → E) (p : ℕ → Seminorm ℝ E) :
    MeasurableSet (goodPaths d p) :=
  (qLinearPaths_measurableSet d).inter (boundedPaths_measurableSet d p)

/-! ## Extension on Good Paths -/

/-- On good paths, ω|_D is ℚ-linear and bounded by a continuous seminorm.
    This data suffices to uniquely extend ω|_D to a ContinuousLinearMap on E
    (by uniform continuity from boundedness + density of D + completeness of ℝ,
    then ℚ-linearity + continuity + density of ℚ in ℝ gives ℝ-linearity).

    ## Construction (BLT / uniform extension theorem)
    1. **Continuous extension**: On good paths, ω restricted to range(d) satisfies
       |ω(d_i) - ω(d_j)| ≤ C * q(d_i - d_j) (from ℚ-linearity + boundedness).
       This gives uniform continuity w.r.t. the seminorm q, so Dense.extend gives
       a continuous function g : E → ℝ with g(d_n) = ω(d_n).
    2. **ℚ-linearity of g**: g(a•x + b•y) = a•g(x) + b•g(y) for a, b ∈ ℚ.
       Both sides are continuous in x, y, and agree on range(d) × range(d).
    3. **ℝ-linearity**: g(r•x) = r•g(x) for r ∈ ℝ by density of ℚ in ℝ.

    Ref: Rudin, *Functional Analysis*, Thm 1.18 (bounded linear extension). -/
axiom extensionCLM [SeparableSpace E] [NuclearSpace E] [Nonempty E]
    (d : ℕ → E) (hd : DenseRange d)
    (p : ℕ → Seminorm ℝ E) (ω : E → ℝ) (hω : ω ∈ goodPaths d p) :
    WeakDual ℝ E

/-- The extension agrees with ω on the dense sequence.
    Follows from the BLT construction: Dense.extend agrees with ω on range(d).

    Ref: follows from extensionCLM construction. -/
axiom extensionCLM_eq_on_dense [SeparableSpace E] [NuclearSpace E] [Nonempty E]
    (d : ℕ → E) (hd : DenseRange d)
    (p : ℕ → Seminorm ℝ E) (ω : E → ℝ) (hω : ω ∈ goodPaths d p) (n : ℕ) :
    (extensionCLM d hd p ω hω : E →L[ℝ] ℝ) (d n) = ω (d n)

/-- For a continuous linear functional l, embed(l) ∈ goodPaths.
    Proof: l is ℝ-linear (hence ℚ-linear on all Finsupp combinations),
    and bounded by continuity. -/
lemma embed_mem_goodPaths [SeparableSpace E] [NuclearSpace E] [Nonempty E]
    (d : ℕ → E) (p : ℕ → Seminorm ℝ E)
    (hp_top : WithSeminorms (fun n => p n))
    (l : WeakDual ℝ E) :
    weakDualEmbed E l ∈ goodPaths d p := by
  constructor
  · -- ℚ-linearity: l is ℝ-linear, so l(∑ cᵢ • d(i)) = ∑ cᵢ * l(d(i))
    simp only [qLinearPaths, Set.mem_iInter, Set.mem_setOf_eq]
    intro c
    simp only [weakDualEmbed, Finsupp.sum]
    rw [map_sum]
    simp_rw [map_smul, smul_eq_mul]
  · -- Boundedness: l is continuous, hence bounded by finitely many p_n
    simp only [boundedPaths, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq]
    -- View |l(·)| as a continuous seminorm and apply bound_of_continuous
    have hl_cont : Continuous ((normSeminorm ℝ ℝ).comp l.toLinearMap) := by
      show Continuous (fun x => ‖l x‖)
      exact continuous_norm.comp l.cont
    obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous hp_top _ hl_cont
    -- hC : (normSeminorm ℝ ℝ).comp l.toLinearMap ≤ C • s.sup p
    -- i.e., ‖l(x)‖ ≤ C * (s.sup p)(x) for all x
    refine ⟨s, ⌈(C : ℝ)⌉₊, fun c => ?_⟩
    set x := c.sum fun i a => (a : ℝ) • d i
    have h := hC x
    simp only [Seminorm.comp_apply, coe_normSeminorm, Seminorm.smul_apply,
      NNReal.smul_def] at h
    calc |weakDualEmbed E l x| = ‖l x‖ := (Real.norm_eq_abs _).symm
      _ ≤ (C : ℝ) * (s.sup p) x := h
      _ ≤ (↑⌈(C : ℝ)⌉₊ : ℝ) * (s.sup p) x := by
          apply mul_le_mul_of_nonneg_right _ (apply_nonneg _ _)
          exact Nat.le_ceil _

/-- The extension of embed(l) recovers l.
    Proof: both are ContinuousLinearMaps that agree on the dense set D,
    hence they agree everywhere by uniqueness of continuous extension. -/
lemma extensionCLM_embed [SeparableSpace E] [NuclearSpace E] [Nonempty E]
    (d : ℕ → E) (hd : DenseRange d)
    (p : ℕ → Seminorm ℝ E)
    (hp_top : WithSeminorms (fun n => p n))
    (l : WeakDual ℝ E) :
    extensionCLM d hd p (weakDualEmbed E l) (embed_mem_goodPaths d p hp_top l) = l := by
  -- Both are ContinuousLinearMaps: show they're equal as functions E → ℝ
  apply ContinuousLinearMap.ext
  intro f
  -- Both sides are continuous functions E → ℝ that agree on range(d) (dense)
  -- Use Continuous.ext_on: two continuous functions to T2 space agreeing on dense set are equal
  have h_ext := Continuous.ext_on (show Dense (Set.range d) from hd)
    (extensionCLM d hd p (weakDualEmbed E l) (embed_mem_goodPaths d p hp_top l) :
      E →L[ℝ] ℝ).cont
    (l : E →L[ℝ] ℝ).cont
    (fun x hx => ?_)
  exact congr_fun h_ext f
  -- Show agreement on range(d): extensionCLM(embed(l))(d n) = l(d n)
  obtain ⟨n, rfl⟩ := hx
  exact extensionCLM_eq_on_dense d hd p (weakDualEmbed E l)
    (embed_mem_goodPaths d p hp_top l) n

/-! ## Measurable Projection -/

/-- Auxiliary projection given explicit dense sequence and seminorms.
    On good paths, extends ω to a ContinuousLinearMap; on bad paths, returns 0. -/
def measurableProjectionAux [SeparableSpace E] [NuclearSpace E] [Nonempty E]
    (d : ℕ → E) (hd : DenseRange d)
    (p : ℕ → Seminorm ℝ E) : (E → ℝ) → WeakDual ℝ E :=
  fun ω =>
    if hω : ω ∈ goodPaths d p then
      extensionCLM d hd p ω hω
    else 0

/-- The measurable projection P : (E → ℝ) → WeakDual ℝ E.

    On good paths (ℚ-linear + bounded on dense sequence), P(ω) is the unique
    continuous linear extension of ω|_D. On bad paths, P(ω) = 0. -/
def measurableProjection [SeparableSpace E] [NuclearSpace E] [Nonempty E] :
    (E → ℝ) → WeakDual ℝ E :=
  measurableProjectionAux (denseSeq E) (denseRange_denseSeq E)
    (NuclearSpace.nuclear_hilbert_embeddings (E := E)).choose

/-- The projection map is measurable.
    For each f : E, ω ↦ P(ω)(f) is measurable because:
    - goodPaths is measurable (countable ⋂/⋃)
    - On goodPaths, P(ω)(f) = lim ω(d_n) for d_n → f (pointwise limit of measurable functions)
    - On badPaths, P(ω)(f) = 0 (constant)
    - Piecewise of measurable functions on measurable sets is measurable

    Ref: standard measurability of piecewise + pointwise limits (Billingsley, §13). -/
axiom measurable_measurableProjection [SeparableSpace E] [NuclearSpace E] [Nonempty E] :
    Measurable (measurableProjection (E := E))

/-- The projection composed with the embedding is the identity on WeakDual ℝ E.
    For l ∈ WeakDual ℝ E, embed(l) ∈ goodPaths (l is linear + bounded), and
    extensionCLM(embed(l)) = l by uniqueness of continuous extension from dense. -/
lemma projection_embed_eq [SeparableSpace E] [NuclearSpace E] [Nonempty E] :
    (measurableProjection (E := E)) ∘ weakDualEmbed E = id := by
  ext l
  simp only [Function.comp_apply, id_eq]
  -- Unfold to measurableProjectionAux
  show measurableProjectionAux (denseSeq E) (denseRange_denseSeq E)
    (NuclearSpace.nuclear_hilbert_embeddings (E := E)).choose (weakDualEmbed E l) = l
  -- embed(l) ∈ goodPaths
  have hp_top : WithSeminorms (fun n =>
      (NuclearSpace.nuclear_hilbert_embeddings (E := E)).choose n) :=
    (NuclearSpace.nuclear_hilbert_embeddings (E := E)).choose_spec.2.1
  have h_mem := embed_mem_goodPaths (denseSeq E)
    (NuclearSpace.nuclear_hilbert_embeddings (E := E)).choose hp_top l
  -- dite picks the "if" branch
  simp only [measurableProjectionAux, dif_pos h_mem]
  -- extensionCLM recovers l
  exact extensionCLM_embed (denseSeq E) (denseRange_denseSeq E)
    (NuclearSpace.nuclear_hilbert_embeddings (E := E)).choose hp_top l

/-! ## Almost-everywhere properties

These axioms use the **joint characteristic function** hypothesis:
  h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
    ∫ ω, exp(I * ↑(∑ i, s i * ω(x i))) dν = Φ(∑ i, s i • x i)

This captures all finite-dimensional marginals of ν, not just the 1D marginals.
It is provable from the projective limit property. -/

/-- ℚ-linearity holds ν-a.e.

    For fixed c : ℕ →₀ ℚ, the random variable
    X(ω) = ω(∑ cᵢ•dᵢ) - ∑ cᵢ*ω(dᵢ)
    has CF E[e^{itX}] = Φ(t·∑cᵢ•dᵢ - t·∑cᵢ•dᵢ) = Φ(0) = 1
    (using h_cf_joint with test vectors {∑cᵢ•dᵢ, d_{i₁}, ..., d_{iₖ}}
    and scalars {t, -tc₁, ..., -tcₖ}).
    Hence X = 0 a.s. (by Measure.ext_of_charFun with δ₀).
    Countable intersection over c ∈ ℕ →₀ ℚ preserves full measure.

    Ref: Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. IV, §3.3. -/
axiom qLinearPaths_ae [SeparableSpace E] [NuclearSpace E] [Nonempty E]
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_normalized : Φ 0 = 1) :
    ∀ᵐ ω ∂ν, ω ∈ qLinearPaths (denseSeq E)

/-- Boundedness holds ν-a.e.

    For each element x in the ℚ-span, the Markov/Chebyshev inequality gives:
    P(|ω(x)| ≥ R) ≤ (1 - Re(Φ(tx))) / (1 - cos(tR))
    By continuity of Φ at 0, the numerator → 0 as x → 0.
    NuclearSpace seminorms give uniform control.

    Ref: Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. IV, §3.3;
    also Billingsley, "Convergence of Probability Measures", §6. -/
axiom boundedPaths_ae [SeparableSpace E] [NuclearSpace E] [Nonempty E]
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_cont : Continuous Φ)
    (h_cf_single : ∀ f : E, ∫ ω : E → ℝ,
      Complex.exp (Complex.I * ↑(ω f)) ∂ν = Φ f)
    (h_normalized : Φ 0 = 1) :
    ∀ᵐ ω ∂ν, ω ∈ boundedPaths (denseSeq E)
      (NuclearSpace.nuclear_hilbert_embeddings (E := E)).choose

/-- The good paths have full ν-measure. Combines ℚ-linearity and boundedness a.e. -/
lemma goodPaths_ae [SeparableSpace E] [NuclearSpace E] [Nonempty E]
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_cf_cont : Continuous Φ)
    (h_normalized : Φ 0 = 1) :
    ∀ᵐ ω ∂ν, ω ∈ goodPaths (denseSeq E)
      (NuclearSpace.nuclear_hilbert_embeddings (E := E)).choose := by
  -- Derive the single-variable CF from the joint CF (n=1 case)
  have h_cf_single : ∀ f : E, ∫ ω : E → ℝ,
      Complex.exp (Complex.I * ↑(ω f)) ∂ν = Φ f := by
    intro f
    have := h_cf_joint 1 (fun _ => 1) (fun _ => f)
    simp at this
    exact this
  have hq := qLinearPaths_ae Φ ν h_cf_joint h_normalized
  have hb := boundedPaths_ae Φ ν h_cf_cont h_cf_single h_normalized
  filter_upwards [hq, hb] with ω h1 h2
  exact ⟨h1, h2⟩

/-- For each f : E, P(ω)(f) = ω(f) for ν-a.e. ω.

    On good paths (full measure by goodPaths_ae):
    - P(ω)(d_n) = ω(d_n) for all n (by extensionCLM_eq_on_dense)
    - P(ω) is continuous, so P(ω)(d_n) → P(ω)(f) for any d_n → f
    - ω(d_n) → ω(f) in probability: using h_cf_joint with test vectors (f, d_n)
      and scalars (t, -t), CF = Φ(t(f-d_n)) → Φ(0) = 1 by continuity
    - A.s. + in-probability convergence to the same limit → P(ω)(f) = ω(f) a.e.

    Ref: Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. IV, §3.3. -/
axiom projection_ae_eq [SeparableSpace E] [NuclearSpace E] [Nonempty E]
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_cf_cont : Continuous Φ)
    (f : E) :
    ∀ᵐ ω ∂ν, (measurableProjection ω : E →L[ℝ] ℝ) f = ω f

/-! ## Derived Properties -/

/-- The pushforward μ = ν.map P is a probability measure when P is measurable. -/
lemma isProbabilityMeasure_map_projection [SeparableSpace E] [NuclearSpace E] [Nonempty E]
    (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (ν.map (measurableProjection (E := E))) :=
  Measure.isProbabilityMeasure_map measurable_measurableProjection.aemeasurable

/-- The characteristic functional of ν.map P equals Φ. -/
lemma charFunctional_map_projection [SeparableSpace E] [NuclearSpace E] [Nonempty E]
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_cf_cont : Continuous Φ) :
    ∀ f : E, ∫ l : WeakDual ℝ E, Complex.exp (Complex.I * ↑(l f))
      ∂(ν.map measurableProjection) = Φ f := by
  intro f
  -- Derive the single-variable CF
  have h_cf_single : ∀ f : E, ∫ ω : E → ℝ,
      Complex.exp (Complex.I * ↑(ω f)) ∂ν = Φ f := by
    intro f'
    have := h_cf_joint 1 (fun _ => 1) (fun _ => f')
    simp at this
    exact this
  rw [integral_map measurable_measurableProjection.aemeasurable]
  · have h_ae : ∀ᵐ ω ∂ν, (measurableProjection ω : E →L[ℝ] ℝ) f = ω f :=
      projection_ae_eq Φ ν h_cf_joint h_cf_cont f
    rw [← h_cf_single f]
    apply integral_congr_ae
    filter_upwards [h_ae] with ω hω
    simp [hω]
  · exact (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp
        (WeakDual.eval_continuous f)))).aestronglyMeasurable

/-- Uniqueness via pushforward factoring: μ' = ν.map P. -/
lemma uniqueness_via_projection [SeparableSpace E] [NuclearSpace E] [Nonempty E]
    (Φ : E → ℂ) (h_continuous : Continuous Φ)
    (h_positive_definite : IsPositiveDefinite Φ) (h_normalized : Φ 0 = 1)
    (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (hν_eq : ν = marginalProjectiveLimit Φ h_continuous h_positive_definite h_normalized)
    (μ' : ProbabilityMeasure (WeakDual ℝ E))
    (hμ' : ∀ f : E, Φ f = ∫ ω, exp (I * (ω f)) ∂μ'.toMeasure) :
    μ' = ⟨ν.map measurableProjection, isProbabilityMeasure_map_projection ν⟩ := by
  -- Step 1: μ'.toMeasure.map embed = ν (via projective limit uniqueness)
  have h_mu'_proj : IsProjectiveLimit (μ'.toMeasure.map (weakDualEmbed E))
      (marginalFamily Φ h_continuous h_positive_definite h_normalized) := by
    intro J
    simp only [marginalFamily]
    suffices key : ((μ'.toMeasure.map (weakDualEmbed E)).map (Finset.restrict J)).map
        (finsetPiMeasEquiv J) =
        (marginalMeasure Φ h_continuous h_positive_definite h_normalized J :
          Measure _) by
      have := congr_arg (fun μ => μ.map (finsetPiMeasEquiv J).symm) key
      simp only [Measure.map_map (finsetPiMeasEquiv J).symm.measurable
        (finsetPiMeasEquiv J).measurable,
        (finsetPiMeasEquiv J).symm_comp_self, Measure.map_id] at this
      exact this
    apply Measure.ext_of_charFun
    ext ξ
    rw [marginalMeasure_charFun]
    rw [Measure.map_map (finsetPiMeasEquiv J).measurable (Finset.measurable_restrict J),
      Measure.map_map ((finsetPiMeasEquiv J).measurable.comp
        (Finset.measurable_restrict J)) measurable_weakDualEmbed]
    rw [charFun_apply,
      integral_map
        (((finsetPiMeasEquiv J).measurable.comp (Finset.measurable_restrict J)).comp
          measurable_weakDualEmbed).aemeasurable
        (by fun_prop : AEStronglyMeasurable _ _)]
    have h_inner_eq : ∀ l : WeakDual ℝ E,
        @inner ℝ _ _ (((⇑(finsetPiMeasEquiv J) ∘ Finset.restrict J) ∘
          weakDualEmbed E) l) ξ =
        l (∑ k : Fin J.card, (ξ k) • finsetTestVectors J k) := by
      intro l
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
        finsetPiMeasEquiv, finsetReindexEquiv, finsetTestVectors,
        MeasurableEquiv.trans_apply, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
        MeasurableEquiv.coe_toLp, Function.comp_apply, Finset.restrict,
        weakDualEmbed]
      rw [map_sum]
      simp_rw [map_smul, smul_eq_mul]
    simp_rw [h_inner_eq, mul_comm _ Complex.I]
    rw [← hμ']
    rfl
  have h_mu'_embed : μ'.toMeasure.map (weakDualEmbed E) = ν := by
    rw [hν_eq]
    exact marginalProjectiveLimit_unique Φ h_continuous h_positive_definite h_normalized
      h_mu'_proj
  -- Step 2: μ' = (μ'.map embed).map P = ν.map P = μ
  apply Subtype.ext
  show μ'.toMeasure = ν.map measurableProjection
  rw [← h_mu'_embed]
  rw [Measure.map_map measurable_measurableProjection measurable_weakDualEmbed]
  rw [show measurableProjection ∘ weakDualEmbed E = id from projection_embed_eq]
  simp [Measure.map_id]

end
