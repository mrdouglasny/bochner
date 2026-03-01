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

- `qLinearPaths` — set of ω that are ℚ-linear on the dense sequence
- `boundedPaths` — set of ω bounded by a NuclearSpace seminorm
- `goodPaths` — intersection (measurable, full measure under ν)
- `measurableProjection` — P : (E → ℝ) → WeakDual ℝ E
- `weakDualEmbed` — the embedding WeakDual ℝ E → (E → ℝ)

## Sorries (6)

1. `extensionCLM` — construct ContinuousLinearMap from good path
2. `extensionCLM_eq_on_dense` — extension agrees with ω on dense sequence
3. `extensionCLM_embed` — extension of embed(l) equals l
4. `measurable_measurableProjection` — P is measurable
5. `goodPaths_ae` — ν(goodPaths) = 1
6. `projection_ae_eq` — P(ω)(f) = ω(f) ν-a.e.

## References

- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. IV, §3.3
- Minlos, "Generalized random processes and their extension to measures" (1959)
-/

import Bochner.Minlos.ProjectiveFamily
import Mathlib.Topology.Bases

open BigOperators MeasureTheory Complex TopologicalSpace Classical

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

/-! ## Good Paths -/

/-- The set of "ℚ-linear paths" on a sequence d : ℕ → E.
    ω is ℚ-linear on the range of d: for all i, j and rational a, b,
    ω(a • d i + b • d j) = a * ω(d i) + b * ω(d j).

    This is a countable intersection of measurable sets. -/
def qLinearPaths (d : ℕ → E) : Set (E → ℝ) :=
  ⋂ (i : ℕ) (j : ℕ) (a : ℚ) (b : ℚ),
    { ω | ω ((a : ℝ) • d i + (b : ℝ) • d j) = (a : ℝ) * ω (d i) + (b : ℝ) * ω (d j) }

lemma qLinearPaths_measurableSet (d : ℕ → E) :
    MeasurableSet (qLinearPaths d) := by
  apply MeasurableSet.iInter; intro i
  apply MeasurableSet.iInter; intro j
  apply MeasurableSet.iInter; intro a
  apply MeasurableSet.iInter; intro b
  apply measurableSet_eq_fun
  · exact measurable_pi_apply _
  · exact ((measurable_pi_apply (d i)).const_mul _).add
      ((measurable_pi_apply (d j)).const_mul _)

/-- The set of "bounded paths" on a sequence d : ℕ → E with respect to
    seminorms p : ℕ → Seminorm ℝ E.
    ω is bounded on the ℚ-span: ∃ s : Finset ℕ, ∃ C : ℕ, for all
    ℚ-linear combinations a • d i + b • d j,
    |ω(a • d i + b • d j)| ≤ C * (s.sup p)(a • d i + b • d j).

    Combined with ℚ-linearity, this gives uniform continuity:
    |ω(d i) - ω(d j)| ≤ C * q(d i - d j).

    This is measurable (countable ⋃/⋂ over ℕ × ℕ × ℚ × ℚ). -/
def boundedPaths (d : ℕ → E) (p : ℕ → Seminorm ℝ E) : Set (E → ℝ) :=
  ⋃ (s : Finset ℕ) (C : ℕ), ⋂ (i : ℕ) (j : ℕ) (a : ℚ) (b : ℚ),
    { ω | |ω ((a : ℝ) • d i + (b : ℝ) • d j)| ≤
        (C : ℝ) * (s.sup p) ((a : ℝ) • d i + (b : ℝ) • d j) }

lemma boundedPaths_measurableSet (d : ℕ → E) (p : ℕ → Seminorm ℝ E) :
    MeasurableSet (boundedPaths d p) := by
  apply MeasurableSet.iUnion; intro s
  apply MeasurableSet.iUnion; intro C
  apply MeasurableSet.iInter; intro i
  apply MeasurableSet.iInter; intro j
  apply MeasurableSet.iInter; intro a
  apply MeasurableSet.iInter; intro b
  exact measurableSet_le
    ((measurable_pi_apply ((a : ℝ) • d i + (b : ℝ) • d j)).norm) measurable_const

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

    The construction uses `IsDenseInducing.extend` applied to the dense
    inclusion of D into E, with ω|_D as the function to extend.

    **Sorry**: the full construction of the ContinuousLinearMap. -/
def extensionCLM [SeparableSpace E] [NuclearSpace E] [Nonempty E]
    (d : ℕ → E) (hd : DenseRange d)
    (p : ℕ → Seminorm ℝ E) (ω : E → ℝ) (hω : ω ∈ goodPaths d p) :
    WeakDual ℝ E :=
  sorry

/-- The extension agrees with ω on the dense sequence.
    This follows from the definition: on D, the extension equals ω|_D. -/
lemma extensionCLM_eq_on_dense [SeparableSpace E] [NuclearSpace E] [Nonempty E]
    (d : ℕ → E) (hd : DenseRange d)
    (p : ℕ → Seminorm ℝ E) (ω : E → ℝ) (hω : ω ∈ goodPaths d p) (n : ℕ) :
    (extensionCLM d hd p ω hω : E →L[ℝ] ℝ) (d n) = ω (d n) :=
  sorry

/-- For a continuous linear functional l, embed(l) ∈ goodPaths.
    Proof: l is ℝ-linear (hence ℚ-linear), and bounded by continuity. -/
lemma embed_mem_goodPaths [SeparableSpace E] [NuclearSpace E] [Nonempty E]
    (d : ℕ → E) (p : ℕ → Seminorm ℝ E)
    (hp_top : WithSeminorms (fun n => p n))
    (l : WeakDual ℝ E) :
    weakDualEmbed E l ∈ goodPaths d p := by
  constructor
  · -- ℚ-linearity: l is ℝ-linear, hence ℚ-linear
    simp only [qLinearPaths, Set.mem_iInter, Set.mem_setOf_eq]
    intro i j a b
    simp only [weakDualEmbed, map_add, map_smul, smul_eq_mul]
  · -- Boundedness: l is continuous, hence bounded by finitely many p_n
    simp only [boundedPaths, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq]
    -- View |l(·)| as a continuous seminorm and apply bound_of_continuous
    have hl_cont : Continuous ((normSeminorm ℝ ℝ).comp l.toLinearMap) := by
      show Continuous (fun x => ‖l x‖)
      exact continuous_norm.comp l.cont
    obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous hp_top _ hl_cont
    -- hC : (normSeminorm ℝ ℝ).comp l.toLinearMap ≤ C • s.sup p
    -- i.e., ‖l(x)‖ ≤ C * (s.sup p)(x) for all x
    refine ⟨s, ⌈(C : ℝ)⌉₊, fun i j a b => ?_⟩
    set x := (a : ℝ) • d i + (b : ℝ) • d j
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
    - Piecewise of measurable functions on measurable sets is measurable -/
lemma measurable_measurableProjection [SeparableSpace E] [NuclearSpace E] [Nonempty E] :
    Measurable (measurableProjection (E := E)) := by
  -- The weak-* Borel σ-algebra is generated by evaluations.
  -- So it suffices to show each eval_f ∘ P is measurable.
  -- P(ω)(f) = extensionCLM(ω)(f) on goodPaths, 0 otherwise.
  -- The extensionCLM(ω)(f) = lim ω(d_n) for d_n → f (pointwise limit of measurable functions).
  -- The piecewise of measurable functions on a measurable set is measurable.
  sorry

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

/-- ℚ-linearity holds ν-a.e.

    For fixed i, j ∈ ℕ and a, b ∈ ℚ, the random variable
    X(ω) = ω(a•d_i + b•d_j) - a•ω(d_i) - b•ω(d_j)
    has characteristic function E[e^{itX}] = Φ(t(a•d_i+b•d_j) - ta•d_i - tb•d_j) = Φ(0) = 1.
    Hence X = 0 a.s. (a measure with CF ≡ 1 is δ₀).
    Countable intersection over (i, j, a, b) ∈ ℕ × ℕ × ℚ × ℚ preserves full measure. -/
private lemma qLinearPaths_ae [SeparableSpace E] [NuclearSpace E] [Nonempty E]
    (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_eq : ∀ f : E, ∫ ω : E → ℝ, Complex.exp (Complex.I * ↑(ω f)) ∂ν =
      (fun f : E => ∫ ω : E → ℝ, Complex.exp (Complex.I * ↑(ω f)) ∂ν) f)
    (h_cf_one : (fun f : E => ∫ ω : E → ℝ,
      Complex.exp (Complex.I * ↑(ω f)) ∂ν) 0 = 1) :
    ∀ᵐ ω ∂ν, ω ∈ qLinearPaths (denseSeq E) := by
  simp only [qLinearPaths, Set.mem_iInter, Set.mem_setOf_eq]
  -- Countable intersection: suffices to show each condition holds a.e.
  rw [eventually_countable_forall]; intro i
  rw [eventually_countable_forall]; intro j
  rw [eventually_countable_forall]; intro a
  rw [eventually_countable_forall]; intro b
  -- For fixed i, j, a, b: show ω(a•d_i + b•d_j) = a*ω(d_i) + b*ω(d_j) a.e.
  -- The random variable X = ω(a•d_i + b•d_j) - a*ω(d_i) - b*ω(d_j) has CF ≡ 1
  -- (since t•(a•d_i+b•d_j) - ta•d_i - tb•d_j = 0, giving Φ(0) = 1)
  -- A probability measure on ℝ with CF ≡ 1 is δ₀, hence X = 0 a.s.
  sorry

/-- Boundedness holds ν-a.e.

    For each element x = a•d_i + b•d_j, the Markov/Chebyshev inequality gives:
    P(|ω(x)| ≥ R) ≤ (1 - Re(Φ(tx))) / (1 - cos(tR))
    By continuity of Φ at 0, the numerator → 0 as x → 0.
    NuclearSpace seminorms give uniform control. -/
private lemma boundedPaths_ae [SeparableSpace E] [NuclearSpace E] [Nonempty E]
    (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_cont : Continuous (fun f : E => ∫ ω : E → ℝ,
      Complex.exp (Complex.I * ↑(ω f)) ∂ν))
    (h_cf_one : (fun f : E => ∫ ω : E → ℝ,
      Complex.exp (Complex.I * ↑(ω f)) ∂ν) 0 = 1) :
    ∀ᵐ ω ∂ν, ω ∈ boundedPaths (denseSeq E)
      (NuclearSpace.nuclear_hilbert_embeddings (E := E)).choose := by
  sorry

/-- The good paths have full ν-measure. Combines ℚ-linearity and boundedness a.e. -/
lemma goodPaths_ae [SeparableSpace E] [NuclearSpace E] [Nonempty E]
    (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_cont : Continuous (fun f : E => ∫ ω : E → ℝ,
      Complex.exp (Complex.I * ↑(ω f)) ∂ν))
    (h_cf_one : (fun f : E => ∫ ω : E → ℝ,
      Complex.exp (Complex.I * ↑(ω f)) ∂ν) 0 = 1) :
    ∀ᵐ ω ∂ν, ω ∈ goodPaths (denseSeq E)
      (NuclearSpace.nuclear_hilbert_embeddings (E := E)).choose := by
  have hq := qLinearPaths_ae ν (fun f => rfl) h_cf_one
  have hb := boundedPaths_ae ν h_cf_cont h_cf_one
  filter_upwards [hq, hb] with ω h1 h2
  exact ⟨h1, h2⟩

/-- For each f : E, P(ω)(f) = ω(f) for ν-a.e. ω.

    Proof: On good paths (full measure by goodPaths_ae):
    - P(ω)(d_n) = ω(d_n) for all n (by extensionCLM_eq_on_dense)
    - P(ω) is continuous, so P(ω)(d_n) → P(ω)(f) for any d_n → f
    - ω(d_n) → ω(f) in probability: CF of (ω(f) - ω(d_n)) is
      Φ(t(f - d_n)) → Φ(0) = 1 by continuity of Φ
    - A.s. + in-probability convergence to the same limit → P(ω)(f) = ω(f) a.e. -/
lemma projection_ae_eq [SeparableSpace E] [NuclearSpace E] [Nonempty E]
    (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_eq : ∀ f : E, ∫ ω : E → ℝ, Complex.exp (Complex.I * ↑(ω f)) ∂ν =
      (fun f : E => ∫ ω : E → ℝ, Complex.exp (Complex.I * ↑(ω f)) ∂ν) f)
    (h_cf_cont : Continuous (fun f : E => ∫ ω : E → ℝ,
      Complex.exp (Complex.I * ↑(ω f)) ∂ν))
    (f : E) :
    ∀ᵐ ω ∂ν, (measurableProjection ω : E →L[ℝ] ℝ) f = ω f := by
  sorry

/-! ## Derived Properties -/

/-- The pushforward μ = ν.map P is a probability measure when P is measurable. -/
lemma isProbabilityMeasure_map_projection [SeparableSpace E] [NuclearSpace E] [Nonempty E]
    (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (ν.map (measurableProjection (E := E))) :=
  Measure.isProbabilityMeasure_map measurable_measurableProjection.aemeasurable

/-- The characteristic functional of ν.map P equals the CF of ν. -/
lemma charFunctional_map_projection [SeparableSpace E] [NuclearSpace E] [Nonempty E]
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_eq : ∀ f : E, ∫ ω : E → ℝ, Complex.exp (Complex.I * ↑(ω f)) ∂ν = Φ f)
    (h_cf_cont : Continuous Φ) :
    ∀ f : E, ∫ l : WeakDual ℝ E, Complex.exp (Complex.I * ↑(l f))
      ∂(ν.map measurableProjection) = Φ f := by
  intro f
  rw [integral_map measurable_measurableProjection.aemeasurable]
  · have h_ae : ∀ᵐ ω ∂ν, (measurableProjection ω : E →L[ℝ] ℝ) f = ω f := by
      apply projection_ae_eq
      · intro f'; exact rfl
      · rwa [show (fun f : E => ∫ ω : E → ℝ,
          Complex.exp (Complex.I * ↑(ω f)) ∂ν) = Φ from funext h_cf_eq]
    rw [← h_cf_eq f]
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
