/-
Copyright (c) 2026 Axiomatic AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Minlos.Mathlib.Analysis.Normed.Operator.Compact.FiniteRank
public import Minlos.Mathlib.Analysis.LocallyConvex.NuclearMap
public import Minlos.Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Hilbert–Schmidt operators

A continuous linear map `T` between Hilbert spaces is **Hilbert–Schmidt** if
`∑ᵢ ‖T (v i)‖²` is uniformly bounded over finite orthonormal families `v`
(Bourbaki, *EVT* V p. 51 déf. 9; *Théories spectrales* IV §1). Mathlib has no
Hilbert–Schmidt class; this file provides:

* `ContinuousLinearMap.IsHilbertSchmidt`: the (basis-free) predicate;
* `HilbertBasis.tsum_enorm_sq_eq_adjoint` and
  `HilbertBasis.tsum_enorm_sq_eq`: `∑ᵢ ‖T (b i)‖ₑ²` does not depend on the Hilbert basis, and
  equals the corresponding sum for the adjoint — via the `ℝ≥0∞`-valued Parseval double sum;
* `ContinuousLinearMap.isHilbertSchmidt_iff_summable`: `T` is Hilbert–Schmidt iff
  `∑ᵢ ‖T (b i)‖²` converges for one (equivalently, every) Hilbert basis;
* `ContinuousLinearMap.IsHilbertSchmidt.isCompactOperator`: Hilbert–Schmidt operators are
  compact (finite-rank truncations along a basis converge in operator norm, by a tail
  Cauchy–Schwarz estimate);
* `ContinuousLinearMap.isHilbertSchmidt_iff_exists_hasSum_norm_sq`: `T` is Hilbert–Schmidt iff
  `‖T x‖² = ∑ₙ ‖⟪vₙ, x⟫‖²` with `∑ₙ ‖vₙ‖² < ∞`, the seminorms of the Sazonov topology;
* `ContinuousLinearMap.IsHilbertSchmidt.comp_left`: the ideal property `S ∘ T`;
* `ContinuousLinearMap.IsNuclear.exists_isHilbertSchmidt_comp`: a nuclear map into a Hilbert space
  factors through `ℓ²` by a Hilbert–Schmidt map.

## References

* [N. Bourbaki, *Espaces vectoriels topologiques*, chap. V and VII][bourbaki2023evt]
* [N. Bourbaki, *Théories spectrales*, IV §1 nos. 1, 9][bourbaki2023spectral]
* [M. Reed, B. Simon, *Methods of Modern Mathematical Physics I*, Theorem VI.22]

## Provenance

Ported from or4nge19/QuantumlibCore `pin-v4.34.1` `9a741c08`,
`QuantumlibCore/ToMathlib/Analysis/InnerProductSpace/HilbertSchmidt.lean` (Lean v4.34.1, Mathlib
`d13f23b7`), with module paths renamed; notices kept.
-/

@[expose] public section

open Filter Topology
open scoped ENNReal InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- A continuous linear map between inner-product spaces is **Hilbert–Schmidt** if the sums
`∑ᵢ ‖T (v i)‖²` over finite orthonormal families are uniformly bounded. -/
def IsHilbertSchmidt (T : E →L[𝕜] F) : Prop :=
  ∃ C : ℝ, ∀ (n : ℕ) (v : Fin n → E), Orthonormal 𝕜 v → ∑ i, ‖T (v i)‖ ^ 2 ≤ C

end ContinuousLinearMap

/-! ### The `ℝ≥0∞`-valued Parseval and Bessel identities -/

section ENorm

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Parseval, `ℝ`-valued `HasSum` form: `∑ⱼ ‖⟪c j, y⟫‖² = ‖y‖²`. -/
theorem HilbertBasis.hasSum_norm_sq_inner {κ : Type*} (c : HilbertBasis κ 𝕜 F) (y : F) :
    HasSum (fun j => ‖⟪c j, y⟫_𝕜‖ ^ 2) (‖y‖ ^ 2) := by
  have h := c.hasSum_inner_mul_inner y y
  have hre := h.mapL (RCLike.reCLM (K := 𝕜))
  have h1 : (fun j => RCLike.reCLM (K := 𝕜) (⟪y, c j⟫_𝕜 * ⟪c j, y⟫_𝕜))
      = fun j => ‖⟪c j, y⟫_𝕜‖ ^ 2 := by
    funext j
    rw [RCLike.reCLM_apply, ← inner_conj_symm y (c j), RCLike.conj_mul]
    norm_cast
  have h2 : RCLike.reCLM (K := 𝕜) (⟪y, y⟫_𝕜) = ‖y‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := 𝕜) y
  rw [h1, h2] at hre
  exact hre

/-- Parseval, `ℝ≥0∞`-valued: `∑ⱼ ‖⟪c j, y⟫‖ₑ² = ‖y‖ₑ²`. -/
theorem HilbertBasis.tsum_enorm_sq_inner {κ : Type*} (c : HilbertBasis κ 𝕜 F) (y : F) :
    ∑' j, (‖⟪c j, y⟫_𝕜‖ₑ : ℝ≥0∞) ^ 2 = ‖y‖ₑ ^ 2 := by
  have h := c.hasSum_norm_sq_inner y
  have hof := ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) h.summable
  rw [h.tsum_eq] at hof
  calc ∑' j, (‖⟪c j, y⟫_𝕜‖ₑ : ℝ≥0∞) ^ 2
      = ∑' j, ENNReal.ofReal (‖⟪c j, y⟫_𝕜‖ ^ 2) := by
        refine tsum_congr fun j => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    _ = ENNReal.ofReal (‖y‖ ^ 2) := hof.symm
    _ = ‖y‖ₑ ^ 2 := by
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- Bessel, `ℝ≥0∞`-valued: `∑ᵢ ‖⟪v i, x⟫‖ₑ² ≤ ‖x‖ₑ²` for an orthonormal family. -/
theorem Orthonormal.tsum_enorm_sq_inner_le {ι' : Type*} {v : ι' → F} (hv : Orthonormal 𝕜 v)
    (x : F) : ∑' i, (‖⟪v i, x⟫_𝕜‖ₑ : ℝ≥0∞) ^ 2 ≤ ‖x‖ₑ ^ 2 := by
  have hb := hv.tsum_inner_products_le x
  have hsum := hv.inner_products_summable x
  calc ∑' i, (‖⟪v i, x⟫_𝕜‖ₑ : ℝ≥0∞) ^ 2
      = ∑' i, ENNReal.ofReal (‖⟪v i, x⟫_𝕜‖ ^ 2) := by
        refine tsum_congr fun i => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    _ = ENNReal.ofReal (∑' i, ‖⟪v i, x⟫_𝕜‖ ^ 2) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsum).symm
    _ ≤ ENNReal.ofReal (‖x‖ ^ 2) := ENNReal.ofReal_le_ofReal hb
    _ = ‖x‖ₑ ^ 2 := by
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

end ENorm

/-! ### Basis independence via the double Parseval sum -/

section Core

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  (T : E →L[𝕜] F)

/-- The `ℝ≥0∞`-valued Hilbert–Schmidt sum of `T` over a Hilbert basis equals that of the
adjoint over any Hilbert basis of the target. -/
theorem HilbertBasis.tsum_enorm_sq_map_eq_adjoint {ι κ : Type*} (b : HilbertBasis ι 𝕜 E)
    (c : HilbertBasis κ 𝕜 F) :
    ∑' i, (‖T (b i)‖ₑ : ℝ≥0∞) ^ 2
      = ∑' j, (‖ContinuousLinearMap.adjoint T (c j)‖ₑ : ℝ≥0∞) ^ 2 := by
  have h1 : ∀ i, (‖T (b i)‖ₑ : ℝ≥0∞) ^ 2 = ∑' j, (‖⟪c j, T (b i)⟫_𝕜‖ₑ : ℝ≥0∞) ^ 2 :=
    fun i => (c.tsum_enorm_sq_inner (T (b i))).symm
  have h2 : ∀ j, (‖ContinuousLinearMap.adjoint T (c j)‖ₑ : ℝ≥0∞) ^ 2
      = ∑' i, (‖⟪b i, ContinuousLinearMap.adjoint T (c j)⟫_𝕜‖ₑ : ℝ≥0∞) ^ 2 :=
    fun j => (b.tsum_enorm_sq_inner (ContinuousLinearMap.adjoint T (c j))).symm
  calc ∑' i, (‖T (b i)‖ₑ : ℝ≥0∞) ^ 2
      = ∑' i, ∑' j, (‖⟪c j, T (b i)⟫_𝕜‖ₑ : ℝ≥0∞) ^ 2 := tsum_congr h1
    _ = ∑' j, ∑' i, (‖⟪c j, T (b i)⟫_𝕜‖ₑ : ℝ≥0∞) ^ 2 := ENNReal.tsum_comm
    _ = ∑' j, ∑' i, (‖⟪b i, ContinuousLinearMap.adjoint T (c j)⟫_𝕜‖ₑ : ℝ≥0∞) ^ 2 := by
        refine tsum_congr fun j => tsum_congr fun i => ?_
        have hval : ‖⟪b i, ContinuousLinearMap.adjoint T (c j)⟫_𝕜‖ = ‖⟪c j, T (b i)⟫_𝕜‖ := by
          rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm (T (b i)) (c j)]
          exact RCLike.norm_conj _
        rw [← ofReal_norm, ← ofReal_norm, hval]
    _ = ∑' j, (‖ContinuousLinearMap.adjoint T (c j)‖ₑ : ℝ≥0∞) ^ 2 :=
        tsum_congr fun j => (h2 j).symm

/-- **Basis independence** of the Hilbert–Schmidt sum. -/
theorem HilbertBasis.tsum_enorm_sq_map_eq {ι ι' : Type*} (b : HilbertBasis ι 𝕜 E)
    (b' : HilbertBasis ι' 𝕜 E) :
    ∑' i, (‖T (b i)‖ₑ : ℝ≥0∞) ^ 2 = ∑' i, (‖T (b' i)‖ₑ : ℝ≥0∞) ^ 2 := by
  obtain ⟨w, c, -⟩ := exists_hilbertBasis 𝕜 F
  rw [b.tsum_enorm_sq_map_eq_adjoint T c, b'.tsum_enorm_sq_map_eq_adjoint T c]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The `ℝ≥0∞` sum over a basis versus real summability. -/
theorem HilbertBasis.tsum_enorm_sq_map_lt_top_iff {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    ∑' i, (‖T (b i)‖ₑ : ℝ≥0∞) ^ 2 < ⊤ ↔ Summable fun i => ‖T (b i)‖ ^ 2 := by
  have hval : ∀ i, (‖T (b i)‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖T (b i)‖ ^ 2) := fun i => by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [tsum_congr hval]
  constructor
  · intro h
    have := ENNReal.summable_toReal h.ne
    refine this.congr fun i => ?_
    rw [ENNReal.toReal_ofReal (by positivity)]
  · intro h
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) h]
    exact ENNReal.ofReal_lt_top

/-- **A Hilbert–Schmidt map has square-summable images of every Hilbert basis**, with a
basis-independent sum. Conversely, square-summability along one basis makes the map
Hilbert–Schmidt. -/
theorem ContinuousLinearMap.isHilbertSchmidt_iff_summable {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    T.IsHilbertSchmidt ↔ Summable fun i => ‖T (b i)‖ ^ 2 := by
  constructor
  · rintro ⟨C, hC⟩
    refine summable_of_sum_le (c := C) (fun i => by positivity) fun s => ?_
    -- enumerate the finset as an orthonormal `Fin n`-family
    classical
    set n := s.card with hn
    set v : Fin n → E := fun k => b (s.equivFin.symm k) with hv
    have hvon : Orthonormal 𝕜 v :=
      b.orthonormal.comp _ (Subtype.val_injective.comp s.equivFin.symm.injective)
    have hle := hC n v hvon
    have h1 : ∑ k : Fin n, ‖T (v k)‖ ^ 2 = ∑ x : ↥s, ‖T (b (x : ι))‖ ^ 2 :=
      Fintype.sum_equiv s.equivFin.symm _ _ (fun k => rfl)
    have h2 : ∑ x : ↥s, ‖T (b (x : ι))‖ ^ 2 = ∑ i ∈ s, ‖T (b i)‖ ^ 2 :=
      Finset.sum_coe_sort s (fun i => ‖T (b i)‖ ^ 2)
    rw [h1, h2] at hle
    exact hle
  · intro hsum
    -- the tail bound: every finite orthonormal family is dominated by the adjoint sum
    obtain ⟨w, c, -⟩ := exists_hilbertBasis 𝕜 F
    have htop : ∑' i, (‖T (b i)‖ₑ : ℝ≥0∞) ^ 2 < ⊤ :=
      (b.tsum_enorm_sq_map_lt_top_iff T).mpr hsum
    refine ⟨∑' i, ‖T (b i)‖ ^ 2, fun n v hvon => ?_⟩
    -- pass through `ℝ≥0∞`
    have key : ∑ k : Fin n, (‖T (v k)‖ₑ : ℝ≥0∞) ^ 2 ≤ ∑' i, (‖T (b i)‖ₑ : ℝ≥0∞) ^ 2 := by
      have hAdj := b.tsum_enorm_sq_map_eq_adjoint T c
      calc ∑ k : Fin n, (‖T (v k)‖ₑ : ℝ≥0∞) ^ 2
          = ∑ k : Fin n, ∑' j, (‖⟪c j, T (v k)⟫_𝕜‖ₑ : ℝ≥0∞) ^ 2 :=
            Finset.sum_congr rfl fun k _ => (c.tsum_enorm_sq_inner (T (v k))).symm
        _ = ∑' j, ∑ k : Fin n, (‖⟪c j, T (v k)⟫_𝕜‖ₑ : ℝ≥0∞) ^ 2 := by
            rw [← Summable.tsum_finsetSum fun k _ => ENNReal.summable]
        _ ≤ ∑' j, (‖ContinuousLinearMap.adjoint T (c j)‖ₑ : ℝ≥0∞) ^ 2 := by
            refine ENNReal.tsum_le_tsum fun j => ?_
            have hswap : ∀ k,
                ‖⟪c j, T (v k)⟫_𝕜‖ₑ = ‖⟪v k, ContinuousLinearMap.adjoint T (c j)⟫_𝕜‖ₑ := by
              intro k
              rw [← ofReal_norm, ← ofReal_norm]
              congr 1
              rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm (T (v k)) (c j)]
              exact (RCLike.norm_conj _).symm
            calc ∑ k : Fin n, (‖⟪c j, T (v k)⟫_𝕜‖ₑ : ℝ≥0∞) ^ 2
                = ∑ k : Fin n, (‖⟪v k, ContinuousLinearMap.adjoint T (c j)⟫_𝕜‖ₑ : ℝ≥0∞) ^ 2 := by
                  refine Finset.sum_congr rfl fun k _ => by rw [hswap k]
              _ ≤ ∑' k : Fin n, (‖⟪v k, ContinuousLinearMap.adjoint T (c j)⟫_𝕜‖ₑ : ℝ≥0∞) ^ 2 := by
                  rw [tsum_fintype]
              _ ≤ (‖ContinuousLinearMap.adjoint T (c j)‖ₑ : ℝ≥0∞) ^ 2 :=
                  hvon.tsum_enorm_sq_inner_le _
        _ = ∑' i, (‖T (b i)‖ₑ : ℝ≥0∞) ^ 2 := hAdj.symm
    -- convert back to `ℝ`
    have hofreal : ∀ x : F, (‖x‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := fun x => by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    have hL : ∑ k : Fin n, (‖T (v k)‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (∑ k, ‖T (v k)‖ ^ 2) := by
      rw [Finset.sum_congr rfl fun k _ => hofreal (T (v k)),
        ← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
    have hR : ∑' i, (‖T (b i)‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (∑' i, ‖T (b i)‖ ^ 2) := by
      rw [tsum_congr fun i => hofreal (T (b i)),
        ← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsum]
    rw [hL, hR] at key
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp key

/-- **Basis independence of the Hilbert–Schmidt sum**, real-valued form. -/
theorem HilbertBasis.tsum_norm_sq_map_eq {ι ι' : Type*} (b : HilbertBasis ι 𝕜 E)
    (b' : HilbertBasis ι' 𝕜 E) (hb : Summable fun i => ‖T (b i)‖ ^ 2) :
    Summable (fun i => ‖T (b' i)‖ ^ 2) ∧
      ∑' i, ‖T (b' i)‖ ^ 2 = ∑' i, ‖T (b i)‖ ^ 2 := by
  have he := b.tsum_enorm_sq_map_eq T b'
  have hb' : Summable fun i => ‖T (b' i)‖ ^ 2 := by
    rw [← b'.tsum_enorm_sq_map_lt_top_iff T, ← he, b.tsum_enorm_sq_map_lt_top_iff T]
    exact hb
  refine ⟨hb', ?_⟩
  have h1 : ∑' i, (‖T (b i)‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (∑' i, ‖T (b i)‖ ^ 2) := by
    rw [tsum_congr fun i => show (‖T (b i)‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖T (b i)‖ ^ 2) by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)],
      ← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hb]
  have h2 : ∑' i, (‖T (b' i)‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (∑' i, ‖T (b' i)‖ ^ 2) := by
    rw [tsum_congr fun i => show (‖T (b' i)‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖T (b' i)‖ ^ 2) by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)],
      ← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hb']
  rw [h1, h2] at he
  exact (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).mp he.symm

variable {T} in
omit [CompleteSpace E] [CompleteSpace F] in
/-- Hilbert–Schmidt maps are stable under composition with a bounded map on the left. -/
theorem ContinuousLinearMap.IsHilbertSchmidt.comp_left {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] (hT : T.IsHilbertSchmidt) (S : F →L[𝕜] G) :
    (S.comp T).IsHilbertSchmidt := by
  obtain ⟨C, hC⟩ := hT
  refine ⟨‖S‖ ^ 2 * C, fun n v hv => ?_⟩
  calc ∑ i, ‖(S.comp T) (v i)‖ ^ 2 ≤ ∑ i, (‖S‖ * ‖T (v i)‖) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact pow_le_pow_left₀ (norm_nonneg _) (S.le_opNorm (T (v i))) 2
    _ = ‖S‖ ^ 2 * ∑ i, ‖T (v i)‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ‖S‖ ^ 2 * C :=
        mul_le_mul_of_nonneg_left (hC n v hv) (by positivity)

/-- **Hilbert–Schmidt operators are compact** (Bourbaki, *Théories spectrales* IV §1): the
finite-rank truncations along a Hilbert basis converge in operator norm, with tail error
`√(∑_{i ∉ s} ‖T (b i)‖²)` by Bessel and Cauchy–Schwarz. -/
theorem ContinuousLinearMap.IsHilbertSchmidt.isCompactOperator (hT : T.IsHilbertSchmidt) :
    IsCompactOperator T := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  have hsum : Summable fun i : w => ‖T (b i)‖ ^ 2 := (T.isHilbertSchmidt_iff_summable b).mp hT
  -- finite-rank truncations
  set A : Finset w → (E →L[𝕜] F) :=
    fun s => ∑ i ∈ s, (innerSL 𝕜 (b i : E)).smulRight (T (b i)) with hA
  have hAapp : ∀ (s : Finset w) (x : E), A s x = ∑ i ∈ s, ⟪(b i : E), x⟫_𝕜 • T (b i) := by
    intro s x
    rw [hA]
    simp
  have hAcompact : ∀ s : Finset w, IsCompactOperator (A s) := fun s => by
    have hrange : LinearMap.range (A s : E →ₗ[𝕜] F)
        ≤ Submodule.span 𝕜 (Set.range fun i : s => T (b i)) := by
      rintro y ⟨x, rfl⟩
      have hx : (A s : E →ₗ[𝕜] F) x = ∑ i ∈ s, ⟪(b i : E), x⟫_𝕜 • T (b i) := hAapp s x
      rw [hx]
      refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    have hfin : FiniteDimensional 𝕜
        (Submodule.span 𝕜 (Set.range fun i : s => T (b i))) :=
      FiniteDimensional.span_of_finite _ (Set.finite_range _)
    have : FiniteDimensional 𝕜 (LinearMap.range ((A s : E →L[𝕜] F) : E →ₗ[𝕜] F)) :=
      Submodule.finiteDimensional_of_le hrange
    exact isCompactOperator_of_finiteDimensional_range (A s)
  -- the tail estimate `‖T - A s‖ ≤ √(∑_{i ∉ s} ‖T (b i)‖²)`
  have htail : ∀ s : Finset w,
      ‖T - A s‖ ≤ Real.sqrt (∑' i : {i : w // i ∉ s}, ‖T (b (i : w))‖ ^ 2) := by
    intro s
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    -- basis expansion of `T x`
    have hrep : HasSum (fun i : w => ⟪(b i : E), x⟫_𝕜 • T (b i)) (T x) := by
      have h0 := (b.hasSum_repr x).mapL T
      refine h0.congr_fun fun i => ?_
      rw [map_smul, b.repr_apply_apply]
    -- summability of the coefficient and image squares over the tail
    have hx2 : Summable fun i : {i : w // i ∉ s} => ‖⟪(b (i : w) : E), x⟫_𝕜‖ ^ 2 :=
      (b.orthonormal.inner_products_summable x).subtype _
    have hb2 : Summable fun i : {i : w // i ∉ s} => ‖T (b (i : w))‖ ^ 2 := hsum.subtype _
    have hnorms : Summable fun i : {i : w // i ∉ s} =>
        ‖⟪(b (i : w) : E), x⟫_𝕜‖ * ‖T (b (i : w))‖ := by
      refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
        ((hx2.add hb2).div_const 2)
      have := sq_nonneg (‖⟪(b (i : w) : E), x⟫_𝕜‖ - ‖T (b (i : w))‖)
      nlinarith [norm_nonneg (⟪(b (i : w) : E), x⟫_𝕜), norm_nonneg (T (b (i : w)))]
    -- the difference is the tail series
    have hdiff : (T - A s) x = ∑' i : {i : w // i ∉ s}, ⟪(b (i : w) : E), x⟫_𝕜 • T (b (i : w)) := by
      have hsplit := hrep.summable.sum_add_tsum_compl (s := s)
      rw [hrep.tsum_eq] at hsplit
      rw [_root_.sub_apply, hAapp s x, ← hsplit]
      abel
    rw [hdiff]
    -- Cauchy–Schwarz on the tail
    have hbound : ‖∑' i : {i : w // i ∉ s}, ⟪(b (i : w) : E), x⟫_𝕜 • T (b (i : w))‖
        ≤ ∑' i : {i : w // i ∉ s}, ‖⟪(b (i : w) : E), x⟫_𝕜‖ * ‖T (b (i : w))‖ := by
      refine (norm_tsum_le_tsum_norm ?_).trans_eq (tsum_congr fun i => norm_smul _ _)
      refine hnorms.congr fun i => ?_
      rw [norm_smul]
    have hCS : ∑' i : {i : w // i ∉ s}, ‖⟪(b (i : w) : E), x⟫_𝕜‖ * ‖T (b (i : w))‖
        ≤ Real.sqrt (∑' i : {i : w // i ∉ s}, ‖⟪(b (i : w) : E), x⟫_𝕜‖ ^ 2)
          * Real.sqrt (∑' i : {i : w // i ∉ s}, ‖T (b (i : w))‖ ^ 2) := by
      refine hnorms.tsum_le_of_sum_le fun u => ?_
      calc ∑ i ∈ u, ‖⟪(b (i : w) : E), x⟫_𝕜‖ * ‖T (b (i : w))‖
          ≤ Real.sqrt (∑ i ∈ u, ‖⟪(b (i : w) : E), x⟫_𝕜‖ ^ 2)
            * Real.sqrt (∑ i ∈ u, ‖T (b (i : w))‖ ^ 2) :=
            Real.sum_mul_le_sqrt_mul_sqrt u _ _
        _ ≤ Real.sqrt (∑' i : {i : w // i ∉ s}, ‖⟪(b (i : w) : E), x⟫_𝕜‖ ^ 2)
            * Real.sqrt (∑' i : {i : w // i ∉ s}, ‖T (b (i : w))‖ ^ 2) := by
            refine mul_le_mul (Real.sqrt_le_sqrt ?_) (Real.sqrt_le_sqrt ?_)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
            · exact hx2.sum_le_tsum u (fun i _ => by positivity)
            · exact hb2.sum_le_tsum u (fun i _ => by positivity)
    have hBessel : Real.sqrt (∑' i : {i : w // i ∉ s}, ‖⟪(b (i : w) : E), x⟫_𝕜‖ ^ 2) ≤ ‖x‖ := by
      have hle : ∑' i : {i : w // i ∉ s}, ‖⟪(b (i : w) : E), x⟫_𝕜‖ ^ 2 ≤ ‖x‖ ^ 2 := by
        have hsub : Orthonormal 𝕜 fun i : {i : w // i ∉ s} => (b (i : w) : E) :=
          b.orthonormal.comp _ Subtype.val_injective
        exact hsub.tsum_inner_products_le x
      calc Real.sqrt (∑' i : {i : w // i ∉ s}, ‖⟪(b (i : w) : E), x⟫_𝕜‖ ^ 2)
          ≤ Real.sqrt (‖x‖ ^ 2) := Real.sqrt_le_sqrt hle
        _ = ‖x‖ := Real.sqrt_sq (norm_nonneg x)
    calc ‖∑' i : {i : w // i ∉ s}, ⟪(b (i : w) : E), x⟫_𝕜 • T (b (i : w))‖
        ≤ ∑' i : {i : w // i ∉ s}, ‖⟪(b (i : w) : E), x⟫_𝕜‖ * ‖T (b (i : w))‖ := hbound
      _ ≤ Real.sqrt (∑' i : {i : w // i ∉ s}, ‖⟪(b (i : w) : E), x⟫_𝕜‖ ^ 2)
          * Real.sqrt (∑' i : {i : w // i ∉ s}, ‖T (b (i : w))‖ ^ 2) := hCS
      _ ≤ ‖x‖ * Real.sqrt (∑' i : {i : w // i ∉ s}, ‖T (b (i : w))‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hBessel (Real.sqrt_nonneg _)
      _ = Real.sqrt (∑' i : {i : w // i ∉ s}, ‖T (b (i : w))‖ ^ 2) * ‖x‖ := mul_comm _ _
  -- convergence of the truncations and compactness
  have hlim : Tendsto A atTop (𝓝 T) := by
    rw [← tendsto_sub_nhds_zero_iff]
    have h0 := tendsto_tsum_compl_atTop_zero (fun i : w => ‖T (b i)‖ ^ 2)
    have h1 := (Real.continuous_sqrt.tendsto 0).comp h0
    rw [Real.sqrt_zero] at h1
    refine squeeze_zero_norm'
      (a := fun s : Finset w => Real.sqrt (∑' i : {i : w // i ∉ s}, ‖T (b (i : w))‖ ^ 2)) ?_ h1
    filter_upwards [Filter.univ_mem] with s _
    rw [norm_sub_rev]
    exact htail s
  exact isCompactOperator_of_tendsto hlim (Eventually.of_forall hAcompact)

/-- **A Hilbert–Schmidt map is a square-summable sequence of functionals**: `T` is Hilbert–Schmidt
iff `‖T x‖² = ∑ₙ ‖⟪vₙ, x⟫‖²` for some `v` with `∑ₙ ‖vₙ‖² < ∞`. For `⇒` the `vₙ` enumerate the
countably many nonzero `T† cⱼ`, `c` a Hilbert basis of the target (Parseval). -/
theorem ContinuousLinearMap.isHilbertSchmidt_iff_exists_hasSum_norm_sq :
    T.IsHilbertSchmidt ↔ ∃ v : ℕ → E, Summable (fun n => ‖v n‖ ^ 2) ∧
      ∀ x, HasSum (fun n => ‖⟪v n, x⟫_𝕜‖ ^ 2) (‖T x‖ ^ 2) := by
  obtain ⟨κ, b, -⟩ := exists_hilbertBasis 𝕜 E
  have hofreal : ∀ y : E, (‖y‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := fun y => by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have hofreal' : ∀ a : 𝕜, (‖a‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖a‖ ^ 2) := fun a => by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have hofrealF : ∀ y : F, (‖y‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := fun y => by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  constructor
  · intro hT
    obtain ⟨κ', c, -⟩ := exists_hilbertBasis 𝕜 F
    set w : κ' → E := fun j => ContinuousLinearMap.adjoint T (c j) with hw
    have hws : Summable fun j => ‖w j‖ ^ 2 := by
      rw [← c.tsum_enorm_sq_map_lt_top_iff (ContinuousLinearMap.adjoint T),
        ← b.tsum_enorm_sq_map_eq_adjoint T c, b.tsum_enorm_sq_map_lt_top_iff T]
      exact (T.isHilbertSchmidt_iff_summable b).1 hT
    have hTw : ∀ x, HasSum (fun j => ‖⟪w j, x⟫_𝕜‖ ^ 2) (‖T x‖ ^ 2) := fun x => by
      simpa only [hw, ContinuousLinearMap.adjoint_inner_left] using c.hasSum_norm_sq_inner (T x)
    -- enumerate the countable support of `w`
    have hsupp : (Function.support w).Countable := by
      simpa [Function.support] using hws.countable_support
    obtain ⟨e, he⟩ := Set.countable_iff_exists_injective.1 hsupp
    set v : ℕ → E := Function.extend e (fun s => w s) 0 with hv
    have key : ∀ g : E → ℝ, g 0 = 0 → ∀ a, HasSum (g ∘ v) a ↔ HasSum (g ∘ w) a := by
      intro g g0 a
      rw [← he.hasSum_iff fun n hn => by
          simp [hv, Function.extend_apply' _ _ _ hn, g0],
        ← hasSum_subtype_iff_of_support_subset (s := Function.support w) fun j hj => by
          by_contra h
          exact hj (by simp [Function.notMem_support.1 h, g0])]
      congr! 1
      ext s
      simp [hv, he.extend_apply]
    exact ⟨v, ((key (fun u => ‖u‖ ^ 2) (by simp) _).2 hws.hasSum).summable,
      fun x => (key (fun u => ‖⟪u, x⟫_𝕜‖ ^ 2) (by simp) _).2 (hTw x)⟩
  · rintro ⟨v, hv, hTv⟩
    rw [T.isHilbertSchmidt_iff_summable b, ← b.tsum_enorm_sq_map_lt_top_iff T]
    calc ∑' i, (‖T (b i)‖ₑ : ℝ≥0∞) ^ 2 = ∑' i, ∑' n, (‖⟪v n, b i⟫_𝕜‖ₑ : ℝ≥0∞) ^ 2 := by
          refine tsum_congr fun i => ?_
          rw [hofrealF, ← (hTv (b i)).tsum_eq,
            ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hTv (b i)).summable]
          exact tsum_congr fun n => (hofreal' _).symm
      _ = ∑' n, ∑' i, (‖⟪b i, v n⟫_𝕜‖ₑ : ℝ≥0∞) ^ 2 := by
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun n => tsum_congr fun i => ?_
          rw [hofreal', hofreal', norm_inner_symm]
      _ = ∑' n, (‖v n‖ₑ : ℝ≥0∞) ^ 2 := tsum_congr fun n => b.tsum_enorm_sq_inner (v n)
      _ < ⊤ := by
          rw [tsum_congr fun n => hofreal (v n),
            ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hv]
          exact ENNReal.ofReal_lt_top

end Core

/-! ### Nuclear maps into a Hilbert space factor through a Hilbert–Schmidt map -/

namespace ContinuousLinearMap

open scoped lp

variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **A nuclear map into a Hilbert space factors through a Hilbert–Schmidt map**: `u = S ∘ j` with
`j : E →L[𝕜] ℓ²(ℕ, 𝕜)` continuous and `S` Hilbert–Schmidt. For `u = ∑ᵢ fᵢ(·) yᵢ`,
`j x = (√‖yᵢ‖ fᵢ x)ᵢ` and `S eᵢ = yᵢ / √‖yᵢ‖`; cf. [Gel'fand–Vilenkin, IV, Ch. I, §2.3,
Thm 4][gelfand1964generalized4], where `E` is a Hilbert space and `j` Hilbert–Schmidt as well. -/
theorem IsNuclear.exists_isHilbertSchmidt_comp {u : E →L[𝕜] F} (hu : u.IsNuclear) :
    ∃ (j : E →L[𝕜] ℓ²(ℕ, 𝕜)) (S : ℓ²(ℕ, 𝕜) →L[𝕜] F), S.IsHilbertSchmidt ∧ S.comp j = u := by
  obtain ⟨R⟩ := hu
  have ha : ∀ i, √‖R.vec i‖ ^ 2 = ‖R.vec i‖ := fun i ↦ Real.sq_sqrt (norm_nonneg _)
  -- `yᵢ = √‖yᵢ‖ • zᵢ` with `‖zᵢ‖² = ‖yᵢ‖`
  obtain ⟨z, hz⟩ : ∃ z : ℕ → F, ∀ i, z i = ((√‖R.vec i‖ : 𝕜))⁻¹ • R.vec i := ⟨_, fun _ ↦ rfl⟩
  have hvec : ∀ i, (√‖R.vec i‖ : 𝕜) • z i = R.vec i := fun i ↦ by
    by_cases h : R.vec i = 0
    · rw [hz i, h, smul_zero, smul_zero]
    · rw [hz i, smul_smul, mul_inv_cancel₀ (RCLike.ofReal_ne_zero.2
        (Real.sqrt_ne_zero'.2 (norm_pos_iff.2 h))), one_smul]
  have hz2 : ∀ i, ‖z i‖ ^ 2 = ‖R.vec i‖ := fun i ↦ by
    by_cases h : R.vec i = 0
    · simp [hz i, h]
    · rw [hz i, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _),
        mul_pow, inv_pow, ha, sq, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.2 h), one_mul]
  -- `S` is the adjoint of `h ↦ (⟪zᵢ, h⟫)ᵢ`, so `S eᵢ = zᵢ`
  have hle : ∀ h : F, ∀ i, ‖⟪z i, h⟫_𝕜‖ ^ 2 ≤ ‖R.vec i‖ * ‖h‖ ^ 2 := fun h i ↦ by
    rw [← hz2, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
  have hsumT : ∀ h : F, Summable fun i ↦ ‖⟪z i, h⟫_𝕜‖ ^ 2 := fun h ↦
    (R.summable_norm_vec.mul_right _).of_nonneg_of_le (fun _ ↦ by positivity) (hle h)
  have hmemT : ∀ h : F, Memℓp (fun i ↦ ⟪z i, h⟫_𝕜) 2 := fun h ↦ memℓp_gen <| by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hsumT h
  let T : F →L[𝕜] ℓ²(ℕ, 𝕜) := LinearMap.mkContinuous
    { toFun := fun h ↦ ⟨fun i ↦ ⟪z i, h⟫_𝕜, hmemT h⟩
      map_add' := fun h h' ↦ lp.ext <| funext fun i ↦ inner_add_right _ _ _
      map_smul' := fun c h ↦ lp.ext <| funext fun i ↦ inner_smul_right _ _ _ }
    (√(∑' i, ‖R.vec i‖)) fun h ↦ by
      refine lp.norm_le_of_tsum_le (by norm_num) (by positivity) ?_
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, mul_pow,
        Real.sq_sqrt (tsum_nonneg fun i ↦ norm_nonneg (R.vec i)), ← tsum_mul_right]
      exact Summable.tsum_le_tsum (hle h) (hsumT h) (R.summable_norm_vec.mul_right _)
  have hSe : ∀ i, adjoint T (lp.single 2 i 1) = z i := fun i ↦ ext_inner_right 𝕜 fun h ↦ by
    rw [adjoint_inner_left, lp.inner_single_left]
    simp [T, RCLike.inner_apply]
  have hS : (adjoint T).IsHilbertSchmidt := by
    refine (isHilbertSchmidt_iff_summable _ (default : HilbertBasis ℕ 𝕜 ℓ²(ℕ, 𝕜))).2 ?_
    have hb : ∀ i, (default : HilbertBasis ℕ 𝕜 ℓ²(ℕ, 𝕜)) i = lp.single 2 i 1 := fun i ↦
      (HilbertBasis.repr_symm_single _ i).symm
    simpa only [hb, hSe, hz2] using R.summable_norm_vec
  -- `j x = (√‖yᵢ‖ fᵢ x)ᵢ`, bounded by the seminorm of the representation
  have hlej : ∀ x, ∀ i, ‖(√‖R.vec i‖ : 𝕜) * R.func i x‖ ^ 2 ≤ ‖R.vec i‖ * R.seminorm x ^ 2 :=
    fun x i ↦ by
      rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, ha]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (R.norm_func_le i x) 2) (norm_nonneg _)
  have hsumj : ∀ x, Summable fun i ↦ ‖(√‖R.vec i‖ : 𝕜) * R.func i x‖ ^ 2 := fun x ↦
    (R.summable_norm_vec.mul_right _).of_nonneg_of_le (fun _ ↦ by positivity) (hlej x)
  have hmemj : ∀ x, Memℓp (fun i ↦ (√‖R.vec i‖ : 𝕜) * R.func i x) 2 := fun x ↦ memℓp_gen <| by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hsumj x
  let jₗ : E →ₗ[𝕜] ℓ²(ℕ, 𝕜) :=
    { toFun := fun x ↦ ⟨fun i ↦ (√‖R.vec i‖ : 𝕜) * R.func i x, hmemj x⟩
      map_add' := fun x y ↦ lp.ext <| funext fun i ↦
        (congrArg (_ * ·) (map_add (R.func i) x y)).trans (mul_add _ _ _)
      map_smul' := fun c x ↦ lp.ext <| funext fun i ↦
        (congrArg (_ * ·) (map_smul (R.func i) c x)).trans (mul_left_comm _ _ _) }
  have hj : ∀ x, ‖jₗ x‖ ≤ √(∑' i, ‖R.vec i‖) * R.seminorm x := fun x ↦ by
    refine lp.norm_le_of_tsum_le (by norm_num) (by positivity) ?_
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, mul_pow,
      Real.sq_sqrt (tsum_nonneg fun i ↦ norm_nonneg (R.vec i)), ← tsum_mul_right]
    exact Summable.tsum_le_tsum (hlej x) (hsumj x) (R.summable_norm_vec.mul_right _)
  let j : E →L[𝕜] ℓ²(ℕ, 𝕜) := ⟨jₗ, jₗ.continuous_of_le_mul_seminorm (Real.sqrt_nonneg _)
    R.seminorm R.continuous_seminorm hj⟩
  refine ⟨j, adjoint T, hS, ContinuousLinearMap.ext fun x ↦ ?_⟩
  -- `S (j x) = ∑ᵢ √‖yᵢ‖ fᵢ(x) zᵢ = ∑ᵢ fᵢ(x) yᵢ = u x`
  have hterm : ∀ i, adjoint T (lp.single 2 i (j x i)) = R.func i x • R.vec i := fun i ↦ by
    have h1 : (lp.single 2 i (j x i) : ℓ²(ℕ, 𝕜)) = j x i • lp.single 2 i (1 : 𝕜) := by
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [h1, map_smul, hSe, ← hvec i, smul_smul, mul_comm (R.func i x)]
    rfl
  have h := (lp.hasSum_single ENNReal.ofNat_ne_top (j x)).mapL (adjoint T)
  simp only [hterm] at h
  exact h.unique (R.hasSum x)

end ContinuousLinearMap
