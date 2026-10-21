/-
Copyright (c) 2026 Axiomatic AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Nuclear maps

A continuous linear map `u` from a topological vector space `E` into a normed space `F` is
*nuclear* if it is an absolutely summable series of rank-one maps whose functionals are all bounded
by one continuous seminorm:

  `u = ∑ᵢ ⟨·, fᵢ⟩ yᵢ`,   `‖fᵢ x‖ ≤ p x`,   `∑ᵢ ‖yᵢ‖ < ∞`.

This is [Bourbaki, *EVT*, VII, §1, no. 1, déf. 1][bourbaki2023evt] for a normed target, in the
normalised form of its remarks 2–4: the index set is `ℕ`, the equicontinuous family of functionals
is expressed by one continuous seminorm, and the summable scalars are absorbed into the vectors.
A choice of such data is Bourbaki's *écriture nucléaire*, `NuclearRep`; the theorems that use a
nuclear map consume the data, which is why it is a structure and `IsNuclear` is its nonemptiness.

The notion is one the rigged Hilbert space rests on. The inclusion `Φ → H` of a rigged Hilbert
space is nuclear [Gould 1968, 2.9][gould1968spectral], hence factors through a Hilbert–Schmidt map
(`ContinuousLinearMap.IsNuclear.exists_isHilbertSchmidt_comp`), which is all the spectral theorem
needs to yield generalized eigenvectors on `Φ`; and a nuclear space is one on which every
continuous linear map into a Banach space is nuclear [Bourbaki, *EVT*, VII, §4, no. 1,
déf. 1][bourbaki2023evt]. Stating the hypothesis on the map rather than on the space is what keeps
it verifiable: for a concrete rigging it is one estimate, where nuclearity of the space quantifies
over all Banach targets.

## Main definitions and results

* `ContinuousLinearMap.NuclearRep`, `ContinuousLinearMap.IsNuclear`
* `ContinuousLinearMap.NuclearRep.ofCountable`: a representation indexed by any countable type
* `ContinuousLinearMap.NuclearRep.norm_apply_le`: a nuclear map is dominated by a continuous
  seminorm
* `ContinuousLinearMap.IsNuclear.comp_left`, `ContinuousLinearMap.IsNuclear.comp_right`:
  composing with continuous maps on either side preserves nuclearity
* `ContinuousLinearMap.isNuclear_zero`, `ContinuousLinearMap.IsNuclear.add`,
  `ContinuousLinearMap.IsNuclear.smul`, `ContinuousLinearMap.isNuclear_smulRight`: the nuclear
  maps form a subspace containing the rank-one maps

## Provenance

Ported from or4nge19/QuantumlibCore `pin-v4.34.1` `9a741c08`,
`QuantumlibCore/ToMathlib/Analysis/LocallyConvex/NuclearMap.lean` (Lean v4.34.1, Mathlib
`d13f23b7`), with module paths renamed; notices kept.
-/

@[expose] public section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {D E : Type*} [AddCommGroup D] [Module 𝕜 D] [TopologicalSpace D]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A **nuclear representation** of `u` — Bourbaki's *écriture nucléaire*: functionals `func i`
all bounded by one continuous seminorm, and vectors `vec i` with summable norms, such that
`u x = ∑ᵢ func i x • vec i` for every `x`. -/
structure NuclearRep (u : E →L[𝕜] F) where
  /-- The continuous seminorm bounding every functional. -/
  seminorm : Seminorm 𝕜 E
  continuous_seminorm : Continuous seminorm
  /-- The functionals. -/
  func : ℕ → E →L[𝕜] 𝕜
  /-- The vectors. -/
  vec : ℕ → F
  norm_func_le : ∀ i x, ‖func i x‖ ≤ seminorm x
  summable_norm_vec : Summable fun i ↦ ‖vec i‖
  hasSum : ∀ x, HasSum (fun i ↦ func i x • vec i) (u x)

/-- `u` is **nuclear** [Bourbaki, *EVT*, VII, §1, no. 1, déf. 1][bourbaki2023evt]: it has a
nuclear representation. -/
def IsNuclear (u : E →L[𝕜] F) : Prop :=
  Nonempty (NuclearRep u)

namespace NuclearRep

variable {u v : E →L[𝕜] F}

theorem summable_norm_smul (R : NuclearRep u) (x : E) :
    Summable fun i ↦ ‖R.func i x • R.vec i‖ :=
  (R.summable_norm_vec.mul_left (R.seminorm x)).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    fun i ↦ by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (R.norm_func_le i x) (norm_nonneg _)

/-- **A nuclear map is dominated by a continuous seminorm**, with the constant `∑ᵢ ‖yᵢ‖`. -/
theorem norm_apply_le (R : NuclearRep u) (x : E) :
    ‖u x‖ ≤ (∑' i, ‖R.vec i‖) * R.seminorm x := by
  calc ‖u x‖ = ‖∑' i, R.func i x • R.vec i‖ := by rw [(R.hasSum x).tsum_eq]
    _ ≤ ∑' i, ‖R.func i x • R.vec i‖ := norm_tsum_le_tsum_norm (R.summable_norm_smul x)
    _ ≤ ∑' i, R.seminorm x * ‖R.vec i‖ :=
        (R.summable_norm_smul x).tsum_le_tsum (fun i ↦ by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_right (R.norm_func_le i x) (norm_nonneg _))
          (R.summable_norm_vec.mul_left _)
    _ = (∑' i, ‖R.vec i‖) * R.seminorm x := by rw [tsum_mul_left, mul_comm]

/-- Composing on the left with a continuous linear map: the vectors are carried along. -/
def compLeft (R : NuclearRep u) (w : F →L[𝕜] G) : NuclearRep (w.comp u) where
  seminorm := R.seminorm
  continuous_seminorm := R.continuous_seminorm
  func := R.func
  vec i := w (R.vec i)
  norm_func_le := R.norm_func_le
  summable_norm_vec :=
    (R.summable_norm_vec.mul_left ‖w‖).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      fun i ↦ w.le_opNorm (R.vec i)
  hasSum x := by
    simpa [map_smul] using (R.hasSum x).mapL w

/-- Composing on the right with a continuous linear map: the seminorm and the functionals are
pulled back. -/
def compRight (R : NuclearRep u) (w : D →L[𝕜] E) : NuclearRep (u.comp w) where
  seminorm := R.seminorm.comp w.toLinearMap
  continuous_seminorm := R.continuous_seminorm.comp w.continuous
  func i := (R.func i).comp w
  vec := R.vec
  norm_func_le i x := R.norm_func_le i (w x)
  summable_norm_vec := R.summable_norm_vec
  hasSum x := R.hasSum (w x)

/-- Scaling a nuclear map scales its vectors. -/
def smul (R : NuclearRep u) (c : 𝕜) : NuclearRep (c • u) where
  seminorm := R.seminorm
  continuous_seminorm := R.continuous_seminorm
  func := R.func
  vec i := c • R.vec i
  norm_func_le := R.norm_func_le
  summable_norm_vec := by
    simpa [norm_smul] using R.summable_norm_vec.mul_left ‖c‖
  hasSum x := by
    simpa [smul_comm c] using (R.hasSum x).const_smul c

/-- The sum of two nuclear maps: the two representations are interleaved, and bounded by the sum
of their seminorms. -/
def add (R : NuclearRep u) (S : NuclearRep v) : NuclearRep (u + v) where
  seminorm := R.seminorm + S.seminorm
  continuous_seminorm := by
    simpa only [FunLike.coe_add] using R.continuous_seminorm.add S.continuous_seminorm
  func n := if Even n then R.func (n / 2) else S.func (n / 2)
  vec n := if Even n then R.vec (n / 2) else S.vec (n / 2)
  norm_func_le n x := by
    split_ifs
    · exact (R.norm_func_le _ x).trans (le_add_of_nonneg_right (apply_nonneg _ x))
    · exact (S.norm_func_le _ x).trans (le_add_of_nonneg_left (apply_nonneg _ x))
  summable_norm_vec := by
    refine Summable.even_add_odd ?_ ?_
    · simpa [Nat.even_mul] using R.summable_norm_vec
    · have h : ∀ k : ℕ, (2 * k + 1) / 2 = k := fun k ↦ by omega
      simpa [Nat.even_add_one, Nat.even_mul, h] using S.summable_norm_vec
  hasSum x := by
    refine HasSum.even_add_odd ?_ ?_
    · simpa [Nat.even_mul] using R.hasSum x
    · have h : ∀ k : ℕ, (2 * k + 1) / 2 = k := fun k ↦ by omega
      simpa [Nat.even_add_one, Nat.even_mul, h] using S.hasSum x

/-- A nuclear representation over **any countable index type**. Bourbaki's definition takes an
arbitrary index set, whose nonzero terms are then countable (rem. 2); here the terms are carried
to `ℕ` along an injection and extended by zero, so a natural indexing — by a Hilbert basis, say —
can be used directly. -/
noncomputable def ofCountable {ι : Type*} [Countable ι] (p : Seminorm 𝕜 E) (hp : Continuous p)
    (f : ι → E →L[𝕜] 𝕜) (y : ι → F) (hf : ∀ i x, ‖f i x‖ ≤ p x)
    (hy : Summable fun i ↦ ‖y i‖) (hu : ∀ x, HasSum (fun i ↦ f i x • y i) (u x)) :
    NuclearRep u :=
  have he := (Countable.exists_injective_nat ι).choose_spec
  let e := (Countable.exists_injective_nat ι).choose
  { seminorm := p
    continuous_seminorm := hp
    func := Function.extend e f 0
    vec := Function.extend e y 0
    norm_func_le := fun n x ↦ by
      by_cases hn : ∃ i, e i = n
      · obtain ⟨i, rfl⟩ := hn
        rw [he.extend_apply]
        exact hf i x
      · rw [Function.extend_apply' _ _ _ hn]
        simp
    summable_norm_vec := by
      have h : (fun n ↦ ‖Function.extend e y 0 n‖) = Function.extend e (fun i ↦ ‖y i‖) 0 := by
        funext n
        by_cases hn : ∃ i, e i = n
        · obtain ⟨i, rfl⟩ := hn
          rw [he.extend_apply, he.extend_apply]
        · rw [Function.extend_apply' _ _ _ hn, Function.extend_apply' _ _ _ hn]
          simp
      rw [h]
      exact (summable_extend_zero he).2 hy
    hasSum := fun x ↦ by
      have h : (fun n ↦ Function.extend e f 0 n x • Function.extend e y 0 n)
          = Function.extend e (fun i ↦ f i x • y i) 0 := by
        funext n
        by_cases hn : ∃ i, e i = n
        · obtain ⟨i, rfl⟩ := hn
          rw [he.extend_apply, he.extend_apply, he.extend_apply]
        · rw [Function.extend_apply' _ _ _ hn, Function.extend_apply' _ _ _ hn,
            Function.extend_apply' _ _ _ hn]
          simp
      rw [h]
      exact (hasSum_extend_zero he).2 (hu x) }

end NuclearRep

variable {u v : E →L[𝕜] F}

theorem IsNuclear.comp_left (hu : u.IsNuclear) (w : F →L[𝕜] G) : (w.comp u).IsNuclear :=
  let ⟨R⟩ := hu; ⟨R.compLeft w⟩

theorem IsNuclear.comp_right (hu : u.IsNuclear) (w : D →L[𝕜] E) : (u.comp w).IsNuclear :=
  let ⟨R⟩ := hu; ⟨R.compRight w⟩

theorem IsNuclear.smul (hu : u.IsNuclear) (c : 𝕜) : (c • u).IsNuclear :=
  let ⟨R⟩ := hu; ⟨R.smul c⟩

theorem IsNuclear.add (hu : u.IsNuclear) (hv : v.IsNuclear) : (u + v).IsNuclear :=
  let ⟨R⟩ := hu; let ⟨S⟩ := hv; ⟨R.add S⟩

/-- A nuclear map is dominated by a continuous seminorm. -/
theorem IsNuclear.exists_seminorm (hu : u.IsNuclear) :
    ∃ p : Seminorm 𝕜 E, Continuous p ∧ ∀ x, ‖u x‖ ≤ p x := by
  obtain ⟨R⟩ := hu
  refine ⟨(∑' i, ‖R.vec i‖).toNNReal • R.seminorm, ?_, fun x ↦ ?_⟩
  · rw [FunLike.coe_smul]
    exact R.continuous_seminorm.const_smul (∑' i, ‖R.vec i‖).toNNReal
  · rw [smul_apply, NNReal.smul_def, Real.coe_toNNReal _ (tsum_nonneg fun _ ↦
      norm_nonneg _), smul_eq_mul]
    exact R.norm_apply_le x

variable (𝕜 E F) in
theorem isNuclear_zero : (0 : E →L[𝕜] F).IsNuclear :=
  ⟨{ seminorm := 0
     continuous_seminorm := by simpa only [FunLike.coe_zero] using continuous_zero
     func := 0
     vec := 0
     norm_func_le := fun _ _ ↦ by simp
     summable_norm_vec := by simp
     hasSum := fun _ ↦ by simp }⟩

/-- **A rank-one map is nuclear**: one term, bounded by the seminorm `‖f ·‖`. -/
theorem isNuclear_smulRight (f : E →L[𝕜] 𝕜) (y : F) : (f.smulRight y).IsNuclear :=
  ⟨{ seminorm := (normSeminorm 𝕜 𝕜).comp f.toLinearMap
     continuous_seminorm := continuous_norm.comp f.continuous
     func := fun i ↦ if i = 0 then f else 0
     vec := fun i ↦ if i = 0 then y else 0
     norm_func_le := fun i x ↦ by split_ifs <;> simp
     summable_norm_vec := by
       refine (hasSum_ite_eq 0 ‖y‖).summable.congr fun i ↦ ?_
       split_ifs <;> simp_all
     hasSum := fun x ↦ by
       refine (hasSum_ite_eq 0 (f x • y)).congr_fun fun i ↦ ?_
       split_ifs <;> simp_all }⟩

end ContinuousLinearMap
