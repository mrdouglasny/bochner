/-
Copyright (c) 2026 Axiomatic AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive semidefiniteness on finite submatrices

A matrix indexed by an arbitrary type is positive semidefinite exactly when its finite principal
submatrices `M.submatrix e e`, `e : Fin k → n`, are: the quadratic form only sees the finite
support of the test vector. So positive definiteness of a function on a group,
`(Matrix.circulant φ).PosSemidef`, is checked and used on finitely many points.

## Provenance

Ported from or4nge19/QuantumlibCore `pin-v4.34.1` `9a741c08`,
`QuantumlibCore/ToMathlib/LinearAlgebra/Matrix/PosDef.lean` (Lean v4.34.1, Mathlib `d13f23b7`), with
module paths renamed; notices kept.
-/

@[expose] public section

namespace Matrix

variable {n R : Type*} [Ring R] [PartialOrder R] [StarRing R]

theorem posSemidef_iff_forall_fin {M : Matrix n n R} :
    M.PosSemidef ↔ ∀ (k : ℕ) (e : Fin k → n), (M.submatrix e e).PosSemidef := by
  refine ⟨fun h k e ↦ h.submatrix e, fun h ↦ ⟨IsHermitian.ext fun i j ↦ ?_, fun x ↦ ?_⟩⟩
  · simpa using (h 2 ![i, j]).1.apply 0 1
  · classical
    set e : Fin x.support.card → n := fun i ↦ x.support.equivFin.symm i with he
    have he_inj : Function.Injective e := fun a b hab ↦
      x.support.equivFin.symm.injective (Subtype.ext hab)
    have hx : x = (Finsupp.equivFunOnFinite.symm fun i ↦ x (e i)).mapDomain e := by
      ext j
      by_cases hj : j ∈ x.support
      · obtain ⟨i, rfl⟩ : ∃ i, e i = j := ⟨x.support.equivFin ⟨j, hj⟩, by simp [he]⟩
        rw [Finsupp.mapDomain_apply_of_injective he_inj]
        rfl
      · rw [Finsupp.notMem_support_iff.1 hj, Finsupp.mapDomain_of_notMem_range]
        rintro ⟨i, rfl⟩
        exact hj (x.support.equivFin.symm i).2
    rw [hx]
    simpa [Finsupp.sum_mapDomain_index, add_mul, mul_add] using
      (h _ e).2 (Finsupp.equivFunOnFinite.symm fun i ↦ x (e i))

end Matrix
