/-
Copyright (c) 2026 Axiomatic AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Continuity from one seminorm bound

A linear map from a topological vector space into a normed space is continuous as soon as its
norm is dominated by a continuous seminorm.

## Provenance

Ported from or4nge19/QuantumlibCore `pin-v4.34.1` `9a741c08`,
`QuantumlibCore/ToMathlib/Analysis/LocallyConvex/WithSeminorms.lean` (Lean v4.34.1, Mathlib
`d13f23b7`), with module paths renamed; notices kept.
-/

@[expose] public section

variable {𝕜 X G : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup X] [Module 𝕜 X]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem LinearMap.continuous_of_le_seminorm (L : X →ₗ[𝕜] G) (P : Seminorm 𝕜 X)
    (hP : Continuous P) (h : ∀ x, ‖L x‖ ≤ P x) : Continuous L :=
  (norm_withSeminorms 𝕜 G).continuous_of_continuous_comp L fun _ ↦
    Seminorm.continuous_of_le hP fun x ↦ h x

theorem LinearMap.continuous_of_le_mul_seminorm (L : X →ₗ[𝕜] G) {K : ℝ} (hK : 0 ≤ K)
    (P : Seminorm 𝕜 X) (hP : Continuous P) (h : ∀ x, ‖L x‖ ≤ K * P x) : Continuous L :=
  L.continuous_of_le_seminorm (K.toNNReal • P)
    (by
      rw [FunLike.coe_smul]
      exact hP.const_smul K.toNNReal)
    fun x ↦ by simpa [NNReal.smul_def, Real.coe_toNNReal _ hK] using h x
