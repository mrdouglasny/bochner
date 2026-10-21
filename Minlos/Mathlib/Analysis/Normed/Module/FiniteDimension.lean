/-
Copyright (c) 2026 Axiomatic AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Total boundedness by finite-dimensional approximation

Over a locally compact field, a subset of a normed space is totally bounded iff it is bounded and
lies uniformly close to finite-dimensional subspaces: the approximants form a bounded, hence totally
bounded, subset of a proper space. In a Hilbert space this is compactness of closed bounded sets
with uniformly small tails in an orthonormal basis, the criterion behind the tightness of measures.

## Provenance

Ported from or4nge19/QuantumlibCore `pin-v4.34.1` `9a741c08`,
`QuantumlibCore/ToMathlib/Analysis/Normed/Module/FiniteDimension.lean` (Lean v4.34.1, Mathlib
`d13f23b7`), with module paths renamed; notices kept.
-/

@[expose] public section

open Metric

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem totallyBounded_iff_forall_exists_finiteDimensional {A : Set E} :
    TotallyBounded A ↔ Bornology.IsBounded A ∧
      ∀ ε > 0, ∃ F : Submodule 𝕜 E, FiniteDimensional 𝕜 F ∧ ∀ a ∈ A, ∃ f ∈ F, dist a f < ε := by
  refine ⟨fun hA ↦ ⟨hA.isBounded, fun ε hε ↦ ?_⟩, fun ⟨hA, h⟩ ↦ totallyBounded_iff.2 fun ε hε ↦ ?_⟩
  · obtain ⟨t, htf, hAt⟩ := totallyBounded_iff.1 hA ε hε
    refine ⟨Submodule.span 𝕜 t, FiniteDimensional.span_of_finite 𝕜 htf, fun a ha ↦ ?_⟩
    obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.1 (hAt ha)
    exact ⟨y, Submodule.subset_span hyt, hy⟩
  obtain ⟨F, hF, hAF⟩ := h (ε / 2) (half_pos hε)
  have := FiniteDimensional.proper 𝕜 F
  choose! g hgF hg using hAF
  obtain ⟨R, hR⟩ := hA.subset_closedBall 0
  have hB : Bornology.IsBounded {f : F | ∃ a ∈ A, (f : E) = g a} := by
    refine (isBounded_closedBall (x := (0 : F)) (r := R + ε / 2)).subset fun f ⟨a, ha, hfa⟩ ↦ ?_
    rw [mem_closedBall, dist_zero_right, ← Submodule.norm_coe, hfa]
    calc ‖g a‖ ≤ ‖a‖ + ‖g a - a‖ := norm_le_insert' _ _
      _ ≤ R + ε / 2 := by
        gcongr
        · simpa using hR ha
        · rw [← dist_eq_norm, dist_comm]
          exact (hg a ha).le
  obtain ⟨t, htf, htB⟩ := totallyBounded_iff.1
    (hB.isCompact_closure.totallyBounded.subset subset_closure) (ε / 2) (half_pos hε)
  refine ⟨(↑) '' t, htf.image _, fun a ha ↦ ?_⟩
  obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.1 (htB (a := ⟨g a, hgF a ha⟩) ⟨a, ha, rfl⟩)
  refine Set.mem_iUnion₂.2 ⟨y, Set.mem_image_of_mem _ hyt, ?_⟩
  rw [mem_ball] at hy ⊢
  calc dist a y ≤ dist a (g a) + dist (g a) y := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hg a ha) hy
    _ = ε := add_halves ε
