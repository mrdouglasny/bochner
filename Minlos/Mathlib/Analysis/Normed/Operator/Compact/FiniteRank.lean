/-
Copyright (c) 2026 Axiomatic AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Finite-rank operators are compact

A continuous linear map with finite-dimensional range over a locally compact field is a compact
operator ([Bourbaki, *Théories spectrales*, III §1 no. 1][bourbaki2023spectral]).

## Provenance

Ported from or4nge19/QuantumlibCore `pin-v4.34.1` `9a741c08`,
`QuantumlibCore/ToMathlib/Analysis/Normed/Operator/Compact/FiniteRank.lean` (Lean v4.34.1, Mathlib
`d13f23b7`), with module paths renamed; notices kept.
-/

@[expose] public section

open Bornology

/-- **A continuous linear map with finite-dimensional range is compact.** -/
theorem isCompactOperator_of_finiteDimensional_range {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [LocallyCompactSpace 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] (f : E →L[𝕜] F) [FiniteDimensional 𝕜 (LinearMap.range (f : E →ₗ[𝕜] F))] :
    IsCompactOperator f := by
  have : ProperSpace (LinearMap.range (f : E →ₗ[𝕜] F)) := FiniteDimensional.proper 𝕜 _
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  refine ⟨Metric.ball 0 1, Metric.ball_mem_nhds _ one_pos,
    Subtype.val '' closure (f.rangeRestrict '' Metric.ball 0 1), ?_, ?_⟩
  · refine (IsBounded.isCompact_closure ?_).image continuous_subtype_val
    refine (isBounded_iff_forall_norm_le.mpr ⟨‖f‖, fun y hy => ?_⟩)
    obtain ⟨x, hx, rfl⟩ := hy
    change ‖f x‖ ≤ ‖f‖
    calc ‖f x‖ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
      _ ≤ ‖f‖ * 1 := by gcongr; simpa using (Metric.mem_ball.mp hx).le
      _ = ‖f‖ := mul_one _
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨f.rangeRestrict x, subset_closure ⟨x, hx, rfl⟩, rfl⟩
