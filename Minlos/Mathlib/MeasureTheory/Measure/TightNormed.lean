/-
Copyright (c) 2026 Axiomatic AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.Topology.MetricSpace.Thickening
public import Minlos.Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Tightness by flat concentration

In a Banach space over a locally compact field, a set of measures is tight iff it is bounded in
measure and uniformly concentrated near finite-dimensional subspaces: the compact sets are the
closed bounded sets lying uniformly close to finite-dimensional subspaces
(`totallyBounded_iff_forall_exists_finiteDimensional`). Mathlib's criteria
(`MeasureTheory.isTightMeasureSet_iff_tendsto_measure_norm_gt`) need a proper space.

## Provenance

Ported from or4nge19/QuantumlibCore `pin-v4.34.1` `9a741c08`,
`QuantumlibCore/ToMathlib/MeasureTheory/Measure/TightNormed.lean` (Lean v4.34.1, Mathlib
`d13f23b7`), with module paths renamed; notices kept.
-/

@[expose] public section

open Metric Filter
open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {mE : MeasurableSpace E}

/-- **Flat concentration**: a set of measures on a Banach space over a locally compact field is
tight iff it is bounded in measure and uniformly concentrated near finite-dimensional subspaces. -/
theorem isTightMeasureSet_iff_forall_exists_finiteDimensional {S : Set (Measure E)} :
    IsTightMeasureSet S ↔ (∀ ε > 0, ∃ R, ∀ μ ∈ S, μ {x | R < ‖x‖} ≤ ε) ∧
      ∀ δ > 0, ∀ ε > 0, ∃ F : Submodule 𝕜 E, FiniteDimensional 𝕜 F ∧
        ∀ μ ∈ S, μ (cthickening δ (F : Set E))ᶜ ≤ ε := by
  simp_rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  refine ⟨fun h ↦ ⟨fun ε hε ↦ ?_, fun δ hδ ε hε ↦ ?_⟩, fun ⟨hb, hf⟩ ε hε ↦ ?_⟩
  · obtain ⟨K, hK, hKS⟩ := h ε hε
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    refine ⟨R, fun μ hμ ↦ (measure_mono ?_).trans (hKS μ hμ)⟩
    intro x (hx : R < ‖x‖) hxK
    have := hR hxK
    rw [mem_closedBall, dist_zero_right] at this
    exact (not_le.2 hx) this
  · obtain ⟨K, hK, hKS⟩ := h ε hε
    obtain ⟨-, hF⟩ := (totallyBounded_iff_forall_exists_finiteDimensional (𝕜 := 𝕜)).1
      hK.totallyBounded
    obtain ⟨F, hFd, hKF⟩ := hF δ hδ
    refine ⟨F, hFd, fun μ hμ ↦ (measure_mono ?_).trans (hKS μ hμ)⟩
    intro x hx hxK
    refine hx ?_
    obtain ⟨f, hfF, hxf⟩ := hKF x hxK
    exact mem_cthickening_of_dist_le x f δ F hfF hxf.le
  · obtain ⟨ε', hε'0, hε'⟩ := ENNReal.exists_pos_sum_of_countable' (ENNReal.half_pos hε.ne').ne' ℕ
    obtain ⟨R, hR⟩ := hb (ε / 2) (ENNReal.half_pos hε.ne')
    choose F hFd hFS using fun k : ℕ ↦ hf (1 / (k + 1)) (by positivity) (ε' k) (hε'0 k)
    -- the compact set: `‖x‖ ≤ R` and `x` within `1 / (k + 1)` of `F k` for all `k`
    set K := closedBall (0 : E) R ∩ ⋂ k : ℕ, cthickening (1 / ((k : ℝ) + 1)) (F k : Set E)
    have hK : IsCompact K := by
      refine TotallyBounded.isCompact_of_isClosed ?_
        (isClosed_closedBall.inter (isClosed_iInter fun k ↦ isClosed_cthickening))
      refine (totallyBounded_iff_forall_exists_finiteDimensional (𝕜 := 𝕜)).2
        ⟨isBounded_closedBall.subset Set.inter_subset_left, fun η hη ↦ ?_⟩
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hη
      refine ⟨F k, hFd k, fun a ha ↦ ?_⟩
      have hak := mem_cthickening_iff.1 ((Set.mem_iInter.1 ha.2) k)
      obtain ⟨f, hfF, haf⟩ := infEDist_lt_iff.1
        (hak.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hη).2 hk))
      exact ⟨f, hfF, edist_lt_ofReal.1 haf⟩
    refine ⟨K, hK, fun μ hμ ↦ ?_⟩
    have hcompl : Kᶜ ⊆
        {x | R < ‖x‖} ∪ ⋃ k : ℕ, (cthickening (1 / ((k : ℝ) + 1)) (F k : Set E))ᶜ := by
      intro x hx
      by_contra hc
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_compl_iff, not_or,
        not_lt, not_exists, not_not] at hc
      exact hx ⟨by rw [mem_closedBall, dist_zero_right]; exact hc.1, Set.mem_iInter.2 hc.2⟩
    calc μ Kᶜ ≤ μ {x | R < ‖x‖} + ∑' k : ℕ, μ (cthickening (1 / ((k : ℝ) + 1)) (F k : Set E))ᶜ :=
          (measure_mono hcompl).trans ((measure_union_le _ _).trans
            (add_le_add le_rfl (measure_iUnion_le _)))
      _ ≤ ε / 2 + ε / 2 := add_le_add (hR μ hμ)
          ((ENNReal.tsum_le_tsum fun k ↦ hFS k μ hμ).trans hε'.le)
      _ = ε := ENNReal.add_halves ε

end MeasureTheory
