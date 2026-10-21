/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Minlos.PietschBridge
public import Minlos.Mathlib.Analysis.LocallyConvex.NuclearSpace

/-!
# Pietsch's condition, twice

`IsNuclear E` (`Minlos.PietschBridge`) and the class `NuclearSpace ℝ E`
(`Minlos.Mathlib.Analysis.LocallyConvex.NuclearSpace`) state the same condition of Pietsch: every
continuous seminorm `p` satisfies `p x ≤ ∑ₙ cₙ |fₙ x|` with `∑ₙ cₙ < ∞` and `|fₙ| ≤ q` for one
continuous seminorm `q`. `IsNuclear` also asks `p ≤ q`, which `q ⊔ p` provides
(`nuclearSpace_iff_isNuclear`). Through it, `isHilbertNuclear_of_nuclear` and `minlos_theorem`
apply to every `NuclearSpace ℝ E`, and
`MeasureTheory.exists_isProbabilityMeasure_integral_cexp_eq_of_continuous` to every space
`IsNuclear E`.
-/

@[expose] public section

/-- **The two forms of Pietsch's condition agree.** -/
theorem nuclearSpace_iff_isNuclear {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] : NuclearSpace ℝ E ↔ IsNuclear E := by
  refine ⟨fun h p hp ↦ ?_, fun h ↦ ⟨fun p hp ↦ ?_⟩⟩
  · obtain ⟨q, f, a, hq, hfq, ha, hsum, hpf⟩ := NuclearSpace.exists_le_tsum p hp
    refine ⟨q ⊔ p, ?_, fun x ↦ ?_, f, a, ha, hsum, fun n x ↦ ?_, fun x ↦ ?_⟩
    · have : ⇑(q ⊔ p) = fun x ↦ max (q x) (p x) := funext fun x ↦ Seminorm.sup_apply q p x
      rw [this]
      exact hq.max hp
    · rw [Seminorm.sup_apply]
      exact le_max_right _ _
    · rw [Seminorm.sup_apply, ← Real.norm_eq_abs]
      exact (hfq n x).trans (le_max_left _ _)
    · simpa only [Real.norm_eq_abs, mul_comm] using hpf x
  · obtain ⟨q, hq, -, f, c, hc, hsum, hfq, hpf⟩ := h p hp
    exact ⟨q, f, c, hq, fun n x ↦ by simpa only [Real.norm_eq_abs] using hfq n x, hc, hsum,
      fun x ↦ by simpa only [Real.norm_eq_abs, mul_comm] using hpf x⟩
