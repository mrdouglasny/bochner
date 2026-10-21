/-
Copyright (c) 2026 Axiomatic AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.MeasureTheory.Measure.Tight

/-!
# Tight measures are Radon

A finite measure on a Hausdorff space that is inner regular for closed sets — every finite
measure on a metric space — and tight is inner regular for compact sets: a measurable set contains
a closed set of almost full measure, whose intersection with a compact set carrying all but `ε` is
compact. This is the converse of `MeasureTheory.isTightMeasureSet_singleton_of_innerRegular`, and
it holds without separability, where finite measures need not be tight.

## Provenance

Ported from or4nge19/QuantumlibCore `pin-v4.34.1` `9a741c08`,
`QuantumlibCore/ToMathlib/MeasureTheory/Measure/Tight.lean` (Lean v4.34.1, Mathlib `d13f23b7`), with
module paths renamed; notices kept.
-/

@[expose] public section

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} [TopologicalSpace α] [T2Space α]
  {μ : Measure α}

/-- **A tight, closed-regular finite measure is inner regular**: the converse of
`MeasureTheory.isTightMeasureSet_singleton_of_innerRegular`. -/
theorem innerRegular_of_isTightMeasureSet_singleton [IsFiniteMeasure μ] [μ.WeaklyRegular]
    (h : IsTightMeasureSet {μ}) : μ.InnerRegular := by
  have ht : ∀ ε, 0 < ε → ∃ K, IsCompact (closure K) ∧ μ Kᶜ < ε := fun ε hε ↦ by
    obtain ⟨r, hr0, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hε
    obtain ⟨K, hK, hKr⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 h r hr0
    exact ⟨K, hK.isClosed.closure_eq.symm ▸ hK, (hKr μ rfl).trans_lt hrε⟩
  have hr := ((innerRegularWRT_isCompact_closure_iff).1
    (innerRegularWRT_isCompact_closure_of_univ ht)).trans
    Measure.WeaklyRegular.innerRegular_measurable
  exact ⟨fun s hs ↦ hr ⟨hs, measure_ne_top _ _⟩⟩

end MeasureTheory
