/-
Copyright (c) 2026 Axiomatic AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.MeasureTheory.Measure.Content
public import Mathlib.Topology.MetricSpace.Polish
public import Minlos.Mathlib.MeasureTheory.Measure.Tight

/-!
# Prokhorov's theorem on projective limits

A Hausdorff space `X` embedded continuously in a product `∀ i, α i` of Polish spaces carries a
Radon measure with prescribed finite-dimensional marginals `P J` — a projective family — iff these
are uniformly concentrated on the images of compact subsets of `X` (Prokhorov's condition), and
the measure is then unique [Bourbaki, *INT*, IX, §4, no. 2, Thm 1][bourbaki2004integration2].
The measure is built from the content `K ↦ inf_J P J (π_J '' K)` on compact sets
(`MeasureTheory.Content`), which is additive because disjoint compact sets are separated by finitely
many coordinates; outer regularity of the `P J` gives its value on compact sets, inner regularity
its marginals. Nothing is assumed of `X` beyond Hausdorff: `X` is typically the weak dual of a
topological vector space, and this is how Minlos' theorem is proved.

## Main results

* `MeasureTheory.IsProjectiveMeasureFamily.exists_map_restrict_eq`: Prokhorov's theorem, with the
  values of the measure on compact sets
* `MeasureTheory.IsProjectiveMeasureFamily.exists_map_restrict_eq_iff`: Prokhorov's condition is
  necessary and sufficient
* `MeasureTheory.ext_of_map_restrict_eq`: Radon measures with the same marginals are equal
* `MeasureTheory.measure_eq_iInf_preimage_image_restrict`: τ-additivity on compact sets

## Provenance

Ported from or4nge19/QuantumlibCore `pin-v4.34.1` `9a741c08`,
`QuantumlibCore/ToMathlib/MeasureTheory/Constructions/Projective.lean` (Lean v4.34.1, Mathlib
`d13f23b7`), with module paths renamed; notices kept.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace MeasureTheory

variable {ι : Type*} {α : ι → Type*} [∀ i, TopologicalSpace (α i)]
  {X : Type*} [TopologicalSpace X] {f : X → ∀ i, α i}

/-- Disjoint compact sets are separated by finitely many coordinates of a continuous injection
[Bourbaki, *INT*, IX, §4, no. 1, Prop. 2]. -/
theorem exists_finset_disjoint_image_restrict [∀ i, T2Space (α i)] (hf : Continuous f)
    (hinj : f.Injective) {K L : Set X} (hK : IsCompact K) (hL : IsCompact L)
    (hKL : Disjoint K L) :
    ∃ J : Finset ι,
      Disjoint ((fun x ↦ J.restrict (f x)) '' K) ((fun x ↦ J.restrict (f x)) '' L) := by
  classical
  -- the pairs that `J` does not separate form a directed family of closed sets
  set t : Finset ι → Set (X × X) := fun J ↦ {p | J.restrict (f p.1) = J.restrict (f p.2)}
  have htc : ∀ J, IsClosed (t J) := fun J ↦ isClosed_eq
    ((Finset.continuous_restrict J).comp (hf.comp continuous_fst))
    ((Finset.continuous_restrict J).comp (hf.comp continuous_snd))
  have htd : Directed (· ⊇ ·) t := fun J J' ↦ ⟨J ∪ J', fun p hp ↦ by
      simp only [t, mem_ofPred_eq, funext_iff, Finset.restrict] at hp ⊢
      exact fun j ↦ hp ⟨j, Finset.mem_union_left _ j.2⟩,
    fun p hp ↦ by
      simp only [t, mem_ofPred_eq, funext_iff, Finset.restrict] at hp ⊢
      exact fun j ↦ hp ⟨j, Finset.mem_union_right _ j.2⟩⟩
  have hempty : K ×ˢ L ∩ ⋂ J, t J = ∅ := by
    refine eq_empty_of_forall_notMem fun p ⟨⟨hpK, hpL⟩, hp⟩ ↦ ?_
    have : f p.1 = f p.2 := funext fun i ↦ by
      have := congrFun (mem_iInter.1 hp {i}) ⟨i, Finset.mem_singleton_self i⟩
      simpa [Finset.restrict] using this
    exact hKL.ne_of_mem hpK hpL (hinj this)
  obtain ⟨J, hJ⟩ := (hK.prod hL).elim_directed_family_closed t htc
    (disjoint_iff_inter_eq_empty.2 hempty) htd
  refine ⟨J, disjoint_left.2 ?_⟩
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  exact (eq_empty_iff_forall_notMem.1 (disjoint_iff_inter_eq_empty.1 hJ)) (x, y)
    ⟨⟨hx, hy⟩, hxy.symm⟩

section TauAdditivity

variable [∀ i, T2Space (α i)] [T2Space X] [MeasurableSpace X] [BorelSpace X]

/-- **τ-additivity**: a finite inner regular measure is determined on a compact set by its
finite-dimensional marginals, `μ K = inf_J μ (π_J⁻¹ (π_J K))` [Bourbaki, *INT*, IX, §4, no. 2,
Thm 1, (2)]. -/
theorem measure_eq_iInf_preimage_image_restrict (hf : Continuous f) (hinj : f.Injective)
    (μ : Measure X) [IsFiniteMeasure μ] [μ.InnerRegular] {K : Set X} (hK : IsCompact K) :
    μ K = ⨅ J : Finset ι,
      μ ((fun x ↦ J.restrict (f x)) ⁻¹' ((fun x ↦ J.restrict (f x)) '' K)) := by
  classical
  set t : Finset ι → Set X := fun J ↦
    (fun x ↦ J.restrict (f x)) ⁻¹' ((fun x ↦ J.restrict (f x)) '' K) with ht
  have hπ : ∀ J : Finset ι, Continuous fun x ↦ J.restrict (f x) := fun J ↦
    (Finset.continuous_restrict J).comp hf
  refine le_antisymm (le_iInf fun J ↦ measure_mono fun x hx ↦ ⟨x, hx, rfl⟩)
    (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_)
  have hε2 : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 := ENNReal.half_pos (by exact_mod_cast hε.ne')
  obtain ⟨U, hKU, hU, hUlt⟩ := K.exists_isOpen_lt_of_lt (μ K + (ε : ℝ≥0∞) / 2)
    (ENNReal.lt_add_right (measure_ne_top _ _) hε2.ne')
  obtain ⟨L, -, hL, hLlt⟩ := MeasurableSet.univ.exists_isCompact_lt_add (μ := μ)
    (measure_ne_top _ _) hε2.ne'
  -- `⋂ J, t J = K`, so `L \ U` meets some `t J` in nothing
  have htc : ∀ J, IsClosed (t J) := fun J ↦ ((hK.image (hπ J)).isClosed).preimage (hπ J)
  have htd : Directed (· ⊇ ·) t := fun J J' ↦ ⟨J ∪ J',
    fun x ⟨y, hy, hxy⟩ ↦ ⟨y, hy, by
      have := congrArg (Finset.restrict₂ (Finset.subset_union_left (s₂ := J'))) hxy
      exact this⟩,
    fun x ⟨y, hy, hxy⟩ ↦ ⟨y, hy, by
      have := congrArg (Finset.restrict₂ (Finset.subset_union_right (s₁ := J))) hxy
      exact this⟩⟩
  have hempty : (L \ U) ∩ ⋂ J, t J = ∅ := by
    refine eq_empty_of_forall_notMem fun x ⟨⟨_, hxU⟩, hx⟩ ↦ hxU (hKU ?_)
    by_contra hxK
    obtain ⟨J, hJ⟩ := exists_finset_disjoint_image_restrict hf hinj isCompact_singleton hK
      (disjoint_singleton_left.2 hxK)
    exact disjoint_left.1 hJ ⟨x, rfl, rfl⟩ (mem_iInter.1 hx J)
  obtain ⟨J, hJ⟩ := (hL.diff hU).elim_directed_family_closed t htc
    (disjoint_iff_inter_eq_empty.2 hempty) htd
  have hsub : t J ∩ L ⊆ U := fun x ⟨hxt, hxL⟩ ↦ by
    by_contra hxU
    exact (eq_empty_iff_forall_notMem.1 (disjoint_iff_inter_eq_empty.1 hJ)) x ⟨⟨hxL, hxU⟩, hxt⟩
  calc ⨅ J, μ (t J) ≤ μ (t J) := iInf_le _ J
    _ ≤ μ (t J ∩ L) + μ (t J \ L) := measure_le_inter_add_sdiff _ _ _
    _ ≤ μ U + μ Lᶜ := add_le_add (measure_mono hsub) (measure_mono fun x hx ↦ hx.2)
    _ ≤ μ K + ε / 2 + ε / 2 := by
        refine add_le_add hUlt.le ?_
        rw [measure_compl hL.isClosed.measurableSet (measure_ne_top _ _)]
        exact tsub_le_iff_left.2 hLlt.le
    _ = μ K + ε := by rw [add_assoc, ENNReal.add_halves]

end TauAdditivity

section Projective

variable [∀ i, MeasurableSpace (α i)] {P : ∀ J : Finset ι, Measure (∀ j : J, α j)}

omit [∀ i, TopologicalSpace (α i)] [TopologicalSpace X] in
/-- The masses `P J (π_J '' K)` decrease along a projective family. -/
theorem IsProjectiveMeasureFamily.measure_image_restrict_le (hP : IsProjectiveMeasureFamily P)
    (K : Set X) {J J' : Finset ι} (hJ : J ⊆ J') :
    P J' ((fun x ↦ J'.restrict (f x)) '' K) ≤ P J ((fun x ↦ J.restrict (f x)) '' K) := by
  rw [hP J' J hJ]
  refine (measure_mono ?_).trans
    (Measure.le_map_apply (Finset.measurable_restrict₂ hJ).aemeasurable _)
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hx, rfl⟩

variable [∀ i, PolishSpace (α i)] [∀ i, BorelSpace (α i)] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]

/-- **Prokhorov's condition is necessary**: the marginals of a finite inner regular measure are
uniformly concentrated on the images of compact sets. -/
theorem exists_isCompact_forall_map_restrict_compl_le (hf : Continuous f)
    (μ : Measure X) [IsFiniteMeasure μ] [μ.InnerRegular] {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K, IsCompact K ∧ ∀ J : Finset ι,
      μ.map (fun x ↦ J.restrict (f x)) ((fun x ↦ J.restrict (f x)) '' K)ᶜ ≤ ε := by
  obtain ⟨K, -, hK, hKε⟩ := MeasurableSet.univ.exists_isCompact_sdiff_lt (μ := μ)
    (measure_ne_top _ _) hε.ne'
  refine ⟨K, hK, fun J ↦ ?_⟩
  have hπ : Continuous fun x ↦ J.restrict (f x) := (Finset.continuous_restrict J).comp hf
  rw [Measure.map_apply hπ.measurable (hK.image hπ).isClosed.measurableSet.compl]
  calc μ ((fun x ↦ J.restrict (f x)) ⁻¹' ((fun x ↦ J.restrict (f x)) '' K)ᶜ) ≤ μ (univ \ K) :=
        measure_mono fun x hx ↦ ⟨mem_univ x, fun hxK ↦ hx ⟨x, hxK, rfl⟩⟩
    _ ≤ ε := hKε.le

/-- **Prokhorov's theorem on projective limits** [Bourbaki, *INT*, IX, §4, no. 2, Thm 1]. -/
theorem IsProjectiveMeasureFamily.exists_map_restrict_eq [∀ J, IsFiniteMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P) (hf : Continuous f) (hinj : f.Injective)
    (htight : ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ J, P J ((fun x ↦ J.restrict (f x)) '' K)ᶜ ≤ ε) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ μ.InnerRegular ∧
      (∀ K, IsCompact K → μ K = ⨅ J, P J ((fun x ↦ J.restrict (f x)) '' K)) ∧
      ∀ J, μ.map (fun x ↦ J.restrict (f x)) = P J := by
  classical
  set π : ∀ J : Finset ι, X → ∀ j : J, α j := fun J x ↦ J.restrict (f x) with hπdef
  have hπ : ∀ J, Continuous (π J) := fun J ↦ (Finset.continuous_restrict J).comp hf
  have hcl : ∀ J (K : Set X), IsCompact K → MeasurableSet (π J '' K) := fun J K hK ↦
    (hK.image (hπ J)).isClosed.measurableSet
  -- the content `K ↦ inf_J P J (π J '' K)`
  set m : Set X → ℝ≥0∞ := fun K ↦ ⨅ J, P J (π J '' K) with hm
  have hmJ : ∀ K J, m K ≤ P J (π J '' K) := fun K J ↦ iInf_le (fun J ↦ P J (π J '' K)) J
  have hmtop : ∀ K, m K ≠ ⊤ := fun K ↦
    ((hmJ K ∅).trans_lt ((measure_mono (subset_univ _)).trans_lt (measure_lt_top _ _))).ne
  have hadd : ∀ K L, m K + m L = ⨅ J, (P J (π J '' K) + P J (π J '' L)) := fun K L ↦
    ENNReal.iInf_add_iInf fun J J' ↦ ⟨J ∪ J', add_le_add
      (hP.measure_image_restrict_le K Finset.subset_union_left)
      (hP.measure_image_restrict_le L Finset.subset_union_right)⟩
  have hunion : ∀ K L, m (K ∪ L) ≤ m K + m L := fun K L ↦ by
    rw [hadd]
    exact le_iInf fun J ↦ (hmJ _ J).trans (by rw [image_union]; exact measure_union_le _ _)
  let cont : Content X :=
    { toFun := fun K ↦ (m K).toNNReal
      mono' := fun K₁ K₂ h ↦
        ENNReal.toNNReal_mono (hmtop _) (iInf_mono fun J ↦ measure_mono (image_mono h))
      sup_disjoint' := fun K₁ K₂ hd _ _ ↦ by
        obtain ⟨J₀, hJ₀⟩ := exists_finset_disjoint_image_restrict hf hinj K₁.isCompact
          K₂.isCompact hd
        rw [← ENNReal.toNNReal_add (hmtop _) (hmtop _), TopologicalSpace.Compacts.coe_sup]
        congr 1
        refine le_antisymm (hunion _ _) ?_
        rw [hadd]
        refine le_iInf fun J ↦ (iInf_le _ (J ∪ J₀)).trans ?_
        have hsep : Disjoint (π (J ∪ J₀) '' K₁) (π (J ∪ J₀) '' K₂) := by
          refine disjoint_left.2 ?_
          rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
          refine disjoint_left.1 hJ₀ ⟨x, hx, rfl⟩ ⟨y, hy, ?_⟩
          have := congrArg (Finset.restrict₂ (Finset.subset_union_right (s₁ := J))) hxy
          exact this
        rw [← measure_union hsep (hcl _ _ K₂.isCompact), ← image_union]
        exact hP.measure_image_restrict_le _ Finset.subset_union_left
      sup_le' := fun K₁ K₂ ↦ by
        rw [← ENNReal.toNNReal_add (hmtop _) (hmtop _), TopologicalSpace.Compacts.coe_sup]
        exact ENNReal.toNNReal_mono (ENNReal.add_ne_top.2 ⟨hmtop _, hmtop _⟩) (hunion _ _) }
  have hcont : ∀ K : TopologicalSpace.Compacts X, cont K = m K := fun K ↦
    ENNReal.coe_toNNReal (hmtop K)
  set μ := cont.measure with hμ
  have hμU : ∀ U : TopologicalSpace.Opens X, μ U = cont.innerContent U := fun U ↦ by
    rw [hμ, Content.measure_apply _ U.isOpen.measurableSet, Content.outerMeasure_opens]
  -- `μ = m` on compact sets
  have hμK : ∀ K, IsCompact K → μ K = m K := fun K hK ↦ by
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_) ?_
    · obtain ⟨J, hJ⟩ : ∃ J, P J (π J '' K) < m K + ε := by
        have : m K < m K + ε := ENNReal.lt_add_right (hmtop K) (by simpa using hε.ne')
        simpa [hm, iInf_lt_iff] using this
      obtain ⟨V, hKV, hV, hVlt⟩ := (π J '' K).exists_isOpen_lt_of_lt _ hJ
      calc μ K ≤ μ (π J ⁻¹' V) := measure_mono fun x hx ↦ hKV ⟨x, hx, rfl⟩
        _ = cont.innerContent ⟨_, hV.preimage (hπ J)⟩ := hμU ⟨_, hV.preimage (hπ J)⟩
        _ ≤ P J V := iSup₂_le fun K' hK' ↦ by
            rw [hcont]
            exact (hmJ _ J).trans (measure_mono (by rintro _ ⟨x, hx, rfl⟩; exact hK' hx))
        _ ≤ m K + ε := hVlt.le
    · calc m K = cont ⟨K, hK⟩ := (hcont ⟨K, hK⟩).symm
        _ ≤ cont.outerMeasure K := cont.le_outerMeasure_compacts ⟨K, hK⟩
        _ = μ K := (Content.measure_apply _ hK.isClosed.measurableSet).symm
  -- the total mass is at most that of the family
  have hPuniv : ∀ J, P J univ = P ∅ univ := fun J ↦ hP.measure_univ_eq J ∅
  have hμuniv : μ univ ≤ P ∅ univ := by
    rw [← TopologicalSpace.Opens.coe_top, hμU ⊤]
    exact iSup₂_le fun K' _ ↦ by
      rw [hcont]
      exact (hmJ _ ∅).trans (measure_mono (subset_univ _))
  have : IsFiniteMeasure μ := ⟨hμuniv.trans_lt (measure_lt_top _ _)⟩
  -- `μ` is Radon: inner regular on open sets by construction, and tight
  have hopen : μ.InnerRegularWRT IsCompact IsOpen := fun U hU r hr ↦ by
    rw [show U = (⟨U, hU⟩ : TopologicalSpace.Opens X) from rfl, hμU, Content.innerContent,
      lt_iSup_iff] at hr
    obtain ⟨K, hr⟩ := hr
    rw [lt_iSup_iff] at hr
    obtain ⟨hKU, hr⟩ := hr
    exact ⟨K, hKU, K.isCompact, by rwa [hμK K K.isCompact, ← hcont]⟩
  have : μ.WeaklyRegular := Measure.InnerRegularWRT.weaklyRegular_of_finite μ fun U hU r hr ↦
    let ⟨K, hKU, hK, hr⟩ := hopen hU r hr; ⟨K, hKU, hK.isClosed, hr⟩
  have hradon : μ.InnerRegular := by
    refine innerRegular_of_isTightMeasureSet_singleton
      (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.2 fun ε hε ↦ ?_)
    rcases eq_or_ne (μ univ) 0 with h0 | h0
    · exact ⟨∅, isCompact_empty, by rintro _ rfl; simp [h0]⟩
    obtain ⟨K, -, hK, hr⟩ := hopen isOpen_univ (μ univ - ε)
      (ENNReal.sub_lt_self (measure_ne_top _ _) h0 hε.ne')
    refine ⟨K, hK, ?_⟩
    rintro _ rfl
    rw [measure_compl hK.isClosed.measurableSet (measure_ne_top _ _)]
    exact (ENNReal.sub_lt_of_lt_add (measure_mono (subset_univ _))
      (ENNReal.lt_add_of_sub_lt_left (Or.inl (measure_ne_top _ _)) hr)).le
  refine ⟨μ, inferInstance, hradon, hμK, fun J ↦ ?_⟩
  -- the marginal dominates `P J` on compact sets, by tightness
  have hC : ∀ C : Set (∀ j : J, α j), IsCompact C → P J C ≤ μ.map (π J) C := fun C hC ↦ by
    rw [Measure.map_apply (hπ J).measurable hC.isClosed.measurableSet]
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    obtain ⟨K, hK, hKε⟩ := htight ε (by simpa using hε)
    have hK' : IsCompact (K ∩ π J ⁻¹' C) := hK.inter_right (hC.isClosed.preimage (hπ J))
    have key : ∀ J', P J C ≤ P J' (π J' '' (K ∩ π J ⁻¹' C)) + ε := fun J' ↦ by
      have hJJ : J ⊆ J' ∪ J := Finset.subset_union_right
      calc P J C = P (J' ∪ J) (Finset.restrict₂ hJJ ⁻¹' C) := by
            rw [hP _ J hJJ, Measure.map_apply (Finset.measurable_restrict₂ hJJ)
              hC.isClosed.measurableSet]
        _ ≤ P (J' ∪ J) (Finset.restrict₂ hJJ ⁻¹' C ∩ π (J' ∪ J) '' K) +
            P (J' ∪ J) (π (J' ∪ J) '' K)ᶜ :=
          (measure_le_inter_add_sdiff _ _ (π (J' ∪ J) '' K)).trans
            (add_le_add le_rfl (measure_mono fun z (hz : z ∈ _ \ _) ↦ hz.2))
        _ ≤ P (J' ∪ J) (π (J' ∪ J) '' (K ∩ π J ⁻¹' C)) + ε := by
          refine add_le_add (measure_mono ?_) (hKε _)
          rintro _ ⟨hzC, x, hxK, rfl⟩
          exact ⟨x, ⟨hxK, hzC⟩, rfl⟩
        _ ≤ P J' (π J' '' (K ∩ π J ⁻¹' C)) + ε :=
          add_le_add_left (hP.measure_image_restrict_le _ Finset.subset_union_left) _
    calc P J C ≤ m (K ∩ π J ⁻¹' C) + ε := by
          rw [hm, ENNReal.iInf_add]
          exact le_iInf key
      _ = μ (K ∩ π J ⁻¹' C) + ε := by rw [hμK _ hK']
      _ ≤ μ (π J ⁻¹' C) + ε := add_le_add_left (measure_mono inter_subset_right) _
  -- hence everywhere by inner regularity, and equality by the total masses
  have hle : ∀ A, MeasurableSet A → P J A ≤ μ.map (π J) A := fun A hA ↦ by
    rw [hA.measure_eq_iSup_isCompact (P J)]
    exact iSup₂_le fun C hCA ↦ iSup_le fun hC' ↦ (hC C hC').trans (measure_mono hCA)
  have hmass : μ.map (π J) univ = P J univ := by
    refine le_antisymm ?_ (hle univ MeasurableSet.univ)
    rw [Measure.map_apply (hπ J).measurable MeasurableSet.univ, preimage_univ, hPuniv]
    exact hμuniv
  refine Measure.ext fun A hA ↦ le_antisymm ?_ (hle A hA)
  have h1 := measure_add_measure_compl (μ := μ.map (π J)) hA
  have h2 := measure_add_measure_compl (μ := P J) hA
  have h3 := hle Aᶜ hA.compl
  rw [hmass, ← h2] at h1
  exact (ENNReal.add_le_add_iff_right (measure_ne_top _ _)).1 (h1.le.trans (add_le_add le_rfl h3))

/-- **Prokhorov's theorem on projective limits**, as an equivalence [Bourbaki, *INT*, IX, §4, no. 2,
Thm 1]: a projective family of finite measures is the family of marginals of a Radon measure on `X`
iff it is uniformly concentrated on the images of compact subsets of `X`. -/
theorem IsProjectiveMeasureFamily.exists_map_restrict_eq_iff [∀ J, IsFiniteMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P) (hf : Continuous f) (hinj : f.Injective) :
    (∃ μ : Measure X, IsFiniteMeasure μ ∧ μ.InnerRegular ∧
        ∀ J, μ.map (fun x ↦ J.restrict (f x)) = P J) ↔
      ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ J, P J ((fun x ↦ J.restrict (f x)) '' K)ᶜ ≤ ε := by
  refine ⟨fun ⟨μ, _, _, hμ⟩ ε hε ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨K, hK, hKε⟩ := exists_isCompact_forall_map_restrict_compl_le hf μ hε
    exact ⟨K, hK, fun J ↦ hμ J ▸ hKε J⟩
  · obtain ⟨μ, hμf, hμR, -, hμ⟩ := hP.exists_map_restrict_eq hf hinj h
    exact ⟨μ, hμf, hμR, hμ⟩

/-- **Uniqueness in Prokhorov's theorem**: finite inner regular measures with the same
finite-dimensional marginals are equal. -/
theorem ext_of_map_restrict_eq (hf : Continuous f) (hinj : f.Injective) {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [μ.InnerRegular] [ν.InnerRegular]
    (h : ∀ J : Finset ι,
      μ.map (fun x ↦ J.restrict (f x)) = ν.map (fun x ↦ J.restrict (f x))) :
    μ = ν := by
  have hπ : ∀ J : Finset ι, Continuous fun x ↦ J.restrict (f x) := fun J ↦
    (Finset.continuous_restrict J).comp hf
  have hK : ∀ K, IsCompact K → μ K = ν K := fun K hK ↦ by
    rw [measure_eq_iInf_preimage_image_restrict hf hinj μ hK,
      measure_eq_iInf_preimage_image_restrict hf hinj ν hK]
    refine iInf_congr fun J ↦ ?_
    have hm := ((hK.image (hπ J)).isClosed).measurableSet
    rw [← Measure.map_apply (hπ J).measurable hm, h J, Measure.map_apply (hπ J).measurable hm]
  ext A hA
  rw [hA.measure_eq_iSup_isCompact μ, hA.measure_eq_iSup_isCompact ν]
  exact iSup_congr fun K ↦ iSup_congr fun _ ↦ iSup_congr fun hK' ↦ hK K hK'

end Projective

end MeasureTheory
