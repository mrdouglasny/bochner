/-
Copyright (c) 2026 Axiomatic AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Minlos.Mathlib.Analysis.InnerProductSpace.HilbertSchmidt
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Hilbert–Schmidt operators into `L²(μ)` are integral operators

For any measure `μ` and Hilbert space `K`, a Hilbert–Schmidt operator `K → L²(μ)` is
`k ↦ ⟪κ ·, k⟫` for a kernel `κ ∈ L²(μ; K)` (`ContinuousLinearMap.IsHilbertSchmidt.exists_kernel`),
and every weakly measurable `κ` with `∫ ‖κ‖² < ∞` defines one
(`ContinuousLinearMap.exists_isHilbertSchmidt_of_kernel`). Sazonov's theorem uses the second to
show that second-moment forms are trace class.

## Provenance

Ported from or4nge19/QuantumlibCore `pin-v4.34.1` `9a741c08`,
`QuantumlibCore/ToMathlib/MeasureTheory/Function/LpSpace/HilbertSchmidtKernel.lean` (Lean v4.34.1,
Mathlib `d13f23b7`), its last section, which does not use the kernels on `L²(μ ⊗ ν)` of the rest
of that file; notices kept.
-/

@[expose] public section

open MeasureTheory InnerProductSpace
open scoped ENNReal InnerProductSpace

/-- The `L²` norm as an integral, in `ℝ≥0∞`: `‖f‖ₑ² = ∫⁻ ‖f‖ₑ²`. -/
theorem MeasureTheory.Lp.lintegral_enorm_sq {X E : Type*} {m : MeasurableSpace X}
    {μ : Measure X} [NormedAddCommGroup E] (f : Lp E 2 μ) :
    ∫⁻ x, (‖(f : X → E) x‖ₑ : ℝ≥0∞) ^ 2 ∂μ = (‖f‖ₑ : ℝ≥0∞) ^ 2 := by
  have h := lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := (f : X → E)) (μ := μ) two_pos
  rw [Lp.enorm_def,
    eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top (Lp.aestronglyMeasurable f)]
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using h

namespace ContinuousLinearMap

open MeasureTheory

variable {𝕜 X K : Type*} [RCLike 𝕜] {m : MeasurableSpace X} {μ : Measure X}
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- **A Hilbert–Schmidt operator into `L²(μ)` has a kernel in `L²(μ; K)`**: `S k = ⟪κ ·, k⟫`
almost everywhere, with `κ` square-integrable — the map `𝓛₂(K; L²(μ)) → L²(μ; K)`, converse to
the embedding of [Bourbaki, *Théories spectrales*, IV, §1, no. 9][bourbaki2023spectral]. The
kernel is `κ x = ∑ᵢ conj ((S bᵢ) x) • bᵢ`, formally `S† δₓ`, summed over the countably many
vectors of a Hilbert basis with `S bᵢ ≠ 0`. -/
theorem IsHilbertSchmidt.exists_kernel {S : K →L[𝕜] Lp 𝕜 2 μ} (hS : S.IsHilbertSchmidt) :
    ∃ κ : X → K, MemLp κ 2 μ ∧ ∀ k, ⇑(S k) =ᵐ[μ] fun x ↦ ⟪κ x, k⟫_𝕜 := by
  classical
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 K
  have hsum : Summable fun i ↦ ‖S (b i)‖ ^ 2 := (isHilbertSchmidt_iff_summable S b).1 hS
  have hfin : ∑' i, (‖S (b i)‖ₑ : ℝ≥0∞) ^ 2 < ⊤ := (b.tsum_enorm_sq_map_lt_top_iff S).2 hsum
  -- only countably many basis vectors have a nonzero image
  set I : Set w := Function.support fun i ↦ (‖S (b i)‖ₑ : ℝ≥0∞) ^ 2 with hIdef
  have hI : I.Countable := Summable.countable_support_ennreal hfin.ne
  have : Countable I := hI.to_subtype
  have hzero : ∀ i ∉ I, S (b i) = 0 := fun i hi ↦
    enorm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 (Function.notMem_support.1 hi))
  -- the values at `x` are square-summable almost everywhere: `∫ ∑ |(S bᵢ) x|² = ∑ ‖S bᵢ‖²`
  have hl2 : ∀ f : Lp 𝕜 2 μ, ∫⁻ x, (‖(f : X → 𝕜) x‖ₑ : ℝ≥0∞) ^ 2 ∂μ = (‖f‖ₑ : ℝ≥0∞) ^ 2 :=
    Lp.lintegral_enorm_sq
  have hint : ∫⁻ x, ∑' i : I, (‖(S (b i) : X → 𝕜) x‖ₑ : ℝ≥0∞) ^ 2 ∂μ ≠ ⊤ := by
    rw [lintegral_tsum fun i ↦ (Lp.aestronglyMeasurable _).enorm.pow_const 2]
    simp_rw [hl2]
    exact (lt_of_le_of_lt (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _)
      hfin).ne
  have hae : ∀ᵐ x ∂μ, ∑' i : I, (‖(S (b i) : X → 𝕜) x‖ₑ : ℝ≥0∞) ^ 2 ≠ ⊤ :=
    (ae_lt_top' (AEMeasurable.tsum fun i ↦ (Lp.aestronglyMeasurable _).enorm.pow_const 2)
      hint).mono fun _ h ↦ h.ne
  -- there, `κ x` has the conjugated values on `I`, and `0` off `I`, as coordinates
  set c : X → w → 𝕜 := fun x i ↦ if i ∈ I then starRingEnd 𝕜 ((S (b i) : X → 𝕜) x) else 0
    with hc
  have htsum : ∀ x, ∑' i, (‖c x i‖ₑ : ℝ≥0∞) ^ 2 =
      ∑' i : I, (‖(S (b i) : X → 𝕜) x‖ₑ : ℝ≥0∞) ^ 2 := fun x ↦ by
    rw [tsum_subtype I fun i ↦ (‖(S (b i) : X → 𝕜) x‖ₑ : ℝ≥0∞) ^ 2]
    congr 1
    funext i
    by_cases hi : i ∈ I <;> simp [hc, hi]
  have hmem : ∀ x, ∑' i : I, (‖(S (b i) : X → 𝕜) x‖ₑ : ℝ≥0∞) ^ 2 ≠ ⊤ → Memℓp (c x) 2 :=
    fun x hx ↦ by
      refine memℓp_gen ?_
      have := ENNReal.summable_toReal (htsum x ▸ hx)
      refine this.congr fun i ↦ ?_
      rw [ENNReal.toReal_pow, toReal_enorm, ENNReal.toReal_ofNat, Real.rpow_two]
  set κ : X → K := fun x ↦ ∑' i : I, starRingEnd 𝕜 ((S (b i) : X → 𝕜) x) • b i with hκdef
  have hκ : ∀ x (hx : ∑' i : I, (‖(S (b i) : X → 𝕜) x‖ₑ : ℝ≥0∞) ^ 2 ≠ ⊤),
      κ x = b.repr.symm ⟨c x, hmem x hx⟩ := fun x hx ↦ by
    have hsupp : Function.support (fun i ↦ c x i • b i) ⊆ I := fun i hi ↦ by
      by_contra hiI
      exact hi (by simp [hc, hiI])
    rw [hκdef]
    refine Eq.trans (tsum_congr fun i ↦ ?_)
      ((hasSum_subtype_iff_of_support_subset hsupp).2 (b.hasSum_repr_symm ⟨c x, hmem x hx⟩)).tsum_eq
    simp [hc, i.2]
  have hκmeas : AEStronglyMeasurable κ μ :=
    AEStronglyMeasurable.tsum fun i ↦ (RCLike.continuous_conj.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable _)).smul_const (b i)
  refine ⟨κ, ?_, fun k ↦ ?_⟩
  · -- `‖κ x‖² = ∑ᵢ |(S bᵢ) x|²` by Parseval, whose integral is finite
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero
      ENNReal.ofNat_ne_top hκmeas]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    refine lt_of_eq_of_lt (lintegral_congr_ae (hae.mono fun x hx ↦ ?_)) hint.lt_top
    dsimp only
    rw [hκ x hx, ← b.tsum_enorm_sq_inner, ← htsum x]
    congr 1
    funext i
    rw [← b.repr_apply_apply, LinearIsometryEquiv.apply_symm_apply]
  -- `S k = ∑ᵢ ⟪bᵢ, k⟫ • S bᵢ` over `I`, absolutely in `L²`
  have hk : HasSum (fun i : I ↦ b.repr k i • S (b i)) (S k) := by
    have h := (b.hasSum_repr k).mapL S
    simp only [map_smul] at h
    refine (hasSum_subtype_iff_of_support_subset (s := I) fun i hi ↦ ?_).2 h
    by_contra hiI
    exact hi (by simp only [hzero i hiI, smul_zero])
  have habs : ∑' i : I, ‖b.repr k i • S (b i)‖ₑ ≠ ⊤ := by
    rw [tsum_enorm_ne_top_iff_summable_norm]
    have hr' : Summable fun i ↦ ‖b.repr k i‖ ^ 2 := by
      have := (lp.memℓp (b.repr k)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      simpa [Real.rpow_two] using this
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun i ↦ ?_)
      (((hr'.subtype I).add (hsum.subtype I)).div_const 2)
    simp only [Function.comp_apply, norm_smul]
    linarith [two_mul_le_add_sq ‖b.repr k i‖ ‖S (b i)‖]
  have hpt := Lp.hasSum_coeFn_tsum habs
  rw [hk.tsum_eq] at hpt
  filter_upwards [hpt, hae, ae_all_iff.2 fun i : I ↦ Lp.coeFn_smul (b.repr k i) (S (b i))]
    with x hx hxs hxc
  have hL : (S k : X → 𝕜) x = ∑' i : I, b.repr k i * (S (b i) : X → 𝕜) x := by
    rw [← hx.tsum_eq]
    congr 1
    funext i
    rw [hxc i, Pi.smul_apply, smul_eq_mul]
  rw [hL, hκ x hxs, ← b.repr.inner_map_map, LinearIsometryEquiv.apply_symm_apply,
    lp.inner_eq_tsum, tsum_subtype I fun i ↦ b.repr k i * (S (b i) : X → 𝕜) x]
  congr 1
  funext i
  by_cases hi : i ∈ I
  · rw [Set.indicator_of_mem hi]
    simp [hc, hi, RCLike.inner_apply]
  · rw [Set.indicator_of_notMem hi]
    simp [hc, hi]

/-- **Conversely, a square-integrable kernel is Hilbert–Schmidt**: when `∫ ‖κ‖² < ∞`,
`k ↦ ⟪κ ·, k⟫` is a Hilbert–Schmidt operator `K → L²(μ)`, of Hilbert–Schmidt norm at most
`(∫ ‖κ‖²)^{1/2}` by Bessel. The kernel need only be weakly measurable: no separability of its range
is assumed, unlike `MemLp κ 2 μ`. -/
theorem exists_isHilbertSchmidt_of_kernel {κ : X → K}
    (hκm : ∀ k, AEStronglyMeasurable (fun x ↦ ⟪κ x, k⟫_𝕜) μ)
    (hκ : Integrable (fun x ↦ ‖κ x‖ ^ 2) μ) :
    ∃ S : K →L[𝕜] Lp 𝕜 2 μ, S.IsHilbertSchmidt ∧ ∀ k, ⇑(S k) =ᵐ[μ] fun x ↦ ⟪κ x, k⟫_𝕜 := by
  have hbound : ∀ k x, ‖⟪κ x, k⟫_𝕜‖ ≤ ‖k‖ * ‖κ x‖ := fun k x ↦ by
    rw [mul_comm]; exact norm_inner_le_norm _ _
  have hofreal : ∀ y : K, (‖y‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := fun y ↦ by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  -- `∫⁻ ‖κ‖ₑ² < ∞`
  have hfin : ∫⁻ x, (‖κ x‖ₑ : ℝ≥0∞) ^ 2 ∂μ < ⊤ := by
    simp_rw [hofreal]
    exact hκ.lintegral_lt_top
  -- the pointwise bound, integrated
  have hle : ∀ k, ∫⁻ x, (‖⟪κ x, k⟫_𝕜‖ₑ : ℝ≥0∞) ^ 2 ∂μ ≤
      (‖k‖ₑ : ℝ≥0∞) ^ 2 * ∫⁻ x, (‖κ x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := fun k ↦ by
    rw [← lintegral_const_mul' _ _ (by simp)]
    refine lintegral_mono fun x ↦ ?_
    rw [← mul_pow, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul
      (norm_nonneg _)]
    exact pow_le_pow_left₀ bot_le (ENNReal.ofReal_le_ofReal (hbound k x)) 2
  have hmem : ∀ k, MemLp (fun x ↦ ⟪κ x, k⟫_𝕜) 2 μ := fun k ↦ by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero
      ENNReal.ofNat_ne_top (hκm k)]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    exact (hle k).trans_lt (ENNReal.mul_lt_top (by simp) hfin)
  -- `k ↦ ⟪κ ·, k⟫` is linear and bounded by `(∫ ‖κ‖²)^{1/2}`
  set L : K →ₗ[𝕜] Lp 𝕜 2 μ :=
    { toFun := fun k ↦ (hmem k).toLp _
      map_add' := fun k k' ↦ by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _
          (Filter.EventuallyEq.of_eq (funext fun x ↦ inner_add_right _ _ _))
      map_smul' := fun c k ↦ by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (funext fun x ↦ by
          simp [inner_smul_right])) }
  have hL : ∀ k, (‖L k‖ₑ : ℝ≥0∞) ^ 2 = ∫⁻ x, (‖⟪κ x, k⟫_𝕜‖ₑ : ℝ≥0∞) ^ 2 ∂μ := fun k ↦ by
    rw [← Lp.lintegral_enorm_sq]
    exact lintegral_congr_ae ((hmem k).coeFn_toLp.mono fun x hx ↦ congrArg (‖·‖ₑ ^ 2) hx)
  have hint : (∫⁻ x, (‖κ x‖ₑ : ℝ≥0∞) ^ 2 ∂μ).toReal = ∫ x, ‖κ x‖ ^ 2 ∂μ := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ by positivity)
      hκ.aestronglyMeasurable]
    simp_rw [hofreal]
  set M := √(∫ x, ‖κ x‖ ^ 2 ∂μ)
  have hLM : ∀ k, ‖L k‖ ≤ M * ‖k‖ := fun k ↦ by
    have h2 : ‖L k‖ ^ 2 ≤ ‖k‖ ^ 2 * ∫ x, ‖κ x‖ ^ 2 ∂μ := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfin.ne) ((hL k).trans_le (hle k))
      rwa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow, toReal_enorm,
        toReal_enorm, hint] at this
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, Real.sq_sqrt (integral_nonneg fun x ↦ by positivity)]
    linarith
  set S : K →L[𝕜] Lp 𝕜 2 μ := L.mkContinuous M hLM
  refine ⟨S, ?_, fun k ↦ (hmem k).coeFn_toLp⟩
  -- Bessel: `∑ᵢ ‖S bᵢ‖² = ∑ᵢ ∫ |⟪κ, bᵢ⟫|² ≤ ∫ ‖κ‖²`
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 K
  rw [S.isHilbertSchmidt_iff_summable b, ← b.tsum_enorm_sq_map_lt_top_iff S]
  refine lt_of_le_of_lt ?_ hfin
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun t ↦ ?_
  calc ∑ i ∈ t, (‖S (b i)‖ₑ : ℝ≥0∞) ^ 2
      = ∫⁻ x, ∑ i ∈ t, (‖⟪(b i : K), κ x⟫_𝕜‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
        rw [lintegral_finsetSum' _ fun i _ ↦ ((hκm (b i)).enorm.pow_const 2).congr
          (ae_of_all _ fun x ↦ by simp only; rw [← ofReal_norm, ← ofReal_norm, norm_inner_symm])]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [show S (b i) = L (b i) from rfl, hL]
        refine lintegral_congr fun x ↦ ?_
        rw [← ofReal_norm, ← ofReal_norm, norm_inner_symm]
    _ ≤ ∫⁻ x, (‖κ x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := lintegral_mono fun x ↦
        (ENNReal.sum_le_tsum t).trans (b.orthonormal.tsum_enorm_sq_inner_le (κ x))

end ContinuousLinearMap
