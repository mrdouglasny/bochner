# Bochner's Theorem — Status

**Total: 0 sorries, 0 axioms — FULLY PROVED**

## PositiveDefinite.lean — 0 sorries

| # | Lemma | Layer | Difficulty | Status |
|---|-------|-------|------------|--------|
| 1 | `IsPositiveDefinite.mul` | 0 | Medium | proved |

## FejerPD.lean — 0 sorries, 0 axioms

| # | Lemma | Layer | Difficulty | Status | Depends on |
|---|-------|-------|------------|--------|------------|
| F1 | `isPositiveDefinite_exp_inner` | 0 | Medium | proved | — |
| F2 | `pd_double_integral_re_nonneg` | 1 | Hard | proved | — |
| F3 | `overlapRatio_tendsto_one` | 0 | Medium | proved | — |
| F4 | `fejer_avg_eq_integral` | 1 | Hard | proved | — |
| F5 | `pd_integral_re_nonneg` | 1 | Medium | proved | F2, F3, F4 |
| F6 | `pd_l1_fourier_re_nonneg_theorem` | 1 | Medium | proved | F1, F5 |

## Bochner.lean — 0 sorries, 0 axioms

| # | Lemma | Layer | Difficulty | Status | Depends on |
|---|-------|-------|------------|--------|------------|
| 2 | `gaussian_eq_charFun` | 0 | Medium | proved | — |
| 3a | `pd_l1_fourier_re_nonneg` | 1 | Hard | proved (via FejerPD) | F6 |
| 3 | `pd_l1_fourier_nonneg` | 1 | Medium | proved | 3a |
| 4 | `measure_of_pd_l1` | 3 | Medium | proved | 3 |
| 6a | `gaussianRegularize_ft_integrable` | 3 | Medium | proved | 3 |
| 6 | `gaussianRegularize_measures_tight` | 4 | Medium | proved | 4 |
| 7 | `bochner_theorem` (existence) | 4 | Medium | proved | 4, 6, 6a |
| 7b | `bochner_theorem` (uniqueness) | 5 | Easy | proved | Mathlib |

## Key proofs

| Lemma | Technique |
|-------|-----------|
| `pd_double_integral_re_nonneg` | SimpleFunc approximation of id + double DCT + PD sum with real coefficients |
| `fejer_avg_eq_integral` | Fubini + indicator function manipulation + translation invariance |
| `pd_integral_re_nonneg` | Fejér average + overlap ratio → 1 + DCT + ge_of_tendsto' |
| `pd_l1_fourier_re_nonneg_theorem` | Schur product with exp character + pd_integral_re_nonneg |
| `IsPositiveDefinite.mul` | Schur product via PSD kernel matrices + Kronecker/submatrix |
| `gaussian_eq_charFun` | Gaussian measure via withDensity + integral_cexp_neg_mul_sq_norm_add |
| `measure_of_pd_l1` | Fourier scaling + inversion + withDensity construction |
| `gaussianRegularize_ft_integrable` | Fatou's lemma + Parseval bound with Gaussian cutoffs |
| `gaussianRegularize_measures_tight` | `isTightMeasureSet_of_inner_tendsto` + charFun tail bound |
| `bochner_theorem` (existence) | Prokhorov + weak convergence + charFun limit |
| `bochner_theorem` (uniqueness) | Mathlib's `Measure.ext_of_charFun` |

## Minlos/ — 0 sorries, 4 axioms

| File | Status |
|------|--------|
| `FinDimMarginals.lean` | proved (0 sorries, 0 axioms) |
| `ProjectiveFamily.lean` | proved (0 sorries, 0 axioms) |
| `SazonovTightness.lean` | proved modulo 2 axioms (0 sorries) |
| `Minlos.lean` | proved modulo 2 axioms (0 sorries) |

### Axioms

1. **`nuclear_support_concentration`** — If E is a nuclear space and ν is a
   probability measure on the algebraic dual E → ℝ whose characteristic
   functional φ(f) = ∫ e^{iω(f)} dν(ω) is continuous on E, then ν-a.e.
   ω is actually a *continuous* linear functional (i.e., ω ∈ E').
   Informally: on nuclear spaces, continuity of the CF forces the measure
   to live on the topological dual, not just the algebraic dual.
   (Ref: Gel'fand-Vilenkin Vol. 4, Ch. IV, Thm 3)

2. **`weakDual_measurableEmbedding`** — The natural map E' → (E → ℝ) sending
   a continuous linear functional l to its underlying function f ↦ l(f) is
   a measurable embedding. This means it is injective, measurable, and its
   range is a measurable set — allowing us to transfer a measure from E → ℝ
   (that concentrates on E') down to a measure on E'.
   (Ref: Bogachev, "Measure Theory" Vol. 2, §7.14)

### Key proofs (Minlos)

| Lemma | Technique |
|-------|-----------|
| `marginalFamily_isProjective` | charFun uniqueness + sum reindexing over finset inclusions |
| `minlos_theorem` (existence) | Kolmogorov extension + `MeasurableEmbedding.comap` + `map_comap` |
| `minlos_theorem` (uniqueness) | `ext_of_charFun` on each marginal + projective limit uniqueness + `comap_map` injectivity |
| `gaussian_averaging_bound` | Pointwise bound Re(1-φ) ≤ ε + 2·qf + integral monotonicity + Gaussian·quadForm integrability via t·exp(-t) ≤ 1 |

## SazonovTightness.lean — 0 sorries, 2 axioms

| # | Definition/Lemma | Status |
|---|-----------------|--------|
| T1 | `SazonovContinuousAt` | defined |
| T2 | `marginalFun` | defined |
| T3 | `marginalFun_isPositiveDefinite` | proved |
| T4 | `one_sub_exp_neg_pos` | proved |
| T5 | `exp_neg_le_exp_neg` | proved |
| T6 | `one_sub_exp_half_sq_pos` | proved |
| T7 | `tail_bound_from_exp_integral` | proved (Chebyshev/Markov via set integrals) |
| T8a | `fubini_gaussian_charFun` | axiom |
| T8b | `gaussian_quadForm_integral_le` | axiom |
| T8 | `gaussian_averaging_bound` | proved (from T8a + T8b + pointwise bound + integrability) |
| T9 | `restrictOp` | proved (definition via π ∘ S ∘ ι) |
| T10 | `restrictOp_isPositive` | proved (symmetry via adjoint, nonneg via quadForm) |
| T11 | `restrictOp_quadForm` | proved (PiLp.inner_apply + sum_inner) |
| T12a | `orthonormal_diag_le_hilbert_trace` | proved (P/Q projection + Parseval + HasSum arithmetic) |
| T12b | `restrictOp_trace_eq_diag` | proved (trace basis independence via LinearMap.trace) |
| T12c | `restrictOp_trace_le` | proved (from T12a + T12b) |
| T13 | `scaled_tail_bound` | proved (from T7 + T8) |
| T14 | `exists_R_for_tail_bound` | proved |
| T15 | `sazonov_tightness` | proved (from T7–T14) |

### Axioms (SazonovTightness)

1. **`fubini_gaussian_charFun`** — Fubini identity for Gaussian averaging:
   ∫_μ (1-exp(-σ²‖y‖²/2)) = C⁻¹ ∫ exp(-b‖x‖²) Re(1-φ(x)) dx,
   where b = 1/(2σ²) and C = ∫ exp(-b‖x‖²) dx. Requires constructing
   the Gaussian measure, showing its charFun is exp(-σ²‖y‖²/2), and Fubini.

2. **`gaussian_quadForm_integral_le`** — Gaussian second moment bound:
   C⁻¹ ∫ exp(-b‖x‖²) ⟪x,Sx⟫ dx ≤ σ²·Tr(S). Requires computing
   E_γ[⟪x,Sx⟫] = σ²·∑ᵢ ⟪eᵢ,Seᵢ⟫ via ONB decomposition or
   differentiation of the Gaussian integral formula.

## Sazonov.lean — 0 sorries, 0 axioms

| # | Definition/Lemma | Status |
|---|-----------------|--------|
| S1 | `IsPositiveTraceClass` | defined |
| S2 | `quadForm` | defined |
| S3 | `quadForm_nonneg` | proved |
| S4 | `quadForm_add` | proved |
| S5 | `inner_sq_le_quadForm_mul` (Cauchy-Schwarz for ⟪·, S·⟫) | proved |
| S6 | `sqrt_quadForm_add_le` (triangle inequality) | proved |
| S7 | `sazonovSeminorm` | defined (all fields proved) |
| S8 | `sazonovTopology` | defined (via `SeminormFamily.moduleFilterBasis`) |

## Notes

- `#print axioms bochner_theorem` shows only: `propext`, `Classical.choice`, `Quot.sound`.
- The proof is structured through FejerPD.lean which proves `Re(𝓕φ(ξ)) ≥ 0` via
  Fejér-averaged double integrals and overlap-ratio kernels.
- `pd_double_integral_re_nonneg` (formerly an axiom) proved via simple function
  approximation: `StronglyMeasurable.approx` for `id : V → V`, double application
  of dominated convergence, and the discrete PD condition for finite sums with
  real (measure) coefficients.
- `fejer_avg_eq_integral` (formerly an axiom) proved via Fubini
  (`integral_integral_swap`) + indicator function manipulation + `dist_comm`.
