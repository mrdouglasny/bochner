# Bochner's Theorem — Status

**Total: 0 sorries, 4 axioms (1 in MeasurableModification.lean, 3 in PietschBridge.lean)**

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
| `NuclearSpace.lean` | definitions only |
| `FinDimMarginals.lean` | proved (0 sorries, 0 axioms) |
| `ProjectiveFamily.lean` | proved (0 sorries, 0 axioms) |
| `SazonovTightness.lean` | proved (0 sorries, 0 axioms) |
| `MeasurableModification.lean` | 0 sorries, 1 axiom |
| `Minlos.lean` | proved (0 sorries, 0 axioms) |
| `PietschBridge.lean` | 0 sorries, 3 axioms (bridge from Pietsch nuclearity) |

### Axiom (MeasurableModification.lean)

1. **`minlos_concentration`** — Minlos concentration bound: for a cylindrical
   measure on a nuclear space with continuous CF, paths are bounded by
   Hilbertian seminorms (Chebyshev + Gaussian averaging + Parseval + HS).
   (Gel'fand-Vilenkin, Vol. 4, Ch. IV, §3.3)

**Proved (5 former axioms → definitions/theorems):**
- **`extensionCLM`** — BLT theorem via continuous extension from dense subset.
- **`extensionCLM_eq_on_dense`** — Extension agrees with ω on dense sequence.
- **`measurable_measurableProjection`** — P is measurable (pointwise limits).
- **`qLinearPaths_ae`** — ℚ-linearity a.e. via `ae_eq_zero_of_charfun_eq_one`.
- **`boundedPaths_ae`** — Boundedness a.e. (depends on `minlos_concentration`).
- **`projection_ae_eq`** — P(ω)(f) = ω(f) ν-a.e. via DCT + CF uniqueness.

### Axioms (PietschBridge.lean)

**Proved (7 former axioms/sorries → definitions/theorems):**
1. **`hilbertianLift`** — Defined via `Seminorm.of` with Minkowski triangle inequality.
2. **`hilbertianLift_apply`** — rfl.
3. **`hilbertianLift_isHilbertian`** — Parallelogram law from linearity of fₙ.
4. **`hilbertianLift_dominates`** — Cauchy-Schwarz via `Real.tsum_le_of_sum_le` + finite CS.
5. **`hilbertianLift_le_dominator`** — Pointwise bound `(f n x)² ≤ (q x)²` + sqrt monotonicity.
6. **`isHilbertSchmidtEmbedding_of_nuclear`** — CS per j + finite/tsum swap + Bessel.
7. **`bessel_hilbertian`** — Jordan-von Neumann bilinearity (additivity from
   parallelogram law, real scaling from `map_real_smul` + density of ℚ) +
   Pythagorean theorem + `S ≤ √S ⟹ S ≤ 1` via `nlinarith`.

3 private axioms (recursive family construction):
8. **`buildHilbertianFamily_isHilbertian`** — Each family member is Hilbertian.
9. **`buildHilbertianFamily_hs`** — Adjacent family members have HS embeddings.
10. **`buildHilbertianFamily_withSeminorms`** — Family generates the topology.

**Proved from axioms:**
- **`nuclearSpace_of_pietsch`** — IsPietschNuclear E → NuclearSpace E.

### Key proofs (Minlos)

| Lemma | Technique |
|-------|-----------|
| `marginalFamily_isProjective` | charFun uniqueness + sum reindexing over finset inclusions |
| `h_cf_joint` | Factor through J.restrict, projective limit, finsetPiMeasEquiv, inner product rewrite, fiber-sum reindexing |
| `minlos_theorem` (existence) | Kolmogorov extension + measurable pushforward P + CF verification |
| `minlos_theorem` (uniqueness) | P ∘ embed = id + projective limit uniqueness + Measure.map factoring |
| `gaussian_averaging_bound` | Pointwise bound Re(1-φ) ≤ ε + 2·qf + integral monotonicity + Gaussian·quadForm integrability via t·exp(-t) ≤ 1 |
| `gaussian_quadForm_integral_le` | Spectral decomposition + cosh bound (x²/2 ≤ cosh(x)-1) + ge_of_tendsto for (exp(tA)-1)/t → A + ULift reindex for universe bridging |

## SazonovTightness.lean — 0 sorries, 0 axioms

| # | Definition/Lemma | Status |
|---|-----------------|--------|
| T1 | `SazonovContinuousAt` | defined |
| T2 | `marginalFun` | defined |
| T3 | `marginalFun_isPositiveDefinite` | proved |
| T4 | `one_sub_exp_neg_pos` | proved |
| T5 | `exp_neg_le_exp_neg` | proved |
| T6 | `one_sub_exp_half_sq_pos` | proved |
| T7 | `tail_bound_from_exp_integral` | proved (Chebyshev/Markov via set integrals) |
| T8a | `fubini_gaussian_charFun` | proved (Fubini + Gaussian Fourier transform) |
| T8b | `gaussian_quadForm_integral_le` | proved (spectral decomposition + cosh bound + ge_of_tendsto) |
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
- `#print axioms minlos_theorem` shows 1 axiom from MeasurableModification
  (`minlos_concentration`) + standard. No `sorryAx`.
- `#print axioms nuclearSpace_of_pietsch` shows 3 private axioms from PietschBridge
  (`buildHilbertianFamily_{isHilbertian,hs,withSeminorms}`) + standard. No `sorryAx`.
- The proof is structured through FejerPD.lean which proves `Re(𝓕φ(ξ)) ≥ 0` via
  Fejér-averaged double integrals and overlap-ratio kernels.
- `pd_double_integral_re_nonneg` (formerly an axiom) proved via simple function
  approximation: `StronglyMeasurable.approx` for `id : V → V`, double application
  of dominated convergence, and the discrete PD condition for finite sums with
  real (measure) coefficients.
- `fejer_avg_eq_integral` (formerly an axiom) proved via Fubini
  (`integral_integral_swap`) + indicator function manipulation + `dist_comm`.
