# Bochner's Theorem — Status

**Total: 0 sorries, 2 axioms**

## PositiveDefinite.lean — 0 sorries

| # | Lemma | Layer | Difficulty | Status |
|---|-------|-------|------------|--------|
| 1 | `IsPositiveDefinite.mul` | 0 | Medium | proved |

## FejerPD.lean — 0 sorries, 2 axioms

| # | Lemma | Layer | Difficulty | Status | Depends on |
|---|-------|-------|------------|--------|------------|
| F1 | `isPositiveDefinite_exp_inner` | 0 | Medium | proved | — |
| F2 | `pd_double_integral_re_nonneg_ax` | 1 | Hard | axiom ✅ | — |
| F3 | `overlapRatio_tendsto_one` | 0 | Medium | proved | — |
| F4 | `fejer_avg_eq_integral_ax` | 1 | Hard | axiom ✅ | — |
| F5 | `pd_integral_re_nonneg` | 1 | Medium | proved | F2, F3, F4 |
| F6 | `pd_l1_fourier_re_nonneg_theorem` | 1 | Medium | proved | F1, F5 |

## Bochner.lean — 0 sorries, 0 axioms (depends on FejerPD axioms)

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

## Proved

| Lemma | Notes |
|-------|-------|
| `conj_symm` | From `.hermitian` field |
| `eval_zero_nonneg` | m=1, c₁=1 specialization |
| `eval_zero_real` | Im(φ(0))=0 from Hermitian symmetry |
| `bounded_by_zero` | 2×2 Cauchy-Schwarz |
| `isPositiveDefinite_precomp_linear` | Composition with linear maps |
| `isPositiveDefinite_charFun` | Forward Bochner: charFun of finite measure is PD |
| `isPositiveDefinite_mul_charFun` | Continuous Schur product: φ · charFun(μ) is PD |
| `isPositiveDefinite_gaussian` | Via `gaussian_eq_charFun` + `isPositiveDefinite_charFun` |
| `gaussianRegularize_pd` | Via `gaussian_eq_charFun` + `isPositiveDefinite_mul_charFun` |
| `gaussianRegularize_integrable` | Bounded × Gaussian decay |
| `gaussianRegularize_tendsto` | exp(-ε‖x‖²) → 1 as ε → 0 |
| `pd_l1_fourier_nonneg` | Im=0 proved + Re≥0 from FejerPD |
| `pd_l1_fourier_real_nonneg` | Derived from `pd_l1_fourier_nonneg` |
| `gaussianRegularize_zero` | φ_ε(0) = φ(0) |
| `IsPositiveDefinite.mul` | Schur product via PSD kernel matrices + Kronecker/submatrix |
| `gaussian_eq_charFun` | Gaussian measure via withDensity + integral_cexp_neg_mul_sq_norm_add |
| `measure_of_pd_l1` | Fourier scaling + inversion + withDensity construction |
| `gaussianRegularize_ft_integrable` | Fatou's lemma + Parseval bound with Gaussian cutoffs |
| `gaussianRegularize_measures_tight` | Tightness via `isTightMeasureSet_of_inner_tendsto` + charFun tail bound |
| `bochner_theorem` (existence) | Assembly: Prokhorov + weak convergence + charFun limit |
| `bochner_theorem` (uniqueness) | From Mathlib's `Measure.ext_of_charFun` |
| `isPositiveDefinite_exp_inner` | exp(2πi⟨·,ξ⟩) PD: sum = |∑ cₖ eₖ|² ≥ 0 |
| `inner_integral_sub` | Haar translation: ∫ y in B, ψ(x-y) = ∫ v in B(x), ψ(v) |
| `overlapRatio_tendsto_one` | Squeeze: ((n-‖v‖)/n)^d ≤ ratio ≤ 1, both → 1 |
| `pd_integral_re_nonneg` | Fejér average + DCT + ge_of_tendsto' |
| `pd_l1_fourier_re_nonneg_theorem` | Schur product with exp character + pd_integral_re_nonneg |

## Axioms

### Axiom 1: `pd_double_integral_re_nonneg_ax` — ✅ Verified (Gemini 2.5 Pro)

Let V be a finite-dimensional real inner product space, ψ : V → ℂ a continuous positive-definite function, and S ⊆ V a bounded measurable set. Then:

$$\operatorname{Re}\!\left(\int_S \int_S \psi(x - y)\, dy\, dx\right) \geq 0$$

**Proof strategy**: Partition S into small cells {Cᵢ} with centers xᵢ. The Riemann sum ∑ᵢⱼ ψ(xᵢ - xⱼ) vol(Cᵢ) vol(Cⱼ) is a PD double sum with real positive coefficients cᵢ = vol(Cᵢ), so Re ≥ 0. The sum converges to the integral by uniform continuity of ψ on {x - y : x, y ∈ S}.

**Ref**: Rudin, *Fourier Analysis on Groups*, Theorem 1.4.3, step 1.

### Axiom 2: `fejer_avg_eq_integral_ax` — ✅ Verified (Gemini 2.5 Pro)

Let V be a finite-dimensional real inner product space, ψ : V → ℂ continuous and integrable, R > 0, and B_R = {x ∈ V : ‖x‖ ≤ R}. Define the overlap ratio:

$$h_R(v) = \frac{\operatorname{vol}(B_R \cap B_R(v))}{\operatorname{vol}(B_R)}, \qquad B_R(v) = \{x \in V : \|x - v\| \leq R\}$$

Then:

$$\frac{1}{\operatorname{vol}(B_R)} \int_{B_R} \int_{B_R} \psi(x - y)\, dy\, dx = \int_V h_R(v)\, \psi(v)\, dv$$

**Proof strategy**: Substitute v = x - y in the inner integral (Haar invariance), then swap order of integration (Fubini). The symmetry dist(x,v) = dist(v,x) converts the inner integral over x into vol(B_R ∩ B_R(v)).

**Ref**: Folland, *A Course in Abstract Harmonic Analysis*, §4.2.

## Recommended work order

**Next**: Eliminate the 2 remaining axioms:
- `pd_double_integral_re_nonneg_ax`: Requires formalizing Riemann sum → integral convergence for continuous functions on bounded sets
- `fejer_avg_eq_integral_ax`: Requires Fubini (integral_integral_swap) + indicator function manipulation + dist_comm symmetry

## Notes

- The main theorem `bochner_theorem` now compiles (modulo 2 integration theory axioms).
  `#print axioms bochner_theorem` shows: `fejer_avg_eq_integral_ax`, `pd_double_integral_re_nonneg_ax`, plus standard Lean axioms.
- The proof is structured through FejerPD.lean which reduces `Re(𝓕φ(ξ)) ≥ 0` to two
  clean integration theory facts: (1) PD double integral positivity, (2) Fubini identity.
- `gaussianRegularize_ft_integrable` proved via Fatou's lemma: approximate
  ‖𝓕 φ_ε‖ by ‖𝓕 φ_ε * exp(-‖ξ‖²/(n+1))‖, each bounded by (φ 0).re
  via Parseval identity, then take liminf.
- `pd_l1_fourier_nonneg` Im=0: proved via Hermitian symmetry +
  `integral_conj` + `integral_neg_eq_self` (change of variables v → -v).
- `IsPositiveDefinite` is a `structure` with two fields:
  `hermitian` (φ(-x) = conj(φ(x))) and `nonneg` (Re ≥ 0 condition)
- `gaussianRegularize_measures_tight` proved using `isTightMeasureSet_of_inner_tendsto`,
  `measureReal_abs_inner_gt_le_integral_charFun`, and continuity of φ at 0.
