# Exports Catalog

Public definitions, theorems, and classes exported by this project.

## Main Theorems

| Name | File | Type Signature |
|------|------|---------------|
| `bochner_theorem` | Main.lean | `(φ : V → ℂ) → Continuous φ → IsPositiveDefinite φ → φ 0 = 1 → ∃! μ : ProbabilityMeasure V, ∀ ξ, charFun μ ξ = φ ξ` |
| `minlos_theorem` | Minlos.lean | `[IsHilbertNuclear E] [SeparableSpace E] → (Φ : E → ℂ) → Continuous Φ → IsPositiveDefinite Φ → Φ 0 = 1 → ∃! μ : ProbabilityMeasure (WeakDual ℝ E), ∀ f, Φ f = ∫ ω, exp(I * ω f) ∂μ` |
| `isHilbertNuclear_of_nuclear` | PietschBridge.lean | `IsNuclear E → IsHilbertNuclear E` |

## Classes and Structures

| Name | File | Description |
|------|------|-------------|
| `IsPositiveDefinite φ` | PositiveDefinite.lean | PD condition: `∑ᵢⱼ cᵢ* cⱼ φ(xᵢ - xⱼ) ≥ 0` |
| `IsHilbertNuclear E` | NuclearSpace.lean | Hilbertian seminorms with HS embeddings (Gel'fand-Vilenkin) |
| `IsNuclear E` | PietschBridge.lean | Pietsch nuclear dominance: `p(x) ≤ Σ |fₙ(x)| cₙ` |
| `Seminorm.IsHilbertian p` | NuclearSpace.lean | Parallelogram law: `p(x+y)² + p(x-y)² = 2(p(x)² + p(y)²)` |
| `Seminorm.IsOrthonormalSeq p e` | NuclearSpace.lean | `p.innerProd(eᵢ, eⱼ) = δᵢⱼ` |
| `Seminorm.IsHilbertSchmidtEmbedding p q` | NuclearSpace.lean | `q ≤ p` and `∑ q(eₖ)² ≤ C` for all p-ONS |
| `IsNuclearMap T` | NuclearSpace.lean | `T(x) = Σ φₙ(x) • yₙ` with `Σ ‖φₙ‖‖yₙ‖ < ∞` |
| `IsPositiveTraceClass S` | Sazonov.lean | Positive self-adjoint trace-class operator |
| `SazonovIndex H` | Sazonov.lean | Index type for Sazonov seminorm family |

## PositiveDefinite.lean

| Name | Signature |
|------|-----------|
| `IsPositiveDefinite.conj_symm` | `φ(-x) = conj(φ(x))` |
| `IsPositiveDefinite.eval_zero_nonneg` | `0 ≤ (φ 0).re` |
| `IsPositiveDefinite.eval_zero_real` | `(φ 0).im = 0` |
| `IsPositiveDefinite.bounded_by_zero` | `‖φ(x)‖ ≤ (φ 0).re` |
| `IsPositiveDefinite.mul` | `PD φ → PD ψ → PD (φ * ψ)` (Schur product) |
| `isPositiveDefinite_precomp_linear` | `PD ψ → PD (ψ ∘ T)` for linear T |

## FejerPD.lean

| Name | Signature |
|------|-----------|
| `pd_l1_fourier_re_nonneg_theorem` | `PD φ → Integrable φ → Continuous φ → 0 ≤ (𝓕φ ξ).re` |

## Main.lean

| Name | Signature |
|------|-----------|
| `isPositiveDefinite_charFun` | `IsPositiveDefinite (charFun μ)` |
| `isPositiveDefinite_gaussian` | `IsPositiveDefinite (x ↦ exp(-ε‖x‖²))` |
| `pd_l1_fourier_nonneg` | `PD + L¹ + continuous → 𝓕φ ≥ 0 and real` |
| `measure_of_pd_l1` | `PD + L¹ + normalized + FT integrable → ∃ μ, charFun μ = φ` |
| `gaussianRegularize_pd` | `PD φ → PD (φ · exp(-ε‖·‖²))` |
| `gaussianRegularize_integrable` | `PD + continuous → φ_ε integrable` |
| `gaussianRegularize_ft_integrable` | `PD + continuous → 𝓕(φ_ε) integrable` |
| `gaussianRegularize_measures_tight` | `PD + continuous + normalized → {μ_ε} tight` |
| `bochner_theorem` | Main theorem (existence + uniqueness) |

## Sazonov.lean

| Name | Signature |
|------|-----------|
| `quadForm S x` | `⟪x, Sx⟫` |
| `quadForm_nonneg` | `S positive → 0 ≤ quadForm S x` |
| `quadForm_add` | Expansion of `quadForm S (x + y)` |
| `inner_sq_le_quadForm_mul` | Cauchy-Schwarz: `⟪x,Sy⟫² ≤ qf(x) · qf(y)` |
| `sqrt_quadForm_add_le` | Triangle inequality for `√(qf)` |
| `sazonovSeminorm S` | Seminorm from positive operator |
| `sazonovTopology H` | Sazonov topology on Hilbert space |

## Minlos/NuclearSpace.lean

| Name | Signature |
|------|-----------|
| `Seminorm.innerProd p x y` | Polarization: `(p(x+y)² - p(x-y)²) / 4` |
| `WeakDual.eval_measurable f` | `l ↦ l(f)` is measurable (cylinder σ-algebra) |

## Minlos/PietschBridge.lean

| Name | Signature |
|------|-----------|
| `hilbertianLift f c q` | `r(x) = √(Σ fₙ(x)² cₙ)` — Hilbertian seminorm from nuclear expansion |
| `hilbertianLift_isHilbertian` | Parallelogram law holds |
| `hilbertianLift_dominates` | `p(x) ≤ r(x)` via Cauchy-Schwarz |
| `hilbertianLift_le_dominator` | `r(x) ≤ q(x)` |
| `Seminorm.innerProd_self` | `p.innerProd(x,x) = p(x)²` |
| `Seminorm.innerProd_comm` | Symmetry |
| `Seminorm.innerProd_add_left` | Bilinearity (left, for Hilbertian) |
| `Seminorm.innerProd_smul_left` | `p.innerProd(a•x, y) = a · p.innerProd(x,y)` |
| `Seminorm.innerProd_sum_left` | Left-linearity over finite sums |
| `bessel_hilbertian` | `|φ| ≤ R, R-ONS {eⱼ} → Σ φ(eⱼ)² ≤ 1` |
| `isHilbertSchmidtEmbedding_of_nuclear` | HS embedding from nuclear expansion |
| `isHilbertNuclear_of_nuclear` | `IsNuclear E → IsHilbertNuclear E` |

## Minlos/SazonovTightness.lean

| Name | Signature |
|------|-----------|
| `SazonovContinuousAt φ` | CF continuous at 0 in Sazonov topology |
| `marginalFun φ v` | `t ↦ φ(Σ tⱼ vⱼ)` — finite-dim marginal CF |
| `marginalFun_isPositiveDefinite` | Marginal CF is PD |
| `tail_bound_from_exp_integral` | Chebyshev: `P(‖y‖ ≥ R) ≤ C/(1-exp(-σ²R²/2))` |
| `fubini_gaussian_charFun` | Gaussian averaging Fubini identity |
| `gaussian_quadForm_integral_le` | `∫ g · qf ≤ σ² · Tr(S)` via spectral decomposition |
| `gaussian_averaging_bound` | `∫ (1-exp(-σ²‖x‖²/2)) ≤ ε + 2σ²·Tr(S)` |
| `restrictOp S v` | Restriction of operator to finite-dim subspace |
| `restrictOp_isPositive` | Positivity preserved under restriction |
| `restrictOp_trace_le` | `Tr(S|_V) ≤ Tr(S)` via Parseval |
| `sazonov_tightness` | Sazonov CF continuity → tightness |

## Minlos/MinlosConcentration.lean

| Name | Signature |
|------|-----------|
| `concentrationBadSet d p C` | `{ω | ∃ c : ℕ →₀ ℚ, |ω(x_c)| > C · p(x_c)}` |
| `concentrationBadSetN d p C N` | Support-restricted bad set |
| `combined_quadratic_bound` | `1 - Re(Φ(x)) ≤ ε + K·p(x)²` |
| `joint_kernel_bound_finite` | Gaussian averaging on kernel elements |
| `tail_bound_uniform` | Dimension-free Gaussian tail bound via Gram matrix |
| `gram_schmidt_seminorm` | ONB construction for Hilbertian seminorms |
| `linear_combination_ae` | `ω(Σ βⱼ eⱼ) = Σ βⱼ ω(eⱼ)` a.e. from h_cf_joint |
| `nuclear_cylindrical_concentration` | Full concentration bound |
| `minlos_concentration` | Convenience wrapper |

## Minlos/FinDimMarginals.lean

| Name | Signature |
|------|-----------|
| `marginalCF Φ J` | Marginal CF on EuclideanSpace |
| `marginalCF_continuous` | Continuity |
| `marginalCF_pd` | Positive definiteness |
| `marginal_measure_exists` | Bochner → marginal measure exists |

## Minlos/ProjectiveFamily.lean

| Name | Signature |
|------|-----------|
| `marginalMeasure Φ J` | Marginal probability measure |
| `marginalFamily Φ` | Family of marginals indexed by finsets |
| `marginalFamily_isProjective` | Kolmogorov consistency |
| `marginalProjectiveLimit Φ` | Projective limit measure on `E → ℝ` |

## Minlos/MeasurableModification.lean

| Name | Signature |
|------|-----------|
| `weakDualEmbed E` | Canonical embedding `WeakDual ℝ E → (E → ℝ)` |
| `measurableProjection` | Measurable map `(E → ℝ) →ₘ WeakDual ℝ E` |
| `extensionCLM` | BLT extension of ω to continuous linear functional |
| `measurable_measurableProjection` | P is measurable |
| `projection_embed_eq` | `P ∘ embed = id` |
| `projection_ae_eq` | `P(ω)(f) = ω(f)` ν-a.e. |
| `qLinearPaths_ae` | ℚ-linearity a.e. |
| `boundedPaths_ae` | Boundedness a.e. |

## Minlos/Main.lean

| Name | Signature |
|------|-----------|
| `minlos_theorem` | Main theorem: `[IsHilbertNuclear E] → PD + cont + normalized Φ → ∃! μ on E', charFun = Φ` |
| `minlos_uniqueness` | Uniqueness of representing measure |
