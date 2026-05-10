# Axiom audit — bochner

*Last updated 2026-05-10.*

## Purpose

In this project, an **axiom** is a *vetted provable theorem with a vetted
discharge plan* — not a fundamental unprovable assumption. Each axiom
listed below is:

1. A standard textbook fact, with explicit literature citation.
2. Reviewed for type correctness, hypothesis sufficiency, and
   non-vacuity (typically by a Gemini deep-think pass and/or a
   literature cross-check).
3. Accompanied by a concrete plan to discharge it into a Lean theorem
   (inline in the row, or linked to a dedicated discharge-plan doc).

We use the `axiom` keyword as a *staging point* — it lets the project
proceed to use a result before its full Lean proof is assembled, while
keeping the trust boundary explicit and discharge progress trackable.
The goal is for every entry below to eventually become a proved
theorem.

Format and conventions for this audit doc:
`~/.claude/AXIOM_AUDIT_FORMAT.md`.

---

## Headline status

**Main library axioms: 0.**

`bochner_theorem` and `minlos_theorem` are fully proved (`#print
axioms` shows only `propext`, `Classical.choice`, `Quot.sound` —
standard logical axioms). See README for proof outline.

**Test/demo axioms: 4** (all in `Test/WhiteNoise.lean` — *not load-bearing
for the main library*; instance-provider axioms used to demonstrate the
white-noise construction).

---

## Test/demo axioms (Test/WhiteNoise.lean)

These instance-provider axioms enable the white-noise construction
demo. They are *not* consumed by `bochner_theorem` or `minlos_theorem`
themselves.

| Axiom | File:Line | Rating | Vetting | Strategy / Plan |
|---|---|---|---|---|
| `schwartz_separableSpace` | `Test/WhiteNoise.lean` | Standard | LP | Hermite basis is countable + dense in `𝓢(ℝ)`. Provable from Mathlib's `SchwartzMap` API + Hermite expansion. |
| `schwartz_isHilbertNuclear` | `Test/WhiteNoise.lean` | Standard | LP | Hermite-Sobolev norms `‖f‖_k² = Σ (1+n)^{2k} |⟨f, hₙ⟩|²` are Hilbertian, generate the Schwartz topology, and have Hilbert-Schmidt consecutive inclusions (since `Σ (1+n)^{-2} < ∞`). Bridge: `gaussian-field` proves `DyninMityaginSpace → NuclearSpace` (Pietsch); `isHilbertNuclear_of_nuclear` (proved here, 0 axioms) completes the chain. |
| `schwartzMap_l2Norm_continuous` | `Test/WhiteNoise.lean` | Standard | LP, SA | Continuity of `f ↦ ∫ f²` on `𝓢(ℝ)`. Follows from rapid decay: `∫ f² ≤ (∫ (1+x²)⁻¹) · sup_x (1+x²)|f(x)|²`, so dominated by Schwartz seminorms `‖x^α f‖_∞`. |
| `whiteNoiseCF_pd` | `Test/WhiteNoise.lean` | Standard | LP | The white-noise characteristic functional `exp(-½‖f‖²_L²)` is positive-definite. Provable from Schoenberg's theorem (Gaussian RBF is PD on any inner-product space) + pullback via `isPositiveDefinite_precomp_linear`. |

---

## Strategy

The 4 test-demo axioms are all standard and dischargeable, but the
main library is already complete and they are scope-creep relative to
bochner/minlos. They serve as concrete instance providers for the
white-noise existence demo and could be discharged when broader
nuclear-space + Schwartz-space infrastructure (currently in
`gaussian-field`) is upstreamed or imported into `bochner`.

---

## Verification

```
find . -name '*.lean' -not -path './.lake/*' -not -path './future/*' \
  | xargs grep -lE '^axiom '
```
