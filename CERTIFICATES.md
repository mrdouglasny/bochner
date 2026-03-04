# Certificate System for Formal Mathematics

A general-purpose system for tracking axiom provenance in Lean 4 formal mathematics projects. Certificates document where each axiom is justified — whether by a Lean proof in another library, symbolic computation, verified numerics, or textbook citation — in a format that is both valid Lean source and machine-verifiable.

## Motivation

Formal math projects routinely use Lean's `axiom` keyword as a placeholder for results proved elsewhere. Without systematic tracking:
- It is unclear which axioms have proofs and where they live
- Cross-repository dependencies are invisible to consumers
- There is no standard way to record non-Lean justifications (CAS verification, textbook theorems)
- Axiom statements can drift out of sync with their proofs

Certificates solve this by providing a single artifact per axiom that is:
1. **Valid Lean source** — importable and type-checked by `lake build`
2. **Human-readable** — structured doc comments with provenance metadata
3. **Machine-verifiable** — a script can check hashes, resolve sources, and type-check
4. **Tamper-evident** — SHA-256 hash detects unauthorized modifications

## Certificate File Format

Each certificate is a `.lean` file with three layers:

### Layer 1: Structured Doc Comment

A `/-! ... -/` block with fixed fields in Markdown:

```lean
/-!
# Certificate: my_axiom_name

## Metadata
- **Axiom**: `my_axiom_name`
- **Status**: Verified
- **Method**: LeanProof
- **Date**: 2026-03-04

## Source
- **Repository**: https://github.com/org/repo
- **Commit**: abc1234def5678...
- **File**: Path/To/File.lean
- **Declaration**: Namespace.my_axiom_name
- **DOI**: (none)

## Proof Summary
Brief human-readable description of the proof strategy.

## SHA-256
HASH: <sha256 hex digest, computed with this line set to "HASH: PENDING">
-/
```

### Layer 2: Lean Type Check

The certificate imports the file that declares the axiom/theorem and restates its full type signature as an `example`. Lean verifies the stated type matches the actual declaration during compilation:

```lean
import MyProject.FileDeclaringAxiom

-- Restates the expected type — compilation fails if the declaration's type drifts
example : ∀ (X : Type), SomeProperty X := my_axiom_name
```

This guarantees the certificate stays in sync with the declaration it documents. If the type signature changes — added hypotheses, different type class, renamed types — the `example` won't elaborate and `lake build` fails. This is strictly stronger than `#check`, which only confirms existence without verifying the type matches any expectation.

### Layer 3: Machine-Readable Metadata

A Lean structure holding the same information programmatically, enabling tooling to query certificates:

```lean
def my_axiom_name_cert : CertificateInfo where
  axiomName    := "my_axiom_name"
  statement    := "∀ (X : Type), SomeProperty X"
  status       := .Verified
  method       := .LeanProof
  sources      := [{ repo := some "https://github.com/org/repo",
                      commit := some "abc1234", file := some "Path/To/File.lean",
                      leanName := some "Namespace.my_axiom_name" }]
  proofChain   := some "StepA → StepB → StepC"
  date         := "2026-03-04"
  sha256       := "..."
```

## Certificate Schema

Projects using this system define these shared types in a `CertificateSchema.lean`:

```lean
inductive VerificationMethod where
  | LeanProof         -- Proved in a Lean 4 library (repo + commit + file)
  | SymbolicAlgebra   -- Verified by CAS (Mathematica, Sage, Macaulay2, etc.)
  | VerifiedNumerics  -- Interval arithmetic or proof-producing numerics
  | TextbookCitation  -- Cited from published mathematics (DOI + page + theorem)
  | PeerReview        -- Reviewed by domain expert
  deriving Repr, BEq

inductive CertificateStatus where
  | Verified          -- Full machine-checked or human-verified proof exists
  | Cited             -- Referenced in literature but not machine-verified
  | Conjectured       -- Expected to hold, no proof yet
  deriving Repr, BEq

structure Source where
  repo     : Option String := none   -- Git repository URL
  commit   : Option String := none   -- Full or abbreviated commit hash
  file     : Option String := none   -- File path within the repository
  leanName : Option String := none   -- Fully qualified Lean declaration name
  doi      : Option String := none   -- DOI for published sources
  textRef  : Option String := none   -- Human-readable citation (author, title, page)
  url      : Option String := none   -- Any other URL
  deriving Repr

inductive CertificateRole where
  | Import   -- Axiom consumed from an external source
  | Export   -- Result proved here, offered to downstream consumers
  deriving Repr, BEq

structure CertificateInfo where
  axiomName   : String                -- The Lean declaration name
  statement   : String                -- The Lean type signature as a string
  role        : CertificateRole
  status      : CertificateStatus
  method      : VerificationMethod
  sources     : List Source           -- Ordered newest-first (see Reference Migration)
  proofChain  : Option String := none -- Human-readable proof outline
  date        : String                -- ISO 8601 date of last verification
  sourceHash  : Option String := none -- For Import certs: SHA-256 of the source's export cert
  deriving Repr
```

## Directory Layout

```
project/
  certificates/
    CertificateSchema.lean          -- Shared type definitions (above)
    import/                         -- Axioms THIS project consumes
      AxiomA.lean
      AxiomB.lean
    export/                         -- Results THIS project proves for others
      TheoremX.lean
  scripts/
    verify_certificates.sh          -- Verification CLI
```

**Import certificates** document axioms the project depends on, with pointers to where they are proved. **Export certificates** document theorems the project proves that other projects may want to consume as axioms.

## Trust Model: Cross-Repository Attestation

A certificate cannot meaningfully verify itself — anyone who can edit it can recompute its hash. Instead, trust comes from **agreement between independent repositories**.

### How It Works

The source repo (where the proof lives) and the consumer repo (where the axiom lives) each maintain their own certificate for the same result. Verification means checking that they agree.

**Source repo** publishes an **export certificate** in `certificates/export/`:
```
certificates/export/SchwartzIsHilbertNuclear.lean
```
This contains the theorem's metadata, proof summary, and a content hash of itself.

**Consumer repo** publishes an **import certificate** in `certificates/import/`:
```
certificates/import/SchwartzIsHilbertNuclear.lean
```
This references the source repo, commit, export certificate path, and records the **expected hash of the export certificate**.

### Verification

`--verify` performs cross-repository comparison:

1. For each import certificate, read the source repo URL, commit, and export certificate path
2. Fetch the export certificate at the pinned commit (via `gh api repos/:owner/:repo/contents/:path?ref=:commit` or raw git)
3. Compute its content hash
4. Compare against the hash stored in the import certificate

If they match: the proof is confirmed to exist at the stated location with the stated content. If they don't: something changed — the export certificate was modified, the commit was amended, or the import certificate is stale.

### What the Hash Provides

The hash acts as a **binding** between the two certificates. It is not self-verifying — it is cross-verifying. Neither repo can unilaterally forge consistency:
- If the source repo changes their export certificate, the consumer's stored hash won't match
- If the consumer repo edits their import certificate's hash, it won't match what the source actually contains
- The pinned commit prevents the source from silently replacing the certificate at the same path

### Computing the Hash

The hash covers the export certificate's full contents, with the hash line itself replaced by a placeholder during computation:

```bash
sed 's/^HASH: .*/HASH: PENDING/' export_certificate.lean | shasum -a 256 | cut -d' ' -f1
```

The import certificate stores this hash in its `sourceHash` field:
```lean
  sourceHash := "a1b2c3d4e5f6..."  -- SHA-256 of the export certificate at the pinned commit
```

## Verification Script

A shell script `scripts/verify_certificates.sh` with four modes:

### `--list`
Prints a summary table of all certificates:
```
Axiom                          Status     Method          Source
schwartz_isHilbertNuclear      Verified   LeanProof       gaussian-field@37d4f01
schwartz_separableSpace        Verified   LeanProof       gaussian-field@37d4f01
```

### `--verify`
For each certificate:
1. **Lean type-check** — run `lake env lean <file>` to verify it compiles (axiom still exists, signature matches)
2. **Cross-repo hash check** (import certs only):
   - Fetch the export certificate from the source repo at the pinned commit
   - Recompute its content hash
   - Compare against the `sourceHash` in the import certificate
3. **Source resolution** (method-dependent):
   - `LeanProof`: verify the repo/commit exists via `git ls-remote` or `gh api`
   - `TextbookCitation`: verify DOI resolves via `curl -sI https://doi.org/<doi>`
   - `SymbolicAlgebra`: check that the referenced script/output exists
4. **Migration target check**: for any declared migration targets, check if the target declaration now exists
5. Report pass/fail per certificate

### `--generate <axiom-name>`
Scaffold a new certificate file from a template, prompting for method and source information.

### `--update-hashes`
Recompute SHA-256 hashes for all certificates (use after intentional edits).

## Verification Methods in Detail

### LeanProof

The axiom is proved as a theorem in an external Lean 4 library. The certificate records:
- Repository URL and commit hash (pinning the exact version)
- File path and fully qualified declaration name
- A human-readable proof chain summarizing the argument

Verification: check that the commit exists in the remote repository and that the declaration name matches.

### SymbolicAlgebra

The axiom is verified by a computer algebra system. The certificate records:
- CAS tool and version (e.g., "Mathematica 14.0", "SageMath 10.3")
- Path to the computation script
- Hash of the script and its output
- Human-readable summary of what was computed

Verification: optionally re-run the script and compare output hashes.

### VerifiedNumerics

The axiom is verified by interval arithmetic or a proof-producing numerical tool. The certificate records:
- Tool and version (e.g., "VNODE-LP", "Arb", "CoqInterval")
- Input parameters and precision
- Output certificate or proof artifact
- Hash of the numerical certificate

### TextbookCitation

The axiom is a known result from published mathematics. The certificate records:
- DOI (when available)
- Full citation: author, title, year, publisher
- Specific location: page, theorem/proposition number, section
- Any notes on how the formal statement corresponds to the published one

Verification: check that the DOI resolves.

### PeerReview

The axiom has been reviewed by a domain expert. The certificate records:
- Reviewer name and affiliation
- Date of review
- Reviewer's notes or assessment
- Any conditions or caveats

## Example: Export Certificate (in source repo)

This lives in **gaussian-field** at `certificates/export/SchwartzIsHilbertNuclear.lean`:

```lean
/-!
# Export Certificate: schwartz_isHilbertNuclear

## Metadata
- **Declaration**: `GaussianField.schwartz_isHilbertNuclear`
- **Role**: Export
- **Status**: Verified
- **Method**: LeanProof
- **Date**: 2026-03-04

## Proof Summary
Schwartz space is Hilbert-nuclear via the chain:
  DyninMityaginSpace (Hermite basis)
  → NuclearSpace (Pietsch nuclear dominance)
  → IsNuclear (bochner bridge, ‖·‖ = |·| for ℝ)
  → IsHilbertNuclear (Hilbertian lift + Bessel inequality)
transferred along SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq.

## Migration Targets
- **mathlib4**: expected as `SchwartzMap.isHilbertNuclear`

## SHA-256
HASH: a1b2c3d4...
-/

import SchwartzNuclear.HermiteNuclear

-- Restates the exported type — fails to compile if the declaration changes
example {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D] :
    IsHilbertNuclear (SchwartzMap D ℝ) :=
  GaussianField.schwartz_isHilbertNuclear

open CertificateSchema in
def schwartz_isHilbertNuclear_cert : CertificateInfo where
  axiomName  := "GaussianField.schwartz_isHilbertNuclear"
  statement  := "IsHilbertNuclear (SchwartzMap D ℝ)"
  role       := .Export
  status     := .Verified
  method     := .LeanProof
  sources    := [{
    file     := some "SchwartzNuclear/HermiteNuclear.lean",
    leanName := some "GaussianField.schwartz_isHilbertNuclear"
  }]
  proofChain := some "DyninMityaginSpace → NuclearSpace → IsNuclear → IsHilbertNuclear, via CLE transfer"
  date       := "2026-03-04"
  sourceHash := none  -- Export certs don't reference another cert
```

## Example: Import Certificate (in consumer repo)

This lives in **GFF4D** at `certificates/import/SchwartzIsHilbertNuclear.lean`:

```lean
/-!
# Import Certificate: schwartz_isHilbertNuclear

## Metadata
- **Axiom**: `schwartz_isHilbertNuclear`
- **Role**: Import
- **Status**: Verified
- **Method**: LeanProof
- **Date**: 2026-03-04

## Source
- **Repository**: https://github.com/mrdouglasny/gaussian-field
- **Commit**: 37d4f01
- **Export Certificate**: certificates/export/SchwartzIsHilbertNuclear.lean
- **Declaration**: GaussianField.schwartz_isHilbertNuclear
- **Source Hash**: a1b2c3d4...

## SHA-256
HASH: f9e8d7c6...
-/

import OSforGFF.GaussianFieldBridge

-- Restates the axiom's type — fails to compile if the axiom declaration changes
example : IsHilbertNuclear (SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℝ) :=
  schwartz_isHilbertNuclear

open CertificateSchema in
def schwartz_isHilbertNuclear_cert : CertificateInfo where
  axiomName  := "schwartz_isHilbertNuclear"
  statement  := "IsHilbertNuclear (SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℝ)"
  role       := .Import
  status     := .Verified
  method     := .LeanProof
  sources    := [{
    repo     := some "https://github.com/mrdouglasny/gaussian-field",
    commit   := some "37d4f01",
    file     := some "SchwartzNuclear/HermiteNuclear.lean",
    leanName := some "GaussianField.schwartz_isHilbertNuclear"
  }]
  proofChain := some "DyninMityaginSpace → NuclearSpace → IsNuclear → IsHilbertNuclear, via CLE transfer"
  date       := "2026-03-04"
  sourceHash := some "a1b2c3d4..."  -- Must match hash of source's export cert at pinned commit
```

## Example: TextbookCitation Certificate

```lean
/-!
# Certificate: schwartz_space_is_nuclear

## Metadata
- **Axiom**: `schwartz_space_is_nuclear`
- **Status**: Cited
- **Method**: TextbookCitation
- **Date**: 2026-03-04

## Source
- **DOI**: 10.1007/978-3-642-61961-8
- **Citation**: Pietsch, A. "Nuclear Locally Convex Spaces" (Springer, 1972)
- **Location**: Chapter 4, Theorem 4.4.20, p. 187

## Notes
Pietsch proves that the Schwartz space S(ℝⁿ) is nuclear using the
eigenvalue characterization of nuclear operators. The formal statement
uses the Hilbert-nuclear characterization which is equivalent by
Theorem 4.2.6 in the same reference.

## SHA-256
HASH: e5f6a7b8...
-/

import MyProject.SchwartzAxiom

-- Restates the axiom's type — fails to compile if the axiom declaration changes
example : NuclearSpace (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ) :=
  schwartz_space_is_nuclear

open CertificateSchema in
def schwartz_space_is_nuclear_cert : CertificateInfo where
  axiomName  := "schwartz_space_is_nuclear"
  statement  := "NuclearSpace (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)"
  status     := .Cited
  method     := .TextbookCitation
  sources    := [{
    doi     := some "10.1007/978-3-642-61961-8",
    textRef := some "Pietsch, Nuclear Locally Convex Spaces (1972), Thm 4.4.20, p. 187"
  }]
  date       := "2026-03-04"
  sha256     := "e5f6a7b8..."
```

## Integration with Lake

Add certificates as a Lean library target so `lake build` type-checks them:

```lean
-- In lakefile.lean:
lean_lib «Certificates» where
  srcDir := "certificates"
```

This ensures certificate files stay in sync with the declarations they document — if a type signature changes, the `example` in the certificate won't elaborate and the build fails.

## Reference Migration

Proofs move. A result proved in a standalone library may later be incorporated into mathlib, or migrated between repositories. The certificate system handles this through **source history** and **migration detection**.

### The Problem

When `schwartz_isHilbertNuclear` is proved in gaussian-field today, the certificate points to that repo. If the proof is later upstreamed into mathlib:
- The original repo/commit still works but is no longer the canonical source
- The declaration name may change (e.g., `GaussianField.schwartz_isHilbertNuclear` becomes `SchwartzMap.isHilbertNuclear`)
- The consuming project may eventually drop the `axiom` entirely and import the result directly
- Other projects may have certificates pointing to the old location

### Source History

The `CertificateInfo` schema uses `sources: List Source` (not a single source) deliberately. When a reference migrates, **append the new source rather than replacing the old one**. The list is ordered newest-first:

```lean
sources := [
  -- Current canonical source (mathlib)
  { repo     := some "https://github.com/leanprover-community/mathlib4",
    commit   := some "def5678...",
    file     := some "Mathlib/Analysis/Schwartz/Nuclear.lean",
    leanName := some "SchwartzMap.isHilbertNuclear" },
  -- Original source (gaussian-field) — retained for provenance
  { repo     := some "https://github.com/mrdouglasny/gaussian-field",
    commit   := some "37d4f01",
    file     := some "SchwartzNuclear/HermiteNuclear.lean",
    leanName := some "GaussianField.schwartz_isHilbertNuclear" }
]
```

This preserves the full provenance chain: who proved it first, where it moved, and where it lives now.

### Migration Lifecycle

A certificate goes through these stages when its proof migrates:

1. **Active**: Proof lives in external library, axiom in consuming project. Certificate points to external library.

2. **Migrated**: Proof has been upstreamed (e.g., into mathlib). Certificate is updated:
   - New source prepended to `sources` list
   - Doc comment updated with a `## Migration History` section
   - Hash recomputed

3. **Superseded**: The consuming project now imports the result directly (no more `axiom`). The certificate transitions:
   - Status changes to `Verified` with method `LeanProof` pointing to mathlib
   - The `axiom` declaration is removed from the project
   - The certificate moves to an `archive/` subdirectory or is annotated with `superseded := true`
   - The `#check` now verifies the theorem (not axiom) exists

4. **Archived**: The certificate is retained in `certificates/archive/` for historical record but is no longer actively verified.

### Schema Extensions for Migration

```lean
structure Source where
  repo       : Option String := none
  commit     : Option String := none
  file       : Option String := none
  leanName   : Option String := none
  doi        : Option String := none
  textRef    : Option String := none
  url        : Option String := none
  migratedTo : Option String := none   -- e.g., "mathlib4" — signals this source is historical
  migratedOn : Option String := none   -- ISO date of migration
  deriving Repr

structure CertificateInfo where
  axiomName   : String
  statement   : String
  status      : CertificateStatus
  method      : VerificationMethod
  sources     : List Source            -- Ordered newest-first; full provenance chain
  proofChain  : Option String := none
  date        : String
  sha256      : String
  superseded  : Bool := false          -- True when the axiom has been eliminated
  deriving Repr
```

### Migration Targets

When creating a certificate, declare where the proof is expected to migrate. This enables automatic detection of completed migrations:

```lean
structure MigrationTarget where
  repo     : String                    -- Target repository URL
  leanName : Option String := none     -- Expected declaration name in target
  tracking : Option String := none     -- PR/issue URL tracking the upstream effort
  deriving Repr

structure CertificateInfo where
  -- ... (other fields as before)
  migrationTargets : List MigrationTarget := []  -- Where this proof is expected to land
```

Example:

```lean
  migrationTargets := [
    { repo     := "https://github.com/leanprover-community/mathlib4",
      leanName := some "SchwartzMap.isHilbertNuclear",
      tracking := some "https://github.com/leanprover-community/mathlib4/pull/NNNN" }
  ]
```

The verification script uses migration targets to **proactively check** whether a migration has completed — searching the target repo for the expected declaration name via `gh api` or `git grep` on the remote. When found, it reports:

```
schwartz_isHilbertNuclear: MIGRATION DETECTED
  → now available in mathlib4 as SchwartzMap.isHilbertNuclear
  Run: verify_certificates.sh --migrate schwartz_isHilbertNuclear
```

The `--migrate` command updates the certificate: prepends the new source, moves the old source to history, and recomputes the hash.

### Migration Detection in `--verify`

Beyond checking declared migration targets, the verification script also performs:

1. **Stale commit check**: If the source repo's default branch has moved far past the pinned commit, flag the certificate for review.

2. **Dead link check**: If `git ls-remote` fails for the pinned commit (repo deleted or force-pushed), flag as broken. The source history ensures the provenance is not lost even if the original repo disappears.

3. **Tracking link check**: If a `tracking` URL (PR or issue) is provided, check its status. A merged PR strongly suggests the migration is complete.

### Doc Comment Migration History

When a certificate is updated for migration, add a section to the doc comment:

```
## Migration History
- **2026-03-04**: Originally proved in gaussian-field (commit 37d4f01)
- **2026-09-15**: Upstreamed to mathlib4 (commit def5678) as SchwartzMap.isHilbertNuclear
- **2026-10-01**: Axiom removed from GFF4D; now imported directly from Mathlib
```

### Eliminating Axioms

The ultimate goal of many certificates is their own obsolescence — the axiom gets a proof, gets upstreamed, and the consuming project imports it directly. The certificate system supports this gracefully:

1. When the proof enters mathlib, update the certificate's primary source
2. Replace the project's `axiom` with a direct import
3. The certificate's `#check` still compiles (now checking a theorem, not an axiom)
4. Set `superseded := true` and move to `certificates/archive/`
5. The verification script reports superseded certificates as informational, not as failures

This turns the certificate from an active tracking document into a historical record of the axiom's journey from conjecture to established mathlib theorem.

## Design Principles

1. **Lean-first**: Certificates are valid `.lean` files. They compile, they type-check, they can be imported.
2. **Method-agnostic**: The same format handles Lean proofs, CAS computations, numerical certificates, and literature citations.
3. **Self-documenting**: A human can read the doc comment and understand the full provenance without any tooling.
4. **Tamper-evident**: The SHA-256 hash detects any modification, intentional or accidental.
5. **Composable**: Export certificates from one project become import certificates for downstream projects, forming a provenance chain.
6. **Minimal overhead**: One file per axiom, a shared schema, and a shell script. No external databases or services required.
