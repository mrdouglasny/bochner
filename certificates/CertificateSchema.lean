/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Certificate Schema

Lean 4 structures for axiom provenance certificates. These types define
machine-readable metadata for tracking where axioms are proved.
-/

/-! ## Schema Types -/

/-- How the axiom was verified. -/
inductive VerificationMethod where
  | LeanProof         -- Proved in a Lean 4 library
  | SymbolicAlgebra   -- Verified by computer algebra system
  | VerifiedNumerics  -- Interval arithmetic or proof-producing numerics
  | TextbookCitation  -- Cited from published mathematics
  | PeerReview        -- Reviewed by domain expert
  deriving Repr, BEq

/-- Status of the certificate. -/
inductive CertificateStatus where
  | Verified          -- Full machine-checked or human-verified proof exists
  | Cited             -- Referenced in literature but not machine-verified
  | Conjectured       -- Expected to hold, no proof yet
  deriving Repr, BEq

/-- Import vs export role. -/
inductive CertificateRole where
  | Import            -- Axiom consumed from an external source
  | Export            -- Result proved here, offered to downstream consumers
  deriving Repr, BEq

/-- A source reference. -/
structure Source where
  repo       : Option String := none   -- Git repository URL
  commit     : Option String := none   -- Commit hash
  file       : Option String := none   -- File path within the repository
  leanName   : Option String := none   -- Fully qualified Lean declaration name
  doi        : Option String := none   -- DOI for published sources
  textRef    : Option String := none   -- Human-readable citation
  url        : Option String := none   -- Any other URL
  migratedTo : Option String := none   -- Target repo if this source is historical
  migratedOn : Option String := none   -- ISO date of migration
  deriving Repr

/-- A migration target — where the proof is expected to land eventually. -/
structure MigrationTarget where
  repo     : String                    -- Target repository URL
  leanName : Option String := none     -- Expected declaration name in target
  tracking : Option String := none     -- PR/issue URL tracking the upstream effort
  deriving Repr

/-- Certificate metadata. -/
structure CertificateInfo where
  axiomName        : String            -- The Lean declaration name
  statement        : String            -- The Lean type signature as a string
  role             : CertificateRole
  status           : CertificateStatus
  method           : VerificationMethod
  sources          : List Source       -- Ordered newest-first
  proofSummary     : Option String := none
  date             : String            -- ISO 8601 date of last verification
  sourceHash       : Option String := none  -- For Import: SHA-256 of source's export cert
  exportCertPath   : Option String := none  -- For Import: path to export cert in source repo
  migrationTargets : List MigrationTarget := []
  superseded       : Bool := false
  deriving Repr
