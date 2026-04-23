import VerifiedMBSE.Matrix.Query

/-!
# Model Boundary: Explicit Declaration of What Is Not Verified

Formal verification only guarantees properties on the *inside* of a
model. This module treats the *outside* of the model as a first-class
object so that "the V&V matrix is green" is not conflated with
"the real system is safe".

A `ModelBoundary` records:

- properties verified formally,
- properties supported by test or analysis rather than proof, and
- residual risks deliberately left out of the model, each annotated
  with a rationale and a mitigation.

The intent is epistemic honesty, not bookkeeping. When the system
changes, the boundary description should be revisited.

## Dependency on `VMatrix`

`ModelBoundary` is parameterized by the `VMatrix` it describes:
`ModelBoundary (vm : VMatrix)`. Accidentally reusing a boundary
description for a different system therefore produces a type error.
The `verifiedCount` field is not stored but derived as a function of
`vm.totalRecords`, so it cannot drift out of sync with the matrix.

Because of the `VMatrix` dependency, this file lives in the `Matrix`
namespace rather than `VV`.
-/

namespace VerifiedMBSE.Matrix

-- ============================================================
-- §1  Risk Categories
-- ============================================================

/-- Category of an unmodeled risk. -/
inductive RiskCategory where
  /-- Physical phenomena outside the formal model (single-event upsets
      from cosmic rays, micrometeoroid impact, material fatigue, ...). -/
  | physical
  /-- Environmental factors (solar activity, thermal extremes, radiation). -/
  | environmental
  /-- Human factors (operator error, procedure misuse, inadequate training). -/
  | human
  /-- Software risks outside the verification boundary (COTS, firmware, OS). -/
  | software
  /-- Hardware risks (manufacturing defects, aging, part substitution). -/
  | hardware
  /-- Organizational and process risks (change management, supply chain). -/
  | organizational
  deriving Repr, BEq, DecidableEq

/-- Human-readable category name. -/
def RiskCategory.toString : RiskCategory → String
  | .physical       => "Physical"
  | .environmental  => "Environmental"
  | .human          => "Human"
  | .software       => "Software"
  | .hardware       => "Hardware"
  | .organizational => "Organizational"

instance : ToString RiskCategory := ⟨RiskCategory.toString⟩

-- ============================================================
-- §2  Evidence Kinds
-- ============================================================

/-- Strength of the evidence supporting a property. Distinguishes proof
    from test and analysis so that `ModelBoundary` does not hide the
    difference. -/
inductive EvidenceKind where
  /-- Formal proof in Lean. -/
  | verified
  /-- Supported by a test campaign (unit test, HIL, qualification). -/
  | tested
  /-- Supported by an analysis method (FMEA, FTA, Monte Carlo). -/
  | analyzed
  deriving Repr, BEq, DecidableEq

/-- Human-readable evidence-kind name. -/
def EvidenceKind.toString : EvidenceKind → String
  | .verified => "Verified"
  | .tested   => "Tested"
  | .analyzed => "Analyzed"

instance : ToString EvidenceKind := ⟨EvidenceKind.toString⟩

-- ============================================================
-- §3  Unmodeled Risk
-- ============================================================

/-- A risk the formal model does not cover. Requires an explicit
    rationale and mitigation so the engineer is forced to name and
    justify the gap. -/
structure UnmodeledRisk where
  /-- Short description of the risk. -/
  description : String
  /-- Category of the risk. -/
  category : RiskCategory
  /-- Rationale for leaving this risk out of the formal model. -/
  rationale : String
  /-- Non-formal mitigation (process, test, redundancy, operational constraint). -/
  mitigation : String
  deriving Repr

-- ============================================================
-- §4  Non-Verified Property
-- ============================================================

/-- A property supported by test or analysis but not proved formally. -/
structure NonFormalProperty where
  /-- Description of the property. -/
  description : String
  /-- Kind of non-formal evidence (`.tested` or `.analyzed`). -/
  kind : EvidenceKind
  /-- Reference to the supporting source (report ID, test campaign name, ...). -/
  source : String
  deriving Repr

-- ============================================================
-- §5  Model Boundary (Dependently Typed on VMatrix)
-- ============================================================

/-- Composite view of what the model covers together with the risks
    outside it.

    Parameterizing by the target `VMatrix` ties the boundary to a
    specific matrix: accidentally reusing a boundary description for a
    different system produces a type error. `verifiedCount` is derived
    from `vm.totalRecords` as a function rather than stored, so it
    cannot drift out of sync. -/
structure ModelBoundary (vm : VMatrix) where
  /-- Identifier of this boundary (typically the system name). -/
  systemName : String
  /-- Properties supported by test or analysis but not proved. -/
  nonFormal : List NonFormalProperty
  /-- Risks deliberately left out of the formal model. -/
  unmodeled : List UnmodeledRisk
  deriving Repr

/-- Number of formally verified properties, derived from the total
    record count of the target `VMatrix`. -/
def ModelBoundary.verifiedCount {vm : VMatrix} (_ : ModelBoundary vm) : Nat :=
  vm.totalRecords

/-- Number of unmodeled risks. -/
def ModelBoundary.unmodeledCount {vm : VMatrix} (mb : ModelBoundary vm) : Nat :=
  mb.unmodeled.length

/-- Number of non-formal properties. -/
def ModelBoundary.nonFormalCount {vm : VMatrix} (mb : ModelBoundary vm) : Nat :=
  mb.nonFormal.length

/-- Total number of tracked items (verified + non-formal + unmodeled). -/
def ModelBoundary.totalItems {vm : VMatrix} (mb : ModelBoundary vm) : Nat :=
  mb.verifiedCount + mb.nonFormalCount + mb.unmodeledCount

/-- Filter unmodeled risks by category. -/
def ModelBoundary.risksInCategory {vm : VMatrix}
    (mb : ModelBoundary vm) (cat : RiskCategory) : List UnmodeledRisk :=
  mb.unmodeled.filter (fun r => r.category == cat)

-- ============================================================
-- §6  Summary
-- ============================================================

/-- Render a `ModelBoundary` as a human-readable summary string. -/
def ModelBoundary.summary {vm : VMatrix} (mb : ModelBoundary vm) : String :=
  let header := s!"Model Boundary: {mb.systemName}"
  let verified := s!"  Verified (formal proof): {mb.verifiedCount}"
  let nonFormal := s!"  Non-formal (test/analysis): {mb.nonFormalCount}"
  let unmodeled := s!"  Unmodeled risks: {mb.unmodeledCount}"
  let total := s!"  Total items: {mb.totalItems}"
  String.intercalate "\n" [header, verified, nonFormal, unmodeled, total]

end VerifiedMBSE.Matrix
