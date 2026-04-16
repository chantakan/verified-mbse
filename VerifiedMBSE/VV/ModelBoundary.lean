/-!
# Model Boundary: Explicit Declaration of What Is Not Verified

Formal verification guarantees properties *inside* the model. This module
makes the model's *outside* a first-class object so that "V&V matrix green"
cannot be mistaken for "the real system is safe."

A `ModelBoundary` records:
- properties that are formally verified,
- properties backed by testing or analysis rather than proof,
- risks that are deliberately left unmodeled, with rationale and mitigation.

The intent is epistemic honesty, not bookkeeping. The boundary should be
reviewed whenever the system is changed.
-/

namespace VerifiedMBSE.VV

-- ============================================================
-- §1  Risk Categories
-- ============================================================

/-- Categories of unmodeled risk. -/
inductive RiskCategory where
  /-- Physical phenomena outside the formal model (e.g. cosmic ray SEUs,
      micro-meteoroid impact, material fatigue). -/
  | physical
  /-- Environmental factors (solar activity, thermal extremes, radiation). -/
  | environmental
  /-- Human factors (operator error, procedure misuse, training gaps). -/
  | human
  /-- Software risks outside the verified boundary (COTS, firmware, OS). -/
  | software
  /-- Hardware risks (manufacturing defects, aging, part substitution). -/
  | hardware
  /-- Organizational / process risks (change management, supply chain). -/
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

/-- How strongly a property is supported. Distinguishes proof from testing
    and analysis so that `ModelBoundary` cannot hide the difference. -/
inductive EvidenceKind where
  /-- Formal proof in Lean. -/
  | verified
  /-- Backed by test campaigns (unit test, HIL, qualification). -/
  | tested
  /-- Backed by analytical methods (FMEA, FTA, Monte Carlo). -/
  | analyzed
  deriving Repr, BEq, DecidableEq

/-- Human-readable kind name. -/
def EvidenceKind.toString : EvidenceKind → String
  | .verified => "Verified"
  | .tested   => "Tested"
  | .analyzed => "Analyzed"

instance : ToString EvidenceKind := ⟨EvidenceKind.toString⟩

-- ============================================================
-- §3  Unmodeled Risk
-- ============================================================

/-- UnmodeledRisk: a risk the formal model does not cover, with explicit
    rationale and mitigation. Constructing this value forces the engineer
    to name and justify the gap. -/
structure UnmodeledRisk where
  /-- Short description of the risk. -/
  description : String
  /-- Risk category. -/
  category : RiskCategory
  /-- Why this risk is not formalized. -/
  rationale : String
  /-- Non-formal mitigation (process, test, redundancy, operational limit). -/
  mitigation : String
  deriving Repr

-- ============================================================
-- §4  Non-Verified Property
-- ============================================================

/-- NonFormalProperty: a property supported by test or analysis but not proof. -/
structure NonFormalProperty where
  /-- Property description. -/
  description : String
  /-- Kind of non-formal evidence (`.tested` or `.analyzed`). -/
  kind : EvidenceKind
  /-- Evidence source reference (report ID, test campaign, etc.). -/
  source : String
  deriving Repr

-- ============================================================
-- §5  Model Boundary
-- ============================================================

/-- ModelBoundary: the full picture of what the model does and does not cover. -/
structure ModelBoundary where
  /-- Identifier for this boundary (typically the system name). -/
  systemName : String
  /-- Number of formally verified properties (cross-reference to VVRecord count). -/
  verifiedCount : Nat
  /-- Properties backed by test or analysis but not proof. -/
  nonFormal : List NonFormalProperty
  /-- Risks that are deliberately left unmodeled. -/
  unmodeled : List UnmodeledRisk
  deriving Repr

/-- Count of risks left unmodeled. -/
def ModelBoundary.unmodeledCount (mb : ModelBoundary) : Nat :=
  mb.unmodeled.length

/-- Count of non-formal properties. -/
def ModelBoundary.nonFormalCount (mb : ModelBoundary) : Nat :=
  mb.nonFormal.length

/-- Total evidence items (verified + non-formal + unmodeled). -/
def ModelBoundary.totalItems (mb : ModelBoundary) : Nat :=
  mb.verifiedCount + mb.nonFormalCount + mb.unmodeledCount

/-- Filter unmodeled risks by category. -/
def ModelBoundary.risksInCategory
    (mb : ModelBoundary) (cat : RiskCategory) : List UnmodeledRisk :=
  mb.unmodeled.filter (fun r => r.category == cat)

-- ============================================================
-- §6  Summary
-- ============================================================

/-- Render a ModelBoundary as a human-readable summary. -/
def ModelBoundary.summary (mb : ModelBoundary) : String :=
  let header := s!"Model Boundary: {mb.systemName}"
  let verified := s!"  Verified (formal proof): {mb.verifiedCount}"
  let nonFormal := s!"  Non-formal (test/analysis): {mb.nonFormalCount}"
  let unmodeled := s!"  Unmodeled risks: {mb.unmodeledCount}"
  let total := s!"  Total items: {mb.totalItems}"
  String.intercalate "\n" [header, verified, nonFormal, unmodeled, total]

end VerifiedMBSE.VV
