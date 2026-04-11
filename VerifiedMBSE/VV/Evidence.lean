import VerifiedMBSE.VV.Layer

/-!
# ValidationEvidence: Confidence Levels as Types

Defines a three-tier confidence hierarchy (Confidence < Contract < Trusted),
promotion traces, and `VVRecord` — the unified representation of a V-model cell.
-/

namespace VerifiedMBSE.VV

-- ============================================================
-- §1  ValidationEvidence
-- ============================================================

/-- ValidationEvidence: type representing validation evidence for proposition P.
    Three-tier hierarchy: confidence < contract < trusted. -/
inductive ValidationEvidence (P : Prop) : Type where
  /-- Confidence: probabilistic evidence (early design, expert heuristics). -/
  | confidence : Float → ValidationEvidence P
  /-- Contract: conditional guarantee (after test/simulation). -/
  | contract : (assumption : Prop) → (assumption → P) → ValidationEvidence P
  /-- Trusted: accepted as axiom (hardware test, approved). -/
  | trusted : P → ValidationEvidence P

/-- Returns the confidence level as a numeric value. -/
def ValidationEvidence.confidenceLevel {P : Prop} :
    ValidationEvidence P → Float
  | .confidence p => p
  | .contract _ _ => 0.95
  | .trusted _    => 1.0

/-- Promotion: Confidence → Contract. -/
def ValidationEvidence.promoteToContract {P : Prop}
    (_ : ValidationEvidence P)
    (a : Prop)
    (ev : a → P) :
    ValidationEvidence P :=
  .contract a ev

/-- Promotion: Contract → Trusted (when the assumption holds). -/
def ValidationEvidence.promoteToTrusted {P : Prop}
    (c : ValidationEvidence P)
    (h : match c with
         | .contract a _ => a
         | _ => True) :
    ValidationEvidence P :=
  match c, h with
  | .contract _ ev, h  => .trusted (ev h)
  | .confidence p, _   => .confidence p
  | .trusted p, _      => .trusted p

-- ============================================================
-- §2  ValidationTrace
-- ============================================================

/-- ValidationTrace: record with promotion history. -/
structure ValidationTrace (P : Prop) where
  history : List (ValidationEvidence P)
  current : ValidationEvidence P

/-- Initialize a ValidationTrace. -/
def ValidationTrace.init {P : Prop}
    (ev : ValidationEvidence P) :
    ValidationTrace P :=
  { history := [], current := ev }

/-- Record a promotion in a ValidationTrace. -/
def ValidationTrace.promote {P : Prop}
    (t : ValidationTrace P)
    (next : ValidationEvidence P) :
    ValidationTrace P :=
  { history := t.history ++ [t.current]
    current := next }

/-- Get the current confidence level. -/
def ValidationTrace.currentLevel {P : Prop}
    (t : ValidationTrace P) : Float :=
  t.current.confidenceLevel

/-- Whether the trace has been promoted. -/
def ValidationTrace.hasBeenPromoted {P : Prop}
    (t : ValidationTrace P) : Bool :=
  !t.history.isEmpty

-- ============================================================
-- §3  VVRecord
-- ============================================================

/-- VVRecord: Complete V&V record for a single design item. -/
structure VVRecord where
  layer        : Layer
  spec_name    : String
  verification : Prop
  verified     : verification
  validation   : ValidationTrace verification

-- ============================================================
-- §4  IOValidationSource
-- ============================================================

/-- IOValidationSource: validation evidence obtained from IO. -/
structure IOValidationSource (P : Prop) where
  source_description : String
  declaration : P

/-- Construct a Trusted ValidationEvidence from IO. -/
def fromIOValidation {P : Prop}
    (src : IOValidationSource P) :
    ValidationEvidence P :=
  .trusted src.declaration

-- ============================================================
-- §5  Basic Theorems
-- ============================================================

/-- The confidenceLevel of trusted is 1.0. -/
theorem trusted_is_full_confidence {P : Prop} (h : P) :
    (ValidationEvidence.trusted h).confidenceLevel = 1.0 := by
  simp [ValidationEvidence.confidenceLevel]

/-- promote increases the history by one. -/
theorem promote_extends_history {P : Prop}
    (t : ValidationTrace P) (next : ValidationEvidence P) :
    (t.promote next).history.length = t.history.length + 1 := by
  simp [ValidationTrace.promote, List.length_append]

end VerifiedMBSE.VV
