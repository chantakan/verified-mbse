import VerifiedMBSE.VV.Layer

/-!
# ValidationEvidence: Confidence Levels as Types

Three-tier hierarchy `confidence < contract < trusted`, a promotion
trace recording the history of upgrades, and `VVRecord`, a uniform
representation of one cell of the V model.
-/

namespace VerifiedMBSE.VV

-- ============================================================
-- §1  ValidationEvidence
-- ============================================================

/-- `ValidationEvidence P` — the verification evidence for a proposition
    `P`, organized as a three-tier hierarchy
    `confidence < contract < trusted`. -/
inductive ValidationEvidence (P : Prop) : Type where
  /-- Confidence: probabilistic evidence (early design, expert heuristics). -/
  | confidence : Float → ValidationEvidence P
  /-- Contract: conditional guarantee (after test or simulation). -/
  | contract : (assumption : Prop) → (assumption → P) → ValidationEvidence P
  /-- Trusted: adopted as an axiom (hardware test, approved). -/
  | trusted : P → ValidationEvidence P

/-- Confidence value of an evidence, as a `Float` (for display or
    sorting).

    This `Float` result is not suitable for equality comparisons due to
    rounding. For a "is this trusted?" check, use `isTrusted`, which is
    structural on the constructor. -/
def ValidationEvidence.confidenceLevel {P : Prop} :
    ValidationEvidence P → Float
  | .confidence p => p
  | .contract _ _ => 0.95
  | .trusted _    => 1.0

/-- Whether the evidence was built with the `.trusted` constructor.

    Structural discrimination that avoids `Float` equality; consumed by
    boolean checks such as `fullyTrusted`. -/
def ValidationEvidence.isTrusted {P : Prop} :
    ValidationEvidence P → Bool
  | .trusted _ => true
  | _          => false

/-- Whether the evidence was built with the `.contract` constructor. -/
def ValidationEvidence.isContract {P : Prop} :
    ValidationEvidence P → Bool
  | .contract _ _ => true
  | _             => false

/-- Whether the evidence was built with the `.confidence` constructor. -/
def ValidationEvidence.isConfidence {P : Prop} :
    ValidationEvidence P → Bool
  | .confidence _ => true
  | _             => false

/-- Promotion: `Confidence → Contract`. -/
def ValidationEvidence.promoteToContract {P : Prop}
    (_ : ValidationEvidence P)
    (a : Prop)
    (ev : a → P) :
    ValidationEvidence P :=
  .contract a ev

/-- Promotion: `Contract → Trusted`, given a proof that the assumption
    of the contract actually holds. -/
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

/-- `ValidationTrace P` — record of the promotion history together with
    the current evidence for `P`. -/
structure ValidationTrace (P : Prop) where
  history : List (ValidationEvidence P)
  current : ValidationEvidence P

/-- Initialize a `ValidationTrace` with a single piece of evidence and
    an empty history. -/
def ValidationTrace.init {P : Prop}
    (ev : ValidationEvidence P) :
    ValidationTrace P :=
  { history := [], current := ev }

/-- Record a promotion step in the trace. The previous `current`
    evidence is appended to `history`, and `next` becomes the new
    `current`. -/
def ValidationTrace.promote {P : Prop}
    (t : ValidationTrace P)
    (next : ValidationEvidence P) :
    ValidationTrace P :=
  { history := t.history ++ [t.current]
    current := next }

/-- Current confidence value of the trace. -/
def ValidationTrace.currentLevel {P : Prop}
    (t : ValidationTrace P) : Float :=
  t.current.confidenceLevel

/-- Whether the current evidence is `.trusted` (constructor match). -/
def ValidationTrace.isTrusted {P : Prop}
    (t : ValidationTrace P) : Bool :=
  t.current.isTrusted

/-- Whether the trace has undergone at least one promotion. -/
def ValidationTrace.hasBeenPromoted {P : Prop}
    (t : ValidationTrace P) : Bool :=
  !t.history.isEmpty

-- ============================================================
-- §3  VVRecord
-- ============================================================

/-- Complete V&V record for a single design item. -/
structure VVRecord where
  layer        : Layer
  spec_name    : String
  verification : Prop
  verified     : verification
  validation   : ValidationTrace verification

-- ============================================================
-- §4  IOValidationSource
-- ============================================================

/-- Validation evidence obtained from IO (e.g. test reports, external
    certifications). -/
structure IOValidationSource (P : Prop) where
  source_description : String
  declaration : P

/-- Construct a `.trusted` `ValidationEvidence` from an
    `IOValidationSource`. -/
def fromIOValidation {P : Prop}
    (src : IOValidationSource P) :
    ValidationEvidence P :=
  .trusted src.declaration

-- ============================================================
-- §5  Basic Theorems
-- ============================================================

/-- `.trusted` evidence has a confidence level of `1.0`. -/
theorem trusted_is_full_confidence {P : Prop} (h : P) :
    (ValidationEvidence.trusted h).confidenceLevel = 1.0 := by
  simp [ValidationEvidence.confidenceLevel]

/-- `.trusted` evidence satisfies `isTrusted`. -/
theorem trusted_isTrusted {P : Prop} (h : P) :
    (ValidationEvidence.trusted h).isTrusted = true := by
  simp [ValidationEvidence.isTrusted]

/-- `.confidence` evidence does not satisfy `isTrusted`. -/
theorem confidence_not_isTrusted {P : Prop} (p : Float) :
    (ValidationEvidence.confidence p : ValidationEvidence P).isTrusted = false := by
  simp [ValidationEvidence.isTrusted]

/-- `.contract` evidence does not satisfy `isTrusted`. -/
theorem contract_not_isTrusted {P : Prop} (a : Prop) (ev : a → P) :
    (ValidationEvidence.contract a ev).isTrusted = false := by
  simp [ValidationEvidence.isTrusted]

/-- `promote` extends the history by exactly one entry. -/
theorem promote_extends_history {P : Prop}
    (t : ValidationTrace P) (next : ValidationEvidence P) :
    (t.promote next).history.length = t.history.length + 1 := by
  simp [ValidationTrace.promote, List.length_append]

end VerifiedMBSE.VV
