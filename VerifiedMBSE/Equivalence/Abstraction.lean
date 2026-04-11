/-!
# Abstraction Levels and Design Parameters

Defines `AbstractionLevel` (MBSE analogue of n-truncation) and
`DesignParameter` (discrete analogue of cubical structure).
-/

namespace VerifiedMBSE.Equivalence

-- ============================================================
-- §1  AbstractionLevel
-- ============================================================

/-- AbstractionLevel: design abstraction level.
    MBSE analogue of HoTT n-truncation. -/
inductive AbstractionLevel where
  /-- Concept level: requirements only -/
  | concept
  /-- Logical level: interface definitions -/
  | logical
  /-- Physical level: concrete implementation -/
  | physical
  deriving Repr, BEq, DecidableEq

/-- Refinement relation between abstraction levels: lower refines upper. -/
def AbstractionLevel.refines : AbstractionLevel → AbstractionLevel → Prop
  | .physical, .logical  => True
  | .physical, .concept  => True
  | .logical,  .concept  => True
  | _,         _         => False

/-- Abstraction refinement is transitive. -/
theorem AbstractionLevel.refines_trans
    {l₁ l₂ l₃ : AbstractionLevel}
    (h₁₂ : AbstractionLevel.refines l₁ l₂)
    (h₂₃ : AbstractionLevel.refines l₂ l₃) :
    AbstractionLevel.refines l₁ l₃ := by
  cases l₁ <;> cases l₂ <;> cases l₃ <;> simp [AbstractionLevel.refines] at *

-- ============================================================
-- §2  DesignParameter
-- ============================================================

/-- DesignParameter: design parameter type.
    Discrete analogue of cubical structure. -/
structure DesignParameter (α : Type) where
  /-- Parameter value -/
  value : α
  /-- Valid range -/
  valid : α → Prop
  /-- Current value is within the valid range -/
  inRange : valid value

/-- Parametric invariant:
    inv holds for all valid parameter values.
    Discrete analogue of cubical path Π(p : I). inv(p). -/
def ParametricInvariant {α : Type}
    (param : DesignParameter α)
    (inv : α → Prop) : Prop :=
  ∀ p : α, param.valid p → inv p

/-- Example: power budget parameter (400-600W). -/
def powerBudgetParam : DesignParameter Nat :=
  { value   := 500
    valid   := fun n => 400 ≤ n ∧ n ≤ 600
    inRange := ⟨by omega, by omega⟩ }

end VerifiedMBSE.Equivalence
