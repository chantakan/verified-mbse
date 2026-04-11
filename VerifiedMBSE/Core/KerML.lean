import Mathlib.Order.Basic

/-!
# KerML Core Layer: Dependent Type Semantics

Defines the KerML core layer structures (Element, Type, Feature, Direction) and
direction conjugation as an involution.

## References
- OMG KerML Specification v2.0 Beta (formal/2023-06-03), Part III
- Almeida et al., "An Analysis of the Semantic Foundation of KerML and SysML v2" (ER 2024)
-/

namespace VerifiedMBSE.Core

-- ============================================================
-- §1  Basic Structures
-- ============================================================

/-- KerML Element: root of all model elements. -/
structure Element where
  name : Option String := none
  deriving Repr, BEq

/-- KerML Type: classifier that may own features.
    Semantically represents a set of instances (extent). -/
structure KerMLType extends Element where
  /-- Whether it is abstract (cannot be directly instantiated) -/
  isAbstract : Bool := false
  deriving Repr

/-- Feature: characteristic of a type (named, multiplicity-bearing slot).
    In dependent type theory, corresponds to a projection of Σ(x:A).B(x). -/
structure Feature extends Element where
  /-- Multiplicity lower bound -/
  lower : Nat := 1
  /-- Multiplicity upper bound (0 = unbounded) -/
  upper : Nat := 1
  deriving Repr

-- ============================================================
-- §2  Direction and Conjugation
-- ============================================================

/-- Feature Direction (KerML spec §8.4.4).
    Corresponds to polarity in linear logic: in = negative, out = positive. -/
inductive Direction where
  | in_   -- Input (external → internal)
  | out   -- Output (internal → external)
  | inout -- Bidirectional (self-dual)
  deriving Repr, BEq

/-- Direction inversion via conjugation. Corresponds to negation A⊥ in linear logic. -/
def Direction.conj : Direction → Direction
  | .in_   => .out
  | .out   => .in_
  | .inout => .inout

/-- Direction conjugation is an involution: conj(conj(d)) = d -/
theorem Direction.conj_involution (d : Direction) :
    d.conj.conj = d := by
  cases d <;> rfl

/-- Directed feature: the basic unit of port definitions. -/
structure DirectedFeature extends Feature where
  direction : Direction
  deriving Repr

/-- DirectedFeature conjugation: inverts only the direction, preserving the body. -/
def DirectedFeature.conj (f : DirectedFeature) : DirectedFeature where
  toFeature := f.toFeature
  direction := f.direction.conj

/-- DirectedFeature conjugation is also an involution. -/
theorem DirectedFeature.conj_involution (f : DirectedFeature) :
    f.conj.conj = f := by
  simp [DirectedFeature.conj, Direction.conj_involution]

end VerifiedMBSE.Core
