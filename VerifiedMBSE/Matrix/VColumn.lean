import VerifiedMBSE.VV.Evidence

/-!
# VColumn: A Single Column of the V-Matrix

Defines the subsystem identifier, the `VColumn` structure, per-layer
filters, and the `Complete` predicate.
-/

namespace VerifiedMBSE.Matrix

open VerifiedMBSE.VV

-- ============================================================
-- §1  VColumn
-- ============================================================

/-- One V-matrix column, corresponding to a single subsystem.

    `subsystem` is stored as a `String` to avoid committing to a
    domain-specific enumeration. -/
structure VColumn where
  subsystem : String
  records   : List VVRecord

/-- VVRecords in this column at the given layer. -/
def VColumn.atLayer (col : VColumn) (l : Layer) : List VVRecord :=
  col.records.filter (fun r => r.layer == l)

/-- Whether the column has at least one VVRecord at the given layer. -/
def VColumn.hasLayer (col : VColumn) (l : Layer) : Bool :=
  !(col.atLayer l).isEmpty

/-- Whether the column covers the `system` / `subsystem` / `component`
    layers. -/
def VColumn.allLayersCovered (col : VColumn) : Bool :=
  col.hasLayer .system && col.hasLayer .subsystem && col.hasLayer .component

-- ============================================================
-- §2  Completeness Predicate
-- ============================================================

/-- Column completeness: at least one VVRecord exists at each of the
    `system` / `subsystem` / `component` layers. -/
def VColumn.Complete (col : VColumn) : Prop :=
  (col.atLayer .system).length > 0 ∧
  (col.atLayer .subsystem).length > 0 ∧
  (col.atLayer .component).length > 0

-- ============================================================
-- §3  Confidence
-- ============================================================

/-- Whether every record in the column is `.trusted` (constructor
    match).

    The check uses the structural `ValidationTrace.isTrusted`
    constructor-based discriminator rather than an equality against
    `1.0`, avoiding IEEE 754 float equality. A column that mixes
    `.trusted` with any other evidence constructor returns `false`. -/
def VColumn.fullyTrusted (col : VColumn) : Bool :=
  col.records.all (fun r => r.validation.isTrusted)

-- ============================================================
-- §4  Composition
-- ============================================================

/-- Merge two columns that refer to the same subsystem. -/
def VColumn.merge (c1 c2 : VColumn) (_ : c1.subsystem = c2.subsystem) :
    VColumn :=
  { subsystem := c1.subsystem
    records   := c1.records ++ c2.records }

end VerifiedMBSE.Matrix
