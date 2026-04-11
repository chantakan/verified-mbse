import VerifiedMBSE.VV.Evidence

/-!
# VColumn: A Single Column of the V-Matrix

Defines subsystem identifiers, the `VColumn` structure, layer filters,
and the `Complete` predicate.
-/

namespace VerifiedMBSE.Matrix

open VerifiedMBSE.VV

-- ============================================================
-- §1  VColumn
-- ============================================================

/-- VColumn: a V-matrix column for one subsystem.
    The subsystem field is a String to avoid requiring a domain-specific SubSystem enum. -/
structure VColumn where
  subsystem : String
  records   : List VVRecord

/-- Get VVRecords for a specific layer. -/
def VColumn.atLayer (col : VColumn) (l : Layer) : List VVRecord :=
  col.records.filter (fun r => r.layer == l)

/-- Whether the column has a VVRecord at a specific layer. -/
def VColumn.hasLayer (col : VColumn) (l : Layer) : Bool :=
  !(col.atLayer l).isEmpty

/-- Whether all layers of the column are filled. -/
def VColumn.allLayersCovered (col : VColumn) : Bool :=
  col.hasLayer .system && col.hasLayer .subsystem && col.hasLayer .component

-- ============================================================
-- §2  Completeness Predicate
-- ============================================================

/-- Column completeness: at least one VVRecord exists at every layer. -/
def VColumn.Complete (col : VColumn) : Prop :=
  (col.atLayer .system).length > 0 ∧
  (col.atLayer .subsystem).length > 0 ∧
  (col.atLayer .component).length > 0

-- ============================================================
-- §3  Confidence
-- ============================================================

/-- Whether the column is fully trusted (confidence 1.0). -/
def VColumn.fullyTrusted (col : VColumn) : Bool :=
  col.records.all (fun r => r.validation.currentLevel == 1.0)

-- ============================================================
-- §4  Composition
-- ============================================================

/-- VColumn composition: merge columns for the same subsystem. -/
def VColumn.merge (c1 c2 : VColumn) (_ : c1.subsystem = c2.subsystem) :
    VColumn :=
  { subsystem := c1.subsystem
    records   := c1.records ++ c2.records }

end VerifiedMBSE.Matrix
