import VerifiedMBSE.Matrix.VColumn

/-!
# VMatrix: The Complete V-Matrix Structure

Defines the `VMatrix` structure, `SubSystemComplete`,
and `Complete` (matrix completeness predicate).
-/

namespace VerifiedMBSE.Matrix

-- ============================================================
-- §1  VMatrix
-- ============================================================

/-- VMatrix: two-dimensional V-model matrix. -/
structure VMatrix where
  columns : List VColumn

-- ============================================================
-- §2  Completeness Predicate
-- ============================================================

/-- Subsystem completeness: a column exists for every specified subsystem. -/
def VMatrix.SubSystemComplete (m : VMatrix) (subsystems : List String) : Prop :=
  ∀ s ∈ subsystems, ∃ col ∈ m.columns, col.subsystem = s

/-- Matrix completeness: all columns are layer-complete. -/
def VMatrix.Complete (m : VMatrix) (subsystems : List String) : Prop :=
  m.SubSystemComplete subsystems ∧ ∀ col ∈ m.columns, col.Complete

-- ============================================================
-- §3  Utilities
-- ============================================================

/-- Construct a VMatrix from two VColumns. -/
def VMatrix.fromColumns (c1 c2 : VColumn) : VMatrix :=
  { columns := [c1, c2] }

/-- fromColumns contains both columns. -/
theorem VMatrix.fromColumns_contains_both (c1 c2 : VColumn) :
    c1 ∈ (VMatrix.fromColumns c1 c2).columns ∧
    c2 ∈ (VMatrix.fromColumns c1 c2).columns := by
  simp [VMatrix.fromColumns]

/-- Whether the V-matrix is fully trusted. -/
def VMatrix.fullyTrusted (m : VMatrix) : Bool :=
  m.columns.all (fun col => col.fullyTrusted)

end VerifiedMBSE.Matrix
