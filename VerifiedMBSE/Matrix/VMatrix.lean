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

/-- VMatrix: V 字モデルの2次元行列。 -/
structure VMatrix where
  columns : List VColumn

-- ============================================================
-- §2  完全性述語
-- ============================================================

/-- サブシステム完全性: 指定された全サブシステムにカラムが存在する。 -/
def VMatrix.SubSystemComplete (m : VMatrix) (subsystems : List String) : Prop :=
  ∀ s ∈ subsystems, ∃ col ∈ m.columns, col.subsystem = s

/-- 行列完全性: 全カラムがレイヤー完全。 -/
def VMatrix.Complete (m : VMatrix) (subsystems : List String) : Prop :=
  m.SubSystemComplete subsystems ∧ ∀ col ∈ m.columns, col.Complete

-- ============================================================
-- §3  ユーティリティ
-- ============================================================

/-- 二つの VColumn から VMatrix を構成する。 -/
def VMatrix.fromColumns (c1 c2 : VColumn) : VMatrix :=
  { columns := [c1, c2] }

/-- fromColumns は両カラムを含む。 -/
theorem VMatrix.fromColumns_contains_both (c1 c2 : VColumn) :
    c1 ∈ (VMatrix.fromColumns c1 c2).columns ∧
    c2 ∈ (VMatrix.fromColumns c1 c2).columns := by
  simp [VMatrix.fromColumns]

/-- V 字行列が全て trusted か。 -/
def VMatrix.fullyTrusted (m : VMatrix) : Bool :=
  m.columns.all (fun col => col.fullyTrusted)

end VerifiedMBSE.Matrix
