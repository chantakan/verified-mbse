import VerifiedMBSE.VV.Evidence

/-!
# VColumn: V 字行列の一列

サブシステム識別子、VColumn 構造体、レイヤーフィルタ、完全性述語を定義する。
-/

namespace VerifiedMBSE.Matrix

open VerifiedMBSE.VV

-- ============================================================
-- §1  VColumn
-- ============================================================

/-- VColumn: 一つのサブシステムに対する V 字カラム。
    subsystem フィールドは String にして衛星固有の SubSystem 列挙を不要にする。 -/
structure VColumn where
  subsystem : String
  records   : List VVRecord

/-- 特定レイヤーの VVRecord を取得する。 -/
def VColumn.atLayer (col : VColumn) (l : Layer) : List VVRecord :=
  col.records.filter (fun r => r.layer == l)

/-- カラムが特定レイヤーに VVRecord を持つか。 -/
def VColumn.hasLayer (col : VColumn) (l : Layer) : Bool :=
  !(col.atLayer l).isEmpty

/-- カラムの全レイヤーが埋まっているか。 -/
def VColumn.allLayersCovered (col : VColumn) : Bool :=
  col.hasLayer .system && col.hasLayer .subsystem && col.hasLayer .component

-- ============================================================
-- §2  完全性述語
-- ============================================================

/-- カラム完全性: 全レイヤーに少なくとも1つの VVRecord がある。 -/
def VColumn.Complete (col : VColumn) : Prop :=
  (col.atLayer .system).length > 0 ∧
  (col.atLayer .subsystem).length > 0 ∧
  (col.atLayer .component).length > 0

-- ============================================================
-- §3  確信度
-- ============================================================

/-- カラムが全て trusted (確信度 1.0) か。 -/
def VColumn.fullyTrusted (col : VColumn) : Bool :=
  col.records.all (fun r => r.validation.currentLevel == 1.0)

-- ============================================================
-- §4  合成
-- ============================================================

/-- VColumn の合成: 同一サブシステムのカラムを結合。 -/
def VColumn.merge (c1 c2 : VColumn) (_ : c1.subsystem = c2.subsystem) :
    VColumn :=
  { subsystem := c1.subsystem
    records   := c1.records ++ c2.records }

end VerifiedMBSE.Matrix
