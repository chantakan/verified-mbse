import VerifiedMBSE.VV.Evidence

/-!
# VColumn: A Single Column of the V-Matrix

サブシステム識別子、`VColumn` 構造体、レイヤフィルタ、
および `Complete` 述語を定義する。
-/

namespace VerifiedMBSE.Matrix

open VerifiedMBSE.VV

-- ============================================================
-- §1  VColumn
-- ============================================================

/-- VColumn: 1 サブシステムに対応する V 行列の列。
    `subsystem` はドメイン固有の enum 化を避けるため String で持つ。 -/
structure VColumn where
  subsystem : String
  records   : List VVRecord

/-- 特定レイヤの VVRecord を取得する。 -/
def VColumn.atLayer (col : VColumn) (l : Layer) : List VVRecord :=
  col.records.filter (fun r => r.layer == l)

/-- 列が特定レイヤに VVRecord を持つか。 -/
def VColumn.hasLayer (col : VColumn) (l : Layer) : Bool :=
  !(col.atLayer l).isEmpty

/-- 全レイヤ（system/subsystem/component）を埋めているか。 -/
def VColumn.allLayersCovered (col : VColumn) : Bool :=
  col.hasLayer .system && col.hasLayer .subsystem && col.hasLayer .component

-- ============================================================
-- §2  Completeness Predicate
-- ============================================================

/-- 列の完全性: 各レイヤに少なくとも 1 件の VVRecord が存在する。 -/
def VColumn.Complete (col : VColumn) : Prop :=
  (col.atLayer .system).length > 0 ∧
  (col.atLayer .subsystem).length > 0 ∧
  (col.atLayer .component).length > 0

-- ============================================================
-- §3  Confidence
-- ============================================================

/-- 列のすべてのレコードが `.trusted` であるか（構造子判別）。

    旧実装は `currentLevel == 1.0` の Float 等号に依存していたが、IEEE 754 の
    等号比較は推奨されないため、`ValidationTrace.isTrusted` の inductive 判別に
    置き換えた（F2）。`.trusted` 以外の混在があれば `false` を返す。 -/
def VColumn.fullyTrusted (col : VColumn) : Bool :=
  col.records.all (fun r => r.validation.isTrusted)

-- ============================================================
-- §4  Composition
-- ============================================================

/-- VColumn の合成: 同一サブシステムの列をマージする。 -/
def VColumn.merge (c1 c2 : VColumn) (_ : c1.subsystem = c2.subsystem) :
    VColumn :=
  { subsystem := c1.subsystem
    records   := c1.records ++ c2.records }

end VerifiedMBSE.Matrix
