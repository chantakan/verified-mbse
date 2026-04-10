import VerifiedMBSE.Matrix.VMatrix

/-!
# V 字行列のクエリと診断

column, cell, allRecords, summary 等のクエリ関数を定義する。
-/

namespace VerifiedMBSE.Matrix

open VerifiedMBSE.VV

-- ============================================================
-- §1  クエリ
-- ============================================================

/-- 特定サブシステムのカラムを取得する。 -/
def VMatrix.column (m : VMatrix) (s : String) : Option VColumn :=
  m.columns.find? (fun col => col.subsystem == s)

/-- 特定セルの VVRecord を取得する。 -/
def VMatrix.cell (m : VMatrix) (l : Layer) (s : String) :
    List VVRecord :=
  match m.column s with
  | some col => col.atLayer l
  | none     => []

/-- 全 VVRecord を平坦化して取得する。 -/
def VMatrix.allRecords (m : VMatrix) : List VVRecord :=
  m.columns.foldl (fun acc col => acc ++ col.records) []

/-- VVRecord の総数。 -/
def VMatrix.totalRecords (m : VMatrix) : Nat :=
  m.allRecords.length

-- ============================================================
-- §2  診断情報
-- ============================================================

/-- VVRecord のサマリー文字列。 -/
def VVRecord.summary (r : VVRecord) : String :=
  let layerStr := match r.layer with
    | .system    => "SYS"
    | .subsystem => "SUB"
    | .component => "CMP"
  let confStr := toString r.validation.currentLevel
  s!"[{layerStr}] {r.spec_name} (confidence: {confStr})"

/-- VColumn のサマリー文字列。 -/
def VColumn.summary (col : VColumn) : String :=
  let recordSummaries := col.records.map VVRecord.summary
  s!"=== {col.subsystem} ({col.records.length} records) ===\n" ++
    String.intercalate "\n" recordSummaries

/-- VMatrix のサマリー文字列。 -/
def VMatrix.summary (m : VMatrix) : String :=
  let header := s!"V-Matrix: {m.columns.length} subsystems, {m.totalRecords} records"
  let colSummaries := m.columns.map VColumn.summary
  header ++ "\n\n" ++ String.intercalate "\n\n" colSummaries

end VerifiedMBSE.Matrix
