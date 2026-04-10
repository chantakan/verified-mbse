import VerifiedMBSE.Output.Render
import VerifiedMBSE.Matrix.Query

/-!
# V-Matrix → Markdown テーブル生成

VMatrix を Markdown テーブルとして出力する。
-/

namespace VerifiedMBSE.Output

open VerifiedMBSE.VV
open VerifiedMBSE.Matrix

-- ============================================================
-- §1  VVRecord → Markdown セル
-- ============================================================

/-- VVRecord を Markdown セル文字列に変換。 -/
def vvRecordToMdCell (r : VVRecord) : String :=
  let mark := if r.validation.currentLevel == 1.0 then "✅" else "⏳"
  s!"{r.spec_name} {mark}"

-- ============================================================
-- §2  VColumn → Markdown 列
-- ============================================================

/-- 特定レイヤーのセル文字列リストを返す。 -/
def columnCells (col : VColumn) (l : Layer) : List String :=
  (col.atLayer l).map vvRecordToMdCell

-- ============================================================
-- §3  VMatrix → Markdown テーブル
-- ============================================================

/-- 最大セル数を計算（行の高さ揃え用）。 -/
private def maxCells (cols : List VColumn) (l : Layer) : Nat :=
  cols.foldl (fun mx col => max mx (columnCells col l).length) 0

/-- リストを n 個にパディング。 -/
private def padList (xs : List String) (n : Nat) : List String :=
  xs ++ List.replicate (n - xs.length) ""

/-- 文字列を n 文字に右パディング。 -/
private def rightpad (s : String) (n : Nat) : String :=
  s ++ String.ofList (List.replicate (n - s.length) ' ')

/-- VMatrix を Markdown テーブル文字列に変換。 -/
def VMatrix.toMarkdown (m : VMatrix) (title : String := "Satellite") : String :=
  let cols := m.columns
  let totalRecs := m.totalRecords
  let subsysCount := cols.length
  -- ヘッダー
  let header := s!"## V-Matrix: {title} ({totalRecs} records, {subsysCount} subsystems)\n"
  -- テーブルヘッダー
  let colHeaders := cols.map (·.subsystem)
  let headerRow := "| Layer     | " ++ String.intercalate " | " colHeaders ++ " |"
  let sepRow := "|-----------|" ++ String.intercalate "|" (cols.map fun _ => "---------------|")
  -- 各レイヤーの行を生成
  let layers : List Layer := [.system, .subsystem, .component]
  let layerRows := layers.map fun l =>
    let lName := match l with | .system => "System" | .subsystem => "Subsystem" | .component => "Component"
    let nRows := maxCells cols l
    let paddedCols := cols.map fun col => padList (columnCells col l) nRows
    -- 各行
    let rows := List.range nRows |>.map fun i =>
      let label := if i == 0 then lName else ""
      let cells := paddedCols.map fun pc =>
        match pc[i]? with | some s => s | none => ""
      s!"| {rightpad label 9} | " ++ String.intercalate " | " cells ++ " |"
    String.intercalate "\n" rows
  header ++ "\n" ++ headerRow ++ "\n" ++ sepRow ++ "\n" ++
    String.intercalate "\n" layerRows

end VerifiedMBSE.Output
