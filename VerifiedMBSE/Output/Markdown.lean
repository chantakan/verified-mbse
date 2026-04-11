import VerifiedMBSE.Output.Render
import VerifiedMBSE.Matrix.Query

/-!
# V-Matrix → Markdown Table Generation

Renders a `VMatrix` as a Markdown table.
-/

namespace VerifiedMBSE.Output

open VerifiedMBSE.VV
open VerifiedMBSE.Matrix

-- ============================================================
-- §1  VVRecord → Markdown Cell
-- ============================================================

/-- Convert a VVRecord to a Markdown cell string. -/
def vvRecordToMdCell (r : VVRecord) : String :=
  let mark := if r.validation.currentLevel == 1.0 then "✅" else "⏳"
  s!"{r.spec_name} {mark}"

-- ============================================================
-- §2  VColumn → Markdown Column
-- ============================================================

/-- Return a list of cell strings for a specific layer. -/
def columnCells (col : VColumn) (l : Layer) : List String :=
  (col.atLayer l).map vvRecordToMdCell

-- ============================================================
-- §3  VMatrix → Markdown Table
-- ============================================================

/-- Calculate the maximum cell count (for row height alignment). -/
private def maxCells (cols : List VColumn) (l : Layer) : Nat :=
  cols.foldl (fun mx col => max mx (columnCells col l).length) 0

/-- Pad a list to n elements. -/
private def padList (xs : List String) (n : Nat) : List String :=
  xs ++ List.replicate (n - xs.length) ""

/-- Right-pad a string to n characters. -/
private def rightpad (s : String) (n : Nat) : String :=
  s ++ String.ofList (List.replicate (n - s.length) ' ')

/-- Convert a VMatrix to a Markdown table string. -/
def VMatrix.toMarkdown (m : VMatrix) (title : String := "Satellite") : String :=
  let cols := m.columns
  let totalRecs := m.totalRecords
  let subsysCount := cols.length
  -- Header
  let header := s!"## V-Matrix: {title} ({totalRecs} records, {subsysCount} subsystems)\n"
  -- Table header
  let colHeaders := cols.map (·.subsystem)
  let headerRow := "| Layer     | " ++ String.intercalate " | " colHeaders ++ " |"
  let sepRow := "|-----------|" ++ String.intercalate "|" (cols.map fun _ => "---------------|")
  -- Generate rows for each layer
  let layers : List Layer := [.system, .subsystem, .component]
  let layerRows := layers.map fun l =>
    let lName := match l with | .system => "System" | .subsystem => "Subsystem" | .component => "Component"
    let nRows := maxCells cols l
    let paddedCols := cols.map fun col => padList (columnCells col l) nRows
    -- Each row
    let rows := List.range nRows |>.map fun i =>
      let label := if i == 0 then lName else ""
      let cells := paddedCols.map fun pc =>
        match pc[i]? with | some s => s | none => ""
      s!"| {rightpad label 9} | " ++ String.intercalate " | " cells ++ " |"
    String.intercalate "\n" rows
  header ++ "\n" ++ headerRow ++ "\n" ++ sepRow ++ "\n" ++
    String.intercalate "\n" layerRows

end VerifiedMBSE.Output
