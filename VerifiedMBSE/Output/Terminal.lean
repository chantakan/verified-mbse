import VerifiedMBSE.Output.Render
import VerifiedMBSE.Matrix.Query

/-!
# V-Matrix → Terminal Summary Generation

Renders a `VMatrix` as a terminal summary with box-drawing characters
and confidence bars.
-/

namespace VerifiedMBSE.Output

open VerifiedMBSE.VV
open VerifiedMBSE.Matrix

-- ============================================================
-- §1  Confidence Bar
-- ============================================================

/-- Display confidence as a bar (20 characters wide). -/
def confidenceBar (level : Float) : String :=
  let filled := (level * 20.0).toUInt32.toNat
  let filled := min filled 20
  let bar := String.ofList (List.replicate filled '█')
  let empty := String.ofList (List.replicate (20 - filled) '░')
  bar ++ empty

/-- Percentage string. -/
def confidencePct (level : Float) : String :=
  let pct := (level * 100.0).toUInt32.toNat
  s!"{pct}%"

-- ============================================================
-- §2  VColumn Summary
-- ============================================================

/-- Calculate the average confidence of a VColumn. -/
def avgConfidence (col : VColumn) : Float :=
  if col.records.isEmpty then 0.0
  else
    let total := col.records.foldl (fun acc r => acc + r.validation.currentLevel) 0.0
    total / col.records.length.toFloat

/-- Summary line for a VColumn. -/
def columnSummaryLine (col : VColumn) : String :=
  let name := col.subsystem
  let padded := name ++ String.ofList (List.replicate (4 - min name.length 4) ' ')
  let avg := avgConfidence col
  s!"  {padded} [{col.records.length}] {confidenceBar avg} {confidencePct avg}"

-- ============================================================
-- §3  VMatrix Summary
-- ============================================================

/-- Convert a VMatrix to a terminal summary string. -/
def VMatrix.toTerminal (m : VMatrix) (title : String := "Satellite") : String :=
  let sep := "═══════════════════════════════════════════"
  let totalRecs := m.totalRecords
  let subsysCount := m.columns.length
  let allTrusted := m.fullyTrusted
  let trustStr := if allTrusted then "ALL TRUSTED" else "MIXED"
  let header :=
    s!"{sep}\n" ++
    s!"  V-Matrix: {title}\n" ++
    s!"  {subsysCount} subsystems │ {totalRecs} records │ {trustStr}\n" ++
    s!"{sep}"
  let colLines := m.columns.map columnSummaryLine
  let body := String.intercalate "\n" colLines
  -- Completeness check
  let allCovered := m.columns.all (·.allLayersCovered)
  let coverStr := if allCovered then "✓ All layers covered" else "✗ Missing layers"
  let footer :=
    s!"{sep}\n" ++
    s!"  Completeness: {coverStr}\n" ++
    s!"{sep}"
  header ++ "\n" ++ body ++ "\n" ++ footer

end VerifiedMBSE.Output
