import VerifiedMBSE.Matrix.VMatrix

/-!
# V-Matrix Queries and Diagnostics

Defines query functions: `column`, `cell`, `allRecords`, `summary`, etc.
-/

namespace VerifiedMBSE.Matrix

open VerifiedMBSE.VV

-- ============================================================
-- §1  Queries
-- ============================================================

/-- Get a column for a specific subsystem. -/
def VMatrix.column (m : VMatrix) (s : String) : Option VColumn :=
  m.columns.find? (fun col => col.subsystem == s)

/-- Get VVRecords for a specific cell. -/
def VMatrix.cell (m : VMatrix) (l : Layer) (s : String) :
    List VVRecord :=
  match m.column s with
  | some col => col.atLayer l
  | none     => []

/-- Get all VVRecords flattened. -/
def VMatrix.allRecords (m : VMatrix) : List VVRecord :=
  m.columns.foldl (fun acc col => acc ++ col.records) []

/-- Total VVRecord count. -/
def VMatrix.totalRecords (m : VMatrix) : Nat :=
  m.allRecords.length

-- ============================================================
-- §2  Diagnostics
-- ============================================================

/-- Summary string for a VVRecord. -/
def VVRecord.summary (r : VVRecord) : String :=
  let layerStr := match r.layer with
    | .system    => "SYS"
    | .subsystem => "SUB"
    | .component => "CMP"
  let confStr := toString r.validation.currentLevel
  s!"[{layerStr}] {r.spec_name} (confidence: {confStr})"

/-- Summary string for a VColumn. -/
def VColumn.summary (col : VColumn) : String :=
  let recordSummaries := col.records.map VVRecord.summary
  s!"=== {col.subsystem} ({col.records.length} records) ===\n" ++
    String.intercalate "\n" recordSummaries

/-- Summary string for a VMatrix. -/
def VMatrix.summary (m : VMatrix) : String :=
  let header := s!"V-Matrix: {m.columns.length} subsystems, {m.totalRecords} records"
  let colSummaries := m.columns.map VColumn.summary
  header ++ "\n\n" ++ String.intercalate "\n\n" colSummaries

end VerifiedMBSE.Matrix
