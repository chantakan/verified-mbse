import VerifiedMBSE.Output.Render
import VerifiedMBSE.Matrix.Query

/-!
# V-Matrix → ターミナルサマリー生成

VMatrix を色付き罫線・信頼度バー付きのサマリーとして出力する。
-/

namespace VerifiedMBSE.Output

open VerifiedMBSE.VV
open VerifiedMBSE.Matrix

-- ============================================================
-- §1  信頼度バー
-- ============================================================

/-- 信頼度をバーで表示（20文字幅）。 -/
def confidenceBar (level : Float) : String :=
  let filled := (level * 20.0).toUInt32.toNat
  let filled := min filled 20
  let bar := String.ofList (List.replicate filled '█')
  let empty := String.ofList (List.replicate (20 - filled) '░')
  bar ++ empty

/-- パーセント文字列。 -/
def confidencePct (level : Float) : String :=
  let pct := (level * 100.0).toUInt32.toNat
  s!"{pct}%"

-- ============================================================
-- §2  VColumn サマリー
-- ============================================================

/-- VColumn の平均信頼度を計算。 -/
def avgConfidence (col : VColumn) : Float :=
  if col.records.isEmpty then 0.0
  else
    let total := col.records.foldl (fun acc r => acc + r.validation.currentLevel) 0.0
    total / col.records.length.toFloat

/-- VColumn のサマリー行。 -/
def columnSummaryLine (col : VColumn) : String :=
  let name := col.subsystem
  let padded := name ++ String.ofList (List.replicate (4 - min name.length 4) ' ')
  let avg := avgConfidence col
  s!"  {padded} [{col.records.length}] {confidenceBar avg} {confidencePct avg}"

-- ============================================================
-- §3  VMatrix サマリー
-- ============================================================

/-- VMatrix をターミナルサマリー文字列に変換。 -/
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
  -- 完全性チェック
  let allCovered := m.columns.all (·.allLayersCovered)
  let coverStr := if allCovered then "✓ All layers covered" else "✗ Missing layers"
  let footer :=
    s!"{sep}\n" ++
    s!"  Completeness: {coverStr}\n" ++
    s!"{sep}"
  header ++ "\n" ++ body ++ "\n" ++ footer

end VerifiedMBSE.Output
