import VerifiedMBSE.Output.Render
import VerifiedMBSE.Core.Component
import VerifiedMBSE.VV.Evidence
import VerifiedMBSE.Matrix.VColumn

/-!
# SysML v2 テキスト記法生成

PartDef, Connector, System, VVRecord, VColumn を
SysML v2 テキスト記法に変換する関数群。
-/

namespace VerifiedMBSE.Output

open VerifiedMBSE.Core
open VerifiedMBSE.VV
open VerifiedMBSE.Matrix

-- ============================================================
-- §1  PortDef → SysML v2
-- ============================================================

/-- ポート型を SysML v2 port def に変換。 -/
def portTypeToSysML (t : KerMLType) : String :=
  s!"port def {baseTypeName t};"

/-- PortDef をパート内のポート宣言に変換。 -/
def portDeclToSysML (p : PortDef) (lvl : Nat) : String :=
  let dir := directionKeyword p.feature.direction
  let typeStr := if isConjugated p.flowType
    then s!"~{baseTypeName p.flowType}" else typeName p.flowType
  let mult := multiplicityStr p.feature.lower p.feature.upper
  let portName := match p.feature.name with | some n => n | none => "unnamed"
  s!"{indent lvl}{dir} port {portName} : {typeStr} {mult};"

-- ============================================================
-- §2  PartDef → SysML v2
-- ============================================================

/-- PartDef を SysML v2 part def に変換。 -/
def partDefToSysML (pd : PartDef) (lvl : Nat) : String :=
  let name := typeName pd.baseType
  let portDecls := pd.ports.map (fun p => portDeclToSysML p (lvl + 1))
  let body := String.intercalate "\n" portDecls
  if portDecls.isEmpty then s!"{indent lvl}part def {name};"
  else s!"{indent lvl}part def {name} \{\n{body}\n{indent lvl}}"

/-- PartDef.toSysML: トップレベル生成。 -/
def PartDef.toSysML (pd : PartDef) : String := partDefToSysML pd 0

-- ============================================================
-- §3  Connector → SysML v2
-- ============================================================

/-- PortRef のドット記法。 -/
def portRefStr (pr : PortRef) : String :=
  let partName := typeName pr.part.baseType
  let portName := match pr.port.feature.name with | some n => n | none => "unnamed"
  s!"{partName}.{portName}"

/-- Connector を SysML v2 connection def に変換。 -/
def connectorToSysML (c : Connector) (name : String) (lvl : Nat) : String :=
  s!"{indent lvl}connection def {name} \{\n" ++
  s!"{indent (lvl + 1)}end source :: {portRefStr c.source};\n" ++
  s!"{indent (lvl + 1)}end target :: {portRefStr c.target};\n" ++
  s!"{indent lvl}}"

/-- Connector.toSysML: 名前を自動生成。 -/
def Connector.toSysML (c : Connector) : String :=
  connectorToSysML c s!"{typeName c.source.part.baseType}_to_{typeName c.target.part.baseType}" 0

-- ============================================================
-- §4  System → SysML v2
-- ============================================================

/-- System を SysML v2 part def に変換。 -/
def systemToSysML (sys : System) (name : String) (lvl : Nat) : String :=
  let partUsages := sys.parts.map fun pd =>
    s!"{indent (lvl+1)}part {(typeName pd.baseType).toLower} : {typeName pd.baseType};"
  let connUsages := sys.connectors.map fun c =>
    s!"{indent (lvl+1)}connect {portRefStr c.source} to {portRefStr c.target};"
  let body := String.intercalate "\n" (partUsages ++ [""] ++ connUsages)
  s!"{indent lvl}part def {name} \{\n{body}\n{indent lvl}}"

/-- System.toSysML: トップレベル生成。 -/
def System.toSysML (sys : System) (name : String) : String := systemToSysML sys name 0

-- ============================================================
-- §5  VVRecord → SysML v2 requirement
-- ============================================================

/-- VVRecord を SysML v2 requirement def に変換。 -/
def vvRecordToSysML (r : VVRecord) (lvl : Nat) : String :=
  let confLevel := r.validation.currentLevel
  let confStr := if confLevel == 1.0 then "trusted"
    else if confLevel >= 0.95 then "contract" else "confidence"
  let lStr := layerToString r.layer
  s!"{indent lvl}requirement def '{r.spec_name}' \{\n" ++
  s!"{indent (lvl+1)}doc /* [{lStr}] Verified by Lean 4 proof.\n" ++
  s!"{indent (lvl+1)}       Validation: {confStr} (level: {toString confLevel}) */\n" ++
  s!"{indent (lvl+1)}attribute layer = \"{lStr}\";\n" ++
  s!"{indent lvl}}"

/-- VVRecord.toSysML: トップレベル生成。 -/
def VVRecord.toSysML (r : VVRecord) : String := vvRecordToSysML r 0

-- ============================================================
-- §6  VColumn → SysML v2 requirement package
-- ============================================================

/-- VColumn の要件群を SysML v2 package に変換。 -/
def vColumnRequirementsToSysML (col : VColumn) (lvl : Nat) : String :=
  let reqs := col.records.map (fun r => vvRecordToSysML r (lvl + 1))
  let body := String.intercalate "\n\n" reqs
  s!"{indent lvl}package '{col.subsystem}_Requirements' \{\n{body}\n{indent lvl}}"

-- ============================================================
-- §7  ポート型収集
-- ============================================================

/-- ポート型定義の一覧を収集（重複排除）。 -/
def collectPortTypes (parts : List PartDef) : List KerMLType :=
  let allTypes := parts.foldl (fun acc pd => acc ++ pd.ports.map (·.flowType)) []
  allTypes.foldl (fun acc t =>
    if acc.any (fun t' => typeName t == typeName t') then acc else acc ++ [t]) []

/-- ポート型定義セクションを生成（共役型を除外）。 -/
def portTypeSection (allParts : List PartDef) (lvl : Nat) : String :=
  let baseTypes := (collectPortTypes allParts).filter (fun t => !isConjugated t)
  let defs := baseTypes.map (fun t => s!"{indent lvl}{portTypeToSysML t}")
  if defs.isEmpty then ""
  else s!"{indent lvl}// ── Port Type Definitions ──\n" ++ String.intercalate "\n" defs

/-- パート定義セクションを生成（重複排除）。 -/
def partDefSection (allParts : List PartDef) (lvl : Nat) : String :=
  let unique := allParts.foldl (fun acc pd =>
    if acc.any (fun pd' => typeName pd.baseType == typeName pd'.baseType)
    then acc else acc ++ [pd]) []
  let defs := unique.map (fun pd => partDefToSysML pd lvl)
  if defs.isEmpty then ""
  else s!"{indent lvl}// ── Part Definitions ──\n" ++ String.intercalate "\n\n" defs

end VerifiedMBSE.Output
