import VerifiedMBSE.Output.Render
import VerifiedMBSE.Core.Component
import VerifiedMBSE.VV.Evidence
import VerifiedMBSE.Matrix.VColumn

/-!
# SysML v2 Textual Notation Generation

Functions to convert `PartDef`, `Connector`, `System`, `VVRecord`, and `VColumn`
into SysML v2 textual notation.
-/

namespace VerifiedMBSE.Output

open VerifiedMBSE.Core
open VerifiedMBSE.VV
open VerifiedMBSE.Matrix

-- ============================================================
-- §1  PortDef → SysML v2
-- ============================================================

/-- Convert a port type to a SysML v2 port def. -/
def portTypeToSysML (t : KerMLType) : String :=
  s!"port def {baseTypeName t};"

/-- Convert a PortDef to a port declaration within a part. -/
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

/-- Convert a PartDef to a SysML v2 part def. -/
def partDefToSysML (pd : PartDef) (lvl : Nat) : String :=
  let name := typeName pd.baseType
  let portDecls := pd.ports.map (fun p => portDeclToSysML p (lvl + 1))
  let body := String.intercalate "\n" portDecls
  if portDecls.isEmpty then s!"{indent lvl}part def {name};"
  else s!"{indent lvl}part def {name} \{\n{body}\n{indent lvl}}"

/-- PartDef.toSysML: top-level generation. -/
def PartDef.toSysML (pd : PartDef) : String := partDefToSysML pd 0

-- ============================================================
-- §3  Connector → SysML v2
-- ============================================================

/-- Dot notation for PortRef. -/
def portRefStr (pr : PortRef) : String :=
  let partName := typeName pr.part.baseType
  let portName := match pr.port.feature.name with | some n => n | none => "unnamed"
  s!"{partName}.{portName}"

/-- Convert a Connector to a SysML v2 connection def. -/
def connectorToSysML (c : Connector) (name : String) (lvl : Nat) : String :=
  s!"{indent lvl}connection def {name} \{\n" ++
  s!"{indent (lvl + 1)}end source :: {portRefStr c.source};\n" ++
  s!"{indent (lvl + 1)}end target :: {portRefStr c.target};\n" ++
  s!"{indent lvl}}"

/-- Connector.toSysML: auto-generate name. -/
def Connector.toSysML (c : Connector) : String :=
  connectorToSysML c s!"{typeName c.source.part.baseType}_to_{typeName c.target.part.baseType}" 0

-- ============================================================
-- §4  System → SysML v2
-- ============================================================

/-- Convert a System to a SysML v2 part def. -/
def systemToSysML (sys : System) (name : String) (lvl : Nat) : String :=
  let partUsages := sys.parts.map fun pd =>
    s!"{indent (lvl+1)}part {(typeName pd.baseType).toLower} : {typeName pd.baseType};"
  let connUsages := sys.connectors.map fun c =>
    s!"{indent (lvl+1)}connect {portRefStr c.source} to {portRefStr c.target};"
  let body := String.intercalate "\n" (partUsages ++ [""] ++ connUsages)
  s!"{indent lvl}part def {name} \{\n{body}\n{indent lvl}}"

/-- System.toSysML: top-level generation. -/
def System.toSysML (sys : System) (name : String) : String := systemToSysML sys name 0

-- ============================================================
-- §5  VVRecord → SysML v2 requirement
-- ============================================================

/-- Convert a VVRecord to a SysML v2 requirement def. -/
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

/-- VVRecord.toSysML: top-level generation. -/
def VVRecord.toSysML (r : VVRecord) : String := vvRecordToSysML r 0

-- ============================================================
-- §6  VColumn → SysML v2 requirement package
-- ============================================================

/-- Convert VColumn requirements to a SysML v2 package. -/
def vColumnRequirementsToSysML (col : VColumn) (lvl : Nat) : String :=
  let reqs := col.records.map (fun r => vvRecordToSysML r (lvl + 1))
  let body := String.intercalate "\n\n" reqs
  s!"{indent lvl}package '{col.subsystem}_Requirements' \{\n{body}\n{indent lvl}}"

-- ============================================================
-- §7  Port Type Collection
-- ============================================================

/-- Collect port type definitions (deduplicated). -/
def collectPortTypes (parts : List PartDef) : List KerMLType :=
  let allTypes := parts.foldl (fun acc pd => acc ++ pd.ports.map (·.flowType)) []
  allTypes.foldl (fun acc t =>
    if acc.any (fun t' => typeName t == typeName t') then acc else acc ++ [t]) []

/-- Generate port type definition section (excluding conjugated types). -/
def portTypeSection (allParts : List PartDef) (lvl : Nat) : String :=
  let baseTypes := (collectPortTypes allParts).filter (fun t => !isConjugated t)
  let defs := baseTypes.map (fun t => s!"{indent lvl}{portTypeToSysML t}")
  if defs.isEmpty then ""
  else s!"{indent lvl}// ── Port Type Definitions ──\n" ++ String.intercalate "\n" defs

/-- Generate part definition section (deduplicated). -/
def partDefSection (allParts : List PartDef) (lvl : Nat) : String :=
  let unique := allParts.foldl (fun acc pd =>
    if acc.any (fun pd' => typeName pd.baseType == typeName pd'.baseType)
    then acc else acc ++ [pd]) []
  let defs := unique.map (fun pd => partDefToSysML pd lvl)
  if defs.isEmpty then ""
  else s!"{indent lvl}// ── Part Definitions ──\n" ++ String.intercalate "\n\n" defs

end VerifiedMBSE.Output
