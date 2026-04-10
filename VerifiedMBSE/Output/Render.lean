import VerifiedMBSE.Core.KerML
import VerifiedMBSE.VV.Layer

/-!
# Output Utilities

Common helper functions: `indent`, `typeName`, `directionKeyword`, etc.
-/

namespace VerifiedMBSE.Output

open VerifiedMBSE.Core

/-- インデントを生成する。 -/
def indent (level : Nat) : String :=
  String.ofList (List.replicate (level * 4) ' ')

/-- KerMLType の名前を取得する。 -/
def typeName (t : KerMLType) : String :=
  match t.name with | some n => n | none => "Anonymous"

/-- 共役型かどうか（名前が "~" で始まるか）。 -/
def isConjugated (t : KerMLType) : Bool :=
  match t.name with | some n => n.startsWith "~" | none => false

/-- 共役型から元の型名を取得する。 -/
def baseTypeName (t : KerMLType) : String :=
  match t.name with
  | some n => if n.startsWith "~" then (n.drop 1).toString else n
  | none   => "Anonymous"

/-- Direction を SysML v2 キーワードに変換。 -/
def directionKeyword (d : Direction) : String :=
  match d with | .in_ => "in" | .out => "out" | .inout => "inout"

/-- Multiplicity を SysML v2 記法に変換。 -/
def multiplicityStr (lower upper : Nat) : String :=
  if lower == upper then s!"[{lower}]"
  else if upper == 0 then s!"[{lower}..*]"
  else s!"[{lower}..{upper}]"

/-- Layer を文字列に変換。 -/
def layerToString (l : VerifiedMBSE.VV.Layer) : String :=
  match l with | .system => "system" | .subsystem => "subsystem" | .component => "component"

/-- Layer を略記に変換。 -/
def layerToAbbr (l : VerifiedMBSE.VV.Layer) : String :=
  match l with | .system => "SYS" | .subsystem => "SUB" | .component => "CMP"

end VerifiedMBSE.Output
