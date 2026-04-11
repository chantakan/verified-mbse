import VerifiedMBSE.Core.KerML
import VerifiedMBSE.VV.Layer

/-!
# Output Utilities

Common helper functions: `indent`, `typeName`, `directionKeyword`, etc.
-/

namespace VerifiedMBSE.Output

open VerifiedMBSE.Core

/-- Generate indentation. -/
def indent (level : Nat) : String :=
  String.ofList (List.replicate (level * 4) ' ')

/-- Get a KerMLType name. -/
def typeName (t : KerMLType) : String :=
  match t.name with | some n => n | none => "Anonymous"

/-- Whether it is a conjugated type (name starts with "~"). -/
def isConjugated (t : KerMLType) : Bool :=
  match t.name with | some n => n.startsWith "~" | none => false

/-- Get the original type name from a conjugated type. -/
def baseTypeName (t : KerMLType) : String :=
  match t.name with
  | some n => if n.startsWith "~" then (n.drop 1).toString else n
  | none   => "Anonymous"

/-- Convert a Direction to a SysML v2 keyword. -/
def directionKeyword (d : Direction) : String :=
  match d with | .in_ => "in" | .out => "out" | .inout => "inout"

/-- Convert Multiplicity to SysML v2 notation. -/
def multiplicityStr (lower upper : Nat) : String :=
  if lower == upper then s!"[{lower}]"
  else if upper == 0 then s!"[{lower}..*]"
  else s!"[{lower}..{upper}]"

/-- Convert a Layer to a string. -/
def layerToString (l : VerifiedMBSE.VV.Layer) : String :=
  match l with | .system => "system" | .subsystem => "subsystem" | .component => "component"

/-- Convert a Layer to an abbreviation. -/
def layerToAbbr (l : VerifiedMBSE.VV.Layer) : String :=
  match l with | .system => "SYS" | .subsystem => "SUB" | .component => "CMP"

end VerifiedMBSE.Output
