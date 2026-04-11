import VerifiedMBSE.Output.Render
import VerifiedMBSE.Behavior.StateMachine

/-!
# StateMachine → SysML v2 State Definition Generation

Since `StateMachine` is type-parametric, concrete string representations are
provided externally via `StateMachineRepr`.
-/

namespace VerifiedMBSE.Output

open VerifiedMBSE.Behavior

-- ============================================================
-- §1  StateMachineRepr
-- ============================================================

/-- TransitionRepr: string representation of a transition. -/
structure TransitionRepr where
  name       : String
  sourceName : String
  targetName : String
  guardDesc  : String := "true"
  effectDesc : String := "identity"

/-- StateRepr: string representation of a state. -/
structure StateRepr where
  name : String
  doc  : String := ""

/-- StateMachineRepr: string representation of a state machine. -/
structure StateMachineRepr where
  name         : String
  states       : List StateRepr
  initialState : String
  transitions  : List TransitionRepr

-- ============================================================
-- §2  SysML v2 Generation
-- ============================================================

/-- Generate state definitions. -/
def stateToSysML (s : StateRepr) (lvl : Nat) : String :=
  if s.doc.isEmpty then s!"{indent lvl}state {s.name};"
  else s!"{indent lvl}state {s.name} \{\n{indent (lvl+1)}doc /* {s.doc} */\n{indent lvl}}"

/-- Generate transition definitions. -/
def transitionToSysML (t : TransitionRepr) (lvl : Nat) : String :=
  let base := s!"{indent lvl}transition {t.name}\n" ++
    s!"{indent (lvl+1)}first {t.sourceName}\n" ++
    s!"{indent (lvl+1)}then {t.targetName}"
  if t.guardDesc == "true" then base ++ ";"
  else base ++ s!"\n{indent (lvl+1)}guard \{{ t.guardDesc }};"

/-- StateMachineRepr → SysML v2 state def。 -/
def stateMachineToSysML (repr : StateMachineRepr) (lvl : Nat) : String :=
  let entry := s!"{indent (lvl+1)}entry state {repr.initialState};"
  let states := repr.states.map (fun s => stateToSysML s (lvl + 1))
  let trans := repr.transitions.map (fun t => transitionToSysML t (lvl + 1))
  let body := String.intercalate "\n\n" ([entry, ""] ++ states ++ [""] ++ trans)
  s!"{indent lvl}state def {repr.name} \{\n{body}\n{indent lvl}}"

/-- StateMachineRepr.toSysML: top-level generation. -/
def StateMachineRepr.toSysML (repr : StateMachineRepr) : String :=
  stateMachineToSysML repr 0

end VerifiedMBSE.Output
