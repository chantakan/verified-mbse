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

/-- TransitionRepr: 遷移の文字列表現。 -/
structure TransitionRepr where
  name       : String
  sourceName : String
  targetName : String
  guardDesc  : String := "true"
  effectDesc : String := "identity"

/-- StateRepr: 状態の文字列表現。 -/
structure StateRepr where
  name : String
  doc  : String := ""

/-- StateMachineRepr: 状態機械の文字列表現。 -/
structure StateMachineRepr where
  name         : String
  states       : List StateRepr
  initialState : String
  transitions  : List TransitionRepr

-- ============================================================
-- §2  SysML v2 生成
-- ============================================================

/-- 状態定義を生成。 -/
def stateToSysML (s : StateRepr) (lvl : Nat) : String :=
  if s.doc.isEmpty then s!"{indent lvl}state {s.name};"
  else s!"{indent lvl}state {s.name} \{\n{indent (lvl+1)}doc /* {s.doc} */\n{indent lvl}}"

/-- 遷移定義を生成。 -/
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

/-- StateMachineRepr.toSysML: トップレベル生成。 -/
def StateMachineRepr.toSysML (repr : StateMachineRepr) : String :=
  stateMachineToSysML repr 0

end VerifiedMBSE.Output
