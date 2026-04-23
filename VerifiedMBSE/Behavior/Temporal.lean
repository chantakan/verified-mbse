import VerifiedMBSE.Behavior.KripkeStructure

/-!
# LTL Temporal Operators via ToKripke Type Class

Defines `Always` (□), `Eventually` (◇), and `Leads` (⇒◇) through the
`ToKripke` type class, so that `Always sm P`, `Always psm P`, and
`Always ct P` share a single API across `StateMachine`,
product state machines, and continuous-time systems.

## Dispatch via `ToKripke`

When `Always x P` receives `x : α`, the `ToKripke α State Data`
instance is resolved and `State` / `Data` are determined via
`outParam`. The predicate `P : State → Data → Prop` is elaborated
with its domain pinned down, so lambdas such as `fun s d => Q s d`
have definite domain types and subsequent tactics like `omega` or
`simp` operate without ambiguity.

## `Next` and `Until`

`Next` (◯) and `Until` (P U Q) depend on the explicit transition
structure of `StateMachine` and do not fit the `KripkeStructure`
abstraction. They live in `StateMachineLTL.lean`.
-/

namespace VerifiedMBSE.Behavior

-- ============================================================
-- §1  Basic Temporal Operators
-- ============================================================

/-- `Always (□ P)`: `P s d` holds at every reachable `(s, d)`.

    Defined as `abbrev` via the type class so that after `intro s d hr`
    the goal lambda β-reduces automatically. -/
abbrev Always {α : Type} {State Data : Type} [ToKripke α State Data]
    (x : α) (P : State → Data → Prop) : Prop :=
  ∀ s d, (ToKripke.toKripke x).reachable s d → P s d

/-- `Eventually (◇ P)`: some reachable `(s, d)` satisfies `P s d`. -/
abbrev Eventually {α : Type} {State Data : Type} [ToKripke α State Data]
    (x : α) (P : State → Data → Prop) : Prop :=
  ∃ s d, (ToKripke.toKripke x).reachable s d ∧ P s d

/-- `Leads (P ⇒ ◇ Q)`: the weak semantics — at every reachable state
    satisfying `P`, a reachable state satisfying `Q` exists. -/
abbrev Leads {α : Type} {State Data : Type} [ToKripke α State Data]
    (x : α) (P Q : State → Data → Prop) : Prop :=
  Always x (fun s d => P s d → Eventually x Q)

-- ============================================================
-- §2  Basic Algebraic Laws
-- ============================================================

/-- `□ P ∧ □ Q → □(P ∧ Q)`. -/
theorem always_and {α : Type} {State Data : Type} [ToKripke α State Data]
    {x : α} {P Q : State → Data → Prop}
    (hP : Always x P) (hQ : Always x Q) :
    Always x (fun s d => P s d ∧ Q s d) :=
  fun s d hr => ⟨hP s d hr, hQ s d hr⟩

/-- `NonEmpty` together with `□ P` implies `◇ P`. -/
theorem always_implies_eventually {α : Type} {State Data : Type}
    [ToKripke α State Data]
    {x : α} {P : State → Data → Prop}
    (hne : (ToKripke.toKripke x).NonEmpty) (h : Always x P) :
    Eventually x P := by
  obtain ⟨s, d, hr⟩ := hne
  exact ⟨s, d, hr, h s d hr⟩

/-- `Leads P P`: reflexivity of `Leads`. -/
theorem always_leads {α : Type} {State Data : Type} [ToKripke α State Data]
    {x : α} {P : State → Data → Prop} :
    Leads x P P :=
  fun s d hr hP => ⟨s, d, hr, hP⟩

end VerifiedMBSE.Behavior
