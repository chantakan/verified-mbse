import VerifiedMBSE.Behavior.StateMachine
import VerifiedMBSE.Behavior.StateMachineKripke
import VerifiedMBSE.Behavior.Temporal

/-!
# StateMachine-specific LTL Operators

`Next` (◯ P) and `Until` (P U Q) depend on the explicit transition
list `sm.transitions`, so they belong to `StateMachine` rather than
`KripkeStructure` and are separated into this module.

Lifting `Next` / `Until` to `KripkeStructure` would require a
per-step relation `K.step : State → Data → State → Data → Prop`
that exposes enough structure for these operators. The `StateMachine`
specialization covers present needs.
-/

namespace VerifiedMBSE.Behavior

-- ============================================================
-- §1  Next (◯)
-- ============================================================

/-- `Next (◯ P)`: from `(s, d)`, some transition leads to a successor
    state at which `P` holds. Depends on `sm.transitions`, so this
    operator is specific to `StateMachine`. -/
def Next {S D : Type} {inv : S → D → Prop}
    (sm : StateMachine S D inv)
    (P : S → D → Prop) (s : S) (d : D) : Prop :=
  ∃ t ∈ sm.transitions,
    t.source = s ∧ t.guard d ∧ P t.target (t.effect d)

-- ============================================================
-- §2  Until (P U Q)
-- ============================================================

/-- `Until P Q`: some state where `Q` holds is reached while `P`
    holds throughout.

    `now` case: `Q` already holds at the current state.
    `later` case: `P` holds at the current state, and `Until` continues
    after advancing one transition (inductively). -/
inductive Until {S D : Type} {inv : S → D → Prop}
    (sm : StateMachine S D inv)
    (P Q : S → D → Prop) : S → D → Prop where
  | now   : ∀ {s : S} {d : D}, Q s d →
            Until sm P Q s d
  | later : ∀ {s : S} {d : D} (t : Transition S D inv),
            P s d →
            t ∈ sm.transitions →
            t.source = s →
            t.guard d →
            Until sm P Q t.target (t.effect d) →
            Until sm P Q s d

/-- `Until P Q` implies `Eventually Q`, given a reachability witness.

    The reachability witness `hr` of the starting state propagates
    through the inductive structure of `Until`, yielding a reachable
    state at which `Q` holds. -/
theorem until_implies_eventually
    {S D : Type} {inv : S → D → Prop}
    {sm : StateMachine S D inv}
    {P Q : S → D → Prop}
    {s : S} {d : D}
    (hr : Reachable sm s d)
    (h : Until sm P Q s d) :
    Eventually sm Q := by
  induction h with
  | now hq =>
      exact ⟨_, _, hr, hq⟩
  | later t _hP hmem hsrc hguard _hU ih =>
      exact ih (Reachable.step t hr hmem hsrc hguard)

end VerifiedMBSE.Behavior
