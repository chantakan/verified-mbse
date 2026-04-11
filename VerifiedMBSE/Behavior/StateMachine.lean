import VerifiedMBSE.Core.Component

/-!
# State Machine: Dependently Typed Behavioral Model

Defines `Transition` (with invariant preservation embedded as a type-level proof),
`StateMachine`, the inductive proposition `Reachable`, and the safety theorem
`Reachable.inv_holds`.

## Key Design Decision
Embedding invariant preservation in `Transition.preserves` makes transitions that
violate the invariant unconstructible (type error).
-/

namespace VerifiedMBSE.Behavior

-- ============================================================
-- §1  Transition
-- ============================================================

/-- Transition: transition defined over control state S and data type D.
    The `preserves` field guarantees invariant preservation at the type level. -/
structure Transition (S : Type) (D : Type) (inv : S → D → Prop) where
  /-- Source control state -/
  source   : S
  /-- Target control state -/
  target   : S
  /-- Guard condition -/
  guard    : D → Prop
  /-- Effect (data transformation) -/
  effect   : D → D
  /-- Type-level contract for invariant preservation -/
  preserves : ∀ d : D, guard d → inv source d → inv target (effect d)

-- ============================================================
-- §2  StateMachine
-- ============================================================

/-- StateMachine: state machine consisting of an initial state and a list of transitions. -/
structure StateMachine (S : Type) (D : Type) (inv : S → D → Prop) where
  /-- Initial control state -/
  initialState : S
  /-- List of transitions -/
  transitions  : List (Transition S D inv)

/-- Well-formedness of StateMachine: data satisfying the invariant exists in the initial state. -/
def StateMachine.WellFormed {S D : Type} {inv : S → D → Prop}
    (sm : StateMachine S D inv) : Prop :=
  ∃ d₀ : D, inv sm.initialState d₀

-- ============================================================
-- §3  Reachable (Reachability)
-- ============================================================

/-- Reachable: inductive proposition for reachable (control state, data value) pairs.
    Tracking both enables induction for inv_holds. -/
inductive Reachable {S D : Type} {inv : S → D → Prop}
    (sm : StateMachine S D inv) : S → D → Prop where
  /-- The initial state is reachable -/
  | init : ∀ (d₀ : D), inv sm.initialState d₀ →
           Reachable sm sm.initialState d₀
  /-- The next state is reachable via a transition -/
  | step : ∀ {s : S} {d : D} (t : Transition S D inv),
           Reachable sm s d →
           t ∈ sm.transitions →
           t.source = s →
           t.guard d →
           Reachable sm t.target (t.effect d)

-- ============================================================
-- §4  Safety Theorem
-- ============================================================

/-- Safety theorem: all reachable pairs satisfy the invariant.
    Directly provable by induction since Transition.preserves is embedded in the type. -/
theorem Reachable.inv_holds {S D : Type} {inv : S → D → Prop}
    {sm : StateMachine S D inv} {s : S} {d : D}
    (h : Reachable sm s d) : inv s d := by
  induction h with
  | init d₀ hd₀ =>
      exact hd₀
  | step t _hr _hmem hsrc hguard ih =>
      rw [← hsrc] at ih
      exact t.preserves _ hguard ih

/-- The initial state of a WellFormed state machine has data satisfying the invariant. -/
theorem StateMachine.initial_inv_holds {S D : Type} {inv : S → D → Prop}
    {sm : StateMachine S D inv}
    (hwf : sm.WellFormed) :
    ∃ d : D, inv sm.initialState d :=
  hwf

end VerifiedMBSE.Behavior
