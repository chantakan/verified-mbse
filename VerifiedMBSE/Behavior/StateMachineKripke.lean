import VerifiedMBSE.Behavior.StateMachine
import VerifiedMBSE.Behavior.KripkeStructure

/-!
# StateMachine → KripkeStructure via ToKripke

Provides a `ToKripke` instance for `StateMachine S D inv`, letting
calls like `Always sm P` be resolved transparently through type-class
resolution.

## `ToKripke` instance rather than `Coe`

A `Coe (StateMachine S D inv) (KripkeStructure S D)` instance fails
Lean 4.30's strict semi-out-params check because `inv` appears in the
source type but cannot flow from the target `KripkeStructure S D`.

The `ToKripke` type class marks only `State` and `Data` as `outParam`,
so instance matching on the full shape `α = StateMachine S D inv`
resolves naturally and picks up `inv` along the way.

## Filling the `KripkeStructure` fields

`KripkeStructure` exposes `inv`, `step`, `reachable_inv`, and
`step_preserves_reachable`, and `StateMachine.toKripke` populates all
four:

- `inv` — the `inv : S → D → Prop` parameter of `StateMachine`,
  passed through directly so `(sm.toKripke).inv = inv` holds
  definitionally.
- `reachable_inv` — a thin wrapper around `Reachable.inv_holds`.
- `step` — existentially quantified one-step relation over
  `sm.transitions`.
- `step_preserves_reachable` — discharged by the `Reachable.step`
  constructor.

Keeping the definition as `abbrev` preserves the definitional
equalities `(sm.toKripke).inv = inv` and
`(sm.toKripke).reachable s d = Reachable sm s d`.
-/

namespace VerifiedMBSE.Behavior

-- ============================================================
-- §1  StateMachine.toKripke
-- ============================================================

/-- View a `StateMachine` as a `KripkeStructure`.

    Defined as `abbrev` so elaboration is reducible and the following
    definitional equalities hold:

    - `(sm.toKripke).inv = inv` (the type parameter itself)
    - `(sm.toKripke).reachable s d = Reachable sm s d`
    - `(sm.toKripke).step s d s' d'` unfolds to the existential over
      `sm.transitions`

    ### `step` definition

    `step s d s' d'` holds when some transition `t ∈ sm.transitions`
    satisfies `t.source = s`, `t.guard d`, `t.target = s'`, and
    `t.effect d = d'`.

    ### `step_preserves_reachable` proof

    Unfolding the existential supplies the transition `t` together
    with the required equalities; the `Reachable.step` constructor
    then closes the goal directly. -/
abbrev StateMachine.toKripke
    {S D : Type} {inv : S → D → Prop}
    (sm : StateMachine S D inv) : KripkeStructure S D :=
  { inv := inv
    reachable := Reachable sm
    reachable_inv := fun _ _ hr => hr.inv_holds
    step := fun s d s' d' =>
      ∃ (t : Transition S D inv),
        t ∈ sm.transitions ∧ t.source = s ∧ t.guard d ∧
        t.target = s' ∧ t.effect d = d'
    step_preserves_reachable := by
      intro s d s' d' hr hstep
      -- 存在量化を開き、等式 `t.target = s'` と `t.effect d = d'` は rfl で統合
      obtain ⟨t, hmem, hsrc, hguard, rfl, rfl⟩ := hstep
      exact Reachable.step t hr hmem hsrc hguard }

-- ============================================================
-- §2  ToKripke instance
-- ============================================================

/-- `ToKripke` instance for `StateMachine`.

    Calls such as `Always sm P` with `sm : StateMachine S D inv`
    resolve `ToKripke (StateMachine S D inv) S D`, and `State = S` /
    `Data = D` are determined via the `outParam` fields of the class. -/
instance instToKripkeStateMachine
    {S D : Type} {inv : S → D → Prop} :
    ToKripke (StateMachine S D inv) S D where
  toKripke sm := sm.toKripke

-- ============================================================
-- §3  WellFormed → NonEmpty
-- ============================================================

/-- `sm.WellFormed` implies `sm.toKripke.NonEmpty`. -/
theorem StateMachine.wellFormed_imp_nonEmpty
    {S D : Type} {inv : S → D → Prop}
    {sm : StateMachine S D inv}
    (hwf : sm.WellFormed) :
    sm.toKripke.NonEmpty := by
  obtain ⟨d₀, hd₀⟩ := hwf
  exact ⟨sm.initialState, d₀, Reachable.init d₀ hd₀⟩

/-- Dot-notation alias: `hwf.nonEmpty`. -/
theorem StateMachine.WellFormed.nonEmpty
    {S D : Type} {inv : S → D → Prop}
    {sm : StateMachine S D inv}
    (hwf : sm.WellFormed) :
    sm.toKripke.NonEmpty :=
  StateMachine.wellFormed_imp_nonEmpty hwf

end VerifiedMBSE.Behavior
