/-!
# KripkeStructure: Semantic Foundation for LTL Operators

Abstracts the reachability relation, invariant, and one-step relation
so that LTL operators (`Always`, `Eventually`, `Leads`) share a common
API across `StateMachine`, `ProductStateMachine`, `ProductKripke`, and
future continuous-time systems.

The `ToKripke` type class lifts a concrete type `α` to a
`KripkeStructure State Data` value, which is what the LTL operators
and Kripke-level lemmas actually consume.

## Design decisions

### `ToKripke` type class rather than `Coe`

A `Coe (StateMachine S D inv) (KripkeStructure S D)` instance fails
Lean 4.30's strict "semi-out-params" check because `inv` appears in
the source type but never in the target: the elaborator reports that
`inv` cannot flow from the target back to the source.

`ToKripke` sidesteps this by making `State` and `Data` `outParam`s.
Instance resolution matches directly on the concrete shape of `α`
(e.g. `StateMachine TCSMode Nat tcsInvariant`), and extra implicit
arguments such as `inv` are naturally resolved along the way.

### `State` and `Data` as type parameters

Defining `structure KripkeStructure (State : Type) (Data : Type)` with
explicit type parameters avoids elaborator confusion arising from
field projections `K.State` / `K.Data` that would otherwise unfold
lazily. In particular, tactics like `omega` would fail to recognize
`Nat` as equal to a projected `K.Data`.

### Structure fields and the `ProductKripke` axiomatization

`KripkeStructure` carries four fields beyond `reachable`:

| Field | Role |
|---|---|
| `inv` | System invariant: property that must hold at every reachable state. |
| `reachable_inv` | Reachability implies the invariant (corresponds to `StateMachine.Reachable.inv_holds`). |
| `step` | One-step transition relation, used to express the "one side advances while the other is frozen" pattern of interleaving products at the Kripke level. |
| `step_preserves_reachable` | The `step` relation preserves reachability (required when type-checking `ProductKripkeReachable.stepLeft` / `.stepRight`). |

These fields form the axiomatic basis that `ProductKripke x y` relies on
when its `toKripke` instance builds the product from the component
Kripke structures on each side. `Always`, `Eventually`, and `Leads`
depend only on `reachable`, so their type-class-based API is unaffected
by the additional fields.

## Usage

```lean
-- `Always sm P` resolves via the `ToKripke` instance.
#check Always sm (fun s _ => s ≠ .fault)
```
-/

namespace VerifiedMBSE.Behavior

-- ============================================================
-- §1  KripkeStructure
-- ============================================================

/-- Kripke structure: abstract semantic foundation bundling a
    reachability relation, an invariant, and a one-step transition
    relation.

    `State` and `Data` are exposed as explicit type parameters (rather
    than structure fields), which avoids elaborator confusion caused
    by lazy unfolding of field projections `K.State` / `K.Data`.

    ### Fields

    - `inv`: system invariant that must hold at every reachable state.
    - `reachable`: reachability relation, holding on any `(state, data)`
      pair reachable in finitely many steps from an initial state.
    - `reachable_inv`: axiom stating that reachability implies the
      invariant (the Kripke-level counterpart of
      `StateMachine.Reachable.inv_holds`).
    - `step`: one-step transition relation; `step s d s' d'` holds when
      `(s, d)` transitions to `(s', d')` in one step.
    - `step_preserves_reachable`: axiom stating that `step` preserves
      reachability. -/
structure KripkeStructure (State : Type) (Data : Type) where
  /-- System invariant; holds at every reachable state. -/
  inv : State → Data → Prop
  /-- Reachability relation; holds on any `(s, d)` reachable from an
      initial state in finitely many steps. -/
  reachable : State → Data → Prop
  /-- Reachability implies the invariant. -/
  reachable_inv : ∀ s d, reachable s d → inv s d
  /-- One-step transition relation: `(s, d)` transitions to `(s', d')`. -/
  step : State → Data → State → Data → Prop
  /-- `step` sends reachable states to reachable states. -/
  step_preserves_reachable :
    ∀ s d s' d', reachable s d → step s d s' d' → reachable s' d'

/-- The Kripke structure is non-empty: at least one `(s, d)` is reachable. -/
def KripkeStructure.NonEmpty {State Data : Type}
    (K : KripkeStructure State Data) : Prop :=
  ∃ (s : State) (d : Data), K.reachable s d

-- ============================================================
-- §2  ToKripke Type Class
-- ============================================================

/-- `ToKripke α State Data` provides a method for lifting values of
    `α` to `KripkeStructure State Data`.

    `State` and `Data` are `outParam`s, so instance resolution
    determines them automatically from the concrete shape of `α`.
    This lets calls such as `Always sm P` (`sm : StateMachine S D inv`)
    elaborate `P : S → D → Prop` with `S` and `D` pinned down.

    Instances are provided for:
    - `StateMachine S D inv`
    - `ProductKripke x y` (which subsumes `ProductStateMachine sm₁ sm₂`
      as an `abbrev`)

    Continuous-time reachability abstractions can be registered via
    further `ToKripke` instances. -/
class ToKripke (α : Type) (State : outParam Type) (Data : outParam Type) where
  /-- Conversion from `α` to `KripkeStructure State Data`. -/
  toKripke : α → KripkeStructure State Data

end VerifiedMBSE.Behavior
