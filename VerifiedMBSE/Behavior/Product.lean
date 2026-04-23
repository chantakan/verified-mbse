import VerifiedMBSE.Behavior.StateMachine
import VerifiedMBSE.Behavior.StateMachineKripke
import VerifiedMBSE.Behavior.ProductKripke

/-!
# ProductStateMachine: StateMachine-Specialized Layer over `ProductKripke`

The canonical product of two behavioral models lives in
`Behavior/ProductKripke.lean` as `ProductKripke x y`, a marker type
parameterized over arbitrary `[ToKripke α S₁ D₁]` and
`[ToKripke β S₂ D₂]` instances.

This file layers a **StateMachine-specialized API** on top of
`ProductKripke`, providing:

1. `productInv` — the conjunction of two `StateMachine` invariants,
   directly referenced by `Reachable` and `PartDef.invariant` in
   `Examples`.
2. `ProductStateMachine sm₁ sm₂` — an `abbrev` for
   `ProductKripke sm₁ sm₂`.
3. `ProductReachable sm₁ sm₂` — an `abbrev` for
   `ProductKripkeReachable sm₁ sm₂`.
4. `ProductStateMachine.initialState` / `.WellFormed` /
   `.wellFormed_iff` / `.nonEmpty` — dot-notation helpers that only
   make sense under `StateMachine` assumptions.

Because `ProductStateMachine` and `ProductReachable` are `abbrev`s,
instance resolution and `defeq` transparently forward to the
underlying `ProductKripke` definitions, and existing call sites in
`Examples` work without modification.
-/

namespace VerifiedMBSE.Behavior

-- ============================================================
-- §1  Product Invariant
-- ============================================================

/-- Product invariant: the conjunction of two invariants.

    Declared as `abbrev` so that `.1` / `.2` projection and
    `refine ⟨_, _⟩` work transparently. The `inv` field of
    `ProductKripke sm₁ sm₂` is
    `fun p d => (sm₁.toKripke).inv p.1 d.1 ∧ (sm₂.toKripke).inv p.2 d.2`,
    which is `defeq` to `productInv inv₁ inv₂`. -/
abbrev productInv
    {S₁ D₁ : Type} (inv₁ : S₁ → D₁ → Prop)
    {S₂ D₂ : Type} (inv₂ : S₂ → D₂ → Prop) :
    S₁ × S₂ → D₁ × D₂ → Prop :=
  fun p d => inv₁ p.1 d.1 ∧ inv₂ p.2 d.2

-- ============================================================
-- §2  ProductStateMachine (abbrev of ProductKripke)
-- ============================================================

/-- Product state machine, provided as an `abbrev` for
    `ProductKripke sm₁ sm₂`.

    Because it is an `abbrev`, type inference resolves
    `⟨⟩ : ProductStateMachine sm₁ sm₂` as `ProductKripke sm₁ sm₂`, so
    existing patterns such as
    `epsMiniPSM : ProductStateMachine epsSM miniSM := ⟨⟩` work directly.

    The `ToKripke` instance is supplied by `instToKripkeProductKripke`
    and is picked up automatically, since `abbrev` is transparent to
    instance resolution. -/
abbrev ProductStateMachine
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    (sm₁ : StateMachine S₁ D₁ inv₁) (sm₂ : StateMachine S₂ D₂ inv₂) : Type :=
  ProductKripke sm₁ sm₂

/-- Product reachability, provided as an `abbrev` for
    `ProductKripkeReachable sm₁ sm₂`.

    The constructors `init` / `stepLeft` / `stepRight` from
    `ProductKripkeReachable` are usable directly via dot notation. -/
abbrev ProductReachable
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    (sm₁ : StateMachine S₁ D₁ inv₁) (sm₂ : StateMachine S₂ D₂ inv₂) :
    S₁ × S₂ → D₁ × D₂ → Prop :=
  ProductKripkeReachable sm₁ sm₂

-- ============================================================
-- §3  StateMachine 特化 API (initialState / WellFormed)
-- ============================================================

/-- Initial state of a product state machine: the pair of component
    initial states.

    `ProductKripke` has no notion of an initial state in general; this
    definition is specific to the `StateMachine` specialization. -/
def ProductStateMachine.initialState
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    (_ : ProductStateMachine sm₁ sm₂) : S₁ × S₂ :=
  (sm₁.initialState, sm₂.initialState)

/-- `WellFormed` for a product state machine: both component state
    machines are `WellFormed`.

    The Kripke layer only provides the weaker `NonEmpty` condition;
    this `WellFormed` variant is specific to the `StateMachine`
    specialization. See §4 for conversion to the Kripke-level
    `NonEmpty`. -/
def ProductStateMachine.WellFormed
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    (_ : ProductStateMachine sm₁ sm₂) : Prop :=
  sm₁.WellFormed ∧ sm₂.WellFormed

/-- `ProductStateMachine.WellFormed` unfolds to the conjunction of the
    component `WellFormed` properties. -/
theorem ProductStateMachine.wellFormed_iff
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    (psm : ProductStateMachine sm₁ sm₂) :
    psm.WellFormed ↔ sm₁.WellFormed ∧ sm₂.WellFormed :=
  Iff.rfl

-- ============================================================
-- §4  NonEmpty (WellFormed → NonEmpty bridge)
-- ============================================================

/-- If both `sm₁` and `sm₂` are `WellFormed`, the product Kripke
    structure is `NonEmpty`.

    Acts as a convenience bridge for call sites that hold
    `StateMachine.WellFormed` proofs but need to feed the Kripke-level
    `NonEmpty` into generic operators such as `FDIRBundle.compose`.
    Internally, `WellFormed.nonEmpty` converts each side to
    `NonEmpty`, and the result is assembled by
    `ProductKripke.nonEmpty`. -/
theorem ProductStateMachine.nonEmpty
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    (psm : ProductStateMachine sm₁ sm₂)
    (hwf₁ : sm₁.WellFormed) (hwf₂ : sm₂.WellFormed) :
    psm.toKripke.NonEmpty :=
  ProductKripke.nonEmpty psm hwf₁.nonEmpty hwf₂.nonEmpty

end VerifiedMBSE.Behavior
