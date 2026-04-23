import VerifiedMBSE.Behavior.KripkeStructure

/-!
# ProductKripke: Heterogeneous Product of Kripke Structures

Interleaving product `ProductKripke x y` of two Kripke structures for
arbitrary `[ToKripke α S₁ D₁]` and `[ToKripke β S₂ D₂]`. This module is
independent of `StateMachine` and develops the pure Kripke-level theory
only.

## Heterogeneous composition

`ProductKripke` accepts any two types carrying a `ToKripke` instance,
so the following all use the same API:

- `ProductKripke sm₁ sm₂ : Type` — two `StateMachine`s
- `ProductKripke (pk : ProductKripke sm₁ sm₂) sm₃ : Type` — a 3-way
  nested composition
- `ProductKripke ct₁ ct₂` — two continuous-time systems (once
  `ContinuousSystem` instances exist)

The specialization `ProductStateMachine sm₁ sm₂` for two `StateMachine`
operands is retained as an `abbrev` in `Behavior/Product.lean` and
simply elaborates to `ProductKripke sm₁ sm₂`.

## Design

### `ProductKripke x y` is an empty structure

The type itself acts as a marker encoding the agreement "take the
product of `x` and `y`". Values carry no information and are built with
`⟨⟩`. The structure is kept (rather than using `Unit`) as an extension
point for future metadata such as synchronization tables or labels.

### `ProductKripkeReachable` is interleaving

Each step advances exactly one side — either `x` or `y` — while the
other side remains unchanged. Synchronous (both-sides-at-once) steps
are not modeled.

### Invariant preservation

`ProductKripkeReachable` itself carries no invariant-preservation
obligation. The safety result `inv_holds` is established in two stages:

1. `fst_reachable` / `snd_reachable` project the product reachability
   onto component-level reachability.
2. Each component's `reachable_inv` field (an axiom of the
   `KripkeStructure` record) combines with those projections to derive
   `inv_holds` on the product.

This keeps the `KripkeStructure` definition light: the `step` relation
carries no built-in invariant obligation, and type-level contracts such
as `Transition.preserves` are confined to the component layer.
-/

namespace VerifiedMBSE.Behavior

-- ============================================================
-- §1  ProductKripke 型
-- ============================================================

/-- Marker type for the product of `x : α` and `y : β`, given
    `[ToKripke α S₁ D₁]` and `[ToKripke β S₂ D₂]`.

    An empty structure: values are built with `⟨⟩`. The type itself
    encodes the agreement "consider the product of `x` and `y`"; the
    Kripke semantics are supplied by `ProductKripkeReachable` and
    `ProductKripke.toKripke`.

    The explicit `mk ::` declaration ensures the Lean parser reads the
    following declaration correctly even though the structure has no
    fields. -/
structure ProductKripke
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    (x : α) (y : β) : Type where
  mk ::

-- ============================================================
-- §2  ProductKripkeReachable (Interleaving Semantics)
-- ============================================================

/-- Reachability relation for the product Kripke structure, defined as
    the **interleaving product**.

    - `init`: starts from any pair of component-level reachable points
      `(s₁, d₁)` / `(s₂, d₂)`. Because arbitrary reachable points are
      admitted, subsequent lifting lemmas (`fromLeft`, `fromRight`) do
      not require induction.
    - `stepLeft` / `stepRight`: advances `(toKripke x).step` or
      `(toKripke y).step` by one step while the other side remains
      unchanged. -/
inductive ProductKripkeReachable
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    (x : α) (y : β) : S₁ × S₂ → D₁ × D₂ → Prop where
  /-- Initial case: start from reachable points of both Kripke structures. -/
  | init : ∀ {s₁ : S₁} {s₂ : S₂} {d₁ : D₁} {d₂ : D₂},
      (ToKripke.toKripke x).reachable s₁ d₁ →
      (ToKripke.toKripke y).reachable s₂ d₂ →
      ProductKripkeReachable x y (s₁, s₂) (d₁, d₂)
  /-- Left step: `x` advances by one step, `y` remains unchanged. -/
  | stepLeft : ∀ {s₁ : S₁} {s₂ : S₂} {d₁ : D₁} {d₂ : D₂} {s₁' : S₁} {d₁' : D₁},
      ProductKripkeReachable x y (s₁, s₂) (d₁, d₂) →
      (ToKripke.toKripke x).step s₁ d₁ s₁' d₁' →
      ProductKripkeReachable x y (s₁', s₂) (d₁', d₂)
  /-- Right step: `y` advances by one step, `x` remains unchanged. -/
  | stepRight : ∀ {s₁ : S₁} {s₂ : S₂} {d₁ : D₁} {d₂ : D₂} {s₂' : S₂} {d₂' : D₂},
      ProductKripkeReachable x y (s₁, s₂) (d₁, d₂) →
      (ToKripke.toKripke y).step s₂ d₂ s₂' d₂' →
      ProductKripkeReachable x y (s₁, s₂') (d₁, d₂')

-- ============================================================
-- §3  Projection Lemmas (fst_reachable / snd_reachable)
-- ============================================================

/-- Projection: product reachability implies left-component reachability.

    The `stepLeft` case uses the component's
    `step_preserves_reachable` axiom; the `stepRight` case leaves the
    left component unchanged and returns the induction hypothesis
    directly. -/
theorem ProductKripkeReachable.fst_reachable
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {p : S₁ × S₂} {d : D₁ × D₂}
    (h : ProductKripkeReachable x y p d) :
    (ToKripke.toKripke x).reachable p.1 d.1 := by
  induction h with
  | init hr₁ _hr₂ => exact hr₁
  | stepLeft _hr₀ hstep ih =>
      exact (ToKripke.toKripke x).step_preserves_reachable _ _ _ _ ih hstep
  | stepRight _hr₀ _hstep ih => exact ih

/-- Projection: product reachability implies right-component reachability. -/
theorem ProductKripkeReachable.snd_reachable
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {p : S₁ × S₂} {d : D₁ × D₂}
    (h : ProductKripkeReachable x y p d) :
    (ToKripke.toKripke y).reachable p.2 d.2 := by
  induction h with
  | init _hr₁ hr₂ => exact hr₂
  | stepLeft _hr₀ _hstep ih => exact ih
  | stepRight _hr₀ hstep ih =>
      exact (ToKripke.toKripke y).step_preserves_reachable _ _ _ _ ih hstep

-- ============================================================
-- §4  Safety Theorem (inv_holds)
-- ============================================================

/-- Product-level safety: a product-reachable state satisfies the
    invariant of both components.

    Extracts component reachability via `fst_reachable` / `snd_reachable`
    and applies each component's `reachable_inv` axiom. No induction on
    `ProductKripkeReachable` itself is required. -/
theorem ProductKripkeReachable.inv_holds
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {p : S₁ × S₂} {d : D₁ × D₂}
    (h : ProductKripkeReachable x y p d) :
    (ToKripke.toKripke x).inv p.1 d.1 ∧ (ToKripke.toKripke y).inv p.2 d.2 :=
  ⟨(ToKripke.toKripke x).reachable_inv _ _ h.fst_reachable,
   (ToKripke.toKripke y).reachable_inv _ _ h.snd_reachable⟩

-- ============================================================
-- §5  step_preserves_reachable
-- ============================================================

/-- The product step preserves reachability.

    Supplied to the `step_preserves_reachable` field of
    `ProductKripke.toKripke`. Decomposes the interleaving disjunction
    and applies `stepLeft` / `stepRight` in the respective branches. -/
theorem ProductKripkeReachable.step_preserves_reachable
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β} :
    ∀ (p : S₁ × S₂) (d : D₁ × D₂) (p' : S₁ × S₂) (d' : D₁ × D₂),
      ProductKripkeReachable x y p d →
      (((ToKripke.toKripke x).step p.1 d.1 p'.1 d'.1 ∧ p.2 = p'.2 ∧ d.2 = d'.2)
        ∨ ((ToKripke.toKripke y).step p.2 d.2 p'.2 d'.2 ∧ p.1 = p'.1 ∧ d.1 = d'.1)) →
      ProductKripkeReachable x y p' d' := by
  rintro ⟨s₁, s₂⟩ ⟨d₁, d₂⟩ ⟨s₁', s₂'⟩ ⟨d₁', d₂'⟩ hr hstep
  rcases hstep with
    ⟨hstep₁, rfl, rfl⟩ | ⟨hstep₂, rfl, rfl⟩
  · -- 左 step: s₂ = s₂', d₂ = d₂' は rfl で統合済み
    exact ProductKripkeReachable.stepLeft hr hstep₁
  · -- 右 step: s₁ = s₁', d₁ = d₁' は rfl で統合済み
    exact ProductKripkeReachable.stepRight hr hstep₂

-- ============================================================
-- §6  Lifting Lemmas (fromLeft / fromRight)
-- ============================================================

/-- Lifting: construct product reachability from a left-component
    reachable point together with a `NonEmpty` witness on the right.

    Because `ProductKripkeReachable.init` accepts arbitrary reachable
    points on both sides, the `init` constructor discharges this
    lemma directly — no induction required. -/
theorem ProductKripkeReachable.fromLeft
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {s₁ : S₁} {d₁ : D₁}
    (hr₁ : (ToKripke.toKripke x).reachable s₁ d₁)
    (hne₂ : (ToKripke.toKripke y).NonEmpty) :
    ∃ (s₂ : S₂) (d₂ : D₂), ProductKripkeReachable x y (s₁, s₂) (d₁, d₂) := by
  obtain ⟨s₂, d₂, hr₂⟩ := hne₂
  exact ⟨s₂, d₂, ProductKripkeReachable.init hr₁ hr₂⟩

/-- Lifting: construct product reachability from a right-component
    reachable point together with a `NonEmpty` witness on the left. -/
theorem ProductKripkeReachable.fromRight
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {s₂ : S₂} {d₂ : D₂}
    (hr₂ : (ToKripke.toKripke y).reachable s₂ d₂)
    (hne₁ : (ToKripke.toKripke x).NonEmpty) :
    ∃ (s₁ : S₁) (d₁ : D₁), ProductKripkeReachable x y (s₁, s₂) (d₁, d₂) := by
  obtain ⟨s₁, d₁, hr₁⟩ := hne₁
  exact ⟨s₁, d₁, ProductKripkeReachable.init hr₁ hr₂⟩

-- ============================================================
-- §7  ProductKripke.toKripke
-- ============================================================

/-- View `ProductKripke x y` as a `KripkeStructure (S₁ × S₂) (D₁ × D₂)`.

    Defined as `abbrev` so elaboration is reducible and the following
    definitional equalities hold:

    - `(pk.toKripke).inv p d = (toKripke x).inv p.1 d.1 ∧ (toKripke y).inv p.2 d.2`
    - `(pk.toKripke).reachable p d = ProductKripkeReachable x y p d`
    - `(pk.toKripke).step = ` the interleaving disjunction

    ### `reachable_inv` / `step_preserves_reachable`

    Supplied by the lemmas from §4 and §5
    (`ProductKripkeReachable.inv_holds` and
    `ProductKripkeReachable.step_preserves_reachable`). -/
abbrev ProductKripke.toKripke
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    (_ : ProductKripke x y) : KripkeStructure (S₁ × S₂) (D₁ × D₂) :=
  { inv := fun p d =>
      (ToKripke.toKripke x).inv p.1 d.1 ∧ (ToKripke.toKripke y).inv p.2 d.2
    reachable := ProductKripkeReachable x y
    reachable_inv := fun _ _ hr => ProductKripkeReachable.inv_holds hr
    step := fun p d p' d' =>
      ((ToKripke.toKripke x).step p.1 d.1 p'.1 d'.1 ∧ p.2 = p'.2 ∧ d.2 = d'.2)
      ∨
      ((ToKripke.toKripke y).step p.2 d.2 p'.2 d'.2 ∧ p.1 = p'.1 ∧ d.1 = d'.1)
    step_preserves_reachable := ProductKripkeReachable.step_preserves_reachable }

-- ============================================================
-- §8  ToKripke instance
-- ============================================================

/-- `ToKripke` instance for `ProductKripke x y`.

    Makes `Always pk P`, `Eventually pk P`, and `Leads pk P Q`
    available for products with the same API used for `StateMachine`
    and `ProductStateMachine`. Nested compositions of three or more
    operands (e.g. `ProductKripke (pk : ProductKripke ...) sm₃`) work
    because instance resolution recurses through this declaration. -/
instance instToKripkeProductKripke
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β} :
    ToKripke (ProductKripke x y) (S₁ × S₂) (D₁ × D₂) where
  toKripke pk := pk.toKripke

-- ============================================================
-- §9  ProductKripke.nonEmpty
-- ============================================================

/-- `NonEmpty` on both sides implies `NonEmpty` on the product.

    The `init` constructor assembles a product-reachable state from the
    two component reachable points, so the proof is immediate and
    requires no induction. -/
theorem ProductKripke.nonEmpty
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    (pk : ProductKripke x y)
    (hne₁ : (ToKripke.toKripke x).NonEmpty)
    (hne₂ : (ToKripke.toKripke y).NonEmpty) :
    pk.toKripke.NonEmpty := by
  obtain ⟨s₁, d₁, hr₁⟩ := hne₁
  obtain ⟨s₂, d₂, hr₂⟩ := hne₂
  exact ⟨(s₁, s₂), (d₁, d₂), ProductKripkeReachable.init hr₁ hr₂⟩

end VerifiedMBSE.Behavior
