import VerifiedMBSE.Behavior.Temporal
import VerifiedMBSE.Behavior.StateMachineKripke
import VerifiedMBSE.Behavior.ProductKripke
import VerifiedMBSE.Behavior.Product

/-!
# LTL over ProductKripke (Unified via ToKripke)

LTL over a product Kripke structure is expressed uniformly via the
`ToKripke` type class with `Always` / `Eventually` / `Leads`. This
module provides:

1. **Compatibility aliases** (§1): `Always_prod` / `Eventually_prod` /
   `Leads_prod` as `abbrev`s over the uniform operators. Existing code
   continues to compile unchanged.

2. **Lifting lemmas** (§2–§4): transport component-level LTL
   guarantees to the product (`.of_and`, `.of_left`, `.of_right`).

## Type-class-based generality

The operators and lemmas are parameterized over arbitrary
`{α β : Type} {S₁ D₁ S₂ D₂ : Type} [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]`.
Lifting takes an opposite-side `NonEmpty` witness rather than a
`StateMachine`-specific `WellFormed`:

- For `ProductKripke sm₁ sm₂` (equivalently,
  `ProductStateMachine sm₁ sm₂`), pass `hwf₂.nonEmpty` on the right
  and the original lemmas apply directly.
- For nested compositions such as
  `ProductKripke (pk : ProductKripke ...) sm₃`, pass
  `pk.toKripke.NonEmpty` and the same lemmas are reused without
  specialization.

The `Always_prod` / `Eventually_prod` / `Leads_prod` aliases retain
their original signatures, so call sites need no changes.
-/

namespace VerifiedMBSE.Behavior

-- ============================================================
-- §1  Compatibility Aliases
-- ============================================================

/-- `Always` over a product Kripke structure (compatibility alias).
    `defeq` to `Always pk P`. -/
abbrev Always_prod
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    (pk : ProductKripke x y)
    (P : S₁ × S₂ → D₁ × D₂ → Prop) : Prop :=
  Always pk P

/-- `Eventually` over a product Kripke structure (compatibility alias).
    `defeq` to `Eventually pk P`. -/
abbrev Eventually_prod
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    (pk : ProductKripke x y)
    (P : S₁ × S₂ → D₁ × D₂ → Prop) : Prop :=
  Eventually pk P

/-- `Leads` over a product Kripke structure (compatibility alias).
    `defeq` to `Leads pk P Q`. -/
abbrev Leads_prod
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    (pk : ProductKripke x y)
    (P Q : S₁ × S₂ → D₁ × D₂ → Prop) : Prop :=
  Leads pk P Q

-- ============================================================
-- §2  Safety Lifting (Always)
-- ============================================================

/-- Lift `Always` to the product: component-level `Always` properties
    combine into a conjunction `Always` on the product.

    Component reachability is supplied by `hr.fst_reachable` /
    `hr.snd_reachable`, the projection lemmas on
    `ProductKripkeReachable`. -/
theorem Always_prod.of_and
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {P₁ : S₁ → D₁ → Prop} {P₂ : S₂ → D₂ → Prop}
    (pk : ProductKripke x y)
    (h₁ : Always x P₁) (h₂ : Always y P₂) :
    Always pk (fun p d => P₁ p.1 d.1 ∧ P₂ p.2 d.2) :=
  fun p d hr =>
    ⟨h₁ p.1 d.1 hr.fst_reachable, h₂ p.2 d.2 hr.snd_reachable⟩

/-- One-sided `Always` lifting (left): lift `x`'s `Always` to the
    left component on the product. -/
theorem Always_prod.of_left
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {P₁ : S₁ → D₁ → Prop}
    (pk : ProductKripke x y)
    (h₁ : Always x P₁) :
    Always pk (fun p d => P₁ p.1 d.1) :=
  fun p d hr => h₁ p.1 d.1 hr.fst_reachable

/-- One-sided `Always` lifting (right): lift `y`'s `Always` to the
    right component on the product. -/
theorem Always_prod.of_right
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {P₂ : S₂ → D₂ → Prop}
    (pk : ProductKripke x y)
    (h₂ : Always y P₂) :
    Always pk (fun p d => P₂ p.2 d.2) :=
  fun p d hr => h₂ p.2 d.2 hr.snd_reachable

-- ============================================================
-- §3  Detection Lifting (Eventually)
-- ============================================================

/-- One-sided `Eventually` lifting (left): lift `x`'s `Eventually` to
    the left component on the product.

    Requires a `NonEmpty` witness on the opposite side (`y`) to supply
    the initial data on the right. `ProductKripkeReachable.fromLeft`
    builds the product-reachable state with a single `init`
    constructor. -/
theorem Eventually_prod.of_left
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {P₁ : S₁ → D₁ → Prop}
    (pk : ProductKripke x y)
    (hne₂ : (ToKripke.toKripke y).NonEmpty)
    (h : Eventually x P₁) :
    Eventually pk (fun p d => P₁ p.1 d.1) := by
  obtain ⟨s₁, d₁, hr₁, hP⟩ := h
  obtain ⟨s₂, d₂, hp⟩ := ProductKripkeReachable.fromLeft hr₁ hne₂
  exact ⟨(s₁, s₂), (d₁, d₂), hp, hP⟩

/-- One-sided `Eventually` lifting (right): lift `y`'s `Eventually` to
    the right component on the product. -/
theorem Eventually_prod.of_right
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {P₂ : S₂ → D₂ → Prop}
    (pk : ProductKripke x y)
    (hne₁ : (ToKripke.toKripke x).NonEmpty)
    (h : Eventually y P₂) :
    Eventually pk (fun p d => P₂ p.2 d.2) := by
  obtain ⟨s₂, d₂, hr₂, hP⟩ := h
  obtain ⟨s₁, d₁, hp⟩ := ProductKripkeReachable.fromRight hr₂ hne₁
  exact ⟨(s₁, s₂), (d₁, d₂), hp, hP⟩

-- ============================================================
-- §4  Recovery Lifting (Leads)
-- ============================================================

/-- One-sided `Leads` lifting (left): from `x`'s `Leads P₁ Q₁`, derive
    `P₁ ∘ fst ⇒ ◇ (Q₁ ∘ fst)` on the product. -/
theorem Leads_prod.of_left
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {P₁ Q₁ : S₁ → D₁ → Prop}
    (pk : ProductKripke x y)
    (hne₂ : (ToKripke.toKripke y).NonEmpty)
    (h : Leads x P₁ Q₁) :
    Leads pk (fun p d => P₁ p.1 d.1) (fun p d => Q₁ p.1 d.1) := by
  intro p d hr hP
  have hr₁ := hr.fst_reachable
  have hE : Eventually x Q₁ := h p.1 d.1 hr₁ hP
  exact Eventually_prod.of_left pk hne₂ hE

/-- One-sided `Leads` lifting (right): from `y`'s `Leads P₂ Q₂`, derive
    `P₂ ∘ snd ⇒ ◇ (Q₂ ∘ snd)` on the product. -/
theorem Leads_prod.of_right
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {P₂ Q₂ : S₂ → D₂ → Prop}
    (pk : ProductKripke x y)
    (hne₁ : (ToKripke.toKripke x).NonEmpty)
    (h : Leads y P₂ Q₂) :
    Leads pk (fun p d => P₂ p.2 d.2) (fun p d => Q₂ p.2 d.2) := by
  intro p d hr hP
  have hr₂ := hr.snd_reachable
  have hE : Eventually y Q₂ := h p.2 d.2 hr₂ hP
  exact Eventually_prod.of_right pk hne₁ hE

end VerifiedMBSE.Behavior
