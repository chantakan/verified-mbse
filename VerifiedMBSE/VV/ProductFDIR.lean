import VerifiedMBSE.VV.SubSystemSpec
import VerifiedMBSE.Behavior.ProductTemporal

/-!
# Parallel Composition of SubSystemSpec / FDIRBundle / BehavioralSpec

Binary composition operators for `FDIRBundle`, `BehavioralSpec`, and
`SubSystemSpec` over the product Kripke structure `ProductKripke x y`.
Each operator builds the composed value by composing the corresponding
component of the two operands.

## Contents

1. `FDIRBundle.compose` — parallel composition of two `FDIRBundle`s.
2. `BehavioralSpec.compose` — parallel composition of two `BehavioralSpec`s.
3. `SubSystemSpec.compose` — parallel composition of two `SubSystemSpec`s.

All three are parameterized over arbitrary `[ToKripke α S D]` instances
rather than specialized to `StateMachine`, so compositions of three or
more operands nest directly:

```lean
let s₁₂ := SubSystemSpec.compose s₁ s₂ pk₁₂ hne₁ hne₂ [] ...
let s₁₂₃ := SubSystemSpec.compose s₁₂ s₃ pk₁₂₃ s₁₂.behavioral.nonEmpty hne₃ [] ...
```

The intermediate `pk₁₂ : ProductKripke x₁ x₂` carries its own
`ToKripke` instance, so the `NonEmpty` witness required at the next
level is simply `s₁₂.behavioral.nonEmpty`.

## FDIR composition semantics

- `isFault    := f₁.isFault p.1 ∨ f₂.isFault p.2`   — either side fault
- `isRecovery := f₁.isRecovery p.1 ∨ f₂.isRecovery p.2` — either side recovery
- `isSafe     := f₁.isSafe q.1 ∧ f₂.isSafe q.2`      — both sides safe

### Why `isRecovery` uses `∨`

A natural first instinct is to define
`isRecovery := f₁.isRecovery p.1 ∧ f₂.isRecovery p.2`
(both sides recovering simultaneously), but this condition is typically
unreachable: if only one side experiences a fault, the other remains
frozen at its nominal state, and a component-level `FDIRBundle`
guarantees nothing about whether the non-faulting side ever enters its
recovery predicate.

The `∨` semantics — "whichever side faulted must eventually recover" —
matches the practical requirement and admits a straightforward proof
via `Leads_prod.of_left` / `.of_right`. Use cases requiring stricter
recovery (e.g. synchronized both-side recovery) can bypass this
composition and construct `FDIRBundle pk` directly.

## API granularity

Only binary `compose` is provided at this level. For variadic
composition over a homogeneous list, see the anonymous-payload wrapper
`SubSystemPayload.composeMany` in `VV/VariadicCompose.lean`, which
threads `compose` through `List.foldl`.
-/

namespace VerifiedMBSE.VV

open VerifiedMBSE.Core
open VerifiedMBSE.Behavior

-- ============================================================
-- §1  FDIRBundle.compose
-- ============================================================

/-- Parallel composition of two `FDIRBundle`s.

    Because the type signature is parameterized over
    `{α β} [ToKripke α S₁ D₁] [ToKripke β S₂ D₂] {x : α} {y : β}`,
    the same API supports nested compositions such as
    `FDIRBundle.compose f₁₂ f₃ pk₁₂₃ hne₁₂ hne₃`.

    The result is a unified `FDIRBundle pk` over the product Kripke
    structure `pk : ProductKripke x y`.

    Construction:
    - `safety`    — `Always_prod.of_and` combines both safety properties
      into a conjunction over the product.
    - `detection` — lift the left-side detection with
      `Eventually_prod.of_left` and wrap with `Or.inl`.
    - `recovery`  — use `Leads_prod.of_left` / `.of_right` on the side
      that faulted, then map through `Or.inl` / `Or.inr` into the
      composed `isRecovery`. -/
def FDIRBundle.compose
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    (f₁ : FDIRBundle x) (f₂ : FDIRBundle y)
    (pk : ProductKripke x y)
    (hne₁ : (ToKripke.toKripke x).NonEmpty)
    (hne₂ : (ToKripke.toKripke y).NonEmpty) :
    FDIRBundle pk where
  isFault    := fun p => f₁.isFault p.1 ∨ f₂.isFault p.2
  isRecovery := fun p => f₁.isRecovery p.1 ∨ f₂.isRecovery p.2
  isSafe     := fun q => f₁.isSafe q.1 ∧ f₂.isSafe q.2
  safety := Always_prod.of_and pk f₁.safety f₂.safety
  detection := by
    -- 左の detection を持ち上げて Or.inl
    have h := Eventually_prod.of_left (y := y) pk hne₂
                (P₁ := fun s _ => f₁.isFault s) f₁.detection
    obtain ⟨p, d, hp, hP⟩ := h
    exact ⟨p, d, hp, Or.inl hP⟩
  recovery := by
    -- 積で fault∨fault が成立する reachable state に対して、該当側の recovery を持ち上げる
    intro p d hr hfault
    cases hfault with
    | inl h₁ =>
        -- 左 fault: f₁.recovery を Leads_prod.of_left で積に持ち上げ、Or.inl
        have hLeads :
            Leads_prod pk
              (fun p' d' => (fun s _ => f₁.isFault s) p'.1 d'.1)
              (fun p' d' => (fun s _ => f₁.isRecovery s) p'.1 d'.1) :=
          Leads_prod.of_left (y := y) pk hne₂
            (P₁ := fun s _ => f₁.isFault s)
            (Q₁ := fun s _ => f₁.isRecovery s)
            f₁.recovery
        have hE := hLeads p d hr h₁
        obtain ⟨p', d', hp', hrec⟩ := hE
        exact ⟨p', d', hp', Or.inl hrec⟩
    | inr h₂ =>
        -- 右 fault: 対称
        have hLeads :
            Leads_prod pk
              (fun p' d' => (fun s _ => f₂.isFault s) p'.2 d'.2)
              (fun p' d' => (fun s _ => f₂.isRecovery s) p'.2 d'.2) :=
          Leads_prod.of_right (x := x) pk hne₁
            (P₂ := fun s _ => f₂.isFault s)
            (Q₂ := fun s _ => f₂.isRecovery s)
            f₂.recovery
        have hE := hLeads p d hr h₂
        obtain ⟨p', d', hp', hrec⟩ := hE
        exact ⟨p', d', hp', Or.inr hrec⟩

-- ============================================================
-- §2  BehavioralSpec.compose
-- ============================================================

/-- Parallel composition of two `BehavioralSpec`s.

    The result is a `BehavioralSpec pk` over the product Kripke
    structure. Its `nonEmpty` field is built by `ProductKripke.nonEmpty`
    from the component `NonEmpty` witnesses. -/
def BehavioralSpec.compose
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    (_b₁ : BehavioralSpec x) (_b₂ : BehavioralSpec y)
    (pk : ProductKripke x y)
    (hne₁ : (ToKripke.toKripke x).NonEmpty)
    (hne₂ : (ToKripke.toKripke y).NonEmpty) :
    BehavioralSpec pk where
  nonEmpty := ProductKripke.nonEmpty pk hne₁ hne₂

-- ============================================================
-- §3  SubSystemSpec.compose
-- ============================================================

/-- Parallel composition of two `SubSystemSpec`s.

    Each field of the result is the component-level composition of the
    corresponding field of the operands. The result is a unified
    `SubSystemSpec pk` over the product Kripke structure `pk`.

    - `structural` ← `StructuralSpec.compose` (with `bridge` connectors)
    - `behavioral` ← `BehavioralSpec.compose`
    - `fdir`       ← `FDIRBundle.compose`

    For N-ary composition, nest `compose` calls directly (see the module
    docstring). At the third step and beyond, the `NonEmpty` witness is
    available as `s₁₂.behavioral.nonEmpty`, since the intermediate
    `ProductKripke` carries its own `ToKripke` instance. -/
def SubSystemSpec.compose
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    (spec₁ : SubSystemSpec x) (spec₂ : SubSystemSpec y)
    (pk : ProductKripke x y)
    (hne₁ : (ToKripke.toKripke x).NonEmpty)
    (hne₂ : (ToKripke.toKripke y).NonEmpty)
    (bridge : List Connector)
    (hbridge : ∀ c ∈ bridge,
        c.source.part ∈ spec₁.structural.system.parts ++ spec₂.structural.system.parts ∧
        c.target.part ∈ spec₁.structural.system.parts ++ spec₂.structural.system.parts) :
    SubSystemSpec pk where
  structural :=
    StructuralSpec.compose spec₁.structural spec₂.structural bridge hbridge
  behavioral :=
    BehavioralSpec.compose spec₁.behavioral spec₂.behavioral pk hne₁ hne₂
  fdir :=
    FDIRBundle.compose spec₁.fdir spec₂.fdir pk hne₁ hne₂

end VerifiedMBSE.VV
