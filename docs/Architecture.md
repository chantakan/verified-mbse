# Architecture Guide

## Overview

verified-mbse encodes SysML v2 / KerML concepts as Lean 4 types. The core insight:

```
Specification compliance  ⟺  Type inhabitation
V&V completeness          ⟺  Theorem compilation
Design error              ⟺  Type error
```

This document explains the type-theoretic foundations, key design decisions, and proof patterns used throughout the library.

## Layer Architecture

```
                 ┌──────────────────────────────────────────┐
                 │  Examples/Spacecraft/                     │
                 │  EPS, AOCS, TCS, TTC, Satellite          │
                 └──────────────┬───────────────────────────┘
                                │ uses
  ┌─────────────────────────────┼───────────────────────────────┐
  │                    VerifiedMBSE (library)                    │
  │                                                             │
  │  Output/  ←──  Matrix/  ←──  VV/  ←──  Behavior/  ←──  Core/
  │                                                             │
  │  SysML v2       VColumn     SubSystem   StateMachine  KerMLType
  │  Markdown       VMatrix     Spec        Temporal      PartDef
  │  Terminal       Query       VVBundle    FDIR          Connector
  │                             Evidence                  System
  │                                                             │
  │  Equivalence/ (independent, imports Core/ only)             │
  └─────────────────────────────────────────────────────────────┘
```

**Import rule:** Core ← Behavior ← VV ← Matrix ← Output. No reverse imports.

## Core Layer: KerML Semantics

### The Specialization Preorder

KerML's specialization relation (`A specializes B` = every instance of A is an instance of B) maps to a preorder on `KerMLType`:

```lean
def specializes (a b : KerMLType) : Prop :=
  ∃ s : Specialization, s.specific = a ∧ s.general = b

instance : Preorder KerMLType where
  le       := specializes
  le_refl  := specializes_refl
  le_trans := specializes_trans
```

This enables `≤` notation and Mathlib's order infrastructure.

### Model-Theoretic Semantics

Rather than computing `extent` from syntax (which requires `sorry`), we parameterize over an `Interpretation`:

```lean
def Interpretation := KerMLType → Type
def semanticSpecializes (I : Interpretation) (a b : KerMLType) : Prop :=
  ∃ f : I a → I b, Function.Injective f
```

**Soundness theorem:** Syntactic specialization implies semantic specialization in any model:

```lean
theorem soundness (I : Interpretation) (hI : InterpretationRespects I)
    {a b : KerMLType} (hab : specializes a b) :
    semanticSpecializes I a b
```

### Port Compatibility via Conjugation

SysML v2 port compatibility (output connects to conjugated input) is modeled as an existential:

```lean
def compatible (a b : KerMLType) : Prop :=
  ∃ c : Conjugation, c.original = a ∧ c.conjugated = b
```

A `Connector` carries this proof — you cannot construct a connector between incompatible ports.

### ConnectorSemantic: Categorical Structure

`ConnectorSemantic` forms a category:
- Objects: port flow types
- Morphisms: `I source.flowType → I target.flowType`
- Composition: `compose` (associative)
- Identity: `id_of_eq` (left and right unit laws proven)

This justifies sequential data flow through connector chains.

## Behavior Layer: Invariant Preservation by Construction

### The Key Design Decision

`Transition.preserves` embeds invariant preservation **in the type**:

```lean
structure Transition (S D : Type) (inv : S → D → Prop) where
  source    : S
  target    : S
  guard     : D → Prop
  effect    : D → D
  preserves : ∀ d, guard d → inv source d → inv target (effect d)
```

A transition that violates the invariant is **unconstructible** — it's a type error, not a runtime error.

### Safety Theorem

The central theorem follows by induction on `Reachable`:

```lean
theorem Reachable.inv_holds {sm : StateMachine S D inv} {s d}
    (h : Reachable sm s d) : inv s d
```

This is `□(inv)` in LTL: the invariant holds in every reachable state.

### LTL Embedding

Temporal operators are propositions over `Reachable`:

| LTL | Lean 4 | Type |
|-----|--------|------|
| □ P | `Always sm P` | `∀ s d, Reachable sm s d → P s d` |
| ◇ P | `Eventually sm P` | `∃ s d, Reachable sm s d ∧ P s d` |
| P ⇒ ◇ Q | `Leads sm P Q` | `Always sm (P → Eventually sm Q)` |

### FDIR as a Type

```lean
structure FDIRSpec (sm) (isFault isNominal isSafe) : Prop where
  safety    : Always sm (fun _ d => isSafe d)        -- □(safe)
  detection : Eventually sm (fun s _ => isFault s)    -- ◇(fault)
  recovery  : Leads sm (fun s _ => isFault s)         -- fault ⇒ ◇ recovery
              (fun s _ => isNominal s)
```

Constructing a `FDIRSpec` value = mechanically verifying all three FDIR requirements.

## VV Layer: Evidence Hierarchy

### ValidationEvidence: Three Levels of Confidence

```
confidence (Float)     ←  Weakest. Early design assumptions.
    ↓ promote
contract (Prop → P)    ←  Middle. Test/simulation-backed.
    ↓ promote
trusted (P)            ←  Strongest. Accepted as axiomatic.
```

`ValidationTrace` records the promotion history for audit trails.

### SubSystemSpec: One Type to Rule Them All

```lean
structure SubSystemSpec (S D : Type) (inv : S → D → Prop) where
  structural : StructuralSpec          -- parts + connectors + WellFormed
  behavioral : BehavioralSpec S D inv  -- state machine + WellFormed
  fdir       : FDIRBundle behavioral.sm -- safety + detection + recovery
```

From one `SubSystemSpec`, the framework auto-derives:
- `subsystemRecord` (subsystem-level VVRecord)
- `safetyRecord` (R1 VVRecord)
- `recoveryRecord` (R3 VVRecord)
- `SubSystemVVBundle.allRecords` (all VVRecords for this subsystem)

## Proof Patterns

| Pattern | Tactic | When to use |
|---------|--------|-------------|
| `by simp [defName]` | Definition unfolding | WellFormed, PortRef.mem |
| `by cases x <;> simp [...] <;> omega` | Finite enumeration | Power budgets, mode enumeration |
| `by native_decide` | Decidable Bool propositions | allLayersCovered, totalRecords |
| `fun _ _ h => h.inv_holds` | Direct invariant application | Always proofs (□ inv) |
| `Reachable.step t hr ... rfl trivial` | Reachability construction | Eventually, Leads |
| `by constructor; ... <;> native_decide` | VMatrix.Complete | Completeness proofs |

## Equivalence Layer: HoTT Connections

This advanced module draws parallels between HoTT and MBSE:

| HoTT Concept | MBSE Analogue | Lean 4 Type |
|---|---|---|
| A ≃ B | Interface compatibility | `ComponentEquiv` |
| Univalence | Substitutability | `DesignEquiv` |
| Transport | Design migration | `transport_wellFormed` |
| Path space | Requirement refinement chain | `RequirementRefinement` |
| n-truncation | Abstraction level | `AbstractionLevel` |

`ComponentEquiv` is an equivalence relation (refl, symm, trans) that captures when two components can be swapped without breaking any system property.

## Mode-Dependent Invariants: The TCS Example

EPS and AOCS use mode-independent invariants (`fun _ v => v ≤ 1000`). TCS demonstrates the power of dependent types with **mode-dependent** invariants:

```lean
def tcsInvariant : TCSMode → Nat → Prop
  | .nominal,  t => 150 ≤ t ∧ t ≤ 450   -- 20–45°C operating range
  | .coldCase, t => t ≤ 250              -- heater active
  | .hotCase,  t => 350 ≤ t ∧ t ≤ 650   -- radiator active
  | .survival, t => t ≤ 1000            -- survival range
```

The safety theorem `Reachable.inv_holds` now returns a **different proposition depending on which mode was reached** — this is genuine dependent typing, not just parameterization.
