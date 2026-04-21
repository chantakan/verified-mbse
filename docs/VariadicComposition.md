# Variadic Composition Guide (B-8d)

## Overview

The **variadic composition API** introduced in B-8d provides a mechanism for
composing N `SubSystemSpec` values from a `List` in one shot. It simplifies
the 2-ary `SubSystemSpec.compose` nesting pattern used through B-8c by
putting `List.foldl` in front of it.

This guide covers:

- Why a variadic API is needed
- The design of the core `SubSystemPayload` type
- How to use the 2-ary `compose` and N-ary `composeMany`
- What is intentionally left out of scope (associativity, bridged variants)

---

## 1. Motivation

Up through B-8c, composing N subsystems required repeatedly calling the
2-ary `SubSystemSpec.compose`:

```lean
-- 2 subsystems
let s₁₂ : SubSystemSpec pk₁₂ :=
  SubSystemSpec.compose s₁ s₂ pk₁₂ hne₁ hne₂ [] (by intros; contradiction)

-- 3 subsystems
let pk₁₂₃ : ProductKripke pk₁₂ sm₃ := ⟨⟩
let s₁₂₃ : SubSystemSpec pk₁₂₃ :=
  SubSystemSpec.compose s₁₂ s₃ pk₁₂₃
    s₁₂.behavioral.nonEmpty hne₃ [] (by intros; contradiction)

-- 4, 5, ...
```

The following boilerplate repeats with each additional subsystem:

1. Explicit construction of the `ProductKripke` marker (`⟨⟩`)
2. Passing the `NonEmpty` argument at each stage
3. The empty `bridge = []` along with the trivial `hbridge` proof
4. Hand-writing the type hierarchy `ProductKripke (ProductKripke ...) ...`

Worse, the intermediate spec type `SubSystemSpec (ProductKripke ...)` is
used as the first argument of the next stage. Because a regular `List`
cannot hold values of different types, `foldl` / `foldr` over a list of
specs is not directly possible.

B-8d resolves this with the `SubSystemPayload` type.

---

## 2. Design of `SubSystemPayload`

### 2.1 Definition

```lean
structure SubSystemPayload : Type 1 where
  α            : Type
  S            : Type
  D            : Type
  toKripkeInst : ToKripke α S D
  x            : α
  spec         : @SubSystemSpec α S D toKripkeInst x
```

**Role**: anonymously packages "one composable payload." Bundling
`α`, `S`, `D`, the `ToKripke` instance, `x`, and `spec` into a single
structure lets `List SubSystemPayload` hold heterogeneous
`SubSystemSpec x` values uniformly.

### 2.2 On Universes

Because the `α : Type` field makes the type level-polymorphic,
`SubSystemPayload : Type 1`. Since `List` is universe-polymorphic,
`List SubSystemPayload : Type 1` works without issue, and end users do
not need to worry about universes.

### 2.3 Automatic `ToKripke` Supply

`SubSystemPayload.toKripkeInst` is a regular field, not a type-class
instance, so Lean's instance resolution does not find it when
elaborating `p.spec.name` or similar projections. To fix this,
B-8d registers a global instance that supplies
`ToKripke p.α p.S p.D` from `p.toKripkeInst`:

```lean
instance instToKripkeOfPayload (p : SubSystemPayload) :
    ToKripke p.α p.S p.D :=
  p.toKripkeInst
```

With this in place, `p.spec.name`, `p.spec.structural`,
`p.spec.safetyRecord`, etc. all elaborate directly.

### 2.4 Smart Constructor

Wrap an existing `SubSystemSpec x` into a payload:

```lean
abbrev SubSystemPayload.ofSpec
    {α : Type} {S D : Type} [inst : ToKripke α S D] {x : α}
    (spec : SubSystemSpec x) : SubSystemPayload := ...
```

`ofSpec` is an `abbrev` so that field projections like
`(SubSystemPayload.ofSpec spec).α` reduce automatically and `rfl`-based
sanity tests go through.

**Usage**:

```lean
-- Wrap a StateMachine-based spec
def epsPayload : SubSystemPayload := SubSystemPayload.ofSpec epsSpec

-- Works equally well for an already-composed ProductKripke spec
def combined : SubSystemPayload := SubSystemPayload.ofSpec epsMiniSpec
```

---

## 3. Two-way Composition: `compose`

```lean
def SubSystemPayload.compose (p₁ p₂ : SubSystemPayload) : SubSystemPayload
```

**Behavior**:
- Constructs `ProductKripke p₁.x p₂.x := ⟨⟩` internally
- Supplies `NonEmpty` automatically from each `spec.behavioral.nonEmpty`
- Fixes `bridge = []` (inter-subsystem connectors are out of scope in v1)

**Resulting payload**:
- `α = ProductKripke p₁.x p₂.x`
- `S = p₁.S × p₂.S`
- `D = p₁.D × p₂.D`
- `toKripkeInst = instToKripkeProductKripke`
- `x = ⟨⟩`
- `spec = SubSystemSpec.compose p₁.spec p₂.spec ...` result

**Usage**:

```lean
def epsMini : SubSystemPayload :=
  epsPayload.compose miniPayload

-- Name follows the StructuralSpec.compose naming convention.
example : epsMini.spec.name = "EPS+Mini" := rfl

-- Automatic VVRecord generation keeps working after composition.
def r1 : VVRecord := epsMini.spec.safetyRecord
```

---

## 4. N-way Composition: `composeMany`

```lean
def SubSystemPayload.composeMany :
    List SubSystemPayload → Option SubSystemPayload
  | []      => none
  | p :: ps => some (ps.foldl SubSystemPayload.compose p)
```

**Behavior**:
- `[]` → `none` (nothing to compose)
- `[p]` → `some p` (single-element lists are returned as-is)
- `p₀ :: p₁ :: ... :: pₙ` → `some ((((p₀ ∘ p₁) ∘ p₂) ∘ ...) ∘ pₙ)`

**Usage**:

```lean
-- 4-way composition
def fourSats : Option SubSystemPayload :=
  SubSystemPayload.composeMany
    [ SubSystemPayload.ofSpec epsSpec
    , SubSystemPayload.ofSpec agentSpec₁
    , SubSystemPayload.ofSpec agentSpec₂
    , SubSystemPayload.ofSpec agentSpec₃ ]

example : fourSats.isSome = true := rfl
```

The API uses left-associative `foldl`, which:
- Grows the state type incrementally as `(((S₀ × S₁) × S₂) × S₃)`
- Matches the associativity direction used by `(EPS × Mini) × Mini2` in
  the existing 3-way composition examples
- Keeps projection patterns (`.1.1.1`, `.1.1.2`, `.1.2`, `.2`)
  consistent across examples

---

## 5. Equivalence of Chained and List Notation

Direct chained composition and `composeMany` are **definitionally equal**
and can be related via `rfl`:

```lean
def fourChain : SubSystemPayload :=
  epsPayload.compose miniPayload
    |>.compose mini2Payload
    |>.compose miniPayload

example :
    SubSystemPayload.composeMany
      [ epsPayload, miniPayload, mini2Payload, miniPayload ] =
    some fourChain := rfl
```

Either notation is fine; choose based on context:
- **Chained**: when intermediate results should be named via `def`
- **List**: when many specs should be shown in parallel

---

## 6. Helper Lemmas

### `compose_parts_length`

```lean
theorem SubSystemPayload.compose_parts_length (p₁ p₂ : SubSystemPayload) :
    (p₁.compose p₂).spec.structural.parts.length =
      p₁.spec.structural.system.parts.length +
        p₂.spec.structural.system.parts.length
```

A lift of `StructuralSpec.compose_parts_length` to the payload level.
The right-hand side uses `.system.parts.length` to match the existing
lemma. Since `StructuralSpec.mk'` sets `system_eq_parts := rfl`, the
concrete instances in the examples satisfy
`.structural.parts.length = .structural.system.parts.length` by
`rfl`, so `.parts.length`-form equalities also go through for specific
payloads without needing the lemma.

### `compose_name`

```lean
theorem SubSystemPayload.compose_name (p₁ p₂ : SubSystemPayload) :
    (p₁.compose p₂).spec.name = s!"{p₁.spec.name}+{p₂.spec.name}"
```

### Boundary lemmas

```lean
theorem SubSystemPayload.composeMany_singleton (p : SubSystemPayload) :
    SubSystemPayload.composeMany [p] = some p

theorem SubSystemPayload.composeMany_nil :
    SubSystemPayload.composeMany [] = none
```

---

## 7. Out of Scope

### 7.1 Associativity

`(p₁.compose p₂).compose p₃` and `p₁.compose (p₂.compose p₃)` **cannot**
be equal up to Lean's propositional `=`, because their state types are

- left: `((S₁ × S₂) × S₃)`
- right: `(S₁ × (S₂ × S₃))`

which are not judgmentally equal. Lean's `=` requires type equality,
so these two terms cannot be compared directly.

**Semantic equivalence** (an isomorphism on the state projections) is
provable via `Equivalence.ComponentEquiv`, but that is out of scope for
this API. The same reasoning applies to any `foldl` vs `foldr` equality.

**Practical consequence**: `composeMany` always produces a
**left-associated** composition (`foldl`). Callers can rely on that
associativity direction.

### 7.2 Bridges in the Variadic API

The 2-ary `SubSystemSpec.compose` takes `bridge : List Connector` as its
6th argument. B-8d's `compose` and `composeMany` both fix `bridge = []`.
For 2-ary composition with bridges, B-8e adds the variant

```lean
def SubSystemPayload.composeWithBridge
    (p₁ p₂ : SubSystemPayload)
    (bridge : List Connector)
    (hbridge : ∀ c ∈ bridge,
        c.source.part ∈ p₁.spec.structural.system.parts
                        ++ p₂.spec.structural.system.parts ∧
        c.target.part ∈ p₁.spec.structural.system.parts
                        ++ p₂.spec.structural.system.parts) :
    SubSystemPayload
```

and a definitional-equality lemma

```lean
theorem SubSystemPayload.compose_eq_composeWithBridge_nil (p₁ p₂) :
    p₁.compose p₂ =
      p₁.composeWithBridge p₂ [] (by intros; contradiction) := rfl
```

so the bridge-less case falls out of the bridged API by definition.

**Typical usage (two-phase approach)**:

```lean
-- 1. Use composeWithBridge where inter-subsystem connectors are needed.
let s₀₁ := p₀.composeWithBridge p₁ bridge₀₁ h₀₁

-- 2. Fold the rest of the (bridgeless) payloads with composeMany.
let combined : Option SubSystemPayload :=
  SubSystemPayload.composeMany
    [ SubSystemPayload.ofSpec s₀₁.spec, p₂, p₃, p₄ ]
```

**No variadic list-form `composeManyWithBridges` is provided**, and this is
intentional. The natural signature would be

```lean
-- NOT PROVIDED (permanently out of scope)
def composeManyWithBridges :
    List (SubSystemPayload × List Connector × SomeProof) → Option SubSystemPayload
```

but `SomeProof` (the `hbridge` obligation) depends on the
**accumulated** `parts` of every preceding stage. Because Lean cannot
express this accumulated state in a flat list element, the proof must be
built at call time, stage by stage. In practice this collapses back into
either (a) chained `composeWithBridge` calls, or (b) a closure/builder
pattern that trades elegance for marginal convenience. The `composeWithBridge`
+ `composeMany` two-phase pattern covers realistic use cases (most stages
have no inter-subsystem bridge) without this complexity.

---

## 8. Summary

B-8d enables variadic composition of heterogeneous `SubSystemSpec x`
values by **creating the illusion of a single type through
`SubSystemPayload`**. B-8e completes the 2-ary API by adding bridge
support at the payload level.

| Aspect | B-8c | B-8d | B-8e |
|--------|------|------|------|
| 2-way composition | `SubSystemSpec.compose s₁ s₂ pk hne₁ hne₂ [] (by ...)` | `p₁.compose p₂` | `p₁.composeWithBridge p₂ bridge h` |
| N-way composition | Nested 2-ary calls (by hand) | `composeMany [p₁, p₂, ..., pₙ]` | (unchanged from B-8d) |
| Heterogeneous specs in one list | Impossible | `List SubSystemPayload` | (unchanged) |
| `NonEmpty` argument | Explicit | Automatic (`spec.behavioral.nonEmpty`) | (unchanged) |
| Bridge support (2-ary) | `List Connector` | Fixed `[]` | `List Connector` |
| Bridge support (variadic list) | — | Fixed `[]` | Permanently out of scope |

For realistic N-agent systems like SafeSwarm, the recommended pattern
is a **two-phase approach**: call `composeWithBridge` at the stages that
need inter-subsystem connectors, wrap the result with `ofSpec`, and fold
the remaining bridgeless payloads with `composeMany`.

---

## Related

- B-6: `FDIRBundle.compose` (2-way FDIR composition)
- B-7: Kripke generalization of `SubSystemSpec` + 2-way composition
- B-8a–c: Heterogeneous `ProductKripke` + 3-way nested composition
- **B-8d**: this document — variadic composition API (`composeMany`)
- **B-8e**: this document — bridged 2-ary payload composition (`composeWithBridge`)
- (no B-8f planned) — `composeManyWithBridges` intentionally out of scope

Implementation files for each milestone:
- `VerifiedMBSE/Behavior/ProductKripke.lean` — B-8a–c
- `VerifiedMBSE/VV/ProductFDIR.lean` — B-6/B-7/B-8c merge point
- `VerifiedMBSE/VV/VariadicCompose.lean` — **B-8d + B-8e (subject of this document)**
- `Examples/Spacecraft/Integration.lean` — B-8c 3-way nested sanity test
- `Examples/Spacecraft/VariadicComposeTests.lean` — B-8d + B-8e sanity tests