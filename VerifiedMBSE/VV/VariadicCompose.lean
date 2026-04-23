import VerifiedMBSE.VV.ProductFDIR

/-!
# Variadic Composition API

Compose N `SubSystemSpec`s held in a `List` with a single call. This module
wraps the binary `SubSystemSpec.compose` with `List.foldl` so that N-ary
composition can be written concisely.

## Motivation

Nested binary `SubSystemSpec.compose` calls are verbose. Each step requires
constructing a `ProductKripke` marker, supplying `NonEmpty` proofs for both
operands, and providing an empty-`bridge` `hbridge` proof:

```lean
let s₁₂   := SubSystemSpec.compose s₁ s₂ pk₁₂ hne₁ hne₂ [] (by ...)
let s₁₂₃  := SubSystemSpec.compose s₁₂ s₃ pk₁₂₃ s₁₂.behavioral.nonEmpty hne₃ [] (by ...)
let s₁₂₃₄ := SubSystemSpec.compose s₁₂₃ s₄ pk... s₁₂₃.behavioral.nonEmpty hne₄ [] (by ...)
```

More fundamentally, each step produces an intermediate
`SubSystemSpec (ProductKripke ...)` whose type differs from the next
operand, so heterogeneous values cannot be held uniformly in a `List`.

This module resolves both issues with:

- `SubSystemPayload`: an anonymous package bundling
  `α / S / D / ToKripke instance / x / spec` into a single type, so that
  heterogeneous `SubSystemSpec` values are uniformly held as
  `List SubSystemPayload`.
- `SubSystemPayload.compose`: binary composition of two payloads.
  `NonEmpty` is supplied automatically from each `spec.behavioral.nonEmpty`,
  and `bridge` is fixed to `[]`.
- `SubSystemPayload.composeWithBridge`: binary composition accepting
  inter-subsystem connectors (e.g. communication links, shared power
  buses) as `bridge : List Connector` with an `hbridge` proof of
  part-reference integrity.
- `SubSystemPayload.composeMany`: left-associative `List.foldl` over a
  `List SubSystemPayload`. The empty list yields `none`, a singleton
  yields `some p`, and `n ≥ 2` elements yield
  `some ((((p₀ ∘ p₁) ∘ p₂) ∘ ...) ∘ pₙ)`.
- Equivalence lemma `compose_eq_composeWithBridge_nil`: the bridge-free
  `compose` is definitionally equal to `composeWithBridge [] _`.

**A bridge-enabled variadic API is intentionally not provided.** The
per-step `hbridge` proposition depends on the cumulative parts produced
by previous folding steps, so a precomputed data structure such as
`List (SubSystemPayload × List Connector × Proof)` cannot express it.
In practice, call `composeWithBridge` at the steps that need a bridge
and bundle the remaining steps with `composeMany`.

## Design decisions

### Left-associative fold

`List.foldl` matches the associativity of the existing 3-subsystem
example `(EPS × Mini) × Mini2` in `Examples/Spacecraft/Integration.lean`.
The intermediate state type grows as `((S₁ × S₂) × S₃) × S₄`, so
projections such as `.1.1.1` align with existing patterns.

### `bridge = []` in the variadic API

Binary `SubSystemSpec.compose` accepts a `bridge : List Connector`, but
expressing "at which step a bridge is inserted" in a variadic API is
awkward. `composeMany` fixes `bridge = []` at every step; call sites
that need inter-subsystem connectors invoke `composeWithBridge`
explicitly at the relevant steps.

### Associativity is unproven

`(p₁ ∘ p₂) ∘ p₃` and `p₁ ∘ (p₂ ∘ p₃)` have distinct state types
(`((S₁ × S₂) × S₃)` vs `(S₁ × (S₂ × S₃))`), so strict equality does
not hold. Semantic equivalence (state projections form a bijection)
must be established via `Equivalence.ComponentEquiv` and is out of
scope for this module. Equivalence of `foldl` and `foldr` is deferred
for the same reason.

### `SubSystemPayload : Type 1`

The `α : Type` field forces a universe bump. Because `List` is universe
polymorphic, `List SubSystemPayload : Type 1` composes without friction
and call sites need no explicit type annotations.

### `instToKripkeOfPayload` as a global instance

The `toKripkeInst` field is an ordinary field, which is not eligible for
instance resolution. Without the global instance, projections such as
`p.spec.name` fail to elaborate because `SubSystemSpec.name` requires
`[ToKripke α S D]`. The global instance exposes `p.toKripkeInst` as an
inferable `ToKripke p.α p.S p.D`, making every `p.spec.*` projection
resolve correctly.

### `SubSystemPayload.ofSpec` as an `abbrev`

Defining `ofSpec` as `abbrev` lets field projections of the form
`(SubSystemPayload.ofSpec spec).α` reduce automatically, so sanity
tests close by `rfl`. The composition operators carry proof-relevant
content and remain plain `def`.

-/

namespace VerifiedMBSE.VV

open VerifiedMBSE.Core
open VerifiedMBSE.Behavior

-- ============================================================
-- §1  SubSystemPayload
-- ============================================================

/-- Anonymous composable payload for a single subsystem.

    Bundles `α / S / D / ToKripke instance / x / spec` into a single
    structure so that heterogeneous `SubSystemSpec x` values can be held
    uniformly in a `List`.

    ### Fields

    - `α`: the behavioral model type (e.g. `StateMachine EPSMode Nat epsGlobalInv`
      or `ProductKripke sm₁ sm₂`)
    - `S`, `D`: state and data types
    - `toKripkeInst`: instance interpreting `α` as a Kripke structure
    - `x`: the concrete behavioral model value
    - `spec`: the `SubSystemSpec` over `x`

    ### Universe

    The `α : Type` field forces `SubSystemPayload : Type 1`. Since `List`
    is universe polymorphic, `List SubSystemPayload : Type 1` works
    without friction, and call sites need no explicit type annotations. -/
structure SubSystemPayload : Type 1 where
  /-- The behavioral model type. -/
  α : Type
  /-- State type. -/
  S : Type
  /-- Data type. -/
  D : Type
  /-- Instance interpreting `α` as a Kripke structure. -/
  toKripkeInst : ToKripke α S D
  /-- Concrete behavioral model value (e.g. `StateMachine`, `ProductKripke`). -/
  x : α
  /-- Subsystem specification over `x`. -/
  spec : @SubSystemSpec α S D toKripkeInst x

/-- Exposes the `toKripkeInst` field of a `SubSystemPayload` as a global
    instance.

    Without this instance, projections such as `p.spec.name` or
    `p.spec.structural` fail to elaborate because `SubSystemSpec.name`
    and `SubSystemSpec.structural` require `[ToKripke α S D]`, and
    ordinary structure fields are not visible to instance resolution.

    With this global instance, the following all resolve:
    - `p.spec.name`, `p.spec.structural`, `p.spec.behavioral`, `p.spec.fdir`
    - `p.spec.safetyRecord`, `p.spec.subsystemRecord`, `p.spec.recoveryRecord`
    - Kripke-layer API such as `(ToKripke.toKripke p.x).NonEmpty` -/
instance instToKripkeOfPayload (p : SubSystemPayload) :
    ToKripke p.α p.S p.D :=
  p.toKripkeInst

/-- Convenience constructor building a `SubSystemPayload` from a
    `SubSystemSpec x`.

    Type arguments and the `ToKripke` instance are inferred via
    `[ToKripke α S D]`, so call sites can write
    `SubSystemPayload.ofSpec epsSpec`.

    Defined as `abbrev` so that field projections such as
    `(SubSystemPayload.ofSpec spec).α` reduce automatically, letting
    sanity tests close by `rfl`. -/
abbrev SubSystemPayload.ofSpec
    {α : Type} {S D : Type} [inst : ToKripke α S D] {x : α}
    (spec : SubSystemSpec x) : SubSystemPayload :=
  { α := α, S := S, D := D
    toKripkeInst := inst
    x := x, spec := spec }

-- ============================================================
-- §2  2 機合成
-- ============================================================

/-- Compose two payloads in parallel (bridge-free).

    - Builds the `ProductKripke p₁.x p₂.x` marker internally.
    - Supplies `NonEmpty` proofs from each `spec.behavioral.nonEmpty`
      automatically.
    - Fixes `bridge` to `[]`; for inter-subsystem connectors, use
      `composeWithBridge`.

    The resulting payload satisfies:
    - `α = ProductKripke p₁.x p₂.x`
    - `S = p₁.S × p₂.S`
    - `D = p₁.D × p₂.D`
    - `toKripkeInst = instToKripkeProductKripke`
    - `x = ⟨⟩` (empty marker)
    - `spec = SubSystemSpec.compose p₁.spec p₂.spec ...`

    Uses `letI` to expose `p₁.toKripkeInst` and `p₂.toKripkeInst` as
    local instances so that `ProductKripke p₁.x p₂.x` type-checks and
    its instance resolution succeeds. -/
def SubSystemPayload.compose (p₁ p₂ : SubSystemPayload) : SubSystemPayload :=
  letI := p₁.toKripkeInst
  letI := p₂.toKripkeInst
  let pk : ProductKripke p₁.x p₂.x := ⟨⟩
  { α := ProductKripke p₁.x p₂.x
    S := p₁.S × p₂.S
    D := p₁.D × p₂.D
    toKripkeInst := instToKripkeProductKripke
    x := pk
    spec :=
      SubSystemSpec.compose p₁.spec p₂.spec pk
        p₁.spec.behavioral.nonEmpty
        p₂.spec.behavioral.nonEmpty
        [] (by intros; contradiction) }

-- ============================================================
-- §2.5  Bridged 2-ary composition
-- ============================================================

/-- Compose two payloads in parallel with inter-subsystem bridge connectors.

    Accepts inter-subsystem connectors (e.g. communication links, shared
    power buses) as `bridge : List Connector`, extending the bridge-free
    `compose`.

    ### `hbridge` constraint

    Each connector in `bridge` must have its `source.part` and
    `target.part` located in the concatenated parts of `p₁` and `p₂`.
    This is the payload-level lift of the `hbridge` obligation of the
    binary `SubSystemSpec.compose`:

    ```
    ∀ c ∈ bridge,
      c.source.part ∈ p₁.spec.structural.system.parts
                      ++ p₂.spec.structural.system.parts ∧
      c.target.part ∈ p₁.spec.structural.system.parts
                      ++ p₂.spec.structural.system.parts
    ```

    Call sites supply this proof per invocation.

    ### Implementation

    Uses `letI` to expose local `ToKripke` instances, builds the
    `ProductKripke` marker, and invokes `SubSystemSpec.compose` with
    the given `bridge` / `hbridge`. Passing `bridge = []` and
    `hbridge = by intros; contradiction` produces the same result as
    `compose p₁ p₂`; see `compose_eq_composeWithBridge_nil`.

    ### Relation to the variadic API

    A bridge-enabled variadic form is **intentionally not provided**.
    The per-step `hbridge` proposition depends on the cumulative parts
    produced by previous folding steps, so a precomputed data structure
    such as `List (SubSystemPayload × List Connector × Proof)` cannot
    express it. In practice, call `composeWithBridge` at the steps that
    need a bridge and bundle the remaining steps with `composeMany`. -/
def SubSystemPayload.composeWithBridge
    (p₁ p₂ : SubSystemPayload)
    (bridge : List Connector)
    (hbridge : ∀ c ∈ bridge,
        c.source.part ∈ p₁.spec.structural.system.parts
                        ++ p₂.spec.structural.system.parts ∧
        c.target.part ∈ p₁.spec.structural.system.parts
                        ++ p₂.spec.structural.system.parts) :
    SubSystemPayload :=
  letI := p₁.toKripkeInst
  letI := p₂.toKripkeInst
  let pk : ProductKripke p₁.x p₂.x := ⟨⟩
  { α := ProductKripke p₁.x p₂.x
    S := p₁.S × p₂.S
    D := p₁.D × p₂.D
    toKripkeInst := instToKripkeProductKripke
    x := pk
    spec :=
      SubSystemSpec.compose p₁.spec p₂.spec pk
        p₁.spec.behavioral.nonEmpty
        p₂.spec.behavioral.nonEmpty
        bridge hbridge }

/-- `compose p₁ p₂` and `composeWithBridge p₁ p₂ [] _` are definitionally
    equal.

    Specializing `composeWithBridge` to an empty `bridge` recovers the
    bridge-free `compose`. The equivalence between the "no bridge" and
    "empty bridge" paths is therefore visible at the type level. -/
theorem SubSystemPayload.compose_eq_composeWithBridge_nil
    (p₁ p₂ : SubSystemPayload) :
    p₁.compose p₂ =
      p₁.composeWithBridge p₂ [] (by intros; contradiction) := rfl

-- ============================================================
-- §3  可変長合成
-- ============================================================

/-- Left-associative variadic composition of N payloads.

    - `[]` → `none` (nothing to compose)
    - `[p]` → `some p` (a single payload passes through)
    - `p₀ :: p₁ :: ... :: pₙ` → `some ((((p₀ ∘ p₁) ∘ p₂) ∘ ...) ∘ pₙ)`

    Implemented via `List.foldl`. The left-associative result matches
    the 3-subsystem example `(EPS × Mini) × Mini2`, so the state type
    grows incrementally as `(((S₀ × S₁) × S₂) × ...) × Sₙ`. -/
def SubSystemPayload.composeMany :
    List SubSystemPayload → Option SubSystemPayload
  | []      => none
  | p :: ps => some (ps.foldl SubSystemPayload.compose p)

-- ============================================================
-- §4  補助補題
-- ============================================================

/-- The total part count of a composed payload equals the sum of the
    `.system.parts` counts of the two operands.

    Payload-level lift of `StructuralSpec.compose_parts_length`. Since
    `bridge = []` here, the part count is unaffected.

    The right-hand side uses `.system.parts.length` (rather than
    `.parts.length`) to stay consistent with
    `StructuralSpec.compose_parts_length`. For `StructuralSpec` values
    built by the smart constructor, `.parts = .system.parts` holds
    definitionally, so concrete instances satisfy
    `.structural.parts.length = .structural.system.parts.length`. -/
theorem SubSystemPayload.compose_parts_length
    (p₁ p₂ : SubSystemPayload) :
    (p₁.compose p₂).spec.structural.parts.length =
      p₁.spec.structural.system.parts.length +
        p₂.spec.structural.system.parts.length := by
  simp [SubSystemPayload.compose, SubSystemSpec.compose,
        StructuralSpec.compose, List.length_append]

/-- The composed name takes the form `"{p₁.name}+{p₂.name}"`.

    Payload-level lift of the naming convention used by
    `StructuralSpec.compose` (`s!"{s1.name}+{s2.name}"`). -/
theorem SubSystemPayload.compose_name
    (p₁ p₂ : SubSystemPayload) :
    (p₁.compose p₂).spec.name =
      s!"{p₁.spec.name}+{p₂.spec.name}" := rfl

/-- Composing a singleton list yields the single payload unchanged. -/
theorem SubSystemPayload.composeMany_singleton (p : SubSystemPayload) :
    SubSystemPayload.composeMany [p] = some p := rfl

/-- Composing the empty list yields `none`. -/
theorem SubSystemPayload.composeMany_nil :
    SubSystemPayload.composeMany [] = none := rfl

end VerifiedMBSE.VV
