# Interpretation Pattern

`VerifiedMBSE.Core.Interpretation := KerMLType → Type` is the **semantic
function** that assigns Lean carrier types to the type identifiers
(`KerMLType`) of a domain model. How this function is written governs
both the soundness and the maintainability of the model. This document
captures the recommended pattern and the anti-patterns to avoid.

## TL;DR

- **Anti-pattern**: `match t.name with | some "Foo" => FooType | _ => Unit`.
  Falling through to `_ => Unit` on a string match hides
  unsoundness silently whenever there is a typo.
- **Recommended pattern**: define a domain-specific `inductive`
  enum (TypeTag), provide an embedding from enum to `KerMLType`, and
  build `Interpretation` from an exhaustive pattern match on the enum.
  Confine string comparisons to a single reverse-lookup function.

---

## The Problem: Naïve String Matching

```lean
-- Anti-pattern
def EPSNatInterpretation : Interpretation := fun t =>
  match t.name with
  | some "PowerSupply" => Nat
  | some "Load"        => Nat
  | some "PowerPort"   => Nat
  | some "~PowerPort"  => Nat
  | _                  => Unit  -- ← pitfall
```

### Risks

1. **Silent unsoundness due to typos**: even writing
   `some "Powr Supply"` (a missing space) compiles without complaint,
   and the corresponding `KerMLType` receives `Unit` as its carrier.
   Because `Unit` satisfies every predicate, `SMInvariantCompatible`'s
   invariants become trivially true.
2. **Gaps when extending the model**: if you add a new `PartDef` but
   forget to add the corresponding case to `Interpretation`, the new
   type silently falls through to `_ => Unit`. No type error.
3. **Soundness proofs are hard**: to prove `InterpretationRespects I`,
   you must investigate which `KerMLType` values get mapped to `Unit`,
   and string matching does not let you confirm exhaustiveness
   mechanically.

---

## Recommended Pattern: Tag Enum + Exhaustive Dispatch

### Step 1: Define a Domain-Specific TypeTag Enum

Prepare an `inductive` enum that lists every `KerMLType` appearing in
that subsystem (or composition unit).

```lean
/-- Identifiers for every KerMLType appearing in the EPS subsystem. -/
inductive EPSTypeTag where
  | powerSupply
  | load
  | powerPort
  | powerPortConj
  deriving Repr, BEq, DecidableEq
```

**Key points**:
- `deriving DecidableEq` lets `decide` handle the reverse lookup and
  later proofs.
- Include every type for which the subsystem needs semantics: port
  types, part types, and signal/message types if relevant.

### Step 2: Define the Enum–KerMLType Embedding

Declare that each tag corresponds to a unique string.

```lean
/-- From tag to KerMLType: strings appear **only here**. -/
def EPSTypeTag.toName : EPSTypeTag → String
  | .powerSupply   => "PowerSupply"
  | .load          => "Load"
  | .powerPort     => "PowerPort"
  | .powerPortConj => "~PowerPort"

def EPSTypeTag.toKerMLType (tag : EPSTypeTag) : KerMLType :=
  { name := some tag.toName }
```

### Step 3: Define the Reverse Lookup (String → Enum)

This function is where all string matching is concentrated. Only this
function needs a `_ => none` fallback; callers work through
`Option EPSTypeTag`.

```lean
/-- Reverse lookup from KerMLType.name to EPSTypeTag.
    Out-of-domain types return `none`. -/
def EPSTypeTag.fromName : Option String → Option EPSTypeTag
  | some "PowerSupply"  => some .powerSupply
  | some "Load"         => some .load
  | some "PowerPort"    => some .powerPort
  | some "~PowerPort"   => some .powerPortConj
  | _                   => none
```

### Step 4: Connect Carrier Types via the Enum

Assign a Lean carrier type to each tag using an **exhaustive pattern
match**. Avoiding the `_` case forces the compiler to flag missing
cases when the enum is extended.

```lean
/-- Carrier type per tag. Exhaustive, no `_` case. -/
def EPSTypeTag.interp : EPSTypeTag → Type
  | .powerSupply   => Nat
  | .load          => Nat
  | .powerPort     => Nat
  | .powerPortConj => Nat
```

### Step 5: Assemble the Interpretation

`Interpretation` is `KerMLType → Type`. If the reverse lookup succeeds,
return `.interp`; if it fails (the type is out of domain), return
`Unit` (or `Empty`; see below).

```lean
/-- EPS Interpretation. String matching is confined to `fromName`,
    and carrier-type assignment is guaranteed exhaustive via
    `interp`'s pattern match. -/
def EPSNatInterpretation : Interpretation := fun t =>
  match EPSTypeTag.fromName t.name with
  | some tag => tag.interp
  | none     => Unit
```

---

## Choosing the Fallback Type

What to assign to out-of-domain types (when `fromName` returns `none`)
is a **deliberate design choice**.

| Fallback | Meaning | When to use |
|------------|--------|------|
| `Unit` | "Every instance is `()`" | When out-of-domain references should still work (backward compatibility) |
| `Empty` | "No instances exist" | When out-of-domain use should be banned at the type level |
| `PUnit.{u}` | Universe-polymorphic version of Unit | When universe polymorphism is needed |

**Recommendation**: if the tag enum lists every type your domain
handles, using `Empty` for out-of-domain **bans usage at the type
level**. If you must keep `Unit` for compatibility, document the
**reason** in a comment.

```lean
def EPSNatInterpretation : Interpretation := fun t =>
  match EPSTypeTag.fromName t.name with
  | some tag => tag.interp
  | none     =>
    -- Using Empty would forbid out-of-domain references. We keep
    -- Unit so this interpretation can be loosely connected with
    -- other subsystems in the existing architecture.
    Unit
```

---

## Composition: Interpretations Across Subsystems

When composing multiple subsystems (EPS + AOCS + TCS etc.), either
combine the subsystem tag enums into a sum type, or compose each
subsystem's Interpretation by dispatching on `KerMLType.name`.

### Pattern A: Combine Enums via a Sum Type

```lean
inductive SpacecraftTypeTag where
  | eps  (tag : EPSTypeTag)
  | aocs (tag : AOCSTypeTag)
  | tcs  (tag : TCSTypeTag)
  deriving Repr

def SpacecraftTypeTag.toName : SpacecraftTypeTag → String
  | .eps  tag => tag.toName
  | .aocs tag => tag.toName
  | .tcs  tag => tag.toName

def SpacecraftTypeTag.interp : SpacecraftTypeTag → Type
  | .eps  tag => tag.interp
  | .aocs tag => tag.interp
  | .tcs  tag => tag.interp
```

**Pros**: the type space of every subsystem lands in one enum. Naming
collisions (e.g., both EPS and AOCS defining a `"Mode"` type) are
detected at the type level.

**Cons**: the composite enum must be updated whenever a subsystem is
added.

### Pattern B: Dispatch Between Interpretations

```lean
def SpacecraftInterpretation : Interpretation := fun t =>
  if EPSTypeTag.fromName t.name |>.isSome then
    EPSNatInterpretation t
  else if AOCSTypeTag.fromName t.name |>.isSome then
    AOCSInterpretation t
  else
    Unit
```

**Pros**: subsystems stay strongly independent.

**Cons**: naming collisions are silently resolved (whichever is
detected first wins). To detect collisions you must prove a separate
`no_overlap` lemma.

---

## Guaranteeing Soundness

When proving `InterpretationRespects I` (a hypothesis for the
`soundness` theorem), the tag pattern lets induction proceed on the
finite tag enum.

```lean
-- Example: all specialization inside EPS is trivially reflexive
theorem EPSInterpretationRespects_trivial :
    ∀ tag : EPSTypeTag,
      semanticSpecializes EPSNatInterpretation tag.toKerMLType tag.toKerMLType := by
  intro tag
  exact semanticSpecializes_refl _ _
```

If the pattern match is exhaustive, `cases tag` mechanically discharges
the finite number of cases. With string matching, induction over the
full `Option String` space in `t.name` is not tractable.

---

## Anti-patterns and Countermeasures

| Anti-pattern | Problem | Recommendation |
|-------------|------|------|
| `match t.name with ... \| _ => Unit` inside `Interpretation` | Typo causes silent unsoundness | Extract reverse lookup into a helper + exhaustive tag pattern |
| Using `some "Foo"` literals directly inside `Interpretation` | A model change forces grep across the whole codebase | Concentrate strings in `EPSTypeTag.toName` |
| Hiding out-of-domain types under `Unit` | Misuse by other modules is never caught | Consider `Empty`, or document the reason in a docstring |
| Reusing the same type name across subsystems with different meaning | Dispatch order silently changes meaning | Use a sum-type enum so naming collisions trigger a type error |
| Arguing interpretation soundness on paper | Immediately breaks on extension | Use `cases tag` for a mechanical proof |

---

## Reference Implementation

- `Examples/Spacecraft/EPS.lean`: post-F8, `EPSTypeTag` +
  `EPSNatInterpretation` are implemented via the pattern above. Tests
  check `interp` for every `EPSTypeTag` value via `rfl`.
- `Examples/Spacecraft/F8Tests.lean`: acceptance tests.