import VerifiedMBSE.Core.Compose
import VerifiedMBSE.Behavior.FDIR
import VerifiedMBSE.VV.Evidence

/-!
# SubSystemSpec: Parametric Subsystem Abstraction (Kripke-Generalized)

This module defines `StructuralSpec` (structure), `BehavioralSpec` (behavior),
`FDIRBundle` (FDIR proof bundle), and the integrated `SubSystemSpec` that
combines all three.

## Kripke generalization

`BehavioralSpec`, `FDIRBundle`, and `SubSystemSpec` are parameterized by a
`ToKripke α S D` instance. This lets the same structures represent both
single-machine and product-machine subsystems uniformly:

- `SubSystemSpec sm` — single-subsystem specification (`sm : StateMachine S D inv`)
- `SubSystemSpec psm` — composite-subsystem specification
  (`psm : ProductStateMachine sm₁ sm₂`)

Parallel composition (binary, nestable to N subsystems) is provided by
`SubSystemSpec.compose` in `VV/ProductFDIR.lean`.

## `BehavioralSpec.nonEmpty` instead of `.wellFormed`

`BehavioralSpec x` carries only
`nonEmpty : (ToKripke.toKripke x).NonEmpty` — the Kripke-level
non-emptiness of the reachable state–data set. This is the weakest
condition that supports the Kripke semantics uniformly across
`StateMachine` and `ProductStateMachine`.

For the `StateMachine` case the stronger `sm.WellFormed` implies
`NonEmpty` via `StateMachine.WellFormed.nonEmpty`, so callers with a
`WellFormed` proof in hand can always obtain a `BehavioralSpec`:

```lean
def epsBehavioral : BehavioralSpec epsSM :=
  { nonEmpty := epsSM_WellFormed.nonEmpty }
def epsSpec : SubSystemSpec epsSM := ...
```

Composition needs the full `WellFormed` strength; `SubSystemSpec.compose`
takes it as an explicit argument, mirroring `FDIRBundle.compose`.
-/

namespace VerifiedMBSE.VV

open VerifiedMBSE.Core
open VerifiedMBSE.Behavior

-- ============================================================
-- §1  StructuralSpec
-- ============================================================

/-- Structural aspect of a subsystem: parts, connectors, system, and a
    well-formedness proof. -/
structure StructuralSpec where
  /-- Subsystem name. -/
  name : String
  /-- List of part definitions. -/
  parts : List PartDef
  /-- List of connectors. -/
  connectors : List Connector
  /-- Underlying `System`. -/
  system : System
  /-- Consistency of `system.parts` with the top-level `parts` field. -/
  system_eq_parts : system.parts = parts
  /-- Consistency of `system.connectors` with the top-level `connectors` field. -/
  system_eq_connectors : system.connectors = connectors
  /-- Structural well-formedness of `system`. -/
  wellFormed : system.WellFormed

/-- Smart constructor for `StructuralSpec`.

    Builds `system` internally from the supplied `parts` and `connectors`,
    so the consistency fields (`system_eq_parts`, `system_eq_connectors`)
    are discharged by `rfl`. -/
def StructuralSpec.mk' (name : String)
    (parts : List PartDef)
    (connectors : List Connector)
    (wf : ({ parts := parts, connectors := connectors } : System).WellFormed) :
    StructuralSpec :=
  { name := name
    parts := parts
    connectors := connectors
    system := { parts := parts, connectors := connectors }
    system_eq_parts := rfl
    system_eq_connectors := rfl
    wellFormed := wf }

/-- Proposition stating that every part invariant in `spec` holds. -/
def StructuralSpec.allPartsInvariant (spec : StructuralSpec) : Prop :=
  ∀ p ∈ spec.parts, p.invariant

-- ============================================================
-- §2  BehavioralSpec (Kripke-Generalized)
-- ============================================================

/-- Behavioral aspect of a subsystem, generalized over any `ToKripke α S D`.

    The type-class parameter `[ToKripke α S D]` supplies the Kripke
    semantics for `x : α`, so the same `BehavioralSpec` structure works
    for `x : StateMachine S D inv` and `x : ProductStateMachine sm₁ sm₂`.

    The only field is `nonEmpty`, expressing Kripke-level non-emptiness
    (some reachable `(s, d)` exists). For `x : StateMachine _ _ inv`,
    `StateMachine.WellFormed.nonEmpty` converts the stronger
    `sm.WellFormed` into this field. -/
structure BehavioralSpec
    {α : Type} {S D : Type} [ToKripke α S D]
    (x : α) where
  /-- Kripke-level non-emptiness: some reachable `(s, d)` exists. -/
  nonEmpty : (ToKripke.toKripke x).NonEmpty

-- ============================================================
-- §3  FDIRBundle (Unified via ToKripke)
-- ============================================================

/-- Proof bundle for FDIR (Fault Detection, Isolation, and Recovery)
    requirements, generalized over any `ToKripke α S D`.

    Parameterizing by `[ToKripke α S D]` lets the same structure carry
    FDIR obligations for both single and composite subsystems:

    - `FDIRBundle sm` where `sm : StateMachine S D inv` — single-subsystem FDIR
    - `FDIRBundle psm` where `psm : ProductStateMachine sm₁ sm₂` — composite FDIR

    Construction of a composite `FDIRBundle` from two component bundles
    is provided by `FDIRBundle.compose` in `VV/ProductFDIR.lean`. -/
structure FDIRBundle
    {α : Type} {S D : Type} [ToKripke α S D]
    (x : α) where
  /-- Predicate characterizing fault states. -/
  isFault : S → Prop
  /-- Predicate characterizing recovery states. -/
  isRecovery : S → Prop
  /-- Safety predicate on data. -/
  isSafe : D → Prop
  /-- R1 — Safety: `□ (isSafe d)`. -/
  safety : Always x (fun _ d => isSafe d)
  /-- R2 — Fault detection: `◇ (isFault s)`. -/
  detection : Eventually x (fun s _ => isFault s)
  /-- R3 — Fault recovery: `□ (isFault ⇒ ◇ isRecovery)`. -/
  recovery : Leads x (fun s _ => isFault s) (fun s _ => isRecovery s)

/-- Convert an `FDIRBundle` to an `FDIRSpec` (StateMachine specialization).

    `FDIRSpec` is currently defined only over `StateMachine`, so this
    conversion is meaningful only when the bundle is over a
    `StateMachine` value. For `FDIRBundle` over a product machine,
    consume the fields (`.isFault`, `.safety`, etc.) directly. -/
def FDIRBundle.toFDIRSpec
    {S D : Type} {inv : S → D → Prop}
    {sm : StateMachine S D inv}
    (bundle : FDIRBundle sm) :
    FDIRSpec sm bundle.isFault bundle.isRecovery bundle.isSafe :=
  { safety    := bundle.safety
    detection := bundle.detection
    recovery  := bundle.recovery }

-- ============================================================
-- §4  SubSystemSpec (Kripke-Generalized)
-- ============================================================

/-- A full subsystem specification integrating structure, behavior, and
    FDIR, generalized over any `ToKripke α S D`.

    Because all three components (`StructuralSpec`, `BehavioralSpec x`,
    `FDIRBundle x`) are uniform in `x : α`, the same `SubSystemSpec`
    type covers `StateMachine` and `ProductStateMachine` instances.
    Parallel composition is provided by `SubSystemSpec.compose` in
    `VV/ProductFDIR.lean`.

    Adding a new subsystem amounts to constructing one value of this
    type. -/
structure SubSystemSpec
    {α : Type} {S D : Type} [ToKripke α S D]
    (x : α) where
  /-- Structural specification. -/
  structural : StructuralSpec
  /-- Behavioral specification. -/
  behavioral : BehavioralSpec x
  /-- FDIR proof bundle. -/
  fdir : FDIRBundle x

/-- Subsystem name (drawn from the structural spec). -/
def SubSystemSpec.name
    {α : Type} {S D : Type} [ToKripke α S D] {x : α}
    (spec : SubSystemSpec x) : String :=
  spec.structural.name

/-- Underlying `System` (drawn from the structural spec). -/
def SubSystemSpec.system
    {α : Type} {S D : Type} [ToKripke α S D] {x : α}
    (spec : SubSystemSpec x) : System :=
  spec.structural.system

/-- Retrieve the underlying `StateMachine` (StateMachine specialization).

    Because `SubSystemSpec` is parameterized over `x : α`, recovering a
    `StateMachine` is meaningful only when `x : StateMachine S D inv`.
    In that case `x` itself is the machine and is returned verbatim. -/
def SubSystemSpec.stateMachine
    {S D : Type} {inv : S → D → Prop} {sm : StateMachine S D inv}
    (_spec : SubSystemSpec sm) : StateMachine S D inv :=
  sm

/-- Combined consistency: structural `System.WellFormed` and behavioral
    Kripke `NonEmpty`.

    The behavioral side is `(ToKripke.toKripke x).NonEmpty` — the
    weakest condition that uniformly covers `StateMachine` and
    `ProductStateMachine`. For `StateMachine` instances this is
    derivable from the full `sm.WellFormed` via
    `StateMachine.WellFormed.nonEmpty`. -/
def SubSystemSpec.Consistent
    {α : Type} {S D : Type} [ToKripke α S D] {x : α}
    (spec : SubSystemSpec x) : Prop :=
  spec.structural.system.WellFormed ∧ (ToKripke.toKripke x).NonEmpty

/-- Automatic derivation of `FDIRSpec` (StateMachine specialization).

    `FDIRSpec` is defined only for `StateMachine`, so this derivation
    applies only to `x : StateMachine S D inv`. For other instances,
    use the `spec.fdir` fields (`.safety`, `.detection`, `.recovery`)
    directly. -/
theorem SubSystemSpec.fdir_derivable
    {S D : Type} {inv : S → D → Prop} {sm : StateMachine S D inv}
    (spec : SubSystemSpec sm) :
    FDIRSpec sm
      spec.fdir.isFault spec.fdir.isRecovery spec.fdir.isSafe :=
  spec.fdir.toFDIRSpec

-- ============================================================
-- §5  Automatic VVRecord Generation (Kripke-Generalized)
-- ============================================================

/-
record 生成関数は evidence-level を明示パラメータで受け取る。
デフォルトは `.trusted` を使うため、既存の呼び出しは変更不要で後方互換を保つ。
`.contract`（仮定付き保証）や `.confidence`（確率的評価）を使いたい呼び出し側は、
第 2 引数として明示的に `ValidationEvidence` を渡すことで三層評価が選択できる。

Kripke 一般化された `SubSystemSpec` に対応しており、`x : α` ベースで
StateMachine 版も ProductStateMachine 版も同じ生成関数を使える。
-/

/-- Subsystem-level `VVRecord` for the S1-WellFormed property.

    `ev` is the `ValidationEvidence` attached to
    `spec.structural.system.WellFormed`; it defaults to
    `.trusted spec.structural.wellFormed`. Pass `.contract` or
    `.confidence` explicitly to select a different evidence layer. -/
def SubSystemSpec.subsystemRecord
    {α : Type} {S D : Type} [ToKripke α S D] {x : α}
    (spec : SubSystemSpec x)
    (ev : ValidationEvidence spec.structural.system.WellFormed :=
            .trusted spec.structural.wellFormed) :
    VVRecord :=
  { layer        := .subsystem
    spec_name    := s!"{spec.structural.name}-S1-WellFormed"
    verification := spec.structural.system.WellFormed
    verified     := spec.structural.wellFormed
    validation   := ValidationTrace.init ev }

/-- System-level `VVRecord` for the R1-Safety property.

    `ev` is the `ValidationEvidence` attached to
    `Always x (fun _ d => spec.fdir.isSafe d)`; it defaults to
    `.trusted spec.fdir.safety`. -/
def SubSystemSpec.safetyRecord
    {α : Type} {S D : Type} [ToKripke α S D] {x : α}
    (spec : SubSystemSpec x)
    (ev : ValidationEvidence
            (Always x (fun _ d => spec.fdir.isSafe d)) :=
            .trusted spec.fdir.safety) :
    VVRecord :=
  { layer        := .system
    spec_name    := s!"{spec.structural.name}-R1-Safety"
    verification := Always x (fun _ d => spec.fdir.isSafe d)
    verified     := spec.fdir.safety
    validation   := ValidationTrace.init ev }

/-- System-level `VVRecord` for the R3-Recovery property.

    `ev` is the `ValidationEvidence` attached to the `Leads` proposition;
    it defaults to `.trusted spec.fdir.recovery`. -/
def SubSystemSpec.recoveryRecord
    {α : Type} {S D : Type} [ToKripke α S D] {x : α}
    (spec : SubSystemSpec x)
    (ev : ValidationEvidence
            (Leads x
              (fun s _ => spec.fdir.isFault s)
              (fun s _ => spec.fdir.isRecovery s)) :=
            .trusted spec.fdir.recovery) :
    VVRecord :=
  { layer        := .system
    spec_name    := s!"{spec.structural.name}-R3-Recovery"
    verification := Leads x
                      (fun s _ => spec.fdir.isFault s)
                      (fun s _ => spec.fdir.isRecovery s)
    verified     := spec.fdir.recovery
    validation   := ValidationTrace.init ev }

-- ============================================================
-- §6  Structural Composition
-- ============================================================

/-- Parallel structural composition of two `StructuralSpec`s with an
    optional list of inter-subsystem bridge connectors.

    `bridge` carries connectors whose endpoints cross between `s1` and
    `s2`; `hbridge` witnesses that each endpoint resides in the
    concatenation of the two operand part lists. -/
def StructuralSpec.compose
    (s1 s2 : StructuralSpec) (bridge : List Connector)
    (hbridge : ∀ c ∈ bridge,
        c.source.part ∈ s1.system.parts ++ s2.system.parts ∧
        c.target.part ∈ s1.system.parts ++ s2.system.parts) :
    StructuralSpec :=
  { name := s!"{s1.name}+{s2.name}"
    parts := s1.system.parts ++ s2.system.parts
    connectors := s1.system.connectors ++ s2.system.connectors ++ bridge
    system := System.compose s1.system s2.system bridge
    system_eq_parts := rfl
    system_eq_connectors := rfl
    wellFormed := System.compose_WellFormed s1.system s2.system bridge
                    s1.wellFormed s2.wellFormed hbridge }

/-- The composed part count equals the sum of the operand part counts. -/
theorem StructuralSpec.compose_parts_length
    (s1 s2 : StructuralSpec) (bridge : List Connector)
    (hbridge : ∀ c ∈ bridge,
        c.source.part ∈ s1.system.parts ++ s2.system.parts ∧
        c.target.part ∈ s1.system.parts ++ s2.system.parts) :
    (StructuralSpec.compose s1 s2 bridge hbridge).parts.length =
    s1.system.parts.length + s2.system.parts.length := by
  simp [StructuralSpec.compose, List.length_append]

end VerifiedMBSE.VV
