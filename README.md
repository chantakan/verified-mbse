# verified-mbse

**Machine-verified V&V matrices for spacecraft systems engineering.**

A Lean 4 library that gives SysML v2 / KerML design models a dependent type-theoretic semantics.
If your model type-checks, your V&V matrix is complete and your design constraints are proven correct.

> `lake build` passing with zero `sorry` = every specification verified, every V-matrix cell filled.

## The Problem

Systems engineers maintain V&V matrices — tables that map requirements to verification evidence — in spreadsheets, wikis, or DOORS. This creates three failure modes:

1. **Gaps go unnoticed.** A cell is empty or says "TBD" but nobody catches it before launch review.
2. **Evidence is disconnected.** The proof that "power budget holds across all mode combinations" lives in a separate analysis tool with no formal link to the design model.
3. **Composition is unchecked.** Two subsystems are individually correct, but their integration breaks an assumption neither team documented.

`verified-mbse` eliminates all three by encoding V&V as types:

```
VVRecord = { spec : Prop,  verified : spec,  validation : ValidationTrace spec }
           ─────────────   ───────────────   ─────────────────────────────────
           requirement     machine proof      confidence trace (→ trusted)
```

If a `VVRecord` exists, the requirement is proven. If a `VMatrix.Complete` theorem compiles, every cell is filled.

## Quick Start

### 1. Add to your project

```lean
-- lakefile.lean
require verifiedMbse from git
  "https://github.com/chantakan/verified-mbse.git"
```

### 2. Define components and a state machine

```lean
import VerifiedMBSE

open VerifiedMBSE.Core
open VerifiedMBSE.Behavior
open VerifiedMBSE.VV

-- A component with ports and an invariant
def PowerSupply : PartDef :=
  { baseType  := { name := some "PowerSupply" }
    ports     := [pwrOutPort]
    invariant := True }

-- State machine: invariant preservation is a *type-level contract*
-- (transitions that violate it simply won't compile)
def epsSM : StateMachine EPSMode Nat (fun _ v => v ≤ 1000) where
  initialState := .nominal
  transitions  := [nominalToLowPower, lowPowerToFault, ...]
```

### 3. Bundle everything into one `SubSystemSpec`

```lean
def epsSpec : SubSystemSpec epsSM :=
  { structural := epsStructural   -- System + WellFormed proof
    behavioral := epsBehavioral   -- NonEmpty (Kripke-generalized)
    fdir       := epsFDIR }       -- Safety + Detection + Recovery proofs
```

This single value proves: the structure is well-formed, the state machine preserves its invariant, and all three FDIR requirements hold.

### 4. Compose subsystems (N-way nested composition supported)

```lean
-- 2 subsystems
def epsAocsPK : ProductKripke epsSM aocsSM := ⟨⟩
def epsAocsSpec : SubSystemSpec epsAocsPK :=
  SubSystemSpec.compose epsSpec aocsSpec epsAocsPK
    epsSM_WellFormed.nonEmpty aocsSM_WellFormed.nonEmpty [] (by intros; contradiction)

-- 3 subsystems (nested) — enabled by B-8 ProductKripke generalization
def epsAocsTcsPK : ProductKripke epsAocsPK tcsSM := ⟨⟩
def epsAocsTcsSpec : SubSystemSpec epsAocsTcsPK :=
  SubSystemSpec.compose epsAocsSpec tcsSpec epsAocsTcsPK
    epsAocsSpec.behavioral.nonEmpty tcsSM_WellFormed.nonEmpty [] (by intros; contradiction)
```

The composed spec auto-derives FDIR safety / detection / recovery for the product.

### 5. Build the V-Matrix and prove completeness

```lean
open VerifiedMBSE.Matrix

def satellite : VMatrix :=
  { columns := [epsColumn, aocsColumn, tcsColumn, ttcColumn] }

-- This theorem IS the verification: no gaps in the V-matrix.
theorem sat_complete : satellite.Complete ["EPS", "AOCS", "TCS", "TTC"] := by
  constructor
  · intro s hs; ...   -- every subsystem has a column
  · intro col hcol; ... -- every column covers all layers
```

### 6. Generate human-readable outputs

```lean
open VerifiedMBSE.Output

#eval IO.println (satellite.toMarkdown "MySatellite")
#eval IO.println (satellite.toTerminal "MySatellite")
```

Output:
```
═══════════════════════════════════════════
  V-Matrix: MySatellite
  4 subsystems │ 25 records │ ALL TRUSTED
═══════════════════════════════════════════
  EPS  [5] ████████████████████ 100%
  AOCS [6] ████████████████████ 100%
  TCS  [8] ████████████████████ 100%
  TTC  [6] ████████████████████ 100%
═══════════════════════════════════════════
  Completeness: ✓ All layers covered
═══════════════════════════════════════════
```

## Module Structure

```
VerifiedMBSE/
├── Core/                    # Domain-independent type-theoretic foundations
│   ├── KerML.lean           #   Element, KerMLType, Feature, Direction
│   ├── Port.lean            #   PortDef, Conjugation, compatible
│   ├── Specialization.lean  #   Specialization (preorder), FeatureTyping, Interpretation
│   ├── Component.lean       #   PartDef, PortRef, Connector, System, WellFormed
│   ├── Compose.lean         #   System.compose, compose_WellFormed
│   └── Interpretation.lean  #   PartInstance, ConnectorSemantic, categorical laws
│
├── Behavior/                # Behavioral models (Kripke-generalized LTL)
│   ├── StateMachine.lean    #   Transition, StateMachine, Reachable, inv_holds
│   ├── Temporal.lean        #   Always (□), Eventually (◇), Next, Until, Leads
│   ├── KripkeStructure.lean #   KripkeStructure + ToKripke type class (B-1)
│   ├── StateMachineKripke.lean #   StateMachine → KripkeStructure instance
│   ├── StateMachineLTL.lean    #   Dot-notation for sm.Always / sm.Eventually
│   ├── Product.lean         #   ProductStateMachine (abbrev of ProductKripke)
│   ├── ProductKripke.lean   #   ProductKripke (N-way nested, B-8)
│   ├── ProductTemporal.lean #   Always_prod / Eventually_prod / Leads_prod lifting
│   └── FDIR.lean            #   FDIRSpec, StateMachineComponent
│
├── VV/                      # Verification & Validation framework
│   ├── Layer.lean           #   Layer (8-level ECSS-E-ST-10C: mission→part)
│   ├── Evidence.lean        #   ValidationEvidence, isTrusted, ValidationTrace, VVRecord
│   ├── SubSystemSpec.lean   #   StructuralSpec, BehavioralSpec, FDIRBundle, SubSystemSpec
│   ├── VVBundle.lean        #   mkComponentRecord, SubSystemVVBundle, allRecords
│   ├── Power.lean           #   ModePowerSpec, PowerBudgetOK₂
│   ├── Propagation.lean     #   LayerPropagation, depth-based supports
│   ├── Contract.lean        #   Contract, ContractedSystem, CouplingConstraint
│   └── ProductFDIR.lean     #   FDIRBundle.compose, SubSystemSpec.compose (N-way)
│
├── Matrix/                  # V-matrix construction
│   ├── VColumn.lean         #   VColumn, atLayer, Complete, fullyTrusted (struct-discrim)
│   ├── VMatrix.lean         #   VMatrix, SubSystemComplete, Complete
│   ├── Query.lean           #   column, cell, allRecords, summary
│   └── ModelBoundary.lean   #   ModelBoundary (vm : VMatrix) — dependently typed
│
├── Output/                  # Human-readable output generation
│   ├── Render.lean          #   indent, typeName, layerToAbbr (8-layer)
│   ├── SysML.lean           #   → SysML v2 textual notation
│   ├── StateMachineSysML.lean # → SysML v2 state def
│   ├── Markdown.lean        #   → Markdown table
│   └── Terminal.lean        #   → Terminal summary with confidence bars
│
└── Equivalence/             # HoTT-inspired equivalence (advanced)
    ├── ComponentEquiv.lean  #   PortEquiv, ComponentEquiv, Substitutable
    ├── Refinement.lean      #   DesignEquiv, RequirementRefinement
    ├── Abstraction.lean     #   AbstractionLevel, DesignParameter
    └── Univalence.lean      #   DesignSpace (quotient), ua/ua_inv, Transport, Fiber

Examples/Spacecraft/         # Full satellite case study + acceptance tests
├── EPS.lean                 #   Electric Power Subsystem (+ EPSTypeTag F8 pattern)
├── AOCS.lean                #   Attitude & Orbit Control
├── TCS.lean                 #   Thermal Control (mode-dependent invariants)
├── TTC.lean                 #   Telemetry, Tracking & Command
├── Satellite.lean           #   V-Matrix + completeness + ModelBoundary
├── Integration.lean         #   2-way and 3-way nested composition sanity tests
├── F1F2Tests.lean           #   Evidence parameterization + mixed-evidence tests
├── F3F5F6Tests.lean         #   Specialization preorder, Layer 8-level, ModelBoundary type-binding
└── F8Tests.lean             #   Interpretation pattern (EPSTypeTag + exhaustive dispatch)
```

## Key Types at a Glance

| Type | What it is | Why it matters |
|------|-----------|----------------|
| `PartDef` | Component with ports + invariant | Invariant is a `Prop` — must be proven at instantiation |
| `Connector` | Port-to-port connection | Carries a `compatible` proof — incompatible ports won't compile |
| `System.WellFormed` | All connectors reference valid parts | Structural soundness as a theorem |
| `Transition.preserves` | Invariant preserved across state change | Transitions that break invariants are **unconstructible** |
| `Reachable.inv_holds` | Safety theorem | Every reachable state satisfies the invariant — by induction |
| `ToKripke α S D` | Type class lifting α to KripkeStructure | Unifies LTL over StateMachine / ProductKripke / future continuous-time |
| `ProductKripke x y` | Heterogeneous product of Kripke structures | Enables N-way nested composition (3+ subsystems) |
| `SubSystemSpec` | Structure + behavior + FDIR | One value = complete subsystem verification |
| `SubSystemSpec.compose` | Parallel composition of two specs | Composes FDIR, spawns auto-derived bridge Records |
| `VVRecord` | Machine proof + validation trace | The atomic unit of V&V evidence |
| `ValidationEvidence` | `.trusted` / `.contract` / `.confidence` | 3-level confidence hierarchy; `isTrusted` by constructor (no Float equality) |
| `VMatrix.Complete` | No gaps in the V-matrix | **The main theorem** — if it compiles, you're done |
| `Contract` | Assume-guarantee pair with validity proof | Integration obligations become type errors when missing |
| `ContractedSystem` | Contracts + coupling constraints, all discharged | Catches the "individually correct, jointly broken" failure mode |
| `ModelBoundary (vm)` | **Dependently-typed** verified/tested/analyzed/unmodeled split | `verifiedCount` auto-derived from `vm.totalRecords` — no manual sync |
| `Layer` | 8 levels: mission → part (ECSS-E-ST-10C) | depth-based `supports` relation; new levels added without case explosion |
| `DesignSpace` | `PartDef / ComponentEquiv` quotient | Univalence: equivalent components are equal in design space |
| `ua` / `ua_inv` | Equiv ↔ equality in `DesignSpace` | HoTT univalence via setoid quotient — sorry-free |

## Design Principles

1. **Declarative.** Define a `SubSystemSpec`; proofs and VVRecords are derived.
2. **Verifiable.** `lake build` = all proofs checked. Zero `sorry` = zero gaps.
3. **Readable.** V-Matrix output in Markdown, terminal, and SysML v2 text.
4. **Composable.** N-way nested subsystem composition via `ProductKripke`.
5. **Extensible.** Domain-independent core; spacecraft examples are separate.
6. **Typed discipline.** `ModelBoundary (vm : VMatrix)`, `EPSTypeTag` enum for interpretations — structural checks over string matching.

## Documentation

- **[API Reference](https://chantakan.github.io/verified-mbse/)** — doc-gen4 generated (auto-deployed via GitHub Pages)
- **[Architecture Guide](docs/Architecture.md)** — Type-theoretic foundations, design decisions, proof patterns
- **[Tutorial: Adding a New Subsystem](docs/Tutorial.md)** — Step-by-step walkthrough
- **[Interpretation Pattern](docs/InterpretationPattern.md)** — Best practices for `KerMLType → Type` interpretations (F8)

## Requirements

- Lean 4 (v4.30.0-rc1)
- Mathlib

## Statistics

| | Files | Lines | sorry | warnings |
|---|---|---|---|---|
| Library (VerifiedMBSE/) | 36 | ~3,970 | 0 | 0 |
| Examples (satellite + tests) | 10 | ~3,200 | 0 | 0 |
| Acceptance tests | ~70 examples | — | — | — |

Build: `lake build VerifiedMBSE` (176 jobs) + `lake build Examples` (185 jobs), all passing with zero sorry/warnings.

## License

Apache 2.0