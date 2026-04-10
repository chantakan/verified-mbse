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
  "https://github.com/yourname/verified-mbse.git"
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
def epsSpec : SubSystemSpec EPSMode Nat epsGlobalInv :=
  { structural := epsStructural   -- System + WellFormed proof
    behavioral := epsBehavioral   -- StateMachine + WellFormed
    fdir       := epsFDIR }       -- Safety + Detection + Recovery proofs
```

This single value proves: the structure is well-formed, the state machine preserves its invariant, and all three FDIR requirements hold.

### 4. Build the V-Matrix and prove completeness

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

### 5. Generate human-readable outputs

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
│   ├── Specialization.lean  #   Specialization (preorder), FeatureTyping, Redefinition
│   ├── Component.lean       #   PartDef, PortRef, Connector, System, WellFormed
│   ├── Compose.lean         #   System.compose, compose_WellFormed
│   └── Interpretation.lean  #   PartInstance, ConnectorSemantic, categorical laws
│
├── Behavior/                # Behavioral models
│   ├── StateMachine.lean    #   Transition, StateMachine, Reachable, inv_holds
│   ├── Temporal.lean        #   Always (□), Eventually (◇), Next, Until, Leads
│   └── FDIR.lean            #   FDIRSpec, StateMachineComponent
│
├── VV/                      # Verification & Validation framework
│   ├── Layer.lean           #   Layer (system/subsystem/component)
│   ├── Evidence.lean        #   ValidationEvidence, ValidationTrace, VVRecord
│   ├── SubSystemSpec.lean   #   StructuralSpec, BehavioralSpec, FDIRBundle, SubSystemSpec
│   ├── VVBundle.lean        #   mkComponentRecord, SubSystemVVBundle, allRecords
│   ├── Power.lean           #   ModePowerSpec, PowerBudgetOK₂
│   └── Propagation.lean     #   LayerPropagation, compose
│
├── Matrix/                  # V-matrix construction
│   ├── VColumn.lean         #   VColumn, atLayer, Complete
│   ├── VMatrix.lean         #   VMatrix, SubSystemComplete, Complete
│   └── Query.lean           #   column, cell, allRecords, summary
│
├── Output/                  # Human-readable output generation
│   ├── Render.lean          #   indent, typeName, directionKeyword
│   ├── SysML.lean           #   → SysML v2 textual notation
│   ├── StateMachineSysML.lean # → SysML v2 state def
│   ├── Markdown.lean        #   → Markdown table
│   └── Terminal.lean        #   → Terminal summary with confidence bars
│
└── Equivalence/             # HoTT-inspired equivalence (advanced)
    ├── ComponentEquiv.lean  #   PortEquiv, ComponentEquiv, Substitutable
    ├── Refinement.lean      #   DesignEquiv, RequirementRefinement
    └── Abstraction.lean     #   AbstractionLevel, DesignParameter

Examples/Spacecraft/         # Full satellite case study (4 subsystems, 25 VVRecords)
├── EPS.lean                 #   Electric Power Subsystem
├── AOCS.lean                #   Attitude & Orbit Control
├── TCS.lean                 #   Thermal Control (mode-dependent invariants)
├── TTC.lean                 #   Telemetry, Tracking & Command
└── Satellite.lean           #   V-Matrix construction + completeness proof
```

## Key Types at a Glance

| Type | What it is | Why it matters |
|------|-----------|----------------|
| `PartDef` | Component with ports + invariant | Invariant is a `Prop` — must be proven at instantiation |
| `Connector` | Port-to-port connection | Carries a `compatible` proof — incompatible ports won't compile |
| `System.WellFormed` | All connectors reference valid parts | Structural soundness as a theorem |
| `Transition.preserves` | Invariant preserved across state change | Transitions that break invariants are **unconstructible** |
| `Reachable.inv_holds` | Safety theorem | Every reachable state satisfies the invariant — by induction |
| `SubSystemSpec` | Structure + behavior + FDIR | One value = complete subsystem verification |
| `VVRecord` | Machine proof + validation trace | The atomic unit of V&V evidence |
| `VMatrix.Complete` | No gaps in the V-matrix | **The main theorem** — if it compiles, you're done |

## Design Principles

1. **Declarative.** Define a `SubSystemSpec`; proofs and VVRecords are derived.
2. **Verifiable.** `lake build` = all proofs checked. Zero `sorry` = zero gaps.
3. **Readable.** V-Matrix output in Markdown, terminal, and SysML v2 text.
4. **Composable.** `System.compose_WellFormed` proves composition preserves correctness.
5. **Extensible.** Domain-independent core; spacecraft examples are separate.

## Documentation

- **[Architecture Guide](docs/Architecture.md)** — Type-theoretic foundations, design decisions, proof patterns
- **[Tutorial: Adding a New Subsystem](docs/Tutorial.md)** — Step-by-step walkthrough

## Requirements

- Lean 4 (v4.29.0+)
- Mathlib

## Statistics

| | Files | Lines | sorry |
|---|---|---|---|
| Library | 26 | 2,363 | 0 |
| Examples | 5 | 2,435 | 0 |
| **Total** | **31** | **4,798** | **0** |

## License

Apache 2.0
