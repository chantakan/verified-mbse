# Tutorial: Adding a New Subsystem

This guide walks through adding a new subsystem to your satellite model, from component definitions to V-matrix integration. We'll build a simplified Propulsion subsystem (PROP) as an example.

## Step 1: Define KerML Types and Ports

Every subsystem starts with port type definitions and their conjugation pairs.

```lean
import VerifiedMBSE

open VerifiedMBSE.Core
open VerifiedMBSE.Behavior
open VerifiedMBSE.VV

namespace MyProject.PROP

-- Port types
def ThrustPort     : KerMLType := { name := some "ThrustPort" }
def ConjThrustPort : KerMLType := { name := some "~ThrustPort" }

-- Conjugation (required for connector compatibility)
def thrustConjugation : Conjugation where
  original   := ThrustPort
  conjugated := ConjThrustPort

def thrustCompatible : compatible ThrustPort ConjThrustPort :=
  ⟨thrustConjugation, rfl, rfl⟩

-- Port definitions
def thrustOutPort : PortDef :=
  { feature  := { name := some "thrustOut", lower := 1, upper := 1, direction := .out }
    flowType := ThrustPort }

def thrustInPort : PortDef :=
  { feature  := { name := some "thrustIn", lower := 1, upper := 1, direction := .in_ }
    flowType := ConjThrustPort }
```

**Key point:** `compatible` is a proof that two port types can be connected. Without it, you cannot construct a `Connector`.

## Step 2: Define Components (PartDef)

Each component has a base type, ports, and an invariant. The invariant is a `Prop` — it must be provable wherever the component is instantiated.

```lean
def Thruster : PartDef :=
  { baseType  := { name := some "Thruster" }
    ports     := [thrustInPort]
    invariant := True }  -- Simple: always valid

def PropController : PartDef :=
  { baseType  := { name := some "PropController" }
    ports     := [thrustOutPort]
    invariant := True }
```

**Tip:** Use `True` for invariants that are structurally guaranteed. Use specific propositions (e.g., `fuel ≥ 0`) for constraints that need proofs.

## Step 3: Create Connectors and System

```lean
def ctrlThrustRef : PortRef :=
  { part := PropController, port := thrustOutPort
    mem  := by simp [PropController] }

def thrusterRef : PortRef :=
  { part := Thruster, port := thrustInPort
    mem  := by simp [Thruster] }

def thrustConnector : Connector :=
  { source     := ctrlThrustRef
    target     := thrusterRef
    compatible := thrustCompatible }

def PROPSystem : System :=
  { parts      := [PropController, Thruster]
    connectors := [thrustConnector] }
```

## Step 4: Prove WellFormed

Every `System` needs a `WellFormed` proof: all connector endpoints reference parts in the system.

```lean
theorem PROPSystem_WellFormed : PROPSystem.WellFormed := by
  intro c hc
  simp only [PROPSystem] at hc
  simp only [List.mem_singleton] at hc
  subst hc
  exact ⟨by simp [PROPSystem, thrustConnector, ctrlThrustRef],
         by simp [PROPSystem, thrustConnector, thrusterRef]⟩
```

**Pattern:** For each connector, prove `source.part ∈ parts ∧ target.part ∈ parts` using `simp`.

## Step 5: Define the State Machine

```lean
inductive PROPMode where
  | idle    -- No thrust
  | firing  -- Active thrust
  | fault   -- Fault detected
  deriving Repr, BEq, DecidableEq

-- Global invariant: fuel level ≤ 10000 (arbitrary units)
def propGlobalInv : PROPMode → Nat → Prop := fun _ fuel => fuel ≤ 10000

-- Helper for effect=id transitions
private theorem propGlobal_preserves (src tgt : PROPMode) (g : Nat → Prop) :
    ∀ fuel, g fuel → propGlobalInv src fuel → propGlobalInv tgt (id fuel) :=
  fun _ _ h => h

def propIdleToFiring : Transition PROPMode Nat propGlobalInv where
  source := .idle; target := .firing
  guard := fun _ => True; effect := id
  preserves := propGlobal_preserves .idle .firing (fun _ => True)

-- ... define other transitions ...

def propSM : StateMachine PROPMode Nat propGlobalInv where
  initialState := .idle
  transitions  := [propIdleToFiring, ...]

theorem propSM_WellFormed : propSM.WellFormed :=
  ⟨5000, by unfold propGlobalInv; omega⟩
```

**Key insight:** `Transition.preserves` is a proof obligation. If your `effect` changes the data, you must prove the invariant is maintained. For `effect := id`, the proof is trivial.

## Step 6: Prove FDIR Requirements

```lean
-- R1: Safety □(fuel ≤ 10000)
theorem prop_always_safe :
    Always propSM (fun _ fuel => fuel ≤ 10000) :=
  fun _ _ h => h.inv_holds

-- R2: Detection ◇(fault)
theorem prop_eventually_fault :
    Eventually propSM (fun s _ => s = .fault) :=
  ⟨.fault, 5000, prop_fault_reachable, rfl⟩

-- R3: Recovery □(fault → ◇ idle)
theorem prop_fault_leads_to_idle :
    Leads propSM (fun s _ => s = .fault) (fun s _ => s = .idle) := by
  intro s fuel hr hs; subst hs
  exact ⟨.idle, fuel,
    Reachable.step propFaultToIdle hr (by simp [propSM]) rfl trivial, rfl⟩
```

## Step 7: Bundle into SubSystemSpec (B-7 Kripke-generalized)

Since B-7, `SubSystemSpec` is parameterized by `{α : Type} [ToKripke α S D] (x : α)`,
so you pass the state machine directly (its `ToKripke` instance is resolved automatically).
`BehavioralSpec` carries only a `nonEmpty` witness (Kripke-level), derived from
`WellFormed`:

```lean
def propStructural : StructuralSpec :=
  StructuralSpec.mk' "PROP" [PropController, Thruster] [thrustConnector]
    PROPSystem_WellFormed

def propBehavioral : BehavioralSpec propSM :=
  { nonEmpty := propSM_WellFormed.nonEmpty }

def propFDIR : FDIRBundle propSM :=
  { isFault    := fun s => s = .fault
    isRecovery := fun s => s = .idle
    isSafe     := fun fuel => fuel ≤ 10000
    safety     := prop_always_safe
    detection  := prop_eventually_fault
    recovery   := prop_fault_leads_to_idle }

def propSpec : SubSystemSpec propSM :=
  { structural := propStructural
    behavioral := propBehavioral
    fdir       := propFDIR }
```

## Step 8: Create VVBundle

```lean
def propVVBundle : SubSystemVVBundle propSpec :=
  { componentRecords :=
      [ mkComponentRecord "PROP" 1 PropController trivial
      , mkComponentRecord "PROP" 2 Thruster trivial ] }

-- Verify record count
theorem propVVBundle_count :
    propVVBundle.allRecords.length = 5 := by
  simp [SubSystemVVBundle.allRecords, propVVBundle]
```

`allRecords` automatically includes:
- Your component records (2)
- Subsystem WellFormed record (1, auto-derived from `propSpec`)
- R1 Safety record (1, auto-derived)
- R3 Recovery record (1, auto-derived)

### Using `.contract` or `.confidence` evidence (F1)

The auto-derived records default to `.trusted` evidence (backward compatible).
To generate a VVRecord backed by a weaker evidence level, pass an explicit
`ValidationEvidence` via the `ev :=` named argument:

```lean
-- R1 record, but flagged as contract-level (test-verified, not yet proven in Lean)
def propR1_contract : VVRecord :=
  propSpec.safetyRecord
    (ev := .contract SomeAssumption (fun h => prop_always_safe_modulo_h h))

-- R1 record based on expert judgment (70% confidence)
def propR1_early : VVRecord :=
  propSpec.safetyRecord (ev := .confidence 0.7)
```

`VColumn.fullyTrusted` discriminates on the evidence constructor (not on
`currentLevel == 1.0` Float equality), so mixing `.trusted` and `.contract`
records in a column correctly reports `fullyTrusted = false`.

## Step 9: Add to VMatrix

```lean
open VerifiedMBSE.Matrix

def propColumn : VColumn :=
  { subsystem := "PROP", records := propVVBundle.allRecords }

-- Add to your satellite VMatrix
def mySatellite : VMatrix :=
  { columns := [epsColumn, aocsColumn, propColumn] }

-- Prove completeness
theorem mySatellite_Complete :
    mySatellite.Complete ["EPS", "AOCS", "PROP"] := by
  constructor
  · intro s hs; ...
  · intro col hcol; ... <;> native_decide
```

## Step 10: Generate Outputs

```lean
#eval IO.println (mySatellite.toTerminal "MySatellite")
#eval IO.println (mySatellite.toMarkdown "MySatellite")
```

## (Optional) Step 11: Compose Multiple Subsystems (B-8)

For integration-level verification (FDIR of the joint system), compose
two subsystems into a product spec:

```lean
-- 2-way composition
def epsPropPK : ProductKripke epsSM propSM := ⟨⟩

def epsPropSpec : SubSystemSpec epsPropPK :=
  SubSystemSpec.compose epsSpec propSpec epsPropPK
    epsSM_WellFormed.nonEmpty propSM_WellFormed.nonEmpty
    [] (by intros; contradiction)
```

The composed `SubSystemSpec`:
- Names the joint system `"EPS+PROP"`
- Produces FDIR with `isFault := epsFault ∨ propFault`, `isSafe := epsSafe ∧ propSafe`
- Exposes `safetyRecord` / `recoveryRecord` / `subsystemRecord` at the joint level

For **3 or more subsystems**, nest the compositions — the second-level
`NonEmpty` comes from `.behavioral.nonEmpty`:

```lean
def epsPropTcsPK : ProductKripke epsPropPK tcsSM := ⟨⟩

def epsPropTcsSpec : SubSystemSpec epsPropTcsPK :=
  SubSystemSpec.compose epsPropSpec tcsSpec epsPropTcsPK
    epsPropSpec.behavioral.nonEmpty tcsSM_WellFormed.nonEmpty
    [] (by intros; contradiction)
```

See `Examples/Spacecraft/Integration.lean` for a working `(EPS × Mini) × Mini2` example.

## (Optional) Step 12: Define an Interpretation (F8 Pattern)

If your subsystem participates in `StateMachineComponent` (integrates structure
with behavior via a model-theoretic interpretation), follow the recommended
pattern in `docs/InterpretationPattern.md`:

1. Define a `TypeTag` enum listing every `KerMLType` in the subsystem.
2. Write `toName` / `toKerMLType` (forward) and `fromName` (reverse).
3. Define the type assignment `interp : Tag → Type` **exhaustively** (no `_` case).
4. Compose the `Interpretation` using `fromName` for string matching and
   `interp` for type assignment.

```lean
inductive PROPTypeTag where
  | propController | thruster | thrustPort | thrustPortConj
  deriving Repr, BEq, DecidableEq

def PROPTypeTag.toName : PROPTypeTag → String
  | .propController  => "PropController"
  | .thruster        => "Thruster"
  | .thrustPort      => "ThrustPort"
  | .thrustPortConj  => "~ThrustPort"

def PROPTypeTag.fromName : Option String → Option PROPTypeTag
  | some "PropController" => some .propController
  | some "Thruster"       => some .thruster
  | some "ThrustPort"     => some .thrustPort
  | some "~ThrustPort"    => some .thrustPortConj
  | _                     => none

def PROPTypeTag.interp : PROPTypeTag → Type
  | .propController | .thruster | .thrustPort | .thrustPortConj => Nat

def PROPNatInterpretation : Interpretation := fun t =>
  match PROPTypeTag.fromName t.name with
  | some tag => tag.interp
  | none     => Unit
```

This keeps string literals confined to `fromName`, guarantees soundness for
every tag via exhaustive match, and adding a new PartDef only requires
adding a constructor to the enum (the compiler flags missing cases).

## Checklist

When adding a new subsystem, you need:

- [ ] KerML types + conjugation pairs
- [ ] PortDef definitions
- [ ] PartDef for each component (with invariants)
- [ ] PortRef + Connector (with `compatible` proofs)
- [ ] System + `WellFormed` theorem
- [ ] Mode type (`inductive ... deriving Repr, BEq, DecidableEq`)
- [ ] Global invariant function
- [ ] Transitions (each with `preserves` proof)
- [ ] StateMachine + `WellFormed` theorem
- [ ] FDIR theorems: Always (safety), Eventually (detection), Leads (recovery)
- [ ] `SubSystemSpec sm` bundle (Kripke-generalized: pass the state machine, not `S D inv`)
- [ ] `SubSystemVVBundle` with component records
- [ ] `VColumn` + integration into `VMatrix`
- [ ] `VMatrix.Complete` proof update
- [ ] (Optional) Compose with other subsystems via `SubSystemSpec.compose`
- [ ] (Optional) `TypeTag` enum + `Interpretation` per `docs/InterpretationPattern.md`

If `lake build` passes with zero `sorry`, you're done.