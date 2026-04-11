import VerifiedMBSE.Core.Compose
import VerifiedMBSE.Behavior.FDIR
import VerifiedMBSE.VV.Evidence

/-!
# SubSystemSpec: Parametric Subsystem Abstraction

Defines `StructuralSpec` (structure), `BehavioralSpec` (behavior),
`FDIRBundle` (FDIR proof bundle), and `SubSystemSpec` which integrates all three.
-/

namespace VerifiedMBSE.VV

open VerifiedMBSE.Core
open VerifiedMBSE.Behavior

-- ============================================================
-- §1  StructuralSpec
-- ============================================================

/-- StructuralSpec: structural aspect of a subsystem. -/
structure StructuralSpec where
  /-- Subsystem name -/
  name : String
  /-- List of part definitions -/
  parts : List PartDef
  /-- List of connectors -/
  connectors : List Connector
  /-- System -/
  system : System
  /-- Consistency of system.parts -/
  system_eq_parts : system.parts = parts
  /-- Consistency of system.connectors -/
  system_eq_connectors : system.connectors = connectors
  /-- Structural well-formedness -/
  wellFormed : system.WellFormed

/-- Smart constructor for StructuralSpec. -/
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

/-- Proposition that all part invariants hold. -/
def StructuralSpec.allPartsInvariant (spec : StructuralSpec) : Prop :=
  ∀ p ∈ spec.parts, p.invariant

-- ============================================================
-- §2  BehavioralSpec
-- ============================================================

/-- BehavioralSpec: behavioral aspect of a subsystem. -/
structure BehavioralSpec (S : Type) (D : Type) (inv : S → D → Prop) where
  /-- State machine -/
  sm : StateMachine S D inv
  /-- State machine well-formedness -/
  wellFormed : sm.WellFormed

-- ============================================================
-- §3  FDIRBundle
-- ============================================================

/-- FDIRBundle: proof bundle for FDIR requirements. -/
structure FDIRBundle
    {S D : Type} {inv : S → D → Prop}
    (sm : StateMachine S D inv) where
  /-- Fault state predicate -/
  isFault : S → Prop
  /-- Recovery state predicate -/
  isRecovery : S → Prop
  /-- Data safety condition -/
  isSafe : D → Prop
  /-- R1: Safety □(isSafe d) -/
  safety : Always sm (fun _ d => isSafe d)
  /-- R2: Fault detection ◇(isFault s) -/
  detection : Eventually sm (fun s _ => isFault s)
  /-- R3: Fault recovery □(isFault → ◇ isRecovery) -/
  recovery : Leads sm (fun s _ => isFault s) (fun s _ => isRecovery s)

/-- Conversion from FDIRBundle to FDIRSpec. -/
def FDIRBundle.toFDIRSpec
    {S D : Type} {inv : S → D → Prop}
    {sm : StateMachine S D inv}
    (bundle : FDIRBundle sm) :
    FDIRSpec sm bundle.isFault bundle.isRecovery bundle.isSafe :=
  { safety    := bundle.safety
    detection := bundle.detection
    recovery  := bundle.recovery }

-- ============================================================
-- §4  SubSystemSpec
-- ============================================================

/-- SubSystemSpec: unified subsystem specification integrating structure, behavior, and FDIR.
    Adding a new subsystem requires constructing just one instance of this type. -/
structure SubSystemSpec (S : Type) (D : Type) (inv : S → D → Prop) where
  /-- Structural specification -/
  structural : StructuralSpec
  /-- Behavioral specification -/
  behavioral : BehavioralSpec S D inv
  /-- FDIR proof bundle -/
  fdir : FDIRBundle behavioral.sm

/-- Subsystem name。 -/
def SubSystemSpec.name {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv) : String :=
  spec.structural.name

/-- Get the System. -/
def SubSystemSpec.system {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv) : System :=
  spec.structural.system

/-- Get the StateMachine. -/
def SubSystemSpec.stateMachine {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv) : StateMachine S D inv :=
  spec.behavioral.sm

/-- Consistency: both structural and behavioral parts are WellFormed. -/
def SubSystemSpec.Consistent {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv) : Prop :=
  spec.structural.system.WellFormed ∧ spec.behavioral.sm.WellFormed

/-- Automatic derivation of FDIRSpec. -/
theorem SubSystemSpec.fdir_derivable {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv) :
    FDIRSpec spec.behavioral.sm
      spec.fdir.isFault spec.fdir.isRecovery spec.fdir.isSafe :=
  spec.fdir.toFDIRSpec

-- ============================================================
-- §5  Automatic VVRecord Generation
-- ============================================================

/-- Subsystem-level VVRecord. -/
def SubSystemSpec.subsystemRecord {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv) :
    VVRecord :=
  { layer        := .subsystem
    spec_name    := s!"{spec.structural.name}-S1-WellFormed"
    verification := spec.structural.system.WellFormed
    verified     := spec.structural.wellFormed
    validation   := ValidationTrace.init (.trusted spec.structural.wellFormed) }

/-- System-level VVRecord (R1 Safety). -/
def SubSystemSpec.safetyRecord {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv) :
    VVRecord :=
  { layer        := .system
    spec_name    := s!"{spec.structural.name}-R1-Safety"
    verification := Always spec.behavioral.sm (fun _ d => spec.fdir.isSafe d)
    verified     := spec.fdir.safety
    validation   := ValidationTrace.init (.trusted spec.fdir.safety) }

/-- System-level VVRecord (R3 Recovery). -/
def SubSystemSpec.recoveryRecord {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv) :
    VVRecord :=
  { layer        := .system
    spec_name    := s!"{spec.structural.name}-R3-Recovery"
    verification := Leads spec.behavioral.sm
                      (fun s _ => spec.fdir.isFault s)
                      (fun s _ => spec.fdir.isRecovery s)
    verified     := spec.fdir.recovery
    validation   := ValidationTrace.init (.trusted spec.fdir.recovery) }

-- ============================================================
-- §6  Structural Composition
-- ============================================================

/-- Structurally compose two subsystems. -/
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

/-- The part count of the composed system equals the sum of its parts. -/
theorem StructuralSpec.compose_parts_length
    (s1 s2 : StructuralSpec) (bridge : List Connector)
    (hbridge : ∀ c ∈ bridge,
        c.source.part ∈ s1.system.parts ++ s2.system.parts ∧
        c.target.part ∈ s1.system.parts ++ s2.system.parts) :
    (StructuralSpec.compose s1 s2 bridge hbridge).parts.length =
    s1.system.parts.length + s2.system.parts.length := by
  simp [StructuralSpec.compose, List.length_append]

end VerifiedMBSE.VV
