import VerifiedMBSE.Core.Interpretation
import VerifiedMBSE.Behavior.Temporal

/-!
# FDIR Specification and StateMachineComponent

Defines `FDIRSpec` (a bundle of safety, detection, and recovery requirements)
and `StateMachineComponent`, which integrates structural (`PartDef`) and
behavioral (`StateMachine`) models into a single verified component.
-/

namespace VerifiedMBSE.Behavior

open VerifiedMBSE.Core

-- ============================================================
-- §1  FDIRSpec
-- ============================================================

/-- FDIRSpec: structure bundling three FDIR requirements.
    Constructing a value of this type = mechanized verification of all FDIR requirements. -/
structure FDIRSpec
    {S D : Type} {inv : S → D → Prop}
    (sm : StateMachine S D inv)
    (isFault    : S → Prop)
    (isNominal  : S → Prop)
    (isSafe     : D → Prop) :
    Prop where
  /-- R1 Safety: □(isSafe d) -/
  safety    : Always sm (fun _ d => isSafe d)
  /-- R2 Fault detectability: ◇(isFault s) -/
  detection : Eventually sm (fun s _ => isFault s)
  /-- R3 Fault recoverability: □(isFault s → ◇(isNominal s')) -/
  recovery  : Leads sm (fun s _ => isFault s) (fun s _ => isNominal s)

-- ============================================================
-- §2  StateMachineComponent (Structure + Behavior Integration)
-- ============================================================

/-- SMInvariantCompatible: the state machine invariant implies the PartDef invariant.
    Consistency condition between structural and behavioral models. -/
def SMInvariantCompatible
    (pd  : PartDef)
    (S   : Type)
    (I   : Interpretation)
    (inv : S → I pd.baseType → Prop) : Prop :=
  ∀ (s : S) (d : I pd.baseType), inv s d → pd.invariant

/-- StateMachineComponent: component that adds state machine behavior to a PartDef. -/
structure StateMachineComponent
    (I   : Interpretation)
    (pd  : PartDef)
    (S   : Type)
    (inv : S → I pd.baseType → Prop) where
  /-- Consistency proof -/
  compat : SMInvariantCompatible pd S I inv
  /-- State machine governing the behavior -/
  sm     : StateMachine S (I pd.baseType) inv

/-- Consistency condition for StateMachineComponent. -/
def StateMachineComponent.WellFormed
    {I   : Interpretation}
    {pd  : PartDef}
    {S   : Type}
    {inv : S → I pd.baseType → Prop}
    (smc : StateMachineComponent I pd S inv) : Prop :=
  smc.sm.WellFormed

/-- Phase 2/3 connection theorem: construct a PartInstance from a reachable (state, data) pair. -/
def StateMachineComponent.reachable_gives_instance
    {I   : Interpretation}
    {pd  : PartDef}
    {S   : Type}
    {inv : S → I pd.baseType → Prop}
    (smc : StateMachineComponent I pd S inv)
    {s   : S}
    {d   : I pd.baseType}
    (hr  : Reachable smc.sm s d) :
    PartInstance I pd :=
  { carrier   := d
    inv_holds := smc.compat s d hr.inv_holds }

/-- If WellFormed, a PartInstance exists. -/
noncomputable def StateMachineComponent.wellFormed_gives_instance
    {I   : Interpretation}
    {pd  : PartDef}
    {S   : Type}
    {inv : S → I pd.baseType → Prop}
    (smc : StateMachineComponent I pd S inv)
    (hwf : smc.WellFormed) :
    PartInstance I pd :=
  smc.reachable_gives_instance
    (Reachable.init (Classical.choose hwf) (Classical.choose_spec hwf))

end VerifiedMBSE.Behavior
