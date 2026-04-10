import VerifiedMBSE

/-!
# EPS (Electric Power Subsystem): 電力供給系ケーススタディ

構造モデル（PowerSupply, Load）、状態機械（Nominal/LowPower/Fault）、
FDIR 検証、SubSystemSpec 統合、VVBundle を定義する。
-/

open VerifiedMBSE.Core
open VerifiedMBSE.Behavior
open VerifiedMBSE.VV

namespace Examples.Spacecraft.EPS

-- ============================================================
-- §1  構造定義
-- ============================================================

/-- 電力ポートの KerML 型 -/
def EPSPowerPort     : KerMLType := { name := some "PowerPort" }
def EPSConjPowerPort : KerMLType := { name := some "~PowerPort" }

def epsPowerConjugation : Conjugation where
  original   := EPSPowerPort
  conjugated := EPSConjPowerPort

def epsPowerCompatible : compatible EPSPowerPort EPSConjPowerPort :=
  ⟨epsPowerConjugation, rfl, rfl⟩

def pwrOutPort : PortDef :=
  { feature  := { name := some "pwr", lower := 1, upper := 1, direction := .out }
    flowType := EPSPowerPort }

def pwrInPort : PortDef :=
  { feature  := { name := some "pwr", lower := 1, upper := 1, direction := .in_ }
    flowType := EPSConjPowerPort }

/-- 電力供給器 -/
def PowerSupply : PartDef :=
  { baseType  := { name := some "PowerSupply" }
    ports     := [pwrOutPort]
    invariant := True }

/-- 電力負荷 -/
def Load : PartDef :=
  { baseType  := { name := some "Load" }
    ports     := [pwrInPort]
    invariant := True }

def psPortRef : PortRef :=
  { part := PowerSupply, port := pwrOutPort
    mem  := by simp [PowerSupply] }

def loadPortRef : PortRef :=
  { part := Load, port := pwrInPort
    mem  := by simp [Load] }

def powerConnector : Connector :=
  { source     := psPortRef
    target     := loadPortRef
    compatible := epsPowerCompatible }

/-- EPS サブシステム -/
def EPSSystem : System :=
  { parts      := [PowerSupply, Load]
    connectors := [powerConnector] }

/-- EPS システムの WellFormed -/
theorem EPSSystem_WellFormed : EPSSystem.WellFormed := by
  intro c hc
  simp only [EPSSystem] at hc
  simp only [List.mem_singleton] at hc
  subst hc
  exact ⟨by simp [EPSSystem, powerConnector, psPortRef],
         by simp [EPSSystem, powerConnector, loadPortRef]⟩

-- ============================================================
-- §2  EPS 状態機械
-- ============================================================

/-- EPS の制御状態 -/
inductive EPSMode where
  | nominal   -- 通常動作 (28.0V)
  | lowPower  -- 低電力モード (18.0V)
  | fault     -- 故障モード
  deriving Repr, BEq, DecidableEq

/-- EPS のグローバル安全性不変条件：全モードで v ≤ 1000 -/
def epsGlobalInv : EPSMode → Nat → Prop := fun _ v => v ≤ 1000

private theorem epsGlobal_preserves (src tgt : EPSMode) (g : Nat → Prop) :
    ∀ v : Nat, g v → epsGlobalInv src v → epsGlobalInv tgt (id v) :=
  fun _ _ h => h

def epsNominalToLowPower : Transition EPSMode Nat epsGlobalInv where
  source := .nominal; target := .lowPower
  guard := fun _ => True; effect := id
  preserves := epsGlobal_preserves .nominal .lowPower (fun _ => True)

def epsLowPowerToFault : Transition EPSMode Nat epsGlobalInv where
  source := .lowPower; target := .fault
  guard := fun _ => True; effect := id
  preserves := epsGlobal_preserves .lowPower .fault (fun _ => True)

def epsFaultToLowPower : Transition EPSMode Nat epsGlobalInv where
  source := .fault; target := .lowPower
  guard := fun _ => True; effect := id
  preserves := epsGlobal_preserves .fault .lowPower (fun _ => True)

def epsLowPowerToNominal : Transition EPSMode Nat epsGlobalInv where
  source := .lowPower; target := .nominal
  guard := fun _ => True; effect := id
  preserves := epsGlobal_preserves .lowPower .nominal (fun _ => True)

/-- EPS 状態機械 -/
def epsSM : StateMachine EPSMode Nat epsGlobalInv where
  initialState := .nominal
  transitions  := [ epsNominalToLowPower, epsLowPowerToFault,
                     epsFaultToLowPower, epsLowPowerToNominal ]

theorem epsSM_WellFormed : epsSM.WellFormed :=
  ⟨280, by unfold epsGlobalInv; omega⟩

-- ============================================================
-- §3  安全性と FDIR
-- ============================================================

/-- R1: □(v ≤ 1000) -/
theorem eps_always_safe :
    Always epsSM (fun _ v => v ≤ 1000) :=
  fun _ _ h => h.inv_holds

/-- R2 補題: Fault 到達パスの構成 -/
theorem eps_fault_reachable :
    Reachable epsSM .fault 280 :=
  Reachable.step epsLowPowerToFault
    (Reachable.step epsNominalToLowPower
      (Reachable.init 280 (by unfold epsGlobalInv; omega))
      (by simp [epsSM]) rfl trivial)
    (by simp [epsSM]) rfl trivial

/-- R2: ◇(fault) -/
theorem eps_eventually_fault :
    Eventually epsSM (fun s _ => s = .fault) :=
  ⟨.fault, 280, eps_fault_reachable, rfl⟩

/-- R3: □(fault → ◇ lowPower) -/
theorem eps_fault_leads_to_lowPower :
    Leads epsSM (fun s _ => s = .fault) (fun s _ => s = .lowPower) := by
  intro s d hr hs; subst hs
  exact ⟨.lowPower, d,
    Reachable.step epsFaultToLowPower hr (by simp [epsSM]) rfl trivial, rfl⟩

/-- FDIR 仕様全体の機械検証 -/
theorem epsSM_satisfies_FDIR :
    FDIRSpec epsSM
      (fun s => s = .fault) (fun s => s = .lowPower) (fun v => v ≤ 1000) :=
  { safety    := eps_always_safe
    detection := eps_eventually_fault
    recovery  := eps_fault_leads_to_lowPower }

-- ============================================================
-- §4  SubSystemSpec
-- ============================================================

def epsStructural : StructuralSpec :=
  StructuralSpec.mk' "EPS" [PowerSupply, Load] [powerConnector]
    EPSSystem_WellFormed

def epsBehavioral : BehavioralSpec EPSMode Nat epsGlobalInv :=
  { sm := epsSM, wellFormed := epsSM_WellFormed }

def epsFDIR : FDIRBundle epsSM :=
  { isFault    := fun s => s = .fault
    isRecovery := fun s => s = .lowPower
    isSafe     := fun v => v ≤ 1000
    safety     := eps_always_safe
    detection  := eps_eventually_fault
    recovery   := eps_fault_leads_to_lowPower }

/-- EPS の SubSystemSpec -/
def epsSpec : SubSystemSpec EPSMode Nat epsGlobalInv :=
  { structural := epsStructural
    behavioral := epsBehavioral
    fdir       := epsFDIR }

-- ============================================================
-- §5  ModePowerSpec と VVBundle
-- ============================================================

private def epsModePower' : EPSMode → Nat
  | .nominal  => 100
  | .lowPower => 50
  | .fault    => 20

def epsModePowerSpec : ModePowerSpec EPSMode :=
  { modePower := epsModePower'
    maxPower  := 100
    maxPower_bound := by intro s; cases s <;> simp [epsModePower'] }

/-- EPS の VVBundle -/
def epsVVBundle : SubSystemVVBundle epsSpec :=
  { componentRecords :=
      [ mkComponentRecord "EPS" 1 PowerSupply trivial
      , mkComponentRecord "EPS" 2 Load trivial ] }

/-- EPS VVBundle は 5 レコード -/
theorem epsVVBundle_count :
    epsVVBundle.allRecords.length = 5 := by
  simp [SubSystemVVBundle.allRecords, epsVVBundle]

-- ============================================================
-- §6  StateMachineComponent (Phase 2/3 接続)
-- ============================================================

def EPSNatInterpretation : Interpretation := fun t =>
  match t.name with
  | some "PowerSupply" => Nat | some "Load" => Nat
  | some "PowerPort"   => Nat | some "~PowerPort" => Nat
  | _ => Unit

def epsStateMachineComponent :
    StateMachineComponent EPSNatInterpretation PowerSupply EPSMode epsGlobalInv :=
  { compat := fun _ _ _ => trivial, sm := epsSM }

end Examples.Spacecraft.EPS
