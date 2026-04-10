import VerifiedMBSE
import Examples.Spacecraft.AOCS
import Examples.Spacecraft.TCS

/-!
# TT&C (Telemetry, Tracking & Command): 4列目の V 字カラム

## フレームワーク拡張性の実証

TT&C を追加することで、EPS/AOCS/TCS で確立したパターン
（PartDef → StateMachine → VVRecord → VColumn）が
任意のサブシステムに対して反復適用可能であることを示す。

## EPS/AOCS/TCS/TTC の不変条件の比較

```
         EPS                AOCS               TCS                TTC (本モジュール)
不変条件  fun _ v => v≤1000   fun _ e => e≤36000  mode-dependent     fun _ m => m≤200
         ─── モード無依存 ── ─── モード無依存 ── ─ モード依存 ────── ── モード無依存 ──
```

TTC はモード無依存不変条件（EPS と同型）。
4サブシステム間の電力バジェット制約を拡張する。

## TT&C の物理的背景

- Transponder: 送受信機（S-band / X-band）
- Antenna: パラボラまたはパッチアンテナ
- データ型: linkMargin (Nat, 単位: dB×10. 100 = 10.0 dB)
- 不変条件: linkMargin ≤ 200 (リンクマージン 20 dB 以下)

## References
- ECSS-E-ST-50C: Communications
- Wertz et al. (2011): Space Mission Engineering, Ch.13 (Communications)
-/

open VerifiedMBSE.Core
open VerifiedMBSE.Core
open VerifiedMBSE.Behavior
open Examples.Spacecraft.TCS
open VerifiedMBSE.VV

namespace Examples.Spacecraft.TTC
open Examples.Spacecraft.EPS

-- ============================================================
-- §1  TT&C コンポーネントの構造定義 (PartDef)
-- ============================================================

/-- RF データポートの KerML 型 -/
def RFPort : KerMLType := { name := some "RFPort" }

/-- RF データポートの共役型 -/
def ConjRFPort : KerMLType := { name := some "~RFPort" }

/-- RF ポートの共役関係 -/
def rfConjugation : Conjugation where
  original   := RFPort
  conjugated := ConjRFPort

/-- RF ポートの互換性 -/
def rfCompatible : compatible RFPort ConjRFPort :=
  ⟨rfConjugation, rfl, rfl⟩

-- §1b  PortDef 定義

/-- Transponder の RF 出力ポート -/
def rfOutPort : PortDef :=
  { feature  := { name := some "rfOut", lower := 1, upper := 1, direction := .out }
    flowType := RFPort }

/-- Antenna の RF 入力ポート -/
def rfInPort : PortDef :=
  { feature  := { name := some "rfIn", lower := 1, upper := 1, direction := .in_ }
    flowType := ConjRFPort }

-- §1c  PartDef 定義

/-- Transponder: 送受信機. -/
def Transponder : PartDef :=
  { baseType  := { name := some "Transponder" }
    ports     := [rfOutPort]
    invariant := True }

/-- Antenna: アンテナ. -/
def Antenna : PartDef :=
  { baseType  := { name := some "Antenna" }
    ports     := [rfInPort]
    invariant := True }

-- §1d  PortRef と Connector

def transponderRFOutRef : PortRef :=
  { part := Transponder, port := rfOutPort
    mem  := by simp [Transponder] }

def antennaRFInRef : PortRef :=
  { part := Antenna, port := rfInPort
    mem  := by simp [Antenna] }

/-- Transponder → Antenna の RF 信号接続 -/
def rfConnector : Connector :=
  { source     := transponderRFOutRef
    target     := antennaRFInRef
    compatible := rfCompatible }

-- §1e  System 定義

/-- TT&C サブシステム: Transponder + Antenna -/
def TTCSystem : System :=
  { parts      := [Transponder, Antenna]
    connectors := [rfConnector] }

/-- TT&C システムの型安全性. -/
theorem TTCSystem_WellFormed : TTCSystem.WellFormed := by
  intro c hc
  simp only [TTCSystem] at hc
  simp only [List.mem_singleton] at hc
  subst hc
  exact ⟨by simp [TTCSystem, rfConnector, transponderRFOutRef],
         by simp [TTCSystem, rfConnector, antennaRFInRef]⟩

-- ============================================================
-- §2  TT&C 状態機械
-- ============================================================

/-- TT&C のモード.
    Nominal:  全機能動作（送受信）
    LowRate:  低ビットレート（省電力、コマンド応答のみ）
    Fault:    故障（通信断）                                     -/
inductive TTCMode where
  | nominal
  | lowRate
  | fault
  deriving Repr, BEq, DecidableEq

/-- TT&C のグローバル不変条件:
    リンクマージンは 200 (20.0 dB) 以下.                         -/
def ttcGlobalInv : TTCMode → Nat → Prop := fun _ m => m ≤ 200

/-- effect = id の場合の不変条件保存.                             -/
private theorem ttcGlobal_preserves (src tgt : TTCMode) (g : Nat → Prop) :
    ∀ m : Nat, g m → ttcGlobalInv src m → ttcGlobalInv tgt (id m) :=
  fun _ _ h => h

/-- Nominal → LowRate: 低ビットレートモードへの移行.             -/
def ttcNominalToLowRate : Transition TTCMode Nat ttcGlobalInv where
  source   := .nominal
  target   := .lowRate
  guard    := fun _ => True
  effect   := id
  preserves := ttcGlobal_preserves .nominal .lowRate (fun _ => True)

/-- LowRate → Fault: 通信断.                                     -/
def ttcLowRateToFault : Transition TTCMode Nat ttcGlobalInv where
  source   := .lowRate
  target   := .fault
  guard    := fun _ => True
  effect   := id
  preserves := ttcGlobal_preserves .lowRate .fault (fun _ => True)

/-- Fault → LowRate: 通信復旧.                                   -/
def ttcFaultToLowRate : Transition TTCMode Nat ttcGlobalInv where
  source   := .fault
  target   := .lowRate
  guard    := fun _ => True
  effect   := id
  preserves := ttcGlobal_preserves .fault .lowRate (fun _ => True)

/-- LowRate → Nominal: 全機能復帰.                               -/
def ttcLowRateToNominal : Transition TTCMode Nat ttcGlobalInv where
  source   := .lowRate
  target   := .nominal
  guard    := fun _ => True
  effect   := id
  preserves := ttcGlobal_preserves .lowRate .nominal (fun _ => True)

/-- TT&C 状態機械: 初期状態 Nominal, 4 遷移.                    -/
def ttcSM : StateMachine TTCMode Nat ttcGlobalInv where
  initialState := .nominal
  transitions  := [ ttcNominalToLowRate
                   , ttcLowRateToFault
                   , ttcFaultToLowRate
                   , ttcLowRateToNominal ]

/-- TT&C 状態機械は整合的:
    初期値 linkMargin = 120 (12.0 dB) で不変条件成立.            -/
theorem ttcSM_WellFormed : ttcSM.WellFormed :=
  ⟨120, by unfold ttcGlobalInv; omega⟩

-- ============================================================
-- §3  FDIR 定理
-- ============================================================

/-- R1: 安全性.
    到達可能な全状態でリンクマージン ≤ 200.                       -/
theorem ttc_always_safe :
    Always ttcSM (fun _ m => m ≤ 200) :=
  fun _ _ h => h.inv_holds

/-- R2: Fault 到達可能性.                                        -/
theorem ttc_fault_reachable :
    Reachable ttcSM .fault 120 :=
  Reachable.step ttcLowRateToFault
    (Reachable.step ttcNominalToLowRate
      (Reachable.init 120 (by unfold ttcGlobalInv; omega))
      (by simp [ttcSM])
      rfl
      trivial)
    (by simp [ttcSM])
    rfl
    trivial

/-- R2: Fault 状態は到達可能 (Eventually).                       -/
theorem ttc_eventually_fault :
    Eventually ttcSM (fun s _ => s = .fault) :=
  ⟨.fault, 120, ttc_fault_reachable, rfl⟩

/-- R3: Fault → LowRate 復旧可能性 (Leads).                      -/
theorem ttc_fault_leads_to_lowRate :
    Leads ttcSM (fun s _ => s = .fault) (fun s _ => s = .lowRate) := by
  intro s m hr hs
  subst hs
  exact ⟨.lowRate, m,
    Reachable.step ttcFaultToLowRate hr (by simp [ttcSM]) rfl trivial,
    rfl⟩

/-- TT&C FDIR 仕様の統合.                                        -/
theorem ttcSM_satisfies_FDIR :
    FDIRSpec ttcSM
      (fun s => s = .fault)
      (fun s => s = .lowRate)
      (fun m => m ≤ 200) :=
  { safety    := ttc_always_safe
    detection := ttc_eventually_fault
    recovery  := ttc_fault_leads_to_lowRate }

-- ============================================================
-- §4  電力バジェット: 4 サブシステム拡張
-- ============================================================

/-- TT&C のモード別消費電力 (単位: W). -/
def ttcModePower : TTCMode → Nat
  | .nominal => 40
  | .lowRate => 20
  | .fault   => 5

open VerifiedMBSE.Behavior Examples.Spacecraft.AOCS in
/-- 4 サブシステム電力バジェット制約.
    最悪ケース: EPS-Nom(100) + AOCS-Nom(200) + TCS-Cold(150) + TTC-Nom(40)
              = 490 ≤ 500 (マージン 10W)                          -/
def FullPowerBudgetOK
    (em : EPSMode) (am : AOCSMode) (tm : TCSMode) (cm : TTCMode) : Prop :=
  epsModePower em + aocsModePower am + tcsModePower tm + ttcModePower cm
    ≤ totalPowerBudget

open VerifiedMBSE.Behavior Examples.Spacecraft.AOCS in
/-- 4 サブシステム電力バジェットは全モード組み合わせで満足.
    3×4×4×3 = 144 通りの全列挙.                                 -/
theorem allModes_fullPowerBudget :
    ∀ (em : EPSMode) (am : AOCSMode) (tm : TCSMode) (cm : TTCMode),
    FullPowerBudgetOK em am tm cm := by
  intro em am tm cm
  cases em <;> cases am <;> cases tm <;> cases cm <;>
    simp only [FullPowerBudgetOK, epsModePower, aocsModePower,
               tcsModePower, ttcModePower, totalPowerBudget] <;>
    omega

open VerifiedMBSE.Behavior Examples.Spacecraft.AOCS in
/-- 最悪ケースのマージン: 500 - 490 = 10W.                       -/
theorem worstCase_fullPowerMargin :
    totalPowerBudget -
      (epsModePower .nominal + aocsModePower .nominal +
       tcsModePower .coldCase + ttcModePower .nominal) = 10 := by
  simp [totalPowerBudget, epsModePower, aocsModePower,
        tcsModePower, ttcModePower]

-- ============================================================
-- §5  VVRecord: TT&C の V 字モデル記録
-- ============================================================

/-- TT&C R1: リンクマージン安全性の VVRecord (system). -/
def ttc_r1_VVRecord : VVRecord :=
  { layer        := .system
    spec_name    := "TTC-R1-Safety"
    verification := Always ttcSM (fun _ m => m ≤ 200)
    verified     := ttc_always_safe
    validation   := ValidationTrace.init (.trusted ttc_always_safe) }

/-- TT&C R3: 故障復旧の VVRecord (system). -/
def ttc_r3_VVRecord : VVRecord :=
  { layer        := .system
    spec_name    := "TTC-R3-Recovery"
    verification := Leads ttcSM
                      (fun s _ => s = .fault)
                      (fun s _ => s = .lowRate)
    verified     := ttc_fault_leads_to_lowRate
    validation   := ValidationTrace.init (.trusted ttc_fault_leads_to_lowRate) }

open VerifiedMBSE.Behavior Examples.Spacecraft.AOCS in
/-- 4 サブシステム電力バジェットの VVRecord (system). -/
def fullPowerBudget_VVRecord : VVRecord :=
  { layer        := .system
    spec_name    := "SYS-FullPowerBudget-AllModes"
    verification := ∀ (em : EPSMode) (am : AOCSMode) (tm : TCSMode) (cm : TTCMode),
                      FullPowerBudgetOK em am tm cm
    verified     := allModes_fullPowerBudget
    validation   := ValidationTrace.init (.trusted allModes_fullPowerBudget) }

/-- TT&C S1: WellFormed の VVRecord (subsystem). -/
def ttc_sub_wellformed_VVRecord : VVRecord :=
  { layer        := .subsystem
    spec_name    := "TTC-S1-WellFormed"
    verification := TTCSystem.WellFormed
    verified     := TTCSystem_WellFormed
    validation   := ValidationTrace.init (.trusted TTCSystem_WellFormed) }

/-- Transponder コンポーネントの VVRecord. -/
theorem transponder_inv_holds : Transponder.invariant := trivial

def ttc_comp_transponder_VVRecord : VVRecord :=
  { layer        := .component
    spec_name    := "TTC-C1-Transponder-Invariant"
    verification := Transponder.invariant
    verified     := transponder_inv_holds
    validation   := ValidationTrace.init (.trusted transponder_inv_holds) }

/-- Antenna コンポーネントの VVRecord. -/
theorem antenna_inv_holds : Antenna.invariant := trivial

def ttc_comp_antenna_VVRecord : VVRecord :=
  { layer        := .component
    spec_name    := "TTC-C2-Antenna-Invariant"
    verification := Antenna.invariant
    verified     := antenna_inv_holds
    validation   := ValidationTrace.init (.trusted antenna_inv_holds) }

-- ============================================================
-- §6  4 サブシステム統合
-- ============================================================

open Examples.Spacecraft.AOCS in
/-- EPS + AOCS + TCS + TTC の統合システム. -/
def FullSatelliteSystem4 : System :=
  System.compose
    (System.compose
      (System.compose EPSSystem AOCSSystem [])
      TCSSystem [])
    TTCSystem
    []

open Examples.Spacecraft.AOCS in
/-- 4 サブシステム統合の WellFormed. -/
theorem FullSatelliteSystem4_WellFormed : FullSatelliteSystem4.WellFormed :=
  System.compose_WellFormed
    (System.compose
      (System.compose EPSSystem AOCSSystem [])
      TCSSystem [])
    TTCSystem
    []
    (System.compose_WellFormed
      (System.compose EPSSystem AOCSSystem [])
      TCSSystem []
      (System.compose_WellFormed EPSSystem AOCSSystem []
        EPSSystem_WellFormed AOCSSystem_WellFormed
        (fun _ hc => by simp at hc))
      TCSSystem_WellFormed
      (fun _ hc => by simp at hc))
    TTCSystem_WellFormed
    (fun _ hc => by simp at hc)

open Examples.Spacecraft.AOCS in
/-- 統合システムの部品数: EPS(2) + AOCS(3) + TCS(3) + TTC(2) = 10. -/
theorem FullSatelliteSystem4_parts_count :
    FullSatelliteSystem4.parts.length = 10 := by
  simp [FullSatelliteSystem4, System.compose,
        EPSSystem, AOCSSystem, TCSSystem, TTCSystem]

-- ============================================================
-- §7  TTC の SubSystemSpec 化
-- ============================================================

/-!
## §7 SubSystemSpec によるパラメトリック化

TTC は EPS と同型のモード無依存不変条件を持つ.
SubSystemSpec 化は直接的.
-/

open VerifiedMBSE.VV

/-- TTC の StructuralSpec.
    Transponder + Antenna. -/
def ttcStructural : StructuralSpec :=
  StructuralSpec.mk' "TTC"
    [Transponder, Antenna]
    [rfConnector]
    TTCSystem_WellFormed

/-- ttcStructural の system は TTCSystem と一致. -/
theorem ttcStructural_system_eq :
    ttcStructural.system = TTCSystem := rfl

/-- TTC の BehavioralSpec.
    ttcSM: 3 モード, 4 遷移. -/
def ttcBehavioral : BehavioralSpec TTCMode Nat ttcGlobalInv :=
  { sm := ttcSM
    wellFormed := ttcSM_WellFormed }

/-- TTC の FDIRBundle.
    isFault = .fault, isRecovery = .lowRate, isSafe = (≤ 200). -/
def ttcFDIR : FDIRBundle ttcSM :=
  { isFault    := fun s => s = .fault
    isRecovery := fun s => s = .lowRate
    isSafe     := fun m => m ≤ 200
    safety     := ttc_always_safe
    detection  := ttc_eventually_fault
    recovery   := ttc_fault_leads_to_lowRate }

/-- TTC の SubSystemSpec. -/
def ttcSpec : SubSystemSpec TTCMode Nat ttcGlobalInv :=
  { structural := ttcStructural
    behavioral := ttcBehavioral
    fdir       := ttcFDIR }

/-- TTC の SubSystemSpec は FDIRSpec を導出できる. -/
theorem ttcSpec_fdir :
    FDIRSpec ttcSM
      (fun s => s = .fault)
      (fun s => s = .lowRate)
      (fun m => m ≤ 200) :=
  ttcSpec.fdir_derivable

/-- TTC の SubSystemSpec から自動導出された R1 VVRecord. -/
def ttcSpec_r1_VVRecord : VVRecord := ttcSpec.safetyRecord

/-- TTC の SubSystemSpec から自動導出された R3 VVRecord. -/
def ttcSpec_r3_VVRecord : VVRecord := ttcSpec.recoveryRecord

/-- TTC の SubSystemSpec から自動導出された S1 VVRecord. -/
def ttcSpec_s1_VVRecord : VVRecord := ttcSpec.subsystemRecord

/-- 自動導出された R1 の spec_name は "TTC-R1-Safety". -/
theorem ttcSpec_r1_name :
    ttcSpec_r1_VVRecord.spec_name = "TTC-R1-Safety" := rfl

/-- 自動導出された S1 の spec_name は "TTC-S1-WellFormed". -/
theorem ttcSpec_s1_name :
    ttcSpec_s1_VVRecord.spec_name = "TTC-S1-WellFormed" := rfl

/-- TTC のモード別消費電力 (SubSystemSpec 内の定義). -/
private def ttcModePower' : TTCMode → Nat
  | .nominal => 40
  | .lowRate => 20
  | .fault   => 5

/-- TTC の ModePowerSpec. -/
def ttcModePowerSpec : ModePowerSpec TTCMode :=
  { modePower := ttcModePower'
    maxPower  := 40
    maxPower_bound := by
      intro s; cases s <;> simp [ttcModePower'] }

/-- TTC の SubSystemVVBundle.
    extraSystemRecords に 4 サブシステム電力バジェットを追加. -/
def ttcVVBundle : SubSystemVVBundle ttcSpec :=
  { componentRecords :=
      [ mkComponentRecord "TTC" 1 Transponder trivial
      , mkComponentRecord "TTC" 2 Antenna trivial ]
    extraSystemRecords :=
      [ fullPowerBudget_VVRecord ] }

/-- TTC VVBundle の全 VVRecord 数は 6.
    コンポーネント(2) + サブシステム(1) + R1(1) + R3(1)
    + extra(4サブシステム電力 = 1) = 6. -/
theorem ttcVVBundle_count :
    ttcVVBundle.allRecords.length = 6 := by
  simp [SubSystemVVBundle.allRecords, ttcVVBundle]

-- ============================================================
-- TODO:
-- [✅] TT&C コンポーネントの PartDef (Transponder, Antenna)
-- [✅] ポート定義 (RFPort + 共役)
-- [✅] TTCSystem + WellFormed
-- [✅] 状態機械 (3 モード, 4 遷移)
-- [✅] 安全性定理 (ttc_always_safe)
-- [✅] FDIR 定理 (R1, R2, R3)
-- [✅] 4 サブシステム電力バジェット (144 ケース全証明)
-- [✅] VVRecord (R1, R3, 電力バジェット, WellFormed, 部品)
-- [✅] 4 サブシステム統合 (FullSatelliteSystem4)
-- [✅] SubSystemSpec 化 ★新規
-- [✅] ModePowerSpec ★新規
-- [✅] SubSystemVVBundle ★新規
-- ============================================================

end Examples.Spacecraft.TTC
