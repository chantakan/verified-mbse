import VerifiedMBSE
import Examples.Spacecraft.AOCS

/-!
# TCS (Thermal Control System): モード依存不変条件の実証

## EPS/AOCS との不変条件の比較

```
         EPS                AOCS               TCS (本モジュール)
不変条件  fun _ v => v≤1000   fun _ e => e≤36000  fun mode t => modeDependent mode t
         ─── モード無依存 ── ─── モード無依存 ── ─── モード依存 ───────────────────
```

EPS/AOCS のグローバル不変条件は状態に依存しない:
  `fun _ v => v ≤ 1000`  (全モードで同一の上界)

TCS の不変条件は状態に **依存する** (genuine dependent type):
  Nominal:  150 ≤ temp ∧ temp ≤ 450  (20°C–45°C の運用温度範囲)
  ColdCase: temp ≤ 250               (ヒーター動作中の低温側)
  HotCase:  350 ≤ temp ∧ temp ≤ 650  (ラジエーター動作中の高温側)
  Survival: temp ≤ 1000              (生存温度範囲)

このとき Safety 定理 `Reachable.inv_holds` の型は:
  ∀ mode temp, Reachable tcsSM mode temp → tcsInvariant mode temp

「保証される性質の型自体が、到達したモードに依存する」
── これが依存型理論を SysML v2 に適用する本質的な動機である。

## TCS の物理的背景

- Thermistor: 温度センサー (精度 ~0.5°C)
- Heater: 抵抗加熱素子 (ON/OFF 制御)
- ThermalController: 温度読取 → ヒーター/ラジエーター制御

データ型: Nat (温度, 単位: decidegree. 100 = 10.0°C)
隣接モード間にオーバーラップ区間を設け, 遷移時の
ガード条件で次モードの不変条件が自然に満たされる設計.

## References
- ECSS-E-ST-31C: Thermal control general requirements
- Wertz et al. (2011): Space Mission Engineering, Ch.11 (Thermal)
-/

open VerifiedMBSE.Core
open VerifiedMBSE.Core
open VerifiedMBSE.Behavior
open VerifiedMBSE.VV

namespace Examples.Spacecraft.TCS
open Examples.Spacecraft.EPS

-- ============================================================
-- §1  TCS コンポーネントの構造定義 (PartDef)
-- ============================================================

/-- 温度データポートの KerML 型 -/
def TemperaturePort : KerMLType := { name := some "TemperaturePort" }

/-- 温度データポートの共役型 -/
def ConjTemperaturePort : KerMLType := { name := some "~TemperaturePort" }

/-- ヒーター指令ポートの KerML 型 -/
def HeaterCmdPort : KerMLType := { name := some "HeaterCmdPort" }

/-- ヒーター指令ポートの共役型 -/
def ConjHeaterCmdPort : KerMLType := { name := some "~HeaterCmdPort" }

/-- 温度ポートの共役関係 -/
def temperatureConjugation : Conjugation where
  original   := TemperaturePort
  conjugated := ConjTemperaturePort

/-- ヒーター指令ポートの共役関係 -/
def heaterCmdConjugation : Conjugation where
  original   := HeaterCmdPort
  conjugated := ConjHeaterCmdPort

/-- 温度ポートの互換性 -/
def temperatureCompatible : compatible TemperaturePort ConjTemperaturePort :=
  ⟨temperatureConjugation, rfl, rfl⟩

/-- ヒーター指令ポートの互換性 -/
def heaterCmdCompatible : compatible HeaterCmdPort ConjHeaterCmdPort :=
  ⟨heaterCmdConjugation, rfl, rfl⟩

-- ============================================================
-- §1b  PortDef 定義
-- ============================================================

/-- Thermistor の温度出力ポート -/
def tempOutPort : PortDef :=
  { feature  := { name := some "tempOut", lower := 1, upper := 1, direction := .out }
    flowType := TemperaturePort }

/-- ThermalController のセンサー入力ポート -/
def tempSensorInPort : PortDef :=
  { feature  := { name := some "tempSensorIn", lower := 1, upper := 1, direction := .in_ }
    flowType := ConjTemperaturePort }

/-- ThermalController のヒーター指令出力ポート -/
def heaterCmdOutPort : PortDef :=
  { feature  := { name := some "heaterCmdOut", lower := 1, upper := 1, direction := .out }
    flowType := HeaterCmdPort }

/-- Heater の指令入力ポート -/
def heaterCmdInPort : PortDef :=
  { feature  := { name := some "heaterCmdIn", lower := 1, upper := 1, direction := .in_ }
    flowType := ConjHeaterCmdPort }

-- ============================================================
-- §1c  PartDef 定義
-- ============================================================

/-- Thermistor: 温度センサー. -/
def Thermistor : PartDef :=
  { baseType  := { name := some "Thermistor" }
    ports     := [tempOutPort]
    invariant := True }

/-- Heater: 抵抗加熱素子. -/
def Heater : PartDef :=
  { baseType  := { name := some "Heater" }
    ports     := [heaterCmdInPort]
    invariant := True }

/-- ThermalController: 温度制御演算器. センサー入力とヒーター指令出力. -/
def ThermalController : PartDef :=
  { baseType  := { name := some "ThermalController" }
    ports     := [tempSensorInPort, heaterCmdOutPort]
    invariant := True }

-- ============================================================
-- §1d  PortRef と Connector
-- ============================================================

def thermTempOutRef : PortRef :=
  { part := Thermistor, port := tempOutPort
    mem  := by simp [Thermistor] }

def tcSensorInRef : PortRef :=
  { part := ThermalController, port := tempSensorInPort
    mem  := by simp [ThermalController] }

def tcHeaterCmdOutRef : PortRef :=
  { part := ThermalController, port := heaterCmdOutPort
    mem  := by simp [ThermalController] }

def heaterCmdInRef : PortRef :=
  { part := Heater, port := heaterCmdInPort
    mem  := by simp [Heater] }

/-- Thermistor → ThermalController の温度データ接続 -/
def tempSensorConnector : Connector :=
  { source     := thermTempOutRef
    target     := tcSensorInRef
    compatible := temperatureCompatible }

/-- ThermalController → Heater のヒーター指令接続 -/
def heaterCmdConnector : Connector :=
  { source     := tcHeaterCmdOutRef
    target     := heaterCmdInRef
    compatible := heaterCmdCompatible }

-- ============================================================
-- §1e  System 定義
-- ============================================================

/-- TCS サブシステム: Thermistor + ThermalController + Heater -/
def TCSSystem : System :=
  { parts      := [Thermistor, ThermalController, Heater]
    connectors := [tempSensorConnector, heaterCmdConnector] }

/-- TCS システムの型安全性 (WellFormed). -/
theorem TCSSystem_WellFormed : TCSSystem.WellFormed := by
  intro c hc
  simp only [TCSSystem] at hc
  simp at hc
  rcases hc with rfl | rfl
  · exact ⟨by simp [TCSSystem, tempSensorConnector, thermTempOutRef],
           by simp [TCSSystem, tempSensorConnector, tcSensorInRef]⟩
  · exact ⟨by simp [TCSSystem, heaterCmdConnector, tcHeaterCmdOutRef],
           by simp [TCSSystem, heaterCmdConnector, heaterCmdInRef]⟩

-- ============================================================
-- §2  TCS 状態機械: モード依存不変条件
-- ============================================================

/-!
## §2 の設計: モード依存不変条件

TCS の制御モード:
  Nominal:  定常運用 (20°C–45°C)
  ColdCase: 低温ケース (ヒーター ON, ≤25°C)
  HotCase:  高温ケース (ラジエーター動作, 35°C–65°C)
  Survival: 生存モード (≤100°C, 故障時の最大許容範囲)

隣接モード間のオーバーラップ:
  Nominal [150–450] ∩ ColdCase [0–250] = [150–250]  (遷移ゾーン)
  Nominal [150–450] ∩ HotCase  [350–650] = [350–450] (遷移ゾーン)

遷移のガード条件がオーバーラップ区間を指定することで,
`effect = id` でもターゲットモードの不変条件が自然に成立する.
-/

/-- TCS の制御モード -/
inductive TCSMode where
  | nominal   -- 定常運用 (150–450, つまり 15.0°C–45.0°C)
  | coldCase  -- 低温ケース (0–250, つまり 0.0°C–25.0°C)
  | hotCase   -- 高温ケース (350–650, つまり 35.0°C–65.0°C)
  | survival  -- 生存モード (0–1000, つまり 0.0°C–100.0°C)
  deriving Repr, BEq, DecidableEq

/-- TCS のモード依存不変条件.

    **これが EPS/AOCS との決定的な差異:**
    不変条件の型自体がモードに依存する (genuine dependent type).

    EPS:  `fun _ v => v ≤ 1000`         ← モードを無視
    AOCS: `fun _ err => err ≤ 36000`    ← モードを無視
    TCS:  `fun mode temp => ...mode...` ← **モードが型を決定**       -/
def tcsInvariant : TCSMode → Nat → Prop
  | .nominal,  temp => 150 ≤ temp ∧ temp ≤ 450
  | .coldCase, temp => temp ≤ 250
  | .hotCase,  temp => 350 ≤ temp ∧ temp ≤ 650
  | .survival, temp => temp ≤ 1000

-- ============================================================
-- §2a  遷移の定義
-- ============================================================

/-- Nominal → ColdCase: 温度低下による低温モード移行.
    ガード: temp ≤ 250 (Nominal∩ColdCase のオーバーラップ). -/
def tcsNomToCold : Transition TCSMode Nat tcsInvariant where
  source   := .nominal
  target   := .coldCase
  guard    := fun temp => temp ≤ 250
  effect   := id
  preserves := fun _temp hguard _hinv => by simp only [tcsInvariant, id] at *; omega

/-- ColdCase → Nominal: ヒーター加熱による温度回復.
    ガード: 150 ≤ temp (ColdCase∩Nominal のオーバーラップ). -/
def tcsColdToNom : Transition TCSMode Nat tcsInvariant where
  source   := .coldCase
  target   := .nominal
  guard    := fun temp => 150 ≤ temp
  effect   := id
  preserves := fun _temp hguard hinv => by simp only [tcsInvariant, id] at *; omega

/-- Nominal → HotCase: 温度上昇による高温モード移行.
    ガード: 350 ≤ temp (Nominal∩HotCase のオーバーラップ). -/
def tcsNomToHot : Transition TCSMode Nat tcsInvariant where
  source   := .nominal
  target   := .hotCase
  guard    := fun temp => 350 ≤ temp
  effect   := id
  preserves := fun _temp hguard hinv => by simp only [tcsInvariant, id] at *; omega

/-- HotCase → Nominal: ラジエーター冷却による温度回復.
    ガード: temp ≤ 450 (HotCase∩Nominal のオーバーラップ). -/
def tcsHotToNom : Transition TCSMode Nat tcsInvariant where
  source   := .hotCase
  target   := .nominal
  guard    := fun temp => temp ≤ 450
  effect   := id
  preserves := fun _temp hguard hinv => by simp only [tcsInvariant, id] at *; omega

/-- Nominal → Survival: 重大故障. -/
def tcsNomToSurv : Transition TCSMode Nat tcsInvariant where
  source   := .nominal
  target   := .survival
  guard    := fun _temp => True
  effect   := id
  preserves := fun _temp _hguard hinv => by simp only [tcsInvariant, id] at *; omega

/-- ColdCase → Survival: 低温モード中の故障. -/
def tcsColdToSurv : Transition TCSMode Nat tcsInvariant where
  source   := .coldCase
  target   := .survival
  guard    := fun _temp => True
  effect   := id
  preserves := fun _temp _hguard hinv => by simp only [tcsInvariant, id] at *; omega

/-- HotCase → Survival: 高温モード中の故障. -/
def tcsHotToSurv : Transition TCSMode Nat tcsInvariant where
  source   := .hotCase
  target   := .survival
  guard    := fun _temp => True
  effect   := id
  preserves := fun _temp _hguard hinv => by simp only [tcsInvariant, id] at *; omega

/-- Survival → ColdCase: 最低限復旧 (低温安全モード).
    ガード: temp ≤ 250 (ColdCase の範囲内を確認). -/
def tcsSurvToCold : Transition TCSMode Nat tcsInvariant where
  source   := .survival
  target   := .coldCase
  guard    := fun temp => temp ≤ 250
  effect   := id
  preserves := fun _temp hguard _hinv => by simp only [tcsInvariant, id] at *; omega

-- ============================================================
-- §2b  状態機械
-- ============================================================

/-- TCS の状態機械.
    初期状態: ColdCase (打上げ直後は低温). -/
def tcsSM : StateMachine TCSMode Nat tcsInvariant where
  initialState := .coldCase
  transitions  := [ tcsNomToCold
                   , tcsColdToNom
                   , tcsNomToHot
                   , tcsHotToNom
                   , tcsNomToSurv
                   , tcsColdToSurv
                   , tcsHotToSurv
                   , tcsSurvToCold ]

/-- TCS 状態機械は整合的.
    初期状態 ColdCase で temp = 200 (20.0°C) は安全性制約を満たす. -/
theorem tcsSM_WellFormed : tcsSM.WellFormed :=
  ⟨200, by simp only [tcsSM, tcsInvariant]; omega⟩

-- ============================================================
-- §3  安全性定理: モード依存の保証
-- ============================================================

/-!
## §3 モード依存安全性定理

核心的な型:
  `Always tcsSM (fun mode temp => tcsInvariant mode temp)`
  = `∀ mode temp, Reachable tcsSM mode temp → tcsInvariant mode temp`

これは:
  - mode = .nominal  なら 150 ≤ temp ∧ temp ≤ 450 が保証される
  - mode = .coldCase なら temp ≤ 250 が保証される
  - mode = .hotCase  なら 350 ≤ temp ∧ temp ≤ 650 が保証される
  - mode = .survival なら temp ≤ 1000 が保証される

**保証の型自体がモードに依存する** ── 依存型の本領.
-/

/-- TCS のモード依存安全性:
    全到達可能状態で、そのモードに応じた温度範囲が保証される.

    EPS/AOCS の `fun _ _ h => h.inv_holds` と同一の証明.
    フレームワークがモード依存を自動的に扱う.                      -/
theorem tcs_always_safe :
    Always tcsSM (fun mode temp => tcsInvariant mode temp) :=
  fun _ _ h => h.inv_holds

/-- 到達可能な Nominal モードでは 150 ≤ temp ∧ temp ≤ 450.
    モード依存不変条件の具体的な読み方の例.                        -/
theorem tcs_nominal_bounded (temp : Nat)
    (h : Reachable tcsSM .nominal temp) :
    150 ≤ temp ∧ temp ≤ 450 :=
  h.inv_holds

/-- 到達可能な ColdCase モードでは temp ≤ 250.                    -/
theorem tcs_coldCase_bounded (temp : Nat)
    (h : Reachable tcsSM .coldCase temp) :
    temp ≤ 250 :=
  h.inv_holds

/-- 到達可能な HotCase モードでは 350 ≤ temp ∧ temp ≤ 650.       -/
theorem tcs_hotCase_bounded (temp : Nat)
    (h : Reachable tcsSM .hotCase temp) :
    350 ≤ temp ∧ temp ≤ 650 :=
  h.inv_holds

-- ============================================================
-- §4  FDIR 定理
-- ============================================================

/-- 到達可能性: ColdCase → Nominal (2ステップ: 初期 + ヒーター回復). -/
theorem tcs_eventually_nominal :
    Eventually tcsSM (fun mode _ => mode = .nominal) :=
  ⟨.nominal, 200, Reachable.step tcsColdToNom
    (Reachable.init 200 (by simp only [tcsSM, tcsInvariant]; omega))
    (by simp [tcsSM])
    rfl
    (by change 150 ≤ 200; omega), rfl⟩

/-- Survival モードの到達可能性. -/
theorem tcs_eventually_survival :
    Eventually tcsSM (fun mode _ => mode = .survival) :=
  ⟨.survival, 200,
    Reachable.step tcsColdToSurv
      (Reachable.init 200 (by simp only [tcsSM, tcsInvariant]; omega))
      (by simp [tcsSM])
      rfl
      trivial,
    rfl⟩

/-- Survival → ColdCase への復旧の到達可能性. -/
theorem tcs_fault_leads_to_coldCase :
    Leads tcsSM
      (fun mode _ => mode = .survival)
      (fun mode _ => mode = .coldCase) :=
  fun _ _ _ _ =>
    ⟨.coldCase, 200,
      Reachable.step tcsSurvToCold
        (Reachable.step tcsColdToSurv
          (Reachable.init 200 (by simp only [tcsSM, tcsInvariant]; omega))
          (by simp [tcsSM])
          rfl
          trivial)
        (by simp [tcsSM])
        rfl
        (by change 200 ≤ 250; omega),
      rfl⟩

-- ============================================================
-- §5  電力バジェット: サブシステム横断制約
-- ============================================================

/-!
## §5 電力バジェット

各サブシステムの消費電力はモードに依存する.
EPS/AOCS/TCS のモード組み合わせ全体で
電力バジェットを超えないことを型レベルで保証する.

これは **サブシステム横断的な依存型制約** の実例.
-/

open VerifiedMBSE.Behavior in
/-- EPS のモード別消費電力 (単位: W). -/
def epsModePower : EPSMode → Nat
  | .nominal  => 100
  | .lowPower => 50
  | .fault    => 20

/-- AOCS のモード別消費電力 (単位: W). -/
def aocsModePower : AOCS.AOCSMode → Nat
  | .nominal     => 200
  | .safeMode    => 120
  | .sunPointing => 60
  | .fault       => 30

/-- TCS のモード別消費電力 (単位: W). -/
def tcsModePower : TCSMode → Nat
  | .nominal  => 80
  | .coldCase => 150   -- ヒーター動作中は消費大
  | .hotCase  => 90
  | .survival => 40

/-- 衛星全体の電力バジェット (単位: W). -/
def totalPowerBudget : Nat := 500

/-- 電力バジェット制約:
    全サブシステムの消費電力合計がバジェット以内.

    Π(em : EPSMode)(am : AOCSMode)(tm : TCSMode).
      epsModePower(em) + aocsModePower(am) + tcsModePower(tm) ≤ 500

    これは3つのモード型にまたがる **依存型制約** である.           -/
def PowerBudgetOK (em : EPSMode) (am : AOCS.AOCSMode) (tm : TCSMode) : Prop :=
  epsModePower em + aocsModePower am + tcsModePower tm ≤ totalPowerBudget

/-- 電力バジェットは全モード組み合わせで満足される.

    証明: 3×4×4 = 48 通りの全列挙 + omega.
    最悪ケース: Nominal(100) + Nominal(200) + ColdCase(150) = 450 ≤ 500. -/
theorem allModes_powerBudget :
    ∀ (em : EPSMode) (am : AOCS.AOCSMode) (tm : TCSMode),
    PowerBudgetOK em am tm := by
  intro em am tm
  cases em <;> cases am <;> cases tm <;>
    simp only [PowerBudgetOK, epsModePower, aocsModePower, tcsModePower,
               totalPowerBudget] <;>
    omega

/-- 最悪ケースの電力マージン:
    最大消費 450W に対してバジェット 500W → マージン 50W. -/
theorem worstCase_powerMargin :
    totalPowerBudget - (epsModePower .nominal + aocsModePower .nominal +
                        tcsModePower .coldCase) = 50 := by
  simp [totalPowerBudget, epsModePower, aocsModePower, tcsModePower]

-- ============================================================
-- §6  VVRecord: TCS の V 字モデル記録
-- ============================================================

/-- TCS R1: モード依存安全性の確信度 -/
def tcs_r1_confidence :
    ValidationEvidence (Always tcsSM (fun mode temp => tcsInvariant mode temp)) :=
  .confidence 0.85

/-- TCS R1: 熱真空試験後の承認 -/
def tcs_r1_trusted :
    ValidationEvidence (Always tcsSM (fun mode temp => tcsInvariant mode temp)) :=
  .trusted tcs_always_safe

/-- TCS R1 の ValidationTrace -/
def tcs_r1_validationTrace :
    ValidationTrace (Always tcsSM (fun mode temp => tcsInvariant mode temp)) :=
  ValidationTrace.init tcs_r1_confidence
    |>.promote tcs_r1_trusted

/-- TCS R3: 故障復旧の確信度 -/
def tcs_r3_confidence :
    ValidationEvidence (Leads tcsSM
      (fun s _ => s = .survival) (fun s _ => s = .coldCase)) :=
  .confidence 0.75

/-- TCS R3: 故障復旧の承認 -/
def tcs_r3_trusted :
    ValidationEvidence (Leads tcsSM
      (fun s _ => s = .survival) (fun s _ => s = .coldCase)) :=
  .trusted tcs_fault_leads_to_coldCase

/-- TCS R3 の ValidationTrace -/
def tcs_r3_validationTrace :
    ValidationTrace (Leads tcsSM
      (fun s _ => s = .survival) (fun s _ => s = .coldCase)) :=
  ValidationTrace.init tcs_r3_confidence
    |>.promote tcs_r3_trusted

/-- TCS 安全性要件の VVRecord (system レイヤー). -/
def tcs_r1_VVRecord : VVRecord :=
  { layer        := .system
    spec_name    := "TCS-R1-ModeDependentSafety"
    verification := Always tcsSM (fun mode temp => tcsInvariant mode temp)
    verified     := tcs_always_safe
    validation   := tcs_r1_validationTrace }

/-- TCS 復旧要件の VVRecord (system レイヤー). -/
def tcs_r3_VVRecord : VVRecord :=
  { layer        := .system
    spec_name    := "TCS-R3-Recovery"
    verification := Leads tcsSM
                      (fun s _ => s = .survival)
                      (fun s _ => s = .coldCase)
    verified     := tcs_fault_leads_to_coldCase
    validation   := tcs_r3_validationTrace }

/-- 電力バジェットの VVRecord (system レイヤー). -/
def powerBudget_VVRecord : VVRecord :=
  { layer        := .system
    spec_name    := "SYS-PowerBudget-AllModes"
    verification := ∀ (em : EPSMode) (am : AOCS.AOCSMode) (tm : TCSMode),
                      PowerBudgetOK em am tm
    verified     := allModes_powerBudget
    validation   := ValidationTrace.init (.trusted allModes_powerBudget) }

-- ============================================================
-- §7  EPS × AOCS × TCS: 3サブシステム統合
-- ============================================================

open Examples.Spacecraft.AOCS in
/-- EPS + AOCS + TCS の統合システム. -/
def FullSatelliteSystem : System :=
  System.compose
    (System.compose EPSSystem AOCSSystem [])
    TCSSystem
    []

open Examples.Spacecraft.AOCS in
/-- 3サブシステム統合の WellFormed. -/
theorem FullSatelliteSystem_WellFormed : FullSatelliteSystem.WellFormed :=
  System.compose_WellFormed
    (System.compose EPSSystem AOCSSystem [])
    TCSSystem
    []
    (System.compose_WellFormed EPSSystem AOCSSystem []
      EPSSystem_WellFormed AOCSSystem_WellFormed
      (fun _ hc => by simp at hc))
    TCSSystem_WellFormed
    (fun _ hc => by simp at hc)

open Examples.Spacecraft.AOCS in
/-- 統合システムの部品数: EPS(2) + AOCS(3) + TCS(3) = 8. -/
theorem FullSatelliteSystem_parts_count :
    FullSatelliteSystem.parts.length = 8 := by
  simp [FullSatelliteSystem, System.compose, EPSSystem, AOCSSystem, TCSSystem]

-- ============================================================
-- §8  TCS の SubSystemSpec 化
-- ============================================================

/-!
## §8 SubSystemSpec によるパラメトリック化

TCS は EPS/AOCS と異なり **モード依存不変条件** を持つ.
FDIRBundle.isSafe は `D → Prop` (モード無依存) のため,
全モード共通の上界 `temp ≤ 1000` を isSafe とする.

フルのモード依存安全性 (`tcs_r1_VVRecord`) は
SubSystemVVBundle.extraSystemRecords に追加する.

| 項目 | EPS/AOCS | TCS |
|------|----------|-----|
| isSafe | `d ≤ bound` | `temp ≤ 1000` (survival bound) |
| Full safety | = isSafe | mode-dependent (extra record) |
-/

open VerifiedMBSE.VV

/-- TCS のモード無依存安全性:
    全到達可能状態で temp ≤ 1000 (survival bound).

    tcs_always_safe から各モードの不変条件を case split して導出.
    FDIRBundle.isSafe (モード無依存) に使用する. -/
theorem tcs_always_survival_safe :
    Always tcsSM (fun _ temp => temp ≤ 1000) := by
  intro mode temp hr
  have h := tcs_always_safe mode temp hr
  cases mode <;> simp only [tcsInvariant] at h <;> omega

/-- Survival モードは故障状態に相当する. -/
theorem tcs_eventually_survival_as_fault :
    Eventually tcsSM (fun mode _ => mode = .survival) :=
  tcs_eventually_survival

/-- TCS の StructuralSpec.
    Thermistor + ThermalController + Heater. -/
def tcsStructural : StructuralSpec :=
  StructuralSpec.mk' "TCS"
    [Thermistor, ThermalController, Heater]
    [tempSensorConnector, heaterCmdConnector]
    TCSSystem_WellFormed

/-- tcsStructural の system は TCSSystem と一致. -/
theorem tcsStructural_system_eq :
    tcsStructural.system = TCSSystem := rfl

/-- TCS の BehavioralSpec.
    tcsSM: 4 モード, 8 遷移. -/
def tcsBehavioral : BehavioralSpec TCSMode Nat tcsInvariant :=
  { sm := tcsSM
    wellFormed := tcsSM_WellFormed }

/-- TCS の FDIRBundle.
    isFault = .survival (生存モード = 故障時の退避先)
    isRecovery = .coldCase
    isSafe = temp ≤ 1000 (モード無依存の survival bound).

    Note: モード依存安全性は extraSystemRecords で別途追加. -/
def tcsFDIR : FDIRBundle tcsSM :=
  { isFault    := fun s => s = .survival
    isRecovery := fun s => s = .coldCase
    isSafe     := fun temp => temp ≤ 1000
    safety     := tcs_always_survival_safe
    detection  := tcs_eventually_survival_as_fault
    recovery   := tcs_fault_leads_to_coldCase }

/-- TCS の SubSystemSpec. -/
def tcsSpec : SubSystemSpec TCSMode Nat tcsInvariant :=
  { structural := tcsStructural
    behavioral := tcsBehavioral
    fdir       := tcsFDIR }

/-- TCS の SubSystemSpec は FDIRSpec を導出できる. -/
theorem tcsSpec_fdir :
    FDIRSpec tcsSM
      (fun s => s = .survival)
      (fun s => s = .coldCase)
      (fun temp => temp ≤ 1000) :=
  tcsSpec.fdir_derivable

/-- TCS の SubSystemSpec から自動導出された R1 VVRecord. -/
def tcsSpec_r1_VVRecord : VVRecord := tcsSpec.safetyRecord

/-- TCS の SubSystemSpec から自動導出された R3 VVRecord. -/
def tcsSpec_r3_VVRecord : VVRecord := tcsSpec.recoveryRecord

/-- TCS の SubSystemSpec から自動導出された S1 VVRecord. -/
def tcsSpec_s1_VVRecord : VVRecord := tcsSpec.subsystemRecord

/-- 自動導出された R1 の spec_name は "TCS-R1-Safety". -/
theorem tcsSpec_r1_name :
    tcsSpec_r1_VVRecord.spec_name = "TCS-R1-Safety" := rfl

/-- TCS のモード別消費電力 (SubSystemSpec 内の定義). -/
private def tcsModePower' : TCSMode → Nat
  | .nominal  => 80
  | .coldCase => 150
  | .hotCase  => 90
  | .survival => 40

/-- TCS の ModePowerSpec. -/
def tcsModePowerSpec : ModePowerSpec TCSMode :=
  { modePower := tcsModePower'
    maxPower  := 150
    maxPower_bound := by
      intro s; cases s <;> simp [tcsModePower'] }

/-- TCS の SubSystemVVBundle.
    extraSystemRecords にモード依存安全性と電力バジェットを追加. -/
def tcsVVBundle : SubSystemVVBundle tcsSpec :=
  { componentRecords :=
      [ mkComponentRecord "TCS" 1 Thermistor trivial
      , mkComponentRecord "TCS" 2 ThermalController trivial
      , mkComponentRecord "TCS" 3 Heater trivial ]
    extraSystemRecords :=
      [ tcs_r1_VVRecord      -- フルのモード依存安全性
      , powerBudget_VVRecord  -- 3 サブシステム電力バジェット
      ] }

/-- TCS VVBundle の全 VVRecord 数は 8.
    コンポーネント(3) + サブシステム(1) + R1(1) + R3(1)
    + extra(モード依存R1 + 電力バジェット = 2) = 8. -/
theorem tcsVVBundle_count :
    tcsVVBundle.allRecords.length = 8 := by
  simp [SubSystemVVBundle.allRecords, tcsVVBundle]

-- ============================================================
-- TODO:
-- [✅] TCS コンポーネントの PartDef
-- [✅] ポート定義 (TemperaturePort, HeaterCmdPort + 共役)
-- [✅] TCSSystem + WellFormed
-- [✅] モード依存不変条件 (tcsInvariant)
-- [✅] 状態機械 (4モード, 8遷移)
-- [✅] モード依存安全性定理 (tcs_always_safe)
-- [✅] モード別境界定理 (tcs_nominal_bounded 等)
-- [✅] FDIR 定理 (R1, R3)
-- [✅] 電力バジェット制約 (allModes_powerBudget)
-- [✅] VVRecord (R1, R3, 電力バジェット)
-- [✅] 3サブシステム統合 (FullSatelliteSystem)
-- [✅] SubSystemSpec 化 ★新規
-- [✅] ModePowerSpec ★新規
-- [✅] SubSystemVVBundle ★新規
-- ============================================================

end Examples.Spacecraft.TCS
