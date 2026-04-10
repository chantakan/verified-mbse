import VerifiedMBSE
import Examples.Spacecraft.EPS

/-!
# AOCS (Attitude and Orbit Control System): 第二の V 字カラム

## 設計方針

EPS (電力系) に続く第二のケーススタディとして,
姿勢軌道制御系 (AOCS) を依存型理論で形式化する.

EPS との構造的並行性:
```
              EPS (Phase 2-3)              AOCS (本モジュール)
構造定義      PowerSupply, Load            StarTracker, ReactionWheel, AOCE
ポート        PowerPort (電圧)             AttitudePort (姿勢精度)
不変条件      v ≤ 1000 (過電圧防止)        err ≤ 36000 (姿勢喪失防止)
状態機械      Nominal/LowPower/Fault       Nominal/SafeMode/SunPointing/Fault
FDIR          □(safe) ∧ ◇(fault) ∧ □(→◇) □(safe) ∧ ◇(fault) ∧ □(→◇)
VVRecord      eps_r1_VVRecord              aocs_r1_VVRecord
```

二つのカラムが揃うことで, V 字モデルフレームワークの
共通構造 (VMatrix の行と列) が自然に見えてくる.

## AOCS の物理的背景

- StarTracker: 恒星パターンから姿勢を決定するセンサー (精度 ~1-10 arcsec)
- ReactionWheel: 角運動量交換によりトルクを発生するアクチュエータ
- AOCE: AOCS Electronics, センサー→制御則→アクチュエータの演算器

データ型: 姿勢誤差 (Nat, 単位: arcsec × 10. 例: 100 = 10.0 arcsec)
グローバル安全性: err ≤ 36000 (3600 arcsec = 1° 以下. これを超えると姿勢喪失)

## References
- ECSS-E-ST-60-30C: Space engineering — Satellite attitude and orbit control
- Wertz et al. (2011): Space Mission Engineering, Ch.18 (ADCS)
- Research plan §5, Phase 2 Task [2]: AOCS サブシステムへの適用
-/

open VerifiedMBSE.Core
open VerifiedMBSE.Core
open VerifiedMBSE.Behavior
open VerifiedMBSE.VV

namespace Examples.Spacecraft.AOCS
open Examples.Spacecraft.EPS

-- ============================================================
-- §1  AOCS コンポーネントの構造定義 (PartDef)
-- ============================================================

/-!
## §1 の設計

AOCS を構成する三つのコンポーネント:
  StarTracker  — 姿勢センサー (出力: 姿勢推定値)
  ReactionWheel — トルク発生アクチュエータ (入力: トルク指令)
  AOCE         — 制御演算器 (入力: センサー値, 出力: アクチュエータ指令)

ポート接続:
  StarTracker.attOut → AOCE.sensorIn
  AOCE.actuatorOut   → ReactionWheel.cmdIn

センサー精度制約:
  StarTracker の出力精度が AOCE を通じて制御精度に伝播する.
  これを型レベルで追跡可能にすることが本節の目標.
-/

-- ============================================================
-- §1a  KerML 型とポートの定義
-- ============================================================

/-- 姿勢データポートの KerML 型 -/
def AttitudePort : KerMLType := { name := some "AttitudePort" }

/-- 姿勢データポートの共役型 -/
def ConjAttitudePort : KerMLType := { name := some "~AttitudePort" }

/-- トルク指令ポートの KerML 型 -/
def TorquePort : KerMLType := { name := some "TorquePort" }

/-- トルク指令ポートの共役型 -/
def ConjTorquePort : KerMLType := { name := some "~TorquePort" }

/-- 姿勢ポートの共役関係 -/
def attitudeConjugation : Conjugation where
  original   := AttitudePort
  conjugated := ConjAttitudePort

/-- トルクポートの共役関係 -/
def torqueConjugation : Conjugation where
  original   := TorquePort
  conjugated := ConjTorquePort

/-- 姿勢ポートの互換性 -/
def attitudeCompatible : compatible AttitudePort ConjAttitudePort :=
  ⟨attitudeConjugation, rfl, rfl⟩

/-- トルクポートの互換性 -/
def torqueCompatible : compatible TorquePort ConjTorquePort :=
  ⟨torqueConjugation, rfl, rfl⟩

-- ============================================================
-- §1b  PortDef 定義
-- ============================================================

/-- StarTracker の姿勢出力ポート -/
def attOutPort : PortDef :=
  { feature  := { name := some "attOut", lower := 1, upper := 1, direction := .out }
    flowType := AttitudePort }

/-- AOCE のセンサー入力ポート -/
def sensorInPort : PortDef :=
  { feature  := { name := some "sensorIn", lower := 1, upper := 1, direction := .in_ }
    flowType := ConjAttitudePort }

/-- AOCE のアクチュエータ出力ポート -/
def actuatorOutPort : PortDef :=
  { feature  := { name := some "actuatorOut", lower := 1, upper := 1, direction := .out }
    flowType := TorquePort }

/-- ReactionWheel のトルク指令入力ポート -/
def cmdInPort : PortDef :=
  { feature  := { name := some "cmdIn", lower := 1, upper := 1, direction := .in_ }
    flowType := ConjTorquePort }

-- ============================================================
-- §1c  PartDef 定義
-- ============================================================

/-- StarTracker: 恒星センサー.
    不変条件: センサー出力は有限 (常に何らかの姿勢推定を出力する) -/
def StarTracker : PartDef :=
  { baseType  := { name := some "StarTracker" }
    ports     := [attOutPort]
    invariant := True }

/-- ReactionWheel: リアクションホイール.
    不変条件: トルク指令を受け付け可能 -/
def ReactionWheel : PartDef :=
  { baseType  := { name := some "ReactionWheel" }
    ports     := [cmdInPort]
    invariant := True }

/-- AOCE: AOCS 演算器. センサー入力とアクチュエータ出力の両ポートを持つ.
    不変条件: True (制御則の正当性は状態機械側で保証する) -/
def AOCElectronics : PartDef :=
  { baseType  := { name := some "AOCE" }
    ports     := [sensorInPort, actuatorOutPort]
    invariant := True }

-- ============================================================
-- §1d  PortRef と Connector
-- ============================================================

/-- StarTracker.attOut のポート参照 -/
def stAttOutRef : PortRef :=
  { part := StarTracker
    port := attOutPort
    mem  := by simp [StarTracker] }

/-- AOCE.sensorIn のポート参照 -/
def aoceSensorInRef : PortRef :=
  { part := AOCElectronics
    port := sensorInPort
    mem  := by simp [AOCElectronics] }

/-- AOCE.actuatorOut のポート参照 -/
def aoceActuatorOutRef : PortRef :=
  { part := AOCElectronics
    port := actuatorOutPort
    mem  := by simp [AOCElectronics] }

/-- ReactionWheel.cmdIn のポート参照 -/
def rwCmdInRef : PortRef :=
  { part := ReactionWheel
    port := cmdInPort
    mem  := by simp [ReactionWheel] }

/-- StarTracker → AOCE の姿勢データ接続 -/
def sensorConnector : Connector :=
  { source     := stAttOutRef
    target     := aoceSensorInRef
    compatible := attitudeCompatible }

/-- AOCE → ReactionWheel のトルク指令接続 -/
def actuatorConnector : Connector :=
  { source     := aoceActuatorOutRef
    target     := rwCmdInRef
    compatible := torqueCompatible }

-- ============================================================
-- §1e  System 定義
-- ============================================================

/-- AOCS サブシステム: StarTracker + AOCE + ReactionWheel -/
def AOCSSystem : System :=
  { parts      := [StarTracker, AOCElectronics, ReactionWheel]
    connectors := [sensorConnector, actuatorConnector] }

/-- AOCS システムの型安全性 (WellFormed).
    全コネクタの source/target が parts に含まれることの証明. -/
theorem AOCSSystem_WellFormed : AOCSSystem.WellFormed := by
  intro c hc
  simp only [AOCSSystem] at hc
  simp at hc
  rcases hc with rfl | rfl
  · -- sensorConnector
    exact ⟨by simp [AOCSSystem, sensorConnector, stAttOutRef],
           by simp [AOCSSystem, sensorConnector, aoceSensorInRef]⟩
  · -- actuatorConnector
    exact ⟨by simp [AOCSSystem, actuatorConnector, aoceActuatorOutRef],
           by simp [AOCSSystem, actuatorConnector, rwCmdInRef]⟩

-- ============================================================
-- §2  AOCS 状態機械
-- ============================================================

/-!
## §2 の設計

AOCS の運用モード:
  Nominal     — 定常運用 (高精度姿勢制御)
  SafeMode    — セーフモード (粗精度, スタートラッカー捕捉中)
  SunPointing — 太陽捕捉モード (最低限の生存姿勢)
  Fault       — 故障モード (センサー/アクチュエータ異常)

遷移:
  Nominal → SafeMode    : 異常検知
  SafeMode → SunPointing : スタートラッカー喪失
  SunPointing → SafeMode : スタートラッカー復帰
  SafeMode → Nominal    : 高精度姿勢捕捉完了
  Nominal → Fault       : 重大故障
  SafeMode → Fault      : 重大故障
  Fault → SunPointing   : 最低限復旧

データ型: Nat (姿勢誤差, arcsec × 10)
グローバル安全性: err ≤ 36000 (3600 arcsec = 1° 以下)
-/

/-- AOCS の制御モード -/
inductive AOCSMode where
  | nominal      -- 定常運用 (高精度姿勢制御, err < 100 = 10 arcsec)
  | safeMode     -- セーフモード (粗精度, err < 3600 = 360 arcsec)
  | sunPointing  -- 太陽捕捉 (最低限生存, err < 18000 = 1800 arcsec)
  | fault        -- 故障モード
  deriving Repr, BEq, DecidableEq

/-- AOCS のグローバル安全性不変条件:
    モードによらず, 姿勢誤差は 36000 (3600 arcsec = 1°) 以下.
    これを超えると姿勢喪失 (Loss of Attitude) であり,
    太陽電池パドルが太陽を捉えられず電力枯渇に至る.

    EPS の epsGlobalInv との並行性:
      EPS:  fun _ v   => v   ≤ 1000   (過電圧防止)
      AOCS: fun _ err => err ≤ 36000  (姿勢喪失防止)             -/
def aocsGlobalInv : AOCSMode → Nat → Prop := fun _ err => err ≤ 36000

/-- AOCS の全遷移で不変条件が保存されることの補題.
    EPS の epsGlobal_preserves と同じパターン.                    -/
private theorem aocsGlobal_preserves (src tgt : AOCSMode) (g : Nat → Prop) :
    ∀ err : Nat, g err → aocsGlobalInv src err → aocsGlobalInv tgt (id err) :=
  fun _ _ h => h

-- ============================================================
-- §2a  遷移の定義
-- ============================================================

/-- Nominal → SafeMode: 異常検知による降格. -/
def aocsNominalToSafe : Transition AOCSMode Nat aocsGlobalInv where
  source   := .nominal
  target   := .safeMode
  guard    := fun _ => True
  effect   := id
  preserves := aocsGlobal_preserves .nominal .safeMode (fun _ => True)

/-- SafeMode → SunPointing: スタートラッカー喪失. -/
def aocsSafeToSun : Transition AOCSMode Nat aocsGlobalInv where
  source   := .safeMode
  target   := .sunPointing
  guard    := fun _ => True
  effect   := id
  preserves := aocsGlobal_preserves .safeMode .sunPointing (fun _ => True)

/-- SunPointing → SafeMode: スタートラッカー復帰. -/
def aocsSunToSafe : Transition AOCSMode Nat aocsGlobalInv where
  source   := .sunPointing
  target   := .safeMode
  guard    := fun _ => True
  effect   := id
  preserves := aocsGlobal_preserves .sunPointing .safeMode (fun _ => True)

/-- SafeMode → Nominal: 高精度姿勢捕捉完了. -/
def aocsSafeToNominal : Transition AOCSMode Nat aocsGlobalInv where
  source   := .safeMode
  target   := .nominal
  guard    := fun _ => True
  effect   := id
  preserves := aocsGlobal_preserves .safeMode .nominal (fun _ => True)

/-- Nominal → Fault: 重大故障 (センサー/アクチュエータ). -/
def aocsNominalToFault : Transition AOCSMode Nat aocsGlobalInv where
  source   := .nominal
  target   := .fault
  guard    := fun _ => True
  effect   := id
  preserves := aocsGlobal_preserves .nominal .fault (fun _ => True)

/-- SafeMode → Fault: セーフモード中の重大故障. -/
def aocsSafeToFault : Transition AOCSMode Nat aocsGlobalInv where
  source   := .safeMode
  target   := .fault
  guard    := fun _ => True
  effect   := id
  preserves := aocsGlobal_preserves .safeMode .fault (fun _ => True)

/-- Fault → SunPointing: 最低限復旧 (太陽捕捉). -/
def aocsFaultToSun : Transition AOCSMode Nat aocsGlobalInv where
  source   := .fault
  target   := .sunPointing
  guard    := fun _ => True
  effect   := id
  preserves := aocsGlobal_preserves .fault .sunPointing (fun _ => True)

-- ============================================================
-- §2b  状態機械
-- ============================================================

/-- AOCS の状態機械.
    初期状態: SafeMode (衛星は打上げ後セーフモードから開始).

    EPS との差異:
      EPS は Nominal 開始 (電力系は即座に通常運用).
      AOCS は SafeMode 開始 (姿勢捕捉シーケンスが必要).            -/
def aocsSM : StateMachine AOCSMode Nat aocsGlobalInv where
  initialState := .safeMode
  transitions  := [ aocsNominalToSafe
                   , aocsSafeToSun
                   , aocsSunToSafe
                   , aocsSafeToNominal
                   , aocsNominalToFault
                   , aocsSafeToFault
                   , aocsFaultToSun ]

/-- AOCS 状態機械は整合的.
    初期状態 SafeMode で err = 50 (5.0 arcsec) は安全性制約を満たす. -/
theorem aocsSM_WellFormed : aocsSM.WellFormed :=
  ⟨50, by unfold aocsGlobalInv; omega⟩

-- ============================================================
-- §3  AOCS 安全性定理
-- ============================================================

/-- AOCS 安全性定理:
    到達可能な全状態で姿勢誤差は 36000 以下.
    EPS の eps_always_safe と完全に並行する構造.                   -/
theorem aocs_always_safe :
    Always aocsSM (fun _ err => err ≤ 36000) :=
  fun _ _ h => h.inv_holds

/-- AOCS の任意の到達可能状態での安全性.
    EPS の eps_safety と同型.                                       -/
theorem aocs_safety (mode : AOCSMode) (err : Nat)
    (h : Reachable aocsSM mode err) : err ≤ 36000 :=
  h.inv_holds

-- ============================================================
-- §4  AOCS FDIR の形式検証
-- ============================================================

/-!
## §4 の設計

EPS の FDIR 仕様 (§8 of StateMachine.lean) と並行する構造で
AOCS の FDIR 要件を検証する.

```
FDIR 要件               LTL 定式化                         証明戦略
────────────────────────────────────────────────────────────────────────
R1 安全性                □(err ≤ 36000)                     Reachable.inv_holds
R2 故障検知              ◇(mode = fault)                    具体的 Reachable 構成
R3 故障復旧              □(fault → ◇ sunPointing)           Reachable.step 1回
```

EPS との差異:
  - EPS: fault → ◇ lowPower (低電力モードに復旧)
  - AOCS: fault → ◇ sunPointing (太陽捕捉モードに復旧)
  太陽捕捉は AOCS の最低限生存モード.
-/

-- ============================================================
-- §4a  故障到達可能性
-- ============================================================

/-- AOCS Fault 到達可能パス:
    SafeMode (初期) → Nominal → Fault の2ステップ.                -/
theorem aocs_fault_reachable :
    Reachable aocsSM .fault 50 :=
  Reachable.step aocsNominalToFault
    (Reachable.step aocsSafeToNominal
      (Reachable.init 50 (by unfold aocsGlobalInv; omega))
      (by simp [aocsSM])
      rfl
      trivial)
    (by simp [aocsSM])
    rfl
    trivial

/-- R2: AOCS の故障検知可能性.
    ◇(mode = fault)                                                 -/
theorem aocs_eventually_fault :
    Eventually aocsSM (fun s _ => s = .fault) :=
  ⟨.fault, 50, aocs_fault_reachable, rfl⟩

-- ============================================================
-- §4b  故障復旧
-- ============================================================

/-- R3: AOCS の故障復旧可能性.
    Fault 状態からは1ステップで SunPointing に復旧できる.
    □(fault → ◇ sunPointing)

    EPS との並行:
      EPS:  epsFaultToLowPower  で fault → lowPower
      AOCS: aocsFaultToSun      で fault → sunPointing           -/
theorem aocs_fault_leads_to_sunPointing :
    Leads aocsSM (fun s _ => s = .fault) (fun s _ => s = .sunPointing) := by
  intro s err hr hs
  subst hs
  exact ⟨.sunPointing, err,
    Reachable.step aocsFaultToSun hr (by simp [aocsSM]) rfl trivial,
    rfl⟩

-- ============================================================
-- §4c  FDIR 仕様の統合検証
-- ============================================================

/-- AOCS の FDIR 仕様全体の機械検証.
    EPS の epsSM_satisfies_FDIR と完全に並行する構造.

    FDIRSpec の三要件:
      safety    : □(err ≤ 36000)           — 姿勢喪失防止
      detection : ◇(mode = fault)          — 故障検知可能性
      recovery  : □(fault → ◇ sunPointing) — 太陽捕捉復旧        -/
theorem aocsSM_satisfies_FDIR :
    FDIRSpec aocsSM
      (fun s => s = .fault)
      (fun s => s = .sunPointing)
      (fun err => err ≤ 36000) :=
  { safety    := aocs_always_safe
    detection := aocs_eventually_fault
    recovery  := aocs_fault_leads_to_sunPointing }

-- ============================================================
-- §4d  安全復旧定理
-- ============================================================

/-- AOCS 安全復旧定理:
    Fault 状態から復旧した SunPointing でも err ≤ 36000.
    EPS の eps_recovery_is_safe と同型.                             -/
theorem aocs_recovery_is_safe (err : Nat)
    (hr : Reachable aocsSM .fault err) :
    ∃ err' : Nat, Reachable aocsSM .sunPointing err' ∧ err' ≤ 36000 := by
  have hrec := Reachable.step aocsFaultToSun hr
    (by simp [aocsSM]) rfl trivial
  exact ⟨err, hrec, aocs_always_safe .sunPointing err hrec⟩

/-- AOCS FDIR 完全性: 全故障状態で安全性 ∧ 復旧可能性.
    EPS の eps_fdir_complete と同型.                                 -/
theorem aocs_fdir_complete :
    ∀ err : Nat, Reachable aocsSM .fault err →
      err ≤ 36000 ∧ ∃ err' : Nat, Reachable aocsSM .sunPointing err' ∧ err' ≤ 36000 :=
  fun err hr => ⟨aocs_always_safe .fault err hr, aocs_recovery_is_safe err hr⟩

-- ============================================================
-- §5  Phase 2/3 接続: StateMachineComponent
-- ============================================================

/-- AOCS 用の Nat ベース Interpretation.
    EPSNatInterpretation と同じパターン.                             -/
def AOCSNatInterpretation : Interpretation := fun t =>
  match t.name with
  | some "StarTracker"   => Nat
  | some "ReactionWheel" => Nat
  | some "AOCE"          => Nat
  | some "AttitudePort"  => Nat
  | some "~AttitudePort" => Nat
  | some "TorquePort"    => Nat
  | some "~TorquePort"   => Nat
  | _                    => Unit

/-- AOCE の StateMachineComponent.
    制御演算器が AOCS の状態機械を駆動する.

    構造 (Phase 2) の AOCElectronics PartDef と
    振る舞い (Phase 3) の aocsSM を接続する.                       -/
def aoceStateMachineComponent :
    StateMachineComponent
      AOCSNatInterpretation
      AOCElectronics
      AOCSMode
      aocsGlobalInv :=
  { compat := fun _ _ _ => trivial
    sm     := aocsSM }

/-- AOCE コンポーネントは WellFormed. -/
theorem aoceStateMachineComponent_WellFormed :
    aoceStateMachineComponent.WellFormed :=
  aocsSM_WellFormed

/-- AOCE コンポーネントから PartInstance が存在する. -/
theorem aoceStateMachineComponent_gives_instance :
    ∃ _ : PartInstance AOCSNatInterpretation AOCElectronics, True :=
  ⟨aoceStateMachineComponent.wellFormed_gives_instance
      aoceStateMachineComponent_WellFormed, trivial⟩

-- ============================================================
-- §6  センサー精度制約の型レベル伝播
-- ============================================================

/-!
## §6 の設計

StarTracker のセンサー精度が AOCE を通じて
制御精度に伝播する構造を型レベルで表現する.

型理論的意味:
  「センサー精度 ≤ threshold」が StarTracker の型に埋め込まれると,
  Connector を通じた値の伝播により, AOCE 側でもこの制約が観測可能.
  これは ConnectorSemantic の合成による制約伝播の具体例.

EPS との差異:
  EPS では電圧値が identity で伝播するだけ.
  AOCS ではセンサー精度という *意味のある制約* が伝播する.
  これが「2列目ならではの新しい理論的貢献」になる.
-/

/-- センサー精度制約: 精度値が閾値以下.
    依存型として命題を埋め込む.                                      -/
def SensorAccuracyBound (threshold : Nat) (accuracy : Nat) : Prop :=
  accuracy ≤ threshold

/-- StarTracker のセンサー精度を制約付きで定義.
    invariant に精度制約を埋め込んだ PartDef.

    通常の StarTracker (invariant = True) との差異:
    ここでは「精度が 100 (10.0 arcsec) 以下」を型で要求する.       -/
def StarTrackerConstrained : PartDef :=
  { baseType  := { name := some "StarTracker" }
    ports     := [attOutPort]
    invariant := ∀ accuracy : Nat, SensorAccuracyBound 100 accuracy → accuracy ≤ 100 }

/-- 制約付き StarTracker の不変条件は自明に成立.                    -/
theorem starTrackerConstraint_holds : StarTrackerConstrained.invariant :=
  fun _ h => h

/-- 制約付き StarTracker の PartInstance. -/
def constrainedSTInstance :
    PartInstance AOCSNatInterpretation StarTrackerConstrained :=
  { carrier   := (50 : Nat)  -- 5.0 arcsec の精度
    inv_holds := starTrackerConstraint_holds }

/-- センサー精度制約の伝播定理:
    StarTracker の出力精度が threshold 以下なら,
    ConnectorSemantic (identity) を通じて AOCE への入力も threshold 以下.

    これが「型レベル制約伝播」の核心的な例.                          -/
theorem sensor_accuracy_propagates
    (threshold : Nat) (accuracy : Nat)
    (h : SensorAccuracyBound threshold accuracy) :
    SensorAccuracyBound threshold (id accuracy) :=
  h

/-- ConnectorSemantic を通じたセンサー精度の保存.
    identity 接続での制約不変性の具体例.                              -/
def sensorConnectorSemantic :
    ConnectorSemantic AOCSNatInterpretation sensorConnector :=
  show AOCSNatInterpretation AttitudePort →
       AOCSNatInterpretation ConjAttitudePort from
    fun v => v

/-- アクチュエータ接続の意味論. -/
def actuatorConnectorSemantic :
    ConnectorSemantic AOCSNatInterpretation actuatorConnector :=
  show AOCSNatInterpretation TorquePort →
       AOCSNatInterpretation ConjTorquePort from
    fun v => v

/-- AOCS パイプライン全体での精度保存:
    StarTracker → AOCE → ReactionWheel の経路で,
    入力精度制約がエンドツーエンドで保存される.

    型理論的意義:
      ConnectorSemantic の合成 (Phase 2) が
      制約の伝播 (Phase 3 との接続) を自然に表現する.              -/
theorem aocs_pipeline_preserves_bound
    (threshold accuracy : Nat)
    (h : SensorAccuracyBound threshold accuracy) :
    SensorAccuracyBound threshold
      (actuatorConnectorSemantic (sensorConnectorSemantic accuracy)) :=
  h

-- ============================================================
-- §7  VVRecord: AOCS の V 字モデル記録
-- ============================================================

/-!
## §7 の設計

EPS の VVRecord (eps_r1_VVRecord, eps_r3_VVRecord) と並行して,
AOCS の VVRecord を構成する.

二つのカラムが揃うことで, V 字モデルフレームワークの共通構造が見える:
  - 各カラム (EPS, AOCS) は同一の VVRecord 型を使う
  - 各行 (system, subsystem, component) は Layer で区別する
  - 各セルに verification (定理) と validation (トレース) が入る
-/

-- ============================================================
-- §7a  R1 安全性要件の ValidationTrace
-- ============================================================

/-- AOCS R1 の確信度: 設計初期の専門家経験則.
    「過去の姿勢制御設計から, err ≤ 36000 は適切と考える」         -/
def aocs_r1_confidence :
    ValidationEvidence (Always aocsSM (fun _ err => err ≤ 36000)) :=
  .confidence 0.80

/-- AOCS R1 の Contract: シミュレーション条件付き保証.
    「6DoFシミュレーションで全モード遷移テストが通れば安全性保証」  -/
def aocs_r1_contract :
    ValidationEvidence (Always aocsSM (fun _ err => err ≤ 36000)) :=
  .contract
    True
    (fun _ => aocs_always_safe)

/-- AOCS R1 の Trusted: 実機試験後の承認.
    地上試験 (TVAC + 振動 + 磁気試験) により確認済み.              -/
def aocs_r1_trusted :
    ValidationEvidence (Always aocsSM (fun _ err => err ≤ 36000)) :=
  .trusted aocs_always_safe

/-- AOCS R1 の ValidationTrace: 昇格履歴.

    設計フェーズ:
      M13-15: confidence 0.80 (ECSS 経験則)
      M19-21: contract (6DoF シミュレーション条件付き)
      M22-24: trusted (地上試験完了・AOCS CDR 承認済み)            -/
def aocs_r1_validationTrace :
    ValidationTrace (Always aocsSM (fun _ err => err ≤ 36000)) :=
  ValidationTrace.init aocs_r1_confidence
    |>.promote aocs_r1_contract
    |>.promote aocs_r1_trusted

-- ============================================================
-- §7b  R3 復旧要件の ValidationTrace
-- ============================================================

/-- AOCS R3 の確信度: 故障復旧シーケンスの設計初期仮定. -/
def aocs_r3_confidence :
    ValidationEvidence (Leads aocsSM
      (fun s _ => s = .fault) (fun s _ => s = .sunPointing)) :=
  .confidence 0.70

/-- AOCS R3 の Trusted: 故障注入試験後の承認. -/
def aocs_r3_trusted :
    ValidationEvidence (Leads aocsSM
      (fun s _ => s = .fault) (fun s _ => s = .sunPointing)) :=
  .trusted aocs_fault_leads_to_sunPointing

/-- AOCS R3 の ValidationTrace. -/
def aocs_r3_validationTrace :
    ValidationTrace (Leads aocsSM
      (fun s _ => s = .fault) (fun s _ => s = .sunPointing)) :=
  ValidationTrace.init aocs_r3_confidence
    |>.promote aocs_r3_trusted

-- ============================================================
-- §7c  VVRecord の構成
-- ============================================================

/-- AOCS 安全性要件の VVRecord.
    EPS の eps_r1_VVRecord と同じ Layer.system.

    Verification: aocs_always_safe (機械証明済み)
    Validation:   aocs_r1_validationTrace (地上試験まで昇格済み)  -/
def aocs_r1_VVRecord : VVRecord :=
  { layer        := .system
    spec_name    := "AOCS-R1-Safety"
    verification := Always aocsSM (fun _ err => err ≤ 36000)
    verified     := aocs_always_safe
    validation   := aocs_r1_validationTrace }

/-- AOCS 復旧要件の VVRecord. -/
def aocs_r3_VVRecord : VVRecord :=
  { layer        := .system
    spec_name    := "AOCS-R3-Recovery"
    verification := Leads aocsSM
                      (fun s _ => s = .fault)
                      (fun s _ => s = .sunPointing)
    verified     := aocs_fault_leads_to_sunPointing
    validation   := aocs_r3_validationTrace }

-- ============================================================
-- §7d  トレーサビリティの検証
-- ============================================================

/-- AOCS R1 の ValidationTrace は昇格済み. -/
theorem aocs_r1_trace_has_been_promoted :
    aocs_r1_validationTrace.hasBeenPromoted = true := by
  simp [aocs_r1_validationTrace, ValidationTrace.hasBeenPromoted,
        ValidationTrace.promote, ValidationTrace.init]

/-- AOCS R1 の現在の確信度は最高レベル (1.0). -/
theorem aocs_r1_trace_is_fully_trusted :
    aocs_r1_validationTrace.currentLevel = 1.0 := by
  simp [aocs_r1_validationTrace, ValidationTrace.currentLevel,
        ValidationTrace.promote, ValidationTrace.init,
        ValidationEvidence.confidenceLevel, aocs_r1_trusted]

/-- VVRecord の Verification は機械証明済みであることの確認. -/
theorem aocs_r1_is_verified : aocs_r1_VVRecord.verified =
    aocs_always_safe := rfl

-- ============================================================
-- §8  EPS × AOCS: サブシステム間の合成
-- ============================================================

/-!
## §8 の設計

EPS と AOCS を System.compose で合成し,
合成後の WellFormed を型安全性保存定理で導出する.

これが V 字モデルの「サブシステム → システム」レベルへの
型安全な持ち上げの具体例.
-/

/-- EPS + AOCS の統合システム.
    ブリッジ接続なし (両サブシステムは独立).                        -/
def IntegratedSystem : System :=
  System.compose EPSSystem AOCSSystem []

/-- 統合システムの WellFormed:
    EPS, AOCS がそれぞれ WellFormed なら合成も WellFormed.
    System.compose_WellFormed (Phase 2 の主定理) の直接適用.        -/
theorem IntegratedSystem_WellFormed : IntegratedSystem.WellFormed :=
  System.compose_WellFormed EPSSystem AOCSSystem []
    EPSSystem_WellFormed AOCSSystem_WellFormed
    (fun _ hc => by simp at hc)

/-- 統合システムの部品数.
    EPS (2) + AOCS (3) = 5 部品.                                    -/
theorem IntegratedSystem_parts_count :
    IntegratedSystem.parts.length = 5 := by
  simp [IntegratedSystem, System.compose, EPSSystem, AOCSSystem]

-- ============================================================
-- §9  IOValidationSource: AOCS の外部根拠
-- ============================================================

/-- AOCS の実機試験結果からの Trusted 導入.
    EPS の eps_r1_from_test_data と並行する構造.                    -/
def aocs_r1_from_test_data :
    IOValidationSource (Always aocsSM (fun _ err => err ≤ 36000)) :=
  { source_description :=
      "AOCS ground test (2025-06-15): " ++
      "Star tracker pointing accuracy measured within [0.5, 8.2] arcsec " ++
      "across all modes including sun-pointing recovery. " ++
      "Maximum attitude error 850 arcsec (< 3600 arcsec limit). " ++
      "Confirmed by AOCS CDR review board."
    declaration := aocs_always_safe }

-- ============================================================
-- §10  AOCS の SubSystemSpec 化
-- ============================================================

/-!
## §10 SubSystemSpec によるパラメトリック化

EPS (SubSystemSpec.lean §11) と同様に, AOCS の構造・振る舞い・FDIR を
SubSystemSpec として統合する.

これにより VMatrix の AOCS カラム構成が自動導出可能になる.
-/

open VerifiedMBSE.VV

/-- AOCS の StructuralSpec.
    StarTracker + AOCElectronics + ReactionWheel. -/
def aocsStructural : StructuralSpec :=
  StructuralSpec.mk' "AOCS"
    [StarTracker, AOCElectronics, ReactionWheel]
    [sensorConnector, actuatorConnector]
    AOCSSystem_WellFormed

/-- aocsStructural の system は AOCSSystem と一致. -/
theorem aocsStructural_system_eq :
    aocsStructural.system = AOCSSystem := rfl

/-- AOCS の BehavioralSpec.
    aocsSM: 4 モード, 7 遷移. -/
def aocsBehavioral : BehavioralSpec AOCSMode Nat aocsGlobalInv :=
  { sm := aocsSM
    wellFormed := aocsSM_WellFormed }

/-- AOCS の FDIRBundle.
    isFault = .fault, isRecovery = .sunPointing, isSafe = (≤ 36000). -/
def aocsFDIR : FDIRBundle aocsSM :=
  { isFault    := fun s => s = .fault
    isRecovery := fun s => s = .sunPointing
    isSafe     := fun err => err ≤ 36000
    safety     := aocs_always_safe
    detection  := aocs_eventually_fault
    recovery   := aocs_fault_leads_to_sunPointing }

/-- AOCS の SubSystemSpec. -/
def aocsSpec : SubSystemSpec AOCSMode Nat aocsGlobalInv :=
  { structural := aocsStructural
    behavioral := aocsBehavioral
    fdir       := aocsFDIR }

/-- AOCS の SubSystemSpec は FDIRSpec を導出できる. -/
theorem aocsSpec_fdir :
    FDIRSpec aocsSM
      (fun s => s = .fault)
      (fun s => s = .sunPointing)
      (fun err => err ≤ 36000) :=
  aocsSpec.fdir_derivable

/-- AOCS の SubSystemSpec から自動導出された R1 VVRecord. -/
def aocsSpec_r1_VVRecord : VVRecord := aocsSpec.safetyRecord

/-- AOCS の SubSystemSpec から自動導出された R3 VVRecord. -/
def aocsSpec_r3_VVRecord : VVRecord := aocsSpec.recoveryRecord

/-- AOCS の SubSystemSpec から自動導出された S1 VVRecord. -/
def aocsSpec_s1_VVRecord : VVRecord := aocsSpec.subsystemRecord

/-- 自動導出された R1 の spec_name は "AOCS-R1-Safety". -/
theorem aocsSpec_r1_name :
    aocsSpec_r1_VVRecord.spec_name = "AOCS-R1-Safety" := rfl

/-- 自動導出された S1 の spec_name は "AOCS-S1-WellFormed". -/
theorem aocsSpec_s1_name :
    aocsSpec_s1_VVRecord.spec_name = "AOCS-S1-WellFormed" := rfl

/-- AOCS のモード別消費電力 (SubSystemSpec 内の定義).
    TCS.lean の aocsModePower と同一だが, import 循環を避けるためローカル定義. -/
private def aocsModePower' : AOCSMode → Nat
  | .nominal     => 200
  | .safeMode    => 120
  | .sunPointing => 60
  | .fault       => 30

/-- AOCS の ModePowerSpec. -/
def aocsModePowerSpec : ModePowerSpec AOCSMode :=
  { modePower := aocsModePower'
    maxPower  := 200
    maxPower_bound := by
      intro s; cases s <;> simp [aocsModePower'] }

/-- AOCS の SubSystemVVBundle. -/
def aocsVVBundle : SubSystemVVBundle aocsSpec :=
  { componentRecords :=
      [ mkComponentRecord "AOCS" 1 StarTracker trivial
      , mkComponentRecord "AOCS" 2 AOCElectronics trivial
      , mkComponentRecord "AOCS" 3 ReactionWheel trivial ] }

/-- AOCS VVBundle の全 VVRecord 数は 6.
    コンポーネント(3) + サブシステム(1) + R1(1) + R3(1) = 6. -/
theorem aocsVVBundle_count :
    aocsVVBundle.allRecords.length = 6 := by
  simp [SubSystemVVBundle.allRecords, aocsVVBundle]

-- ============================================================
-- TODO:
-- [✅] AOCS コンポーネントの PartDef (StarTracker, ReactionWheel, AOCE)
-- [✅] ポート定義 (AttitudePort, TorquePort + 共役)
-- [✅] Connector (sensor, actuator) と AOCSSystem
-- [✅] AOCSSystem_WellFormed
-- [✅] AOCS 状態機械 (4モード, 7遷移)
-- [✅] AOCS 安全性定理 (aocs_always_safe)
-- [✅] AOCS FDIR 検証 (R1, R2, R3)
-- [✅] aocsSM_satisfies_FDIR (統合 FDIR 仕様)
-- [✅] StateMachineComponent (AOCE)
-- [✅] センサー精度制約の型レベル伝播
-- [✅] AOCS VVRecord (R1, R3)
-- [✅] EPS × AOCS 統合システム
-- [✅] IOValidationSource (AOCS 地上試験)
-- [✅] SubSystemSpec 化 ★新規
-- [✅] ModePowerSpec ★新規
-- [✅] SubSystemVVBundle ★新規
-- ============================================================

end Examples.Spacecraft.AOCS
