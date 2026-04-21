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
-- §4  SubSystemSpec (B-7: Kripke-generalized)
-- ============================================================

def epsStructural : StructuralSpec :=
  StructuralSpec.mk' "EPS" [PowerSupply, Load] [powerConnector]
    EPSSystem_WellFormed

/-- EPS の BehavioralSpec（B-7: Kripke 一般化後）。
    `nonEmpty` は `StateMachine.WellFormed.nonEmpty` で `epsSM_WellFormed` から変換。 -/
def epsBehavioral : BehavioralSpec epsSM :=
  { nonEmpty := epsSM_WellFormed.nonEmpty }

def epsFDIR : FDIRBundle epsSM :=
  { isFault    := fun s => s = .fault
    isRecovery := fun s => s = .lowPower
    isSafe     := fun v => v ≤ 1000
    safety     := eps_always_safe
    detection  := eps_eventually_fault
    recovery   := eps_fault_leads_to_lowPower }

/-- EPS の SubSystemSpec（B-7: `SubSystemSpec epsSM` 形式）。 -/
def epsSpec : SubSystemSpec epsSM :=
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
-- §6  StateMachineComponent (Phase 2/3 接続) — F8 Interpretation パターン
-- ============================================================

/-!
## F8 Interpretation パターン適用

旧版は `EPSNatInterpretation` の本体で直接 `match t.name with | some "PowerSupply" ... | _ => Unit`
を書いていた。これは typo 時の silent unsoundness（`_ => Unit` に流れて Unit は全述語を
満たしてしまう）や、モデル拡張時の case 漏れなどのリスクがあった。

本節では `docs/InterpretationPattern.md` の推奨パターンに沿って:

1. ドメイン固有の `EPSTypeTag` enum を定義（PowerSupply/Load/PowerPort/~PowerPort を網羅）
2. enum と KerMLType の紐付けを `toName` / `toKerMLType` に集約
3. 逆引き `fromName : Option String → Option EPSTypeTag` を 1 箇所に閉じ込め
4. 担体型割当 `interp : EPSTypeTag → Type` を **`_` なしの網羅的 pattern match** で
5. `EPSNatInterpretation` は `fromName ∘ interp` の合成として構築

これにより、EPS に新型を追加したい場合は `EPSTypeTag` に case を足すだけで
コンパイラが未網羅エラーを出してくれる（文字列の typo は `fromName` の中だけに閉じ込め）。
-/

/-- EPS サブシステムに出現する全 KerMLType の識別子. -/
inductive EPSTypeTag where
  /-- 電力供給器パーツ (`PowerSupply : PartDef`). -/
  | powerSupply
  /-- 電力負荷パーツ (`Load : PartDef`). -/
  | load
  /-- 電力フローポート (`EPSPowerPort`). -/
  | powerPort
  /-- 共役電力ポート (`EPSConjPowerPort` = `~PowerPort`). -/
  | powerPortConj
  deriving Repr, BEq, DecidableEq

/-- Tag から KerMLType の `name` 文字列へ。文字列リテラルが現れるのはこの関数のみ。 -/
def EPSTypeTag.toName : EPSTypeTag → String
  | .powerSupply   => "PowerSupply"
  | .load          => "Load"
  | .powerPort     => "PowerPort"
  | .powerPortConj => "~PowerPort"

/-- Tag から KerMLType への埋め込み（1 対 1）。 -/
def EPSTypeTag.toKerMLType (tag : EPSTypeTag) : KerMLType :=
  { name := some tag.toName }

/-- 逆引き: KerMLType の name から Tag へ。文字列マッチはこの関数の中に集約される。
    ドメイン外の型名は `none` を返す。 -/
def EPSTypeTag.fromName : Option String → Option EPSTypeTag
  | some "PowerSupply"  => some .powerSupply
  | some "Load"         => some .load
  | some "PowerPort"    => some .powerPort
  | some "~PowerPort"   => some .powerPortConj
  | _                   => none

/-- 各 tag の担体型割当。**網羅的 pattern match**（`_` なし）。
    EPS に新 tag を追加するとここで未網羅エラーが出る → 対応を忘れる事故を防ぐ。 -/
def EPSTypeTag.interp : EPSTypeTag → Type
  | .powerSupply   => Nat
  | .load          => Nat
  | .powerPort     => Nat
  | .powerPortConj => Nat

/-- EPS の Interpretation（F8 パターン適用）。

    ## 設計

    - 文字列マッチは `fromName` の 1 箇所に閉じ込められている。
    - 担体型割当は `interp` の網羅的 pattern match で保証される。
    - ドメイン外の型名は `Unit`（既存互換。SafeSwarm で厳格化する場合は `Empty` へ）。 -/
def EPSNatInterpretation : Interpretation := fun t =>
  match EPSTypeTag.fromName t.name with
  | some tag => tag.interp
  | none     => Unit

/-- リファクタ前後で挙動が一致することの健全性チェック: 既存の 4 型では Nat を返す. -/
theorem EPSNatInterpretation_powerSupply :
    EPSNatInterpretation { name := some "PowerSupply" } = Nat := rfl

theorem EPSNatInterpretation_load :
    EPSNatInterpretation { name := some "Load" } = Nat := rfl

theorem EPSNatInterpretation_powerPort :
    EPSNatInterpretation { name := some "PowerPort" } = Nat := rfl

theorem EPSNatInterpretation_powerPortConj :
    EPSNatInterpretation { name := some "~PowerPort" } = Nat := rfl

/-- 既存の StateMachineComponent は `PowerSupply.baseType` (= `{ name := some "PowerSupply" }`)
    を通して `EPSNatInterpretation` に問い合わせるため、リファクタ後も型整合. -/
def epsStateMachineComponent :
    StateMachineComponent EPSNatInterpretation PowerSupply EPSMode epsGlobalInv :=
  { compat := fun _ _ _ => trivial, sm := epsSM }

end Examples.Spacecraft.EPS
