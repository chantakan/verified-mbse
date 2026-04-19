import VerifiedMBSE
import Examples.Spacecraft.EPS

/-!
# Integration: 複数サブシステム合成のテスト

`FDIRBundle.compose` を用いて EPS と簡易 Mini subsystem の FDIR を並列合成する。
積 FDIR 要件束の構築が sorry なしで通ることを確認するのが目的。

## B-6: FDIRBundle 統一後の API

以前は `epsMiniFDIR` の型が `ProductFDIRBundle epsMiniPSM F R Sa`
（`isFault / isRecovery / isSafe` はインデックス）だったが、B-6 で
`ProductFDIRBundle` が統一 `FDIRBundle` に合流したため、型は単に
`FDIRBundle epsMiniPSM` となる（これらはフィールドに移動）。合成後の
`.safety / .detection / .recovery` はそのまま取り出せる。

## テスト対象
- `ProductStateMachine` の構築 (空構造体)
- `FDIRBundle.compose` による `FDIRBundle psm` の自動生成
- 合成後の `safety / detection / recovery` が型検査を通過すること
- 旧 `Always_prod / Eventually_prod / Leads_prod` でも互換に書けること
-/

namespace Examples.Spacecraft.Integration

open VerifiedMBSE.Core
open VerifiedMBSE.Behavior
open VerifiedMBSE.VV
open Examples.Spacecraft.EPS

-- ============================================================
-- §1  Mini Subsystem (最小限の fault/recovery モデル)
-- ============================================================

/-- Mini subsystem の制御状態 (2 値). -/
inductive MiniMode where
  | ok
  | faulty
  deriving Repr, BEq, DecidableEq

/-- Mini の不変条件: データは常に許容される (テスト用)。 -/
def miniInv : MiniMode → Nat → Prop := fun _ _ => True

/-- Mini 遷移の共通 preserves (不変条件が常に True なので自明). -/
private theorem mini_preserves (src tgt : MiniMode) :
    ∀ n : Nat, (fun _ : Nat => True) n → miniInv src n → miniInv tgt (id n) := by
  intros; trivial

/-- 遷移: ok → faulty. -/
def miniToFault : Transition MiniMode Nat miniInv where
  source    := .ok
  target    := .faulty
  guard     := fun _ => True
  effect    := id
  preserves := mini_preserves .ok .faulty

/-- 遷移: faulty → ok. -/
def miniToRecover : Transition MiniMode Nat miniInv where
  source    := .faulty
  target    := .ok
  guard     := fun _ => True
  effect    := id
  preserves := mini_preserves .faulty .ok

/-- Mini subsystem の状態機械. -/
def miniSM : StateMachine MiniMode Nat miniInv where
  initialState := .ok
  transitions  := [miniToFault, miniToRecover]

/-- WellFormed: 初期データとして 0 を供給. -/
theorem miniSM_WellFormed : miniSM.WellFormed := ⟨0, trivial⟩

-- ============================================================
-- §2  Mini の LTL 保証
-- ============================================================

/-- R1: 常に safe (isSafe = True なので自明). -/
theorem mini_always_safe : Always miniSM (fun _ _ => True) :=
  fun _ _ _ => trivial

/-- Fault 状態への到達可能性. -/
theorem mini_fault_reachable : Reachable miniSM .faulty 0 :=
  Reachable.step miniToFault
    (Reachable.init 0 trivial)
    (by simp [miniSM]) rfl trivial

/-- R2: fault は eventually 到達可能. -/
theorem mini_eventually_fault :
    Eventually miniSM (fun s _ => s = .faulty) :=
  ⟨.faulty, 0, mini_fault_reachable, rfl⟩

/-- R3: fault → ◇ ok. -/
theorem mini_fault_leads_to_ok :
    Leads miniSM (fun s _ => s = .faulty) (fun s _ => s = .ok) := by
  intro s d hr hs
  subst hs
  exact ⟨.ok, d,
    Reachable.step miniToRecover hr (by simp [miniSM]) rfl trivial,
    rfl⟩

/-- Mini の FDIRBundle. -/
def miniFDIR : FDIRBundle miniSM where
  isFault    := fun s => s = .faulty
  isRecovery := fun s => s = .ok
  isSafe     := fun _ => True
  safety     := mini_always_safe
  detection  := mini_eventually_fault
  recovery   := mini_fault_leads_to_ok

-- ============================================================
-- §3  EPS × Mini の合成
-- ============================================================

/-- 積状態機械のマーカー (空構造体). -/
def epsMiniPSM : ProductStateMachine epsSM miniSM := ⟨⟩

/-- 合成 FDIRBundle (B-6 で統一 `FDIRBundle psm` に変更):
    - fault:    EPS が .fault または Mini が .faulty
    - recovery: EPS が .lowPower または Mini が .ok
    - safe:     EPS 電圧 ≤ 1000 かつ Mini は常に True -/
def epsMiniFDIR : FDIRBundle epsMiniPSM :=
  FDIRBundle.compose epsFDIR miniFDIR epsMiniPSM
    epsSM_WellFormed miniSM_WellFormed

-- ============================================================
-- §4  サニティチェック: 合成後の各フィールドが defeq で展開可能
-- ============================================================

/-- 合成 isFault は要素の `∨` として取り出せる. -/
example : epsMiniFDIR.isFault =
    (fun p : EPSMode × MiniMode => p.1 = .fault ∨ p.2 = .faulty) := rfl

/-- 合成 isRecovery は要素の `∨` として取り出せる. -/
example : epsMiniFDIR.isRecovery =
    (fun p : EPSMode × MiniMode => p.1 = .lowPower ∨ p.2 = .ok) := rfl

/-- 合成 isSafe は要素の `∧` として取り出せる. -/
example : epsMiniFDIR.isSafe =
    (fun q : Nat × Nat => q.1 ≤ 1000 ∧ True) := rfl

/-- 合成 safety が統一 `Always` として使える. -/
example :
    Always epsMiniPSM
      (fun _ q => q.1 ≤ 1000 ∧ True) :=
  epsMiniFDIR.safety

/-- 合成 detection が統一 `Eventually` として使える. -/
example :
    Eventually epsMiniPSM
      (fun p _ => p.1 = .fault ∨ p.2 = .faulty) :=
  epsMiniFDIR.detection

/-- 合成 recovery が統一 `Leads` として使える. -/
example :
    Leads epsMiniPSM
      (fun p _ => p.1 = .fault    ∨ p.2 = .faulty)
      (fun p _ => p.1 = .lowPower ∨ p.2 = .ok) :=
  epsMiniFDIR.recovery

-- ============================================================
-- §5  後方互換: 旧 `*_prod` エイリアスでも書ける
-- ============================================================

/-- 旧 `Always_prod` エイリアスでも書ける（defeq）. -/
example :
    Always_prod epsMiniPSM
      (fun _ q => q.1 ≤ 1000 ∧ True) :=
  epsMiniFDIR.safety

/-- 旧 `Eventually_prod` エイリアスでも書ける（defeq）. -/
example :
    Eventually_prod epsMiniPSM
      (fun p _ => p.1 = .fault ∨ p.2 = .faulty) :=
  epsMiniFDIR.detection

/-- 旧 `Leads_prod` エイリアスでも書ける（defeq）. -/
example :
    Leads_prod epsMiniPSM
      (fun p _ => p.1 = .fault    ∨ p.2 = .faulty)
      (fun p _ => p.1 = .lowPower ∨ p.2 = .ok) :=
  epsMiniFDIR.recovery

end Examples.Spacecraft.Integration
