import VerifiedMBSE
import Examples.Spacecraft.EPS

/-!
# Integration: 複数サブシステム合成のテスト（B-8c 対応）

`FDIRBundle.compose` と `SubSystemSpec.compose` を用いた並列合成の
サニティテスト。**3 機以上のネスト合成**を B-8c で実現した。

## B-8c での拡張

B-7 までは `ProductStateMachine sm₁ sm₂` が第 1/2 引数とも `StateMachine` に
特化しており、`ProductStateMachine psm mini2SM`（psm を第一引数）が型として
通らなかったため 3 機以上のネスト合成は不可能だった。

B-8c では `ProductKripke` 型自体を `{α β} [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]`
ベースに一般化し、`FDIRBundle.compose` / `SubSystemSpec.compose` の WellFormed
引数を `NonEmpty` に弱化した。これにより:

1. `ProductKripke epsMiniPSM mini2SM`（3 機ネスト）が型として通る
2. 3 機目の合成では `epsMiniSpec.behavioral.nonEmpty` で
   `(ToKripke.toKripke epsMiniPSM).NonEmpty` を供給できる

## テスト対象

- `ProductKripke` の構築 (空構造体、StateMachine 特化 abbrev `ProductStateMachine` と互換)
- `FDIRBundle.compose` による `FDIRBundle pk` の自動生成
- `SubSystemSpec.compose` による `SubSystemSpec pk` の自動生成
- 合成後の `safety / detection / recovery` が型検査を通過すること
- 合成 spec でも VVRecord 生成系が動作すること
- 旧 `Always_prod / Eventually_prod / Leads_prod` でも互換に書けること
- **3 機ネスト合成 `(EPS × Mini) × Mini2` のサニティチェック (B-8c)**
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

/-- Mini の safety: 恒真（テスト用の最小保証）. -/
theorem mini_always_safe : Always miniSM (fun _ _ => True) :=
  fun _ _ _ => trivial

/-- Mini で faulty に到達可能. -/
theorem mini_fault_reachable : Reachable miniSM .faulty 0 :=
  Reachable.step miniToFault
    (Reachable.init 0 trivial)
    (by simp [miniSM]) rfl trivial

/-- Mini の detection: faulty に到達する. -/
theorem mini_eventually_fault :
    Eventually miniSM (fun s _ => s = .faulty) :=
  ⟨.faulty, 0, mini_fault_reachable, rfl⟩

/-- Mini の recovery: faulty → ok. -/
theorem mini_fault_leads_to_ok :
    Leads miniSM (fun s _ => s = .faulty) (fun s _ => s = .ok) := by
  intro s d hr heq
  subst heq
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
-- §3  Mini の SubSystemSpec (B-7)
-- ============================================================

/-- Mini の StructuralSpec（部品なし、空のシステム）。

    積合成テスト専用の最小 structural spec。parts = [] で
    System.WellFormed は「空のコネクタリストに対する任意主張」で自明。 -/
def miniStructural : StructuralSpec :=
  StructuralSpec.mk' "Mini" [] []
    (by intro c hc; simp at hc)

/-- Mini の BehavioralSpec（B-7: Kripke 一般化後）。 -/
def miniBehavioral : BehavioralSpec miniSM :=
  { nonEmpty := miniSM_WellFormed.nonEmpty }

/-- Mini の SubSystemSpec. -/
def miniSpec : SubSystemSpec miniSM :=
  { structural := miniStructural
    behavioral := miniBehavioral
    fdir       := miniFDIR }

-- ============================================================
-- §4  EPS × Mini の合成 (B-6 FDIRBundle, B-7 SubSystemSpec, B-8c NonEmpty)
-- ============================================================

/-- 積状態機械のマーカー (空構造体).

    `ProductStateMachine epsSM miniSM` は B-8 で `ProductKripke epsSM miniSM` の
    `abbrev` として後方互換提供されているため、`⟨⟩` で構築できる。 -/
def epsMiniPSM : ProductStateMachine epsSM miniSM := ⟨⟩

/-- 合成 FDIRBundle（B-6, B-8c）。

    B-8c で `FDIRBundle.compose` の引数が `WellFormed` から `NonEmpty` に
    弱化されたため、`.nonEmpty` で変換して渡す。 -/
def epsMiniFDIR : FDIRBundle epsMiniPSM :=
  FDIRBundle.compose epsFDIR miniFDIR epsMiniPSM
    epsSM_WellFormed.nonEmpty miniSM_WellFormed.nonEmpty

/-- 合成 SubSystemSpec（B-7, B-8c）。`bridge = []`（機間接続なし）で合成。

    名前は `"EPS+Mini"`（StructuralSpec.compose の規約による）。 -/
def epsMiniSpec : SubSystemSpec epsMiniPSM :=
  SubSystemSpec.compose epsSpec miniSpec epsMiniPSM
    epsSM_WellFormed.nonEmpty miniSM_WellFormed.nonEmpty
    [] (by intros; contradiction)

-- ============================================================
-- §5  サニティチェック: 合成 FDIRBundle (B-6)
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
-- §6  サニティチェック: 合成 SubSystemSpec (B-7)
-- ============================================================

/-- 合成 spec の name は "EPS+Mini" になる. -/
example : epsMiniSpec.name = "EPS+Mini" := rfl

/-- 合成 spec の fdir フィールドは `FDIRBundle.compose` の結果と defeq. -/
example :
    epsMiniSpec.fdir.isFault =
      (fun p : EPSMode × MiniMode => p.1 = .fault ∨ p.2 = .faulty) := rfl

/-- 合成 spec の behavioral.nonEmpty が取り出せる. -/
example : (ToKripke.toKripke epsMiniPSM).NonEmpty :=
  epsMiniSpec.behavioral.nonEmpty

-- ============================================================
-- §7  サニティチェック: 合成 spec からの VVRecord 自動生成 (B-7)
-- ============================================================

/-- 合成 spec から S1-WellFormed VVRecord が自動生成できる. -/
def epsMiniSpec_s1_VVRecord : VVRecord := epsMiniSpec.subsystemRecord

/-- 合成 spec から R1-Safety VVRecord が自動生成できる. -/
def epsMiniSpec_r1_VVRecord : VVRecord := epsMiniSpec.safetyRecord

/-- 合成 spec から R3-Recovery VVRecord が自動生成できる. -/
def epsMiniSpec_r3_VVRecord : VVRecord := epsMiniSpec.recoveryRecord

/-- 自動導出された R1 の spec_name は "EPS+Mini-R1-Safety". -/
theorem epsMiniSpec_r1_name :
    epsMiniSpec_r1_VVRecord.spec_name = "EPS+Mini-R1-Safety" := rfl

/-- 自動導出された S1 の spec_name は "EPS+Mini-S1-WellFormed". -/
theorem epsMiniSpec_s1_name :
    epsMiniSpec_s1_VVRecord.spec_name = "EPS+Mini-S1-WellFormed" := rfl

/-- 自動導出された R3 の spec_name は "EPS+Mini-R3-Recovery". -/
theorem epsMiniSpec_r3_name :
    epsMiniSpec_r3_VVRecord.spec_name = "EPS+Mini-R3-Recovery" := rfl

-- ============================================================
-- §8  後方互換: 旧 `*_prod` エイリアスでも書ける
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

-- ============================================================
-- §9  Mini2 Subsystem (B-8c: 3 機合成サニティテスト用)
-- ============================================================

/-- Mini2 の StateMachine。内容は Mini と同じだが独立したインスタンスとして
    定義することで、3 機合成の `SubSystemSpec.compose` で型引数 `x, y` が
    独立に推論される状況をテストする。 -/
def mini2SM : StateMachine MiniMode Nat miniInv where
  initialState := .ok
  transitions  := [miniToFault, miniToRecover]

/-- Mini2 の WellFormed. -/
theorem mini2SM_WellFormed : mini2SM.WellFormed := ⟨0, trivial⟩

/-- Mini2 の safety: 恒真. -/
theorem mini2_always_safe : Always mini2SM (fun _ _ => True) :=
  fun _ _ _ => trivial

/-- Mini2 で faulty に到達可能. -/
theorem mini2_fault_reachable : Reachable mini2SM .faulty 0 :=
  Reachable.step miniToFault
    (Reachable.init 0 trivial)
    (by simp [mini2SM]) rfl trivial

/-- Mini2 の detection: faulty に到達する. -/
theorem mini2_eventually_fault :
    Eventually mini2SM (fun s _ => s = .faulty) :=
  ⟨.faulty, 0, mini2_fault_reachable, rfl⟩

/-- Mini2 の recovery: faulty → ok. -/
theorem mini2_fault_leads_to_ok :
    Leads mini2SM (fun s _ => s = .faulty) (fun s _ => s = .ok) := by
  intro s d hr heq
  subst heq
  exact ⟨.ok, d,
    Reachable.step miniToRecover hr (by simp [mini2SM]) rfl trivial,
    rfl⟩

/-- Mini2 の FDIRBundle (Mini と同じ性質)。 -/
def mini2FDIR : FDIRBundle mini2SM where
  isFault    := fun s => s = .faulty
  isRecovery := fun s => s = .ok
  isSafe     := fun _ => True
  safety     := mini2_always_safe
  detection  := mini2_eventually_fault
  recovery   := mini2_fault_leads_to_ok

/-- Mini2 の StructuralSpec（部品名 "Mini2"）。 -/
def mini2Structural : StructuralSpec :=
  StructuralSpec.mk' "Mini2" [] []
    (by intro c hc; simp at hc)

/-- Mini2 の BehavioralSpec. -/
def mini2Behavioral : BehavioralSpec mini2SM :=
  { nonEmpty := mini2SM_WellFormed.nonEmpty }

/-- Mini2 の SubSystemSpec. -/
def mini2Spec : SubSystemSpec mini2SM :=
  { structural := mini2Structural
    behavioral := mini2Behavioral
    fdir       := mini2FDIR }

-- ============================================================
-- §10  3 機ネスト合成: (EPS × Mini) × Mini2 (B-8c ハイライト)
-- ============================================================

/-- 3 機ネスト合成のマーカー。`epsMiniPSM` (= `ProductKripke epsSM miniSM`) を
    第一引数として `mini2SM` と合成する。

    B-7 では型として通らなかった。B-8c で `ProductKripke` の型引数が
    `{α β} [ToKripke α _] [ToKripke β _]` に一般化されたため、
    `epsMiniPSM : ProductKripke epsSM miniSM` を x として受け取れる。 -/
def epsMiniMini2PK : ProductKripke epsMiniPSM mini2SM := ⟨⟩

/-- 3 機ネスト合成 SubSystemSpec。

    B-8c のハイライト: `epsMiniSpec.behavioral.nonEmpty` で
    `(ToKripke.toKripke epsMiniPSM).NonEmpty` を供給し、再帰的に合成可能。
    WellFormed ベースの旧 API では `psm.WellFormed` の分解に手作業が
    必要だったが、NonEmpty なら `BehavioralSpec.nonEmpty` がそのまま使える。 -/
def epsMiniMini2Spec : SubSystemSpec epsMiniMini2PK :=
  SubSystemSpec.compose epsMiniSpec mini2Spec epsMiniMini2PK
    epsMiniSpec.behavioral.nonEmpty mini2SM_WellFormed.nonEmpty
    [] (by intros; contradiction)

-- ============================================================
-- §11  サニティチェック: 3 機ネスト合成 (B-8c)
-- ============================================================

/-- 3 機合成 spec の name は "EPS+Mini+Mini2". -/
example : epsMiniMini2Spec.name = "EPS+Mini+Mini2" := rfl

/-- 3 機合成 isFault は 2 段 disjunction: `(p.1.1 = .fault ∨ p.1.2 = .faulty) ∨ p.2 = .faulty`. -/
example : epsMiniMini2Spec.fdir.isFault =
    (fun p : (EPSMode × MiniMode) × MiniMode =>
       (p.1.1 = .fault ∨ p.1.2 = .faulty) ∨ p.2 = .faulty) := rfl

/-- 3 機合成 isSafe は 2 段 conjunction: `(q.1.1 ≤ 1000 ∧ True) ∧ True`.
    データ型は **左結合** `(Nat × Nat) × Nat` (Lean の `×` は右結合なので
    型注釈は括弧で明示する必要がある)。 -/
example : epsMiniMini2Spec.fdir.isSafe =
    (fun q : (Nat × Nat) × Nat =>
       (q.1.1 ≤ 1000 ∧ True) ∧ True) := rfl

/-- 3 機合成 behavioral.nonEmpty が取り出せる. -/
example : (ToKripke.toKripke epsMiniMini2PK).NonEmpty :=
  epsMiniMini2Spec.behavioral.nonEmpty

/-- 3 機合成でも R1-Safety VVRecord が自動生成できる. -/
def epsMiniMini2Spec_r1_VVRecord : VVRecord := epsMiniMini2Spec.safetyRecord

/-- 3 機合成 R1 の spec_name は "EPS+Mini+Mini2-R1-Safety". -/
theorem epsMiniMini2Spec_r1_name :
    epsMiniMini2Spec_r1_VVRecord.spec_name = "EPS+Mini+Mini2-R1-Safety" := rfl

end Examples.Spacecraft.Integration
