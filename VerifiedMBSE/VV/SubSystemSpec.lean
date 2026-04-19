import VerifiedMBSE.Core.Compose
import VerifiedMBSE.Behavior.FDIR
import VerifiedMBSE.VV.Evidence

/-!
# SubSystemSpec: Parametric Subsystem Abstraction

`StructuralSpec`（構造）、`BehavioralSpec`（行動）、
`FDIRBundle`（FDIR の証明束）、およびこれら3つを統合した
`SubSystemSpec` を定義する。
-/

namespace VerifiedMBSE.VV

open VerifiedMBSE.Core
open VerifiedMBSE.Behavior

-- ============================================================
-- §1  StructuralSpec
-- ============================================================

/-- StructuralSpec: サブシステムの構造的側面。 -/
structure StructuralSpec where
  /-- サブシステム名 -/
  name : String
  /-- part 定義のリスト -/
  parts : List PartDef
  /-- connector のリスト -/
  connectors : List Connector
  /-- System -/
  system : System
  /-- system.parts との整合性 -/
  system_eq_parts : system.parts = parts
  /-- system.connectors との整合性 -/
  system_eq_connectors : system.connectors = connectors
  /-- 構造的 well-formedness -/
  wellFormed : system.WellFormed

/-- StructuralSpec のスマートコンストラクタ。 -/
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

/-- 全 part 不変条件が成立する命題。 -/
def StructuralSpec.allPartsInvariant (spec : StructuralSpec) : Prop :=
  ∀ p ∈ spec.parts, p.invariant

-- ============================================================
-- §2  BehavioralSpec
-- ============================================================

/-- BehavioralSpec: サブシステムの行動的側面。 -/
structure BehavioralSpec (S : Type) (D : Type) (inv : S → D → Prop) where
  /-- 状態機械 -/
  sm : StateMachine S D inv
  /-- 状態機械の well-formedness -/
  wellFormed : sm.WellFormed

-- ============================================================
-- §3  FDIRBundle
-- ============================================================

/-- FDIRBundle: FDIR 要件の証明束。 -/
structure FDIRBundle
    {S D : Type} {inv : S → D → Prop}
    (sm : StateMachine S D inv) where
  /-- fault 状態の述語 -/
  isFault : S → Prop
  /-- recovery 状態の述語 -/
  isRecovery : S → Prop
  /-- データの safety 条件 -/
  isSafe : D → Prop
  /-- R1: Safety □(isSafe d) -/
  safety : Always sm (fun _ d => isSafe d)
  /-- R2: Fault detection ◇(isFault s) -/
  detection : Eventually sm (fun s _ => isFault s)
  /-- R3: Fault recovery □(isFault → ◇ isRecovery) -/
  recovery : Leads sm (fun s _ => isFault s) (fun s _ => isRecovery s)

/-- FDIRBundle から FDIRSpec への変換。 -/
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

/-- SubSystemSpec: 構造・行動・FDIR を統合したサブシステム仕様。
    新しいサブシステムの追加はこの型の 1 インスタンスの構成で完結する。 -/
structure SubSystemSpec (S : Type) (D : Type) (inv : S → D → Prop) where
  /-- 構造仕様 -/
  structural : StructuralSpec
  /-- 行動仕様 -/
  behavioral : BehavioralSpec S D inv
  /-- FDIR 証明束 -/
  fdir : FDIRBundle behavioral.sm

/-- サブシステム名。 -/
def SubSystemSpec.name {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv) : String :=
  spec.structural.name

/-- System を取得する。 -/
def SubSystemSpec.system {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv) : System :=
  spec.structural.system

/-- StateMachine を取得する。 -/
def SubSystemSpec.stateMachine {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv) : StateMachine S D inv :=
  spec.behavioral.sm

/-- Consistent: 構造側と行動側のいずれも WellFormed。 -/
def SubSystemSpec.Consistent {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv) : Prop :=
  spec.structural.system.WellFormed ∧ spec.behavioral.sm.WellFormed

/-- FDIRSpec の自動導出。 -/
theorem SubSystemSpec.fdir_derivable {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv) :
    FDIRSpec spec.behavioral.sm
      spec.fdir.isFault spec.fdir.isRecovery spec.fdir.isSafe :=
  spec.fdir.toFDIRSpec

-- ============================================================
-- §5  Automatic VVRecord Generation
-- ============================================================

/-
record 生成関数は evidence-level を明示パラメータで受け取る（F1）。
デフォルトは `.trusted` を使うため、既存の呼び出しは変更不要で後方互換を保つ。
`.contract`（仮定付き保証）や `.confidence`（確率的評価）を使いたい呼び出し側は、
第 2 引数として明示的に `ValidationEvidence` を渡すことで三層評価が選択できる。
-/

/-- サブシステムレベルの VVRecord（S1-WellFormed）。

    `ev` は対応する検証命題 `spec.structural.system.WellFormed` に対する
    `ValidationEvidence`。デフォルトは `.trusted spec.structural.wellFormed`。 -/
def SubSystemSpec.subsystemRecord {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv)
    (ev : ValidationEvidence spec.structural.system.WellFormed :=
            .trusted spec.structural.wellFormed) :
    VVRecord :=
  { layer        := .subsystem
    spec_name    := s!"{spec.structural.name}-S1-WellFormed"
    verification := spec.structural.system.WellFormed
    verified     := spec.structural.wellFormed
    validation   := ValidationTrace.init ev }

/-- システムレベルの VVRecord（R1 Safety）。

    `ev` は `Always spec.behavioral.sm (fun _ d => spec.fdir.isSafe d)` に対する
    `ValidationEvidence`。デフォルトは `.trusted spec.fdir.safety`。 -/
def SubSystemSpec.safetyRecord {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv)
    (ev : ValidationEvidence
            (Always spec.behavioral.sm (fun _ d => spec.fdir.isSafe d)) :=
            .trusted spec.fdir.safety) :
    VVRecord :=
  { layer        := .system
    spec_name    := s!"{spec.structural.name}-R1-Safety"
    verification := Always spec.behavioral.sm (fun _ d => spec.fdir.isSafe d)
    verified     := spec.fdir.safety
    validation   := ValidationTrace.init ev }

/-- システムレベルの VVRecord（R3 Recovery）。

    `ev` は `Leads` 命題に対する `ValidationEvidence`。
    デフォルトは `.trusted spec.fdir.recovery`。 -/
def SubSystemSpec.recoveryRecord {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv)
    (ev : ValidationEvidence
            (Leads spec.behavioral.sm
              (fun s _ => spec.fdir.isFault s)
              (fun s _ => spec.fdir.isRecovery s)) :=
            .trusted spec.fdir.recovery) :
    VVRecord :=
  { layer        := .system
    spec_name    := s!"{spec.structural.name}-R3-Recovery"
    verification := Leads spec.behavioral.sm
                      (fun s _ => spec.fdir.isFault s)
                      (fun s _ => spec.fdir.isRecovery s)
    verified     := spec.fdir.recovery
    validation   := ValidationTrace.init ev }

-- ============================================================
-- §6  Structural Composition
-- ============================================================

/-- 2 つのサブシステムを構造的に合成する。 -/
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

/-- 合成後の part 数は各サブシステムの part 数の和に一致する。 -/
theorem StructuralSpec.compose_parts_length
    (s1 s2 : StructuralSpec) (bridge : List Connector)
    (hbridge : ∀ c ∈ bridge,
        c.source.part ∈ s1.system.parts ++ s2.system.parts ∧
        c.target.part ∈ s1.system.parts ++ s2.system.parts) :
    (StructuralSpec.compose s1 s2 bridge hbridge).parts.length =
    s1.system.parts.length + s2.system.parts.length := by
  simp [StructuralSpec.compose, List.length_append]

end VerifiedMBSE.VV
