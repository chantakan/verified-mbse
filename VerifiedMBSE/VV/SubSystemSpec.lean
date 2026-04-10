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

/-- StructuralSpec: サブシステムの構造的側面。 -/
structure StructuralSpec where
  /-- サブシステム名 -/
  name : String
  /-- パート定義リスト -/
  parts : List PartDef
  /-- 接続リスト -/
  connectors : List Connector
  /-- System -/
  system : System
  /-- system.parts の整合性 -/
  system_eq_parts : system.parts = parts
  /-- system.connectors の整合性 -/
  system_eq_connectors : system.connectors = connectors
  /-- 構造的整合性 -/
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

/-- 全パートの不変条件が成立する命題。 -/
def StructuralSpec.allPartsInvariant (spec : StructuralSpec) : Prop :=
  ∀ p ∈ spec.parts, p.invariant

-- ============================================================
-- §2  BehavioralSpec
-- ============================================================

/-- BehavioralSpec: サブシステムの振る舞い的側面。 -/
structure BehavioralSpec (S : Type) (D : Type) (inv : S → D → Prop) where
  /-- 状態機械 -/
  sm : StateMachine S D inv
  /-- 状態機械の整合性 -/
  wellFormed : sm.WellFormed

-- ============================================================
-- §3  FDIRBundle
-- ============================================================

/-- FDIRBundle: FDIR 要件の証明束。 -/
structure FDIRBundle
    {S D : Type} {inv : S → D → Prop}
    (sm : StateMachine S D inv) where
  /-- 故障状態の判定 -/
  isFault : S → Prop
  /-- 復旧先状態の判定 -/
  isRecovery : S → Prop
  /-- データの安全条件 -/
  isSafe : D → Prop
  /-- R1: 安全性 □(isSafe d) -/
  safety : Always sm (fun _ d => isSafe d)
  /-- R2: 故障検知 ◇(isFault s) -/
  detection : Eventually sm (fun s _ => isFault s)
  /-- R3: 故障復旧 □(isFault → ◇ isRecovery) -/
  recovery : Leads sm (fun s _ => isFault s) (fun s _ => isRecovery s)

/-- FDIRBundle → FDIRSpec への変換。 -/
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

/-- SubSystemSpec: 構造 + 振る舞い + FDIR を統合したサブシステム仕様。
    新サブシステム追加時にこのインスタンスを1つ作るだけで完結する。 -/
structure SubSystemSpec (S : Type) (D : Type) (inv : S → D → Prop) where
  /-- 構造仕様 -/
  structural : StructuralSpec
  /-- 振る舞い仕様 -/
  behavioral : BehavioralSpec S D inv
  /-- FDIR 証明束 -/
  fdir : FDIRBundle behavioral.sm

/-- サブシステム名。 -/
def SubSystemSpec.name {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv) : String :=
  spec.structural.name

/-- System を取得。 -/
def SubSystemSpec.system {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv) : System :=
  spec.structural.system

/-- StateMachine を取得。 -/
def SubSystemSpec.stateMachine {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv) : StateMachine S D inv :=
  spec.behavioral.sm

/-- 整合性条件：構造と振る舞いの両方が WellFormed。 -/
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
-- §5  VVRecord の自動生成
-- ============================================================

/-- サブシステムレベルの VVRecord。 -/
def SubSystemSpec.subsystemRecord {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv) :
    VVRecord :=
  { layer        := .subsystem
    spec_name    := s!"{spec.structural.name}-S1-WellFormed"
    verification := spec.structural.system.WellFormed
    verified     := spec.structural.wellFormed
    validation   := ValidationTrace.init (.trusted spec.structural.wellFormed) }

/-- システムレベルの VVRecord (R1 Safety)。 -/
def SubSystemSpec.safetyRecord {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv) :
    VVRecord :=
  { layer        := .system
    spec_name    := s!"{spec.structural.name}-R1-Safety"
    verification := Always spec.behavioral.sm (fun _ d => spec.fdir.isSafe d)
    verified     := spec.fdir.safety
    validation   := ValidationTrace.init (.trusted spec.fdir.safety) }

/-- システムレベルの VVRecord (R3 Recovery)。 -/
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
-- §6  構造合成
-- ============================================================

/-- 二つのサブシステムを構造的に合成する。 -/
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

/-- 合成されたシステムのパート数は部分の和。 -/
theorem StructuralSpec.compose_parts_length
    (s1 s2 : StructuralSpec) (bridge : List Connector)
    (hbridge : ∀ c ∈ bridge,
        c.source.part ∈ s1.system.parts ++ s2.system.parts ∧
        c.target.part ∈ s1.system.parts ++ s2.system.parts) :
    (StructuralSpec.compose s1 s2 bridge hbridge).parts.length =
    s1.system.parts.length + s2.system.parts.length := by
  simp [StructuralSpec.compose, List.length_append]

end VerifiedMBSE.VV
