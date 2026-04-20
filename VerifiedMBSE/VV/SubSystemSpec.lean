import VerifiedMBSE.Core.Compose
import VerifiedMBSE.Behavior.FDIR
import VerifiedMBSE.VV.Evidence

/-!
# SubSystemSpec: Parametric Subsystem Abstraction (Kripke-Generalized)

`StructuralSpec`（構造）、`BehavioralSpec`（行動）、
`FDIRBundle`（FDIR の証明束）、およびこれら3つを統合した
`SubSystemSpec` を定義する。

## B-7: SubSystemSpec / BehavioralSpec の Kripke 一般化

B-6 で `FDIRBundle` を `ToKripke α S D` ベースに統一したのに続き、B-7 で
`BehavioralSpec` と `SubSystemSpec` も同様に `ToKripke α S D` ベースに
一般化した。これにより以下が同一型の構造として扱える:

- `SubSystemSpec sm` — 単一サブシステム仕様（`sm : StateMachine S D inv`）
- `SubSystemSpec psm` — 合成サブシステム仕様（`psm : ProductStateMachine sm₁ sm₂`）

合成（2機合成、ネストにより N 機）は `VV/ProductFDIR.lean` の
`SubSystemSpec.compose` で提供する。

### 破壊的変更 (A 案)

B-7 は **A 案** を採用している。旧 API:

```lean
def epsBehavioral : BehavioralSpec EPSMode Nat epsGlobalInv :=
  { sm := epsSM, wellFormed := epsSM_WellFormed }
def epsSpec : SubSystemSpec EPSMode Nat epsGlobalInv := ...
```

新 API:

```lean
def epsBehavioral : BehavioralSpec epsSM :=
  { nonEmpty := epsSM_WellFormed.nonEmpty }
def epsSpec : SubSystemSpec epsSM := ...
```

`BehavioralSpec` の `wellFormed : sm.WellFormed` フィールドは
`nonEmpty : (toKripke x).NonEmpty` に変わる。`StateMachine.WellFormed.nonEmpty`
で変換可能。合成時に必要な強い `WellFormed` は `SubSystemSpec.compose` に
明示引数として渡す（`FDIRBundle.compose` と一貫）。
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
-- §2  BehavioralSpec (Kripke-Generalized)
-- ============================================================

/-- BehavioralSpec: サブシステムの行動的側面（Kripke 一般化版）。

    `ToKripke α S D` 型クラス経由で意味論が与えられるため、`x : α` として
    `StateMachine S D inv` や `ProductStateMachine sm₁ sm₂` を渡せる。

    `nonEmpty` フィールドは Kripke 構造としての非空性（到達可能な
    `(s, d)` が存在する）。`StateMachine sm` の場合は `sm.WellFormed` から
    `StateMachine.WellFormed.nonEmpty` で変換可能。 -/
structure BehavioralSpec
    {α : Type} {S D : Type} [ToKripke α S D]
    (x : α) where
  /-- Kripke 構造としての非空性: 到達可能な `(s, d)` が存在する。 -/
  nonEmpty : (ToKripke.toKripke x).NonEmpty

-- ============================================================
-- §3  FDIRBundle (Unified via ToKripke, B-6)
-- ============================================================

/-- FDIRBundle: FDIR 要件の証明束（統一版、B-6）。

    `ToKripke α S D` 型クラス経由で意味論が与えられるため、`x : α` として
    `StateMachine S D inv` や `ProductStateMachine sm₁ sm₂` を直接渡せる。

    - `FDIRBundle sm` (sm : StateMachine S D inv) — 単一サブシステムの FDIR
    - `FDIRBundle psm` (psm : ProductStateMachine sm₁ sm₂) — 合成サブシステムの FDIR

    合成された `FDIRBundle` の構築方法は `VV/ProductFDIR.lean` の
    `FDIRBundle.compose` を参照。 -/
structure FDIRBundle
    {α : Type} {S D : Type} [ToKripke α S D]
    (x : α) where
  /-- fault 状態の述語 -/
  isFault : S → Prop
  /-- recovery 状態の述語 -/
  isRecovery : S → Prop
  /-- データの safety 条件 -/
  isSafe : D → Prop
  /-- R1: Safety □(isSafe d) -/
  safety : Always x (fun _ d => isSafe d)
  /-- R2: Fault detection ◇(isFault s) -/
  detection : Eventually x (fun s _ => isFault s)
  /-- R3: Fault recovery □(isFault → ◇ isRecovery) -/
  recovery : Leads x (fun s _ => isFault s) (fun s _ => isRecovery s)

/-- FDIRBundle から FDIRSpec への変換（StateMachine 特化）。

    `FDIRSpec` は現状 `StateMachine` 上にのみ定義されているため、この変換は
    `StateMachine` 版の `FDIRBundle` に対してのみ意味を持つ。積状態機械上の
    `FDIRBundle` は `.isFault` / `.safety` 等のフィールドを直接利用すればよい。 -/
def FDIRBundle.toFDIRSpec
    {S D : Type} {inv : S → D → Prop}
    {sm : StateMachine S D inv}
    (bundle : FDIRBundle sm) :
    FDIRSpec sm bundle.isFault bundle.isRecovery bundle.isSafe :=
  { safety    := bundle.safety
    detection := bundle.detection
    recovery  := bundle.recovery }

-- ============================================================
-- §4  SubSystemSpec (Kripke-Generalized)
-- ============================================================

/-- SubSystemSpec: 構造・行動・FDIR を統合したサブシステム仕様（Kripke 一般化版）。

    `ToKripke α S D` 型クラスを通して、`StateMachine` 版と
    `ProductStateMachine` 版を同一構造で扱える。合成は
    `SubSystemSpec.compose` (VV/ProductFDIR.lean) で提供。

    新しいサブシステムの追加はこの型の 1 インスタンスの構成で完結する。 -/
structure SubSystemSpec
    {α : Type} {S D : Type} [ToKripke α S D]
    (x : α) where
  /-- 構造仕様 -/
  structural : StructuralSpec
  /-- 行動仕様 -/
  behavioral : BehavioralSpec x
  /-- FDIR 証明束 -/
  fdir : FDIRBundle x

/-- サブシステム名。 -/
def SubSystemSpec.name
    {α : Type} {S D : Type} [ToKripke α S D] {x : α}
    (spec : SubSystemSpec x) : String :=
  spec.structural.name

/-- System を取得する。 -/
def SubSystemSpec.system
    {α : Type} {S D : Type} [ToKripke α S D] {x : α}
    (spec : SubSystemSpec x) : System :=
  spec.structural.system

/-- StateMachine を取得する（StateMachine 特化）。

    一般化された `SubSystemSpec` では `x : α` なので、StateMachine を
    取り出せるのは `x : StateMachine S D inv` のケースのみ。この版では
    `x` 自身がそのまま StateMachine として返される。 -/
def SubSystemSpec.stateMachine
    {S D : Type} {inv : S → D → Prop} {sm : StateMachine S D inv}
    (_spec : SubSystemSpec sm) : StateMachine S D inv :=
  sm

/-- Consistent: 構造側 WellFormed かつ 行動側 NonEmpty。

    旧 API の `spec.structural.system.WellFormed ∧ spec.behavioral.sm.WellFormed`
    は、Kripke 一般化後は後者が `NonEmpty` に弱まる。StateMachine 版では
    `StateMachine.WellFormed.nonEmpty` で従来の強い条件から導出可能。 -/
def SubSystemSpec.Consistent
    {α : Type} {S D : Type} [ToKripke α S D] {x : α}
    (spec : SubSystemSpec x) : Prop :=
  spec.structural.system.WellFormed ∧ (ToKripke.toKripke x).NonEmpty

/-- FDIRSpec の自動導出（StateMachine 特化）。

    `FDIRSpec` は StateMachine 特化なので、`x : StateMachine S D inv` の
    ケースのみ対応。一般化された `SubSystemSpec` の他のインスタンス化では
    代わりに `spec.fdir.safety` 等の直接アクセスを使う。 -/
theorem SubSystemSpec.fdir_derivable
    {S D : Type} {inv : S → D → Prop} {sm : StateMachine S D inv}
    (spec : SubSystemSpec sm) :
    FDIRSpec sm
      spec.fdir.isFault spec.fdir.isRecovery spec.fdir.isSafe :=
  spec.fdir.toFDIRSpec

-- ============================================================
-- §5  Automatic VVRecord Generation (Kripke-Generalized)
-- ============================================================

/-
record 生成関数は evidence-level を明示パラメータで受け取る（F1）。
デフォルトは `.trusted` を使うため、既存の呼び出しは変更不要で後方互換を保つ。
`.contract`（仮定付き保証）や `.confidence`（確率的評価）を使いたい呼び出し側は、
第 2 引数として明示的に `ValidationEvidence` を渡すことで三層評価が選択できる。

B-7 で `SubSystemSpec` を Kripke 一般化したことに伴い、これらの生成関数も
`x : α` ベースに一般化された。StateMachine 版も ProductStateMachine 版も
同じ生成関数を使える。
-/

/-- サブシステムレベルの VVRecord（S1-WellFormed）。

    `ev` は対応する検証命題 `spec.structural.system.WellFormed` に対する
    `ValidationEvidence`。デフォルトは `.trusted spec.structural.wellFormed`。 -/
def SubSystemSpec.subsystemRecord
    {α : Type} {S D : Type} [ToKripke α S D] {x : α}
    (spec : SubSystemSpec x)
    (ev : ValidationEvidence spec.structural.system.WellFormed :=
            .trusted spec.structural.wellFormed) :
    VVRecord :=
  { layer        := .subsystem
    spec_name    := s!"{spec.structural.name}-S1-WellFormed"
    verification := spec.structural.system.WellFormed
    verified     := spec.structural.wellFormed
    validation   := ValidationTrace.init ev }

/-- システムレベルの VVRecord（R1 Safety）。

    `ev` は `Always x (fun _ d => spec.fdir.isSafe d)` に対する
    `ValidationEvidence`。デフォルトは `.trusted spec.fdir.safety`。 -/
def SubSystemSpec.safetyRecord
    {α : Type} {S D : Type} [ToKripke α S D] {x : α}
    (spec : SubSystemSpec x)
    (ev : ValidationEvidence
            (Always x (fun _ d => spec.fdir.isSafe d)) :=
            .trusted spec.fdir.safety) :
    VVRecord :=
  { layer        := .system
    spec_name    := s!"{spec.structural.name}-R1-Safety"
    verification := Always x (fun _ d => spec.fdir.isSafe d)
    verified     := spec.fdir.safety
    validation   := ValidationTrace.init ev }

/-- システムレベルの VVRecord（R3 Recovery）。

    `ev` は `Leads` 命題に対する `ValidationEvidence`。
    デフォルトは `.trusted spec.fdir.recovery`。 -/
def SubSystemSpec.recoveryRecord
    {α : Type} {S D : Type} [ToKripke α S D] {x : α}
    (spec : SubSystemSpec x)
    (ev : ValidationEvidence
            (Leads x
              (fun s _ => spec.fdir.isFault s)
              (fun s _ => spec.fdir.isRecovery s)) :=
            .trusted spec.fdir.recovery) :
    VVRecord :=
  { layer        := .system
    spec_name    := s!"{spec.structural.name}-R3-Recovery"
    verification := Leads x
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
