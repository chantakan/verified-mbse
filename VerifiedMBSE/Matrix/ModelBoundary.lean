import VerifiedMBSE.Matrix.Query

/-!
# Model Boundary: Explicit Declaration of What Is Not Verified

形式検証はモデルの *内側* の性質を保証するに過ぎない。本モジュールはモデルの
*外側* を第一級の対象として扱い、「V&V マトリクスが緑である」ことと
「実システムが安全である」ことを混同しないようにする。

`ModelBoundary` は以下を記録する:
- 形式的に検証された性質、
- 証明ではなく試験・解析で裏付けられた性質、
- 意図的にモデル化しない残留リスク（rationale と mitigation を含む）。

意図は帳簿付けではなく epistemic honesty（認識論的誠実さ）にある。
システムに変更が入った際は境界記述も見直すべきである。

## F6 の変更点

旧実装では `ModelBoundary` が文字列 `systemName` と手動同期される
`verifiedCount : Nat` を持つフラット構造体で、対象 `VMatrix` との型上の
紐付けがなかった。本版では `ModelBoundary (vm : VMatrix)` として依存型化し、
`verifiedCount` は `vm.totalRecords` からの関数に置き換わる。これにより
他システム用の境界記述を誤って流用すると型エラーになる。

ファイルは VV から Matrix に移動した（VMatrix への依存のため）。
namespace も `VerifiedMBSE.Matrix` に変更されている。
-/

namespace VerifiedMBSE.Matrix

-- ============================================================
-- §1  Risk Categories
-- ============================================================

/-- 未モデル化リスクのカテゴリ。 -/
inductive RiskCategory where
  /-- 形式モデルの外側にある物理現象（宇宙線 SEU、微小隕石衝突、材料疲労等）。 -/
  | physical
  /-- 環境要因（太陽活動、熱極値、放射線）。 -/
  | environmental
  /-- ヒューマンファクタ（運用者エラー、手順誤用、訓練不足）。 -/
  | human
  /-- 検証境界の外側にあるソフトウェアリスク（COTS、ファームウェア、OS）。 -/
  | software
  /-- ハードウェアリスク（製造不良、経年劣化、部品差替え）。 -/
  | hardware
  /-- 組織・プロセスリスク（変更管理、サプライチェーン）。 -/
  | organizational
  deriving Repr, BEq, DecidableEq

/-- 人間可読のカテゴリ名。 -/
def RiskCategory.toString : RiskCategory → String
  | .physical       => "Physical"
  | .environmental  => "Environmental"
  | .human          => "Human"
  | .software       => "Software"
  | .hardware       => "Hardware"
  | .organizational => "Organizational"

instance : ToString RiskCategory := ⟨RiskCategory.toString⟩

-- ============================================================
-- §2  Evidence Kinds
-- ============================================================

/-- 性質を裏付ける根拠の強さ。証明と試験・解析を区別し、
    `ModelBoundary` がその差を隠さないようにする。 -/
inductive EvidenceKind where
  /-- Lean での形式証明。 -/
  | verified
  /-- 試験キャンペーン（ユニット試験、HIL、認定試験）による裏付け。 -/
  | tested
  /-- 解析手法（FMEA、FTA、Monte Carlo）による裏付け。 -/
  | analyzed
  deriving Repr, BEq, DecidableEq

/-- 人間可読の種別名。 -/
def EvidenceKind.toString : EvidenceKind → String
  | .verified => "Verified"
  | .tested   => "Tested"
  | .analyzed => "Analyzed"

instance : ToString EvidenceKind := ⟨EvidenceKind.toString⟩

-- ============================================================
-- §3  Unmodeled Risk
-- ============================================================

/-- UnmodeledRisk: 形式モデルがカバーしないリスク。rationale と mitigation を
    明示的に要求することで、エンジニアにそのギャップを命名・正当化させる。 -/
structure UnmodeledRisk where
  /-- リスクの短い説明。 -/
  description : String
  /-- リスクのカテゴリ。 -/
  category : RiskCategory
  /-- なぜこのリスクを形式化しないかの根拠。 -/
  rationale : String
  /-- 非形式の緩和策（プロセス、試験、冗長化、運用制約）。 -/
  mitigation : String
  deriving Repr

-- ============================================================
-- §4  Non-Verified Property
-- ============================================================

/-- NonFormalProperty: 試験・解析で裏付けられているが証明されていない性質。 -/
structure NonFormalProperty where
  /-- 性質の説明。 -/
  description : String
  /-- 非形式根拠の種別（`.tested` または `.analyzed`）。 -/
  kind : EvidenceKind
  /-- 根拠ソースの参照（報告書 ID、試験キャンペーン名など）。 -/
  source : String
  deriving Repr

-- ============================================================
-- §5  Model Boundary (Dependently Typed on VMatrix)
-- ============================================================

/-- ModelBoundary: モデルがカバーする範囲と外側のリスクを合わせた全体像。

    対象 VMatrix を型パラメータとして持つことで、他システム用の境界記述を
    誤って流用すると型エラーになる（F6）。`verifiedCount` は関数として
    `vm.totalRecords` から導出されるため、手動同期は不要。 -/
structure ModelBoundary (vm : VMatrix) where
  /-- この境界の識別子（典型的にはシステム名）。 -/
  systemName : String
  /-- 試験・解析で裏付けられているが証明されていない性質。 -/
  nonFormal : List NonFormalProperty
  /-- 意図的に形式化しないリスク。 -/
  unmodeled : List UnmodeledRisk
  deriving Repr

/-- 形式的に検証された性質の数。対象 VMatrix の全レコード数から自動導出される。 -/
def ModelBoundary.verifiedCount {vm : VMatrix} (_ : ModelBoundary vm) : Nat :=
  vm.totalRecords

/-- 未モデル化リスクの件数。 -/
def ModelBoundary.unmodeledCount {vm : VMatrix} (mb : ModelBoundary vm) : Nat :=
  mb.unmodeled.length

/-- 非形式性質の件数。 -/
def ModelBoundary.nonFormalCount {vm : VMatrix} (mb : ModelBoundary vm) : Nat :=
  mb.nonFormal.length

/-- 追跡している項目の総数（verified + non-formal + unmodeled）。 -/
def ModelBoundary.totalItems {vm : VMatrix} (mb : ModelBoundary vm) : Nat :=
  mb.verifiedCount + mb.nonFormalCount + mb.unmodeledCount

/-- 未モデル化リスクをカテゴリで絞り込む。 -/
def ModelBoundary.risksInCategory {vm : VMatrix}
    (mb : ModelBoundary vm) (cat : RiskCategory) : List UnmodeledRisk :=
  mb.unmodeled.filter (fun r => r.category == cat)

-- ============================================================
-- §6  Summary
-- ============================================================

/-- ModelBoundary を人間可読な要約文字列にレンダリングする。 -/
def ModelBoundary.summary {vm : VMatrix} (mb : ModelBoundary vm) : String :=
  let header := s!"Model Boundary: {mb.systemName}"
  let verified := s!"  Verified (formal proof): {mb.verifiedCount}"
  let nonFormal := s!"  Non-formal (test/analysis): {mb.nonFormalCount}"
  let unmodeled := s!"  Unmodeled risks: {mb.unmodeledCount}"
  let total := s!"  Total items: {mb.totalItems}"
  String.intercalate "\n" [header, verified, nonFormal, unmodeled, total]

end VerifiedMBSE.Matrix
