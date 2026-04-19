import VerifiedMBSE.VV.Layer

/-!
# ValidationEvidence: Confidence Levels as Types

Confidence < Contract < Trusted の三層階層、昇格トレース、および V モデルの
セルを統一的に表す `VVRecord` を定義する。
-/

namespace VerifiedMBSE.VV

-- ============================================================
-- §1  ValidationEvidence
-- ============================================================

/-- ValidationEvidence: 命題 P の検証根拠を表す型。
    三層階層: confidence < contract < trusted。 -/
inductive ValidationEvidence (P : Prop) : Type where
  /-- Confidence: 確率的な根拠（初期設計、専門家ヒューリスティクス）。 -/
  | confidence : Float → ValidationEvidence P
  /-- Contract: 条件付き保証（試験・シミュレーション後）。 -/
  | contract : (assumption : Prop) → (assumption → P) → ValidationEvidence P
  /-- Trusted: 公理として採用（ハードウェア試験、承認済み）。 -/
  | trusted : P → ValidationEvidence P

/-- 根拠の信頼度を数値で返す（表示・ソート用）。

    注意: この Float を使った比較は丸め誤差の観点で推奨されない。
    「trusted かどうか」の判定には `isTrusted` を使うこと（F2 参照）。 -/
def ValidationEvidence.confidenceLevel {P : Prop} :
    ValidationEvidence P → Float
  | .confidence p => p
  | .contract _ _ => 0.95
  | .trusted _    => 1.0

/-- ValidationEvidence が `.trusted` 構造子であるかを判定する。
    Float 等号を介さない構造的判別で、`fullyTrusted` 等の Bool 計算で用いる。 -/
def ValidationEvidence.isTrusted {P : Prop} :
    ValidationEvidence P → Bool
  | .trusted _ => true
  | _          => false

/-- ValidationEvidence が `.contract` 構造子であるかを判定する。 -/
def ValidationEvidence.isContract {P : Prop} :
    ValidationEvidence P → Bool
  | .contract _ _ => true
  | _             => false

/-- ValidationEvidence が `.confidence` 構造子であるかを判定する。 -/
def ValidationEvidence.isConfidence {P : Prop} :
    ValidationEvidence P → Bool
  | .confidence _ => true
  | _             => false

/-- 昇格: Confidence → Contract。 -/
def ValidationEvidence.promoteToContract {P : Prop}
    (_ : ValidationEvidence P)
    (a : Prop)
    (ev : a → P) :
    ValidationEvidence P :=
  .contract a ev

/-- 昇格: Contract → Trusted（仮定が実際に成立する場合）。 -/
def ValidationEvidence.promoteToTrusted {P : Prop}
    (c : ValidationEvidence P)
    (h : match c with
         | .contract a _ => a
         | _ => True) :
    ValidationEvidence P :=
  match c, h with
  | .contract _ ev, h  => .trusted (ev h)
  | .confidence p, _   => .confidence p
  | .trusted p, _      => .trusted p

-- ============================================================
-- §2  ValidationTrace
-- ============================================================

/-- ValidationTrace: 昇格履歴を保持するレコード。 -/
structure ValidationTrace (P : Prop) where
  history : List (ValidationEvidence P)
  current : ValidationEvidence P

/-- ValidationTrace の初期化。 -/
def ValidationTrace.init {P : Prop}
    (ev : ValidationEvidence P) :
    ValidationTrace P :=
  { history := [], current := ev }

/-- ValidationTrace に昇格を記録する。 -/
def ValidationTrace.promote {P : Prop}
    (t : ValidationTrace P)
    (next : ValidationEvidence P) :
    ValidationTrace P :=
  { history := t.history ++ [t.current]
    current := next }

/-- 現時点の信頼度を取得する。 -/
def ValidationTrace.currentLevel {P : Prop}
    (t : ValidationTrace P) : Float :=
  t.current.confidenceLevel

/-- 現時点の根拠が `.trusted` かを判定する（構造子一致）。 -/
def ValidationTrace.isTrusted {P : Prop}
    (t : ValidationTrace P) : Bool :=
  t.current.isTrusted

/-- trace が昇格済みかを判定する。 -/
def ValidationTrace.hasBeenPromoted {P : Prop}
    (t : ValidationTrace P) : Bool :=
  !t.history.isEmpty

-- ============================================================
-- §3  VVRecord
-- ============================================================

/-- VVRecord: 単一の設計項目に対する完全な V&V レコード。 -/
structure VVRecord where
  layer        : Layer
  spec_name    : String
  verification : Prop
  verified     : verification
  validation   : ValidationTrace verification

-- ============================================================
-- §4  IOValidationSource
-- ============================================================

/-- IOValidationSource: IO から得られた検証根拠。 -/
structure IOValidationSource (P : Prop) where
  source_description : String
  declaration : P

/-- IO 由来の Trusted ValidationEvidence を構築する。 -/
def fromIOValidation {P : Prop}
    (src : IOValidationSource P) :
    ValidationEvidence P :=
  .trusted src.declaration

-- ============================================================
-- §5  Basic Theorems
-- ============================================================

/-- trusted の confidenceLevel は 1.0。 -/
theorem trusted_is_full_confidence {P : Prop} (h : P) :
    (ValidationEvidence.trusted h).confidenceLevel = 1.0 := by
  simp [ValidationEvidence.confidenceLevel]

/-- trusted は isTrusted を true にする。 -/
theorem trusted_isTrusted {P : Prop} (h : P) :
    (ValidationEvidence.trusted h).isTrusted = true := by
  simp [ValidationEvidence.isTrusted]

/-- confidence は isTrusted を true にしない。 -/
theorem confidence_not_isTrusted {P : Prop} (p : Float) :
    (ValidationEvidence.confidence p : ValidationEvidence P).isTrusted = false := by
  simp [ValidationEvidence.isTrusted]

/-- contract は isTrusted を true にしない。 -/
theorem contract_not_isTrusted {P : Prop} (a : Prop) (ev : a → P) :
    (ValidationEvidence.contract a ev).isTrusted = false := by
  simp [ValidationEvidence.isTrusted]

/-- promote は履歴を 1 つ増やす。 -/
theorem promote_extends_history {P : Prop}
    (t : ValidationTrace P) (next : ValidationEvidence P) :
    (t.promote next).history.length = t.history.length + 1 := by
  simp [ValidationTrace.promote, List.length_append]

end VerifiedMBSE.VV
