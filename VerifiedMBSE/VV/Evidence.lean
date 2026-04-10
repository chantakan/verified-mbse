import VerifiedMBSE.VV.Layer

/-!
# ValidationEvidence: Confidence Levels as Types

Defines a three-tier confidence hierarchy (Confidence < Contract < Trusted),
promotion traces, and `VVRecord` — the unified representation of a V-model cell.
-/

namespace VerifiedMBSE.VV

-- ============================================================
-- §1  ValidationEvidence
-- ============================================================

/-- ValidationEvidence: 命題 P の妥当性確認の根拠を表す型。
    confidence < contract < trusted の三層構造。 -/
inductive ValidationEvidence (P : Prop) : Type where
  /-- Confidence: 確率的根拠（設計初期・専門家経験則）。 -/
  | confidence : Float → ValidationEvidence P
  /-- Contract: 条件付き保証（テスト・シミュレーション後）。 -/
  | contract : (assumption : Prop) → (assumption → P) → ValidationEvidence P
  /-- Trusted: 公理として受入（実機試験・承認済み）。 -/
  | trusted : P → ValidationEvidence P

/-- 確信度を数値で返す。 -/
def ValidationEvidence.confidenceLevel {P : Prop} :
    ValidationEvidence P → Float
  | .confidence p => p
  | .contract _ _ => 0.95
  | .trusted _    => 1.0

/-- 昇格: Confidence → Contract。 -/
def ValidationEvidence.promoteToContract {P : Prop}
    (_ : ValidationEvidence P)
    (a : Prop)
    (ev : a → P) :
    ValidationEvidence P :=
  .contract a ev

/-- 昇格: Contract → Trusted（前提条件が成立した場合）。 -/
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

/-- ValidationTrace: 昇格履歴付きレコード。 -/
structure ValidationTrace (P : Prop) where
  history : List (ValidationEvidence P)
  current : ValidationEvidence P

/-- ValidationTrace の初期化。 -/
def ValidationTrace.init {P : Prop}
    (ev : ValidationEvidence P) :
    ValidationTrace P :=
  { history := [], current := ev }

/-- ValidationTrace への昇格の記録。 -/
def ValidationTrace.promote {P : Prop}
    (t : ValidationTrace P)
    (next : ValidationEvidence P) :
    ValidationTrace P :=
  { history := t.history ++ [t.current]
    current := next }

/-- 現在の確信度レベルを取得。 -/
def ValidationTrace.currentLevel {P : Prop}
    (t : ValidationTrace P) : Float :=
  t.current.confidenceLevel

/-- トレースが昇格済みか。 -/
def ValidationTrace.hasBeenPromoted {P : Prop}
    (t : ValidationTrace P) : Bool :=
  !t.history.isEmpty

-- ============================================================
-- §3  VVRecord
-- ============================================================

/-- VVRecord: 一つの設計項目に対する VV の完全な記録。 -/
structure VVRecord where
  layer        : Layer
  spec_name    : String
  verification : Prop
  verified     : verification
  validation   : ValidationTrace verification

-- ============================================================
-- §4  IOValidationSource
-- ============================================================

/-- IOValidationSource: IO から得た Validation 根拠の型。 -/
structure IOValidationSource (P : Prop) where
  source_description : String
  declaration : P

/-- IO から Trusted ValidationEvidence を構成する。 -/
def fromIOValidation {P : Prop}
    (src : IOValidationSource P) :
    ValidationEvidence P :=
  .trusted src.declaration

-- ============================================================
-- §5  基本定理
-- ============================================================

/-- trusted の confidenceLevel は 1.0。 -/
theorem trusted_is_full_confidence {P : Prop} (h : P) :
    (ValidationEvidence.trusted h).confidenceLevel = 1.0 := by
  simp [ValidationEvidence.confidenceLevel]

/-- promote は履歴を1つ増やす。 -/
theorem promote_extends_history {P : Prop}
    (t : ValidationTrace P) (next : ValidationEvidence P) :
    (t.promote next).history.length = t.history.length + 1 := by
  simp [ValidationTrace.promote, List.length_append]

end VerifiedMBSE.VV
