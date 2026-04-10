/-!
# 抽象化レベルと設計パラメータ

AbstractionLevel（n-truncation の MBSE 版）と
DesignParameter（cubical structure の離散版）を定義する。
-/

namespace VerifiedMBSE.Equivalence

-- ============================================================
-- §1  AbstractionLevel
-- ============================================================

/-- AbstractionLevel: 設計の抽象化レベル。
    HoTT の n-truncation の MBSE 版。 -/
inductive AbstractionLevel where
  /-- コンセプトレベル: 要件のみ -/
  | concept
  /-- 論理レベル: インターフェース定義 -/
  | logical
  /-- 物理レベル: 具体的実装 -/
  | physical
  deriving Repr, BEq, DecidableEq

/-- 抽象化レベル間の洗練関係: 下位は上位を洗練する。 -/
def AbstractionLevel.refines : AbstractionLevel → AbstractionLevel → Prop
  | .physical, .logical  => True
  | .physical, .concept  => True
  | .logical,  .concept  => True
  | _,         _         => False

/-- 抽象化洗練は推移的。 -/
theorem AbstractionLevel.refines_trans
    {l₁ l₂ l₃ : AbstractionLevel}
    (h₁₂ : AbstractionLevel.refines l₁ l₂)
    (h₂₃ : AbstractionLevel.refines l₂ l₃) :
    AbstractionLevel.refines l₁ l₃ := by
  cases l₁ <;> cases l₂ <;> cases l₃ <;> simp [AbstractionLevel.refines] at *

-- ============================================================
-- §2  DesignParameter
-- ============================================================

/-- DesignParameter: 設計パラメータの型。
    Cubical structure の離散版。 -/
structure DesignParameter (α : Type) where
  /-- パラメータ値 -/
  value : α
  /-- 許容範囲 -/
  valid : α → Prop
  /-- 現在値は許容範囲内 -/
  inRange : valid value

/-- パラメトリック不変条件:
    全ての有効なパラメータ値で inv が成立する。
    Cubical path Π(p : I). inv(p) の離散版。 -/
def ParametricInvariant {α : Type}
    (param : DesignParameter α)
    (inv : α → Prop) : Prop :=
  ∀ p : α, param.valid p → inv p

/-- 具体例: 電力バジェットパラメータ（400-600W）。 -/
def powerBudgetParam : DesignParameter Nat :=
  { value   := 500
    valid   := fun n => 400 ≤ n ∧ n ≤ 600
    inRange := ⟨by omega, by omega⟩ }

end VerifiedMBSE.Equivalence
