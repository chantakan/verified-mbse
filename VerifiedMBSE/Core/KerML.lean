import Mathlib.Order.Basic

/-!
# KerML Core Layer: 依存型による意味論

KerML Core 層（Element, Type, Feature, Direction）の構造体と
方向の共役（Conjugation as involution）を定義する。

## References
- OMG KerML Specification v2.0 Beta (formal/2023-06-03), Part III
- Almeida et al., "An Analysis of the Semantic Foundation of KerML and SysML v2" (ER 2024)
-/

namespace VerifiedMBSE.Core

-- ============================================================
-- §1  基本構造体
-- ============================================================

/-- KerML Element: 全モデル要素の根。 -/
structure Element where
  name : Option String := none
  deriving Repr, BEq

/-- KerML Type: フィーチャーを持ち得る分類子。
    意味論的には、インスタンスの集合（extent）を表す。 -/
structure KerMLType extends Element where
  /-- 抽象型（直接インスタンス化不可）かどうか -/
  isAbstract : Bool := false
  deriving Repr

/-- Feature: 型の特徴（名前付き・多重度付きスロット）。
    依存型理論では Σ(x:A).B(x) の射影に対応する。 -/
structure Feature extends Element where
  /-- 多重度下限 -/
  lower : Nat := 1
  /-- 多重度上限（0 = 無限） -/
  upper : Nat := 1
  deriving Repr

-- ============================================================
-- §2  方向と共役
-- ============================================================

/-- フィーチャーの方向（KerML spec §8.4.4）。
    線形論理の極性に対応：in = 負位置、out = 正位置。 -/
inductive Direction where
  | in_   -- 入力（外部→内部）
  | out   -- 出力（内部→外部）
  | inout -- 双方向（自己双対）
  deriving Repr, BEq

/-- Conjugation による方向反転。線形論理の否定 A⊥ に対応。 -/
def Direction.conj : Direction → Direction
  | .in_   => .out
  | .out   => .in_
  | .inout => .inout

/-- 方向の Conjugation は対合（involution）：conj(conj(d)) = d -/
theorem Direction.conj_involution (d : Direction) :
    d.conj.conj = d := by
  cases d <;> rfl

/-- 方向付きフィーチャー：ポート定義の基本単位。 -/
structure DirectedFeature extends Feature where
  direction : Direction
  deriving Repr

/-- DirectedFeature の Conjugation：方向のみ反転し本体は保持。 -/
def DirectedFeature.conj (f : DirectedFeature) : DirectedFeature where
  toFeature := f.toFeature
  direction := f.direction.conj

/-- DirectedFeature の Conjugation も対合。 -/
theorem DirectedFeature.conj_involution (f : DirectedFeature) :
    f.conj.conj = f := by
  simp [DirectedFeature.conj, Direction.conj_involution]

end VerifiedMBSE.Core
