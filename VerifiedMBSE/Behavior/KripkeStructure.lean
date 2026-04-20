/-!
# KripkeStructure: Semantic Foundation for LTL Operators

LTL 演算子 (Always / Eventually / Leads) を `StateMachine` / `ProductStateMachine` /
`ProductKripke` / 将来の連続時間系などに対して**共通 API** で使えるよう、
到達可能性関係と不変条件・1 ステップ関係を抽象化した意味論基盤と、
具体型 `α` を `KripkeStructure State Data` に持ち上げる型クラス `ToKripke` を提供する。

## 設計判断

### なぜ `Coe` ではなく `ToKripke` 型クラスか

`Coe (StateMachine S D inv) (KripkeStructure S D)` instance では、`inv` が α 側にのみ
現れて β 側には出現しないため、Lean 4.30 の strict "semi-out-params" チェックで
「`inv` が β から flow できない」としてエラーになる。

`ToKripke` 型クラスを用意し、`State` と `Data` を `outParam` にすることで、
instance matching は α の具体値 (例: `StateMachine TCSMode Nat tcsInvariant`) から
直接走り、`inv` などの extra implicit args も含めて自然に解決される。

### なぜ `State` / `Data` を型パラメータにしたか

`KripkeStructure.State` / `.Data` が field projection として遅延展開されることによる
elaborator 混乱 (特に `omega` が `Nat` と `K.Data` を区別できない事象) を回避するため、
`structure KripkeStructure (State : Type) (Data : Type)` と型パラメータ化する。

### B-8 での拡張: `inv` / `step` を Kripke 層に昇格

B-8 以前は `reachable` のみが Kripke 層に存在した。B-8 で **`ProductKripke` の
N 機ネスト合成** を実現するため、以下の追加フィールドを導入する:

| フィールド | 役割 |
|---|---|
| `inv` | システム不変条件。到達可能状態が満たす性質を Kripke 層で明示化 |
| `reachable_inv` | 到達可能性 → 不変条件 の含意 (StateMachine の `Reachable.inv_holds` に対応) |
| `step` | 1 ステップ遷移関係。インタリーブ積の「相手側不変、自分側 1 ステップ」を Kripke 層で表現 |
| `step_preserves_reachable` | `step` が到達可能性を保存する (`ProductKripkeReachable.stepLeft/stepRight` の型チェックに必要) |

これらは `ProductKripke x y` の `toKripke` instance が `x` 側 / `y` 側の
`KripkeStructure` を参照して積を構築する際の公理基盤として機能する。
`Always` / `Eventually` / `Leads` は `reachable` フィールドのみに依存するため、
既存の型クラスベース API は後方互換のまま維持される。

## 使用例

```lean
-- `Always sm P` で ToKripke instance 経由に解決
#check Always sm (fun s _ => s ≠ .fault)
```
-/

namespace VerifiedMBSE.Behavior

-- ============================================================
-- §1  KripkeStructure
-- ============================================================

/-- Kripke 構造: 到達可能性関係・不変条件・1 ステップ関係を抽象化した意味論基盤。

    `State` と `Data` を型パラメータとして受け取ることで、elaborator が
    field projection `K.State` / `K.Data` を遅延展開する問題を回避する。

    ### フィールド一覧

    - `inv`: システム不変条件。到達可能な全状態で成立するべき性質。
    - `reachable`: 到達可能性関係。初期状態から有限ステップで到達できる
      `(state, data)` のペアに対して成立する。
    - `reachable_inv`: 到達可能性が不変条件を含意する公理。`StateMachine` の
      `Reachable.inv_holds` に対応。
    - `step`: 1 ステップ遷移関係。`(s, d)` から 1 ステップで `(s', d')` に
      遷移する場合に成立する。
    - `step_preserves_reachable`: `step` が到達可能性を保存する公理。-/
structure KripkeStructure (State : Type) (Data : Type) where
  /-- システムの不変条件。到達可能な全状態で成立する。 -/
  inv : State → Data → Prop
  /-- 到達可能性関係。初期状態から有限ステップで到達できる `(s, d)` に対して成立。 -/
  reachable : State → Data → Prop
  /-- 到達可能性は不変条件を含意する。 -/
  reachable_inv : ∀ s d, reachable s d → inv s d
  /-- 1 ステップ遷移関係。`(s, d)` から 1 ステップで `(s', d')` に遷移する。 -/
  step : State → Data → State → Data → Prop
  /-- step で到達可能状態から到達可能状態へ遷移する。 -/
  step_preserves_reachable :
    ∀ s d s' d', reachable s d → step s d s' d' → reachable s' d'

/-- Kripke 構造が**空でない**: 到達可能な `(s, d)` が少なくとも 1 つ存在する。 -/
def KripkeStructure.NonEmpty {State Data : Type}
    (K : KripkeStructure State Data) : Prop :=
  ∃ (s : State) (d : Data), K.reachable s d

-- ============================================================
-- §2  ToKripke Type Class
-- ============================================================

/-- `ToKripke α State Data`: 型 `α` の値を `KripkeStructure State Data` に
    持ち上げる方法を提供する型クラス。

    `State` と `Data` は `outParam` にしているため、`α` の具体値から instance
    resolution で自動的に決定される。これにより `Always sm P` (sm : StateMachine S D inv)
    のような呼び出しで、`P : S → D → Prop` として `S, D` が明示的に elaborate される。

    instance を追加する対象 (B-8 時点):
    - `StateMachine S D inv` (B-1 で提供)
    - `ProductStateMachine sm₁ sm₂` (B-4 で提供、B-8b で `ProductKripke` に統合予定)
    - 連続時間系の到達可能性抽象 (F10 で拡張予定) -/
class ToKripke (α : Type) (State : outParam Type) (Data : outParam Type) where
  /-- α から KripkeStructure State Data への変換。 -/
  toKripke : α → KripkeStructure State Data

end VerifiedMBSE.Behavior
