/-!
# KripkeStructure: Semantic Foundation for LTL Operators

LTL 演算子 (Always / Eventually / Leads) を `StateMachine` / `ProductStateMachine` /
将来の連続時間系などに対して**共通 API** で使えるよう、
到達可能性関係 `reachable : State → Data → Prop` を抽象化した意味論基盤と、
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

/-- Kripke 構造: 到達可能性関係を抽象化した意味論基盤。

    `State` と `Data` を型パラメータとして受け取ることで、elaborator が
    field projection `K.State` / `K.Data` を遅延展開する問題を回避する。 -/
structure KripkeStructure (State : Type) (Data : Type) where
  /-- 到達可能性関係。初期状態から有限ステップで到達できる
      `(state, data)` のペアに対して成立する。 -/
  reachable : State → Data → Prop

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

    instance を追加する対象 (将来):
    - StateMachine S D inv (本 B-1 で提供)
    - ProductStateMachine sm₁ sm₂ (B-4 で提供予定)
    - 連続時間系の到達可能性抽象 (将来拡張) -/
class ToKripke (α : Type) (State : outParam Type) (Data : outParam Type) where
  /-- α から KripkeStructure State Data への変換。 -/
  toKripke : α → KripkeStructure State Data

end VerifiedMBSE.Behavior
