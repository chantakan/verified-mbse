import VerifiedMBSE.VV.ProductFDIR

/-!
# Variadic Composition API (B-8d)

N 機の `SubSystemSpec` を `List` から一気に合成する API。B-8c の 2 項
`SubSystemSpec.compose` を繰り返し呼ぶ書き方を、`List.foldl` ベースで
簡潔化する。

## モチベーション

B-8c までの N 機合成は以下のように 2 項 `compose` のネストで書く必要があった:

```lean
let s₁₂   := SubSystemSpec.compose s₁ s₂ pk₁₂ hne₁ hne₂ [] (by ...)
let s₁₂₃  := SubSystemSpec.compose s₁₂ s₃ pk₁₂₃ s₁₂.behavioral.nonEmpty hne₃ [] (by ...)
let s₁₂₃₄ := SubSystemSpec.compose s₁₂₃ s₄ pk... s₁₂₃.behavioral.nonEmpty hne₄ [] (by ...)
```

機数が増えるごとに `ProductKripke` マーカー構築・`NonEmpty` 引数・
空 bridge の `hbridge` 証明が定型的に重複する。しかも各ステップで
生成される中間 `spec` の型 `SubSystemSpec (ProductKripke ... )` が
次のステップで第 1 引数として使われるため、異種型を扱えないと
`List` ベースの API が組めない。

B-8d では以下を導入してこれを解決する:

- `SubSystemPayload`: 匿名的に `α / S / D / ToKripke instance / x / spec` を
  パッケージ化した「合成可能な荷物」。これにより異種 `SubSystemSpec` が
  `List SubSystemPayload` として統一的に扱える。
- `SubSystemPayload.compose`: 2 機分の payload を合成。`NonEmpty` は
  各 `spec.behavioral.nonEmpty` から自動供給され、`bridge = []` で
  固定される。
- `SubSystemPayload.composeMany`: `List SubSystemPayload` を `foldl` で
  左結合的に合成。空リストは `none`、単機は `some p`、2 機以上は
  `some ((((p₀ ∘ p₁) ∘ p₂) ∘ ...) ∘ pₙ)`。

## 設計判断

### 左結合 (`foldl`) を採用

既存の `Examples/Spacecraft/Integration.lean` の 3 機合成
`(EPS × Mini) × Mini2` と同じ結合方向にする。型の形が
`((S₁ × S₂) × S₃) × S₄` と段階的に伸びるため、射影 `.1.1.1` 等が
既存のパターンと揃う。

### `bridge = []` に限定

2 項 `SubSystemSpec.compose` は `bridge : List Connector` を受け取れるが、
N 機合成で「どの段に bridge を挟むか」を表現する API は煩雑になるため
初版では全段 `bridge = []` に固定する。機間コネクタが必要な呼び出しは
引き続き 2 項 `compose` を明示的に使う。将来 B-8e で
`composeManyWithBridges : List (SubSystemPayload × List Connector) → ...`
を拡張する余地を残す。

### 結合律は未証明 (意図的)

`(p₁ ∘ p₂) ∘ p₃` と `p₁ ∘ (p₂ ∘ p₃)` は状態型が
`((S₁ × S₂) × S₃)` vs `(S₁ × (S₂ × S₃))` で一致しないため、
厳密な `=` では示せない。意味論的等価性 (state 射影が双射) は
`Equivalence.ComponentEquiv` 経由で別途示す必要があり、本ファイルでは
スコープ外とする。`foldl` / `foldr` の意味論的等価性も同じ理由で
今回は扱わない。

### `SubSystemPayload : Type 1`

`α : Type` フィールドを持つため universe bump する。`List` は universe
polymorphic なので `List SubSystemPayload : Type 1` として問題なく
扱える。実用上は呼び出し側で型を明示する必要はない。

### `instToKripkeOfPayload` を global instance 化

`SubSystemPayload` の `toKripkeInst` フィールドは通常の field なので、
instance resolution の探索対象にならない。`p.spec.name` のような
projection は `SubSystemSpec.name` が要求する `[ToKripke α S D]` を
解決できずに失敗する。これを解決するため、`p : SubSystemPayload` から
`ToKripke p.α p.S p.D` を自動供給する global instance を登録する。

### `SubSystemPayload.ofSpec` は `abbrev`

`(SubSystemPayload.ofSpec spec).α` 等の field projection が自動的に
reduction されて `rfl` でサニティテストが通るよう、`def` ではなく
`abbrev` で定義する。`compose` 側は proof-relevant な中身を持つため
通常の `def` を維持する。

-/

namespace VerifiedMBSE.VV

open VerifiedMBSE.Core
open VerifiedMBSE.Behavior

-- ============================================================
-- §1  SubSystemPayload
-- ============================================================

/-- 匿名的に合成可能な 1 機分のペイロード。

    `α / S / D / ToKripke instance / x / spec` を 1 つの構造体に
    パッケージ化することで、異種 `SubSystemSpec x` を `List` で
    統一的に扱える。

    ### フィールド

    - `α`: 行動モデルの型 (例: `StateMachine EPSMode Nat epsGlobalInv` や
      `ProductKripke sm₁ sm₂`)
    - `S`, `D`: 状態型・データ型
    - `toKripkeInst`: `α` を Kripke 構造として解釈する instance
    - `x`: `α` の具体値
    - `spec`: `x` 上の `SubSystemSpec`

    ### universe 問題

    `α : Type` を持つため `SubSystemPayload : Type 1`。`List` は universe
    polymorphic で `List SubSystemPayload : Type 1` となるが、
    エンドユーザは型明示不要。 -/
structure SubSystemPayload : Type 1 where
  /-- 行動モデルの型。 -/
  α : Type
  /-- 状態型。 -/
  S : Type
  /-- データ型。 -/
  D : Type
  /-- `α` を Kripke 構造として解釈する instance。 -/
  toKripkeInst : ToKripke α S D
  /-- 行動モデルの具体値 (StateMachine、ProductKripke 等)。 -/
  x : α
  /-- `x` 上のサブシステム仕様。 -/
  spec : @SubSystemSpec α S D toKripkeInst x

/-- `SubSystemPayload` の `toKripkeInst` フィールドを global instance として
    自動供給する。

    これがないと `p.spec.name` や `p.spec.structural` 等の projection で
    `SubSystemSpec.name` / `SubSystemSpec.structural` が要求する
    `[ToKripke α S D]` が解決できない（構造体の通常 field は instance
    resolution の探索対象にならないため）。

    このグローバル instance により、以下がすべて型解決可能になる:
    - `p.spec.name`, `p.spec.structural`, `p.spec.behavioral`, `p.spec.fdir`
    - `p.spec.safetyRecord`, `p.spec.subsystemRecord`, `p.spec.recoveryRecord`
    - `(ToKripke.toKripke p.x).NonEmpty` 等の Kripke 層 API -/
instance instToKripkeOfPayload (p : SubSystemPayload) :
    ToKripke p.α p.S p.D :=
  p.toKripkeInst

/-- `SubSystemSpec x` から `SubSystemPayload` を構築する簡便コンストラクタ。

    型引数と instance は `[ToKripke α S D]` 経由で自動的に推論されるため、
    呼び出し側は `SubSystemPayload.ofSpec epsSpec` のように書ける。

    `abbrev` として定義することで、`(SubSystemPayload.ofSpec spec).α` 等の
    field projection が自動 reduction され、`rfl` でサニティテストが
    通るようにしている。 -/
abbrev SubSystemPayload.ofSpec
    {α : Type} {S D : Type} [inst : ToKripke α S D] {x : α}
    (spec : SubSystemSpec x) : SubSystemPayload :=
  { α := α, S := S, D := D
    toKripkeInst := inst
    x := x, spec := spec }

-- ============================================================
-- §2  2 機合成
-- ============================================================

/-- 2 つのペイロードを並列合成する。bridge なし (`[]`) 版。

    - `ProductKripke p₁.x p₂.x` マーカーを内部で構築
    - `NonEmpty` 証明は各 `spec.behavioral.nonEmpty` から自動供給
    - bridge は `[]` に固定 (機間コネクタが必要な場合は
      2 項 `SubSystemSpec.compose` を使う)

    戻り値の payload は:
    - `α = ProductKripke p₁.x p₂.x`
    - `S = p₁.S × p₂.S`
    - `D = p₁.D × p₂.D`
    - `toKripkeInst = instToKripkeProductKripke`
    - `x = ⟨⟩` (空構造体)
    - `spec = SubSystemSpec.compose p₁.spec p₂.spec ...` の結果

    `letI` で `p₁.toKripkeInst` / `p₂.toKripkeInst` を local instance として
    導入し、`ProductKripke p₁.x p₂.x` の型チェックと instance 解決を通す。 -/
def SubSystemPayload.compose (p₁ p₂ : SubSystemPayload) : SubSystemPayload :=
  letI := p₁.toKripkeInst
  letI := p₂.toKripkeInst
  let pk : ProductKripke p₁.x p₂.x := ⟨⟩
  { α := ProductKripke p₁.x p₂.x
    S := p₁.S × p₂.S
    D := p₁.D × p₂.D
    toKripkeInst := instToKripkeProductKripke
    x := pk
    spec :=
      SubSystemSpec.compose p₁.spec p₂.spec pk
        p₁.spec.behavioral.nonEmpty
        p₂.spec.behavioral.nonEmpty
        [] (by intros; contradiction) }

-- ============================================================
-- §3  可変長合成
-- ============================================================

/-- N 機ペイロードを左結合で合成する。

    - `[]` → `none` (合成対象なし)
    - `[p]` → `some p` (単機はそのまま)
    - `p₀ :: p₁ :: ... :: pₙ` → `some ((((p₀ ∘ p₁) ∘ p₂) ∘ ...) ∘ pₙ)`

    `List.foldl` で左結合: 既存の 3 機合成 `(EPS × Mini) × Mini2` と同じ
    結合方向となり、状態型は `(((S₀ × S₁) × S₂) × ... ) × Sₙ` の形で
    段階的に伸びる。 -/
def SubSystemPayload.composeMany :
    List SubSystemPayload → Option SubSystemPayload
  | []      => none
  | p :: ps => some (ps.foldl SubSystemPayload.compose p)

-- ============================================================
-- §4  補助補題
-- ============================================================

/-- 合成後の総 part 数は両ペイロードの `.system.parts` 数の和に一致する。

    `StructuralSpec.compose_parts_length` を payload レベルに持ち上げた
    補助補題。`bridge` は常に `[]` なので part 数に影響しない。

    右辺が `.system.parts.length` なのは既存 `StructuralSpec.compose_parts_length`
    と整合させるため。smart constructor で作られた `StructuralSpec` では
    `.parts = .system.parts` が defeq で成立するため、具体インスタンスに対しては
    `.structural.parts.length` と `.structural.system.parts.length` が一致する。 -/
theorem SubSystemPayload.compose_parts_length
    (p₁ p₂ : SubSystemPayload) :
    (p₁.compose p₂).spec.structural.parts.length =
      p₁.spec.structural.system.parts.length +
        p₂.spec.structural.system.parts.length := by
  simp [SubSystemPayload.compose, SubSystemSpec.compose,
        StructuralSpec.compose, List.length_append]

/-- 合成後の name は `"{p₁.name}+{p₂.name}"` の形になる。

    `StructuralSpec.compose` の命名規約 (`s!"{s1.name}+{s2.name}"`) を
    payload レベルに持ち上げた補題。 -/
theorem SubSystemPayload.compose_name
    (p₁ p₂ : SubSystemPayload) :
    (p₁.compose p₂).spec.name =
      s!"{p₁.spec.name}+{p₂.spec.name}" := rfl

/-- 単機リストの合成結果はその機そのもの。 -/
theorem SubSystemPayload.composeMany_singleton (p : SubSystemPayload) :
    SubSystemPayload.composeMany [p] = some p := rfl

/-- 空リストの合成結果は `none`。 -/
theorem SubSystemPayload.composeMany_nil :
    SubSystemPayload.composeMany [] = none := rfl

end VerifiedMBSE.VV
