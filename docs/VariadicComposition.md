# Variadic Composition Guide (B-8d)

## 概要

B-8d で導入された **可変長合成 API** は、N 機の `SubSystemSpec` を
`List` から一気に合成する仕組みである。B-8c までの 2 項
`SubSystemSpec.compose` ネスト書きを、`List.foldl` ベースで
簡潔化する。

本ガイドは:
- なぜ可変長 API が必要か
- 核となる `SubSystemPayload` 型の設計
- 2 機合成 `compose` と N 機合成 `composeMany` の使い方
- スコープ外の事項 (結合律・bridge 付き版)

を扱う。

---

## 1. モチベーション

B-8c までの N 機合成は、2 項 `SubSystemSpec.compose` を繰り返し呼ぶ
必要があった:

```lean
-- 2 機
let s₁₂ : SubSystemSpec pk₁₂ :=
  SubSystemSpec.compose s₁ s₂ pk₁₂ hne₁ hne₂ [] (by intros; contradiction)

-- 3 機
let pk₁₂₃ : ProductKripke pk₁₂ sm₃ := ⟨⟩
let s₁₂₃ : SubSystemSpec pk₁₂₃ :=
  SubSystemSpec.compose s₁₂ s₃ pk₁₂₃
    s₁₂.behavioral.nonEmpty hne₃ [] (by intros; contradiction)

-- 4 機、5 機、...
```

機数が増えるごとに以下が定型的に重複する:

1. `ProductKripke` マーカー型の明示構築 (`⟨⟩`)
2. 各段の `NonEmpty` 引数の受け渡し
3. 空 `bridge = []` と `hbridge = by intros; contradiction`
4. 型階層 `ProductKripke (ProductKripke ...) ...` の手書き

しかも中間 spec の型 `SubSystemSpec (ProductKripke ...)` が
次段の第 1 引数として使われるため、通常の `List` では異種型を
扱えず、`foldl` / `foldr` でまとめて処理できない。

B-8d はこれを `SubSystemPayload` 型で解決する。

---

## 2. `SubSystemPayload` の設計

### 2.1 型定義

```lean
structure SubSystemPayload : Type 1 where
  α            : Type
  S            : Type
  D            : Type
  toKripkeInst : ToKripke α S D
  x            : α
  spec         : @SubSystemSpec α S D toKripkeInst x
```

**役割**: 「合成可能な 1 機分の荷物」を匿名的にパッケージ化する。
`α`・`S`・`D`・`ToKripke` instance・`x`・`spec` を 1 つの構造体に
詰めることで、異種 `SubSystemSpec x` を `List SubSystemPayload` で
統一的に扱える。

### 2.2 Universe について

`α : Type` フィールドを持つため `SubSystemPayload : Type 1`。
`List` は universe polymorphic なので `List SubSystemPayload : Type 1`
として問題なく扱える。エンドユーザ側で universe を気にする必要はない。

### 2.3 スマートコンストラクタ

既存の `SubSystemSpec x` から payload を構築する:

```lean
def SubSystemPayload.ofSpec
    {α : Type} {S D : Type} [inst : ToKripke α S D] {x : α}
    (spec : SubSystemSpec x) : SubSystemPayload := ...
```

**使用例**:

```lean
-- StateMachine 版の spec を包む
def epsPayload : SubSystemPayload := SubSystemPayload.ofSpec epsSpec

-- 既に合成済みの ProductKripke 版 spec も同じ API で包める
def combined : SubSystemPayload := SubSystemPayload.ofSpec epsMiniSpec
```

---

## 3. 2 機合成: `compose`

```lean
def SubSystemPayload.compose (p₁ p₂ : SubSystemPayload) : SubSystemPayload
```

**挙動**:
- 内部で `ProductKripke p₁.x p₂.x := ⟨⟩` マーカーを構築
- `NonEmpty` 証明は各 `spec.behavioral.nonEmpty` から自動供給
- `bridge = []` に固定 (機間コネクタは初版でサポート外)

**戻り値 payload**:
- `α = ProductKripke p₁.x p₂.x`
- `S = p₁.S × p₂.S`
- `D = p₁.D × p₂.D`
- `toKripkeInst = instToKripkeProductKripke`
- `x = ⟨⟩`
- `spec = SubSystemSpec.compose p₁.spec p₂.spec ...` の結果

**使用例**:

```lean
def epsMini : SubSystemPayload :=
  epsPayload.compose miniPayload

-- name は "EPS+Mini" (StructuralSpec.compose の命名規約)
example : epsMini.spec.name = "EPS+Mini" := rfl

-- 合成後も VVRecord 自動生成は動作する
def r1 : VVRecord := epsMini.spec.safetyRecord
```

---

## 4. N 機合成: `composeMany`

```lean
def SubSystemPayload.composeMany :
    List SubSystemPayload → Option SubSystemPayload
  | []      => none
  | p :: ps => some (ps.foldl SubSystemPayload.compose p)
```

**挙動**:
- `[]` → `none` (合成対象なし)
- `[p]` → `some p` (単機はそのまま)
- `p₀ :: p₁ :: ... :: pₙ` → `some ((((p₀ ∘ p₁) ∘ p₂) ∘ ...) ∘ pₙ)`

**使用例**:

```lean
-- 4 機合成
def fourSats : Option SubSystemPayload :=
  SubSystemPayload.composeMany
    [ SubSystemPayload.ofSpec epsSpec
    , SubSystemPayload.ofSpec agentSpec₁
    , SubSystemPayload.ofSpec agentSpec₂
    , SubSystemPayload.ofSpec agentSpec₃ ]

example : fourSats.isSome = true := rfl
```

`foldl` を使った左結合を採用している。これにより:
- 状態型は `(((S₀ × S₁) × S₂) × S₃)` の形で段階的に伸びる
- 既存の 3 機合成 `(EPS × Mini) × Mini2` と同じ結合方向
- 射影は `.1.1.1`・`.1.1.2`・`.1.2`・`.2` のパターンで一貫

---

## 5. チェーン書きとリスト書きの等価性

直接チェーンした合成と `composeMany` のリスト版は **定義等価** であり、
`rfl` で示せる:

```lean
def fourChain : SubSystemPayload :=
  epsPayload.compose miniPayload
    |>.compose mini2Payload
    |>.compose miniPayload

example :
    SubSystemPayload.composeMany
      [ epsPayload, miniPayload, mini2Payload, miniPayload ] =
    some fourChain := rfl
```

状況に応じて書きやすい方を選べる:
- **チェーン書き**: 中間結果を `def` で名付けたい場合
- **リスト書き**: 機数が多く並列的に見せたい場合

---

## 6. 補助補題

### `compose_parts_length`

```lean
theorem SubSystemPayload.compose_parts_length (p₁ p₂ : SubSystemPayload) :
    (p₁.compose p₂).spec.structural.parts.length =
      p₁.spec.structural.parts.length + p₂.spec.structural.parts.length
```

`StructuralSpec.compose_parts_length` を payload レベルに持ち上げたもの。
`bridge = []` 固定なので parts 数には影響しない。

### `compose_name`

```lean
theorem SubSystemPayload.compose_name (p₁ p₂ : SubSystemPayload) :
    (p₁.compose p₂).spec.name = s!"{p₁.spec.name}+{p₂.spec.name}"
```

### 境界補題

```lean
theorem SubSystemPayload.composeMany_singleton (p : SubSystemPayload) :
    SubSystemPayload.composeMany [p] = some p

theorem SubSystemPayload.composeMany_nil :
    SubSystemPayload.composeMany [] = none
```

---

## 7. スコープ外の事項

### 7.1 結合律 (associativity)

`(p₁.compose p₂).compose p₃` と `p₁.compose (p₂.compose p₃)` は
**型等号では示せない**。なぜなら状態型が

- 前者: `((S₁ × S₂) × S₃)`
- 後者: `(S₁ × (S₂ × S₃))`

と一致しないためである。Lean の `=` は型等号に依存するので、
これらは単純に同じ命題として扱えない。

**意味論的等価性** (state の射影が双射) は `Equivalence.ComponentEquiv`
経由で示せる可能性があるが、本 API ではスコープ外とする。
`foldl` と `foldr` の意味論的等価性も同じ理由で扱わない。

**実用上の帰結**: `composeMany` は **常に左結合** (`foldl` ベース) で
動作する。呼び出し側はこの結合順を前提にしてよい。

### 7.2 Bridge 付き可変長

2 項 `SubSystemSpec.compose` は `bridge : List Connector` を
第 6 引数で受け取る。N 機合成で「どの段に bridge を挟むか」を
表現する API は煩雑になるため、初版 (B-8d) では全段 `bridge = []` に
固定する。

**ワークアラウンド**: 機間コネクタが必要な呼び出しでは、引き続き
2 項 `SubSystemSpec.compose` を明示的に使う。その後
`SubSystemPayload.ofSpec` で payload に wrap すれば、後段の
`composeMany` と組み合わせられる。

**将来拡張余地**: B-8e で以下のような API に拡張できる:

```lean
def composeManyWithBridges :
    List (SubSystemPayload × List Connector) → Option SubSystemPayload
```

ただしこの場合、bridge の `hbridge` (connector の parts 参照整合性)
を後段の合成された parts リストに対して検証する必要があり、
実装は素直ではない。

---

## 8. まとめ

B-8d は **同種性の錯覚を `SubSystemPayload` で作る**ことで、異種
`SubSystemSpec x` の可変長合成を可能にした。

| 観点 | B-8c | B-8d |
|------|------|------|
| 2 機合成 | `SubSystemSpec.compose s₁ s₂ pk hne₁ hne₂ [] (by ...)` | `p₁.compose p₂` |
| N 機合成 | 2 項のネスト書き (手作業) | `composeMany [p₁, p₂, ..., pₙ]` |
| 異種 spec の統一扱い | 不可 | `List SubSystemPayload` で可能 |
| `NonEmpty` 引数 | 明示渡し | `spec.behavioral.nonEmpty` で自動 |
| bridge サポート | `List Connector` | `[]` 固定 (スコープ外) |

SafeSwarm のような N 機エージェント系の実例では、まず 2 項 `compose`
(+ bridge) で機間コネクタを含む組を作り、その組を `ofSpec` で
payload 化して `composeMany` で一気に束ねる、という 2 段構えが
自然な使い方となる。

---

## 関連

- B-6: `FDIRBundle.compose` (2 機 FDIR 合成)
- B-7: `SubSystemSpec` の Kripke 一般化 + 2 機合成
- B-8a-c: `ProductKripke` の異種型化 + 3 機ネスト合成
- **B-8d**: 本文書 (可変長合成 API)
- B-8e (将来): Bridge 付き可変長合成

各マイルストーンの実装ファイル:
- `VerifiedMBSE/Behavior/ProductKripke.lean` — B-8a-c
- `VerifiedMBSE/VV/ProductFDIR.lean` — B-6/B-7/B-8c 合流
- `VerifiedMBSE/VV/VariadicCompose.lean` — **B-8d (本文書の主題)**
- `Examples/Spacecraft/Integration.lean` — B-8c 3 機ネストサニティ
- `Examples/Spacecraft/VariadicComposeTests.lean` — B-8d サニティ