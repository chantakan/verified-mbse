# Interpretation パターン

`VerifiedMBSE.Core.Interpretation := KerMLType → Type` はドメインモデルの型識別子
（`KerMLType`）に Lean の担体型を割り当てる**意味論関数**である。この関数をどう書くかが、
モデルの健全性と保守性を左右する。本ドキュメントはその推奨パターンと、避けるべき
アンチパターンをまとめる。

## TL;DR

- **アンチパターン**: `match t.name with | some "Foo" => FooType | _ => Unit` — 文字列
  マッチで `_ => Unit` に流すと、typo 時に silently unsoundness が潜む。
- **推奨パターン**: ドメイン固有の `inductive` enum（TypeTag）を定義し、
  enum → `KerMLType` への埋め込み関数と、enum → `Type` の網羅的 pattern match で
  `Interpretation` を構築する。文字列比較は enum 逆引きの 1 箇所に閉じ込める。

---

## 問題点: naive な文字列マッチ

```lean
-- アンチパターン
def EPSNatInterpretation : Interpretation := fun t =>
  match t.name with
  | some "PowerSupply" => Nat
  | some "Load"        => Nat
  | some "PowerPort"   => Nat
  | some "~PowerPort"  => Nat
  | _                  => Unit  -- ← 落とし穴
```

### リスク

1. **Typo による silent unsoundness**: `some "Powr Supply"`（space 抜け）と書いても
   コンパイラは検知せず、該当 KerMLType の担体は `Unit` になる。`Unit` は全ての
   述語を満たすため、`SMInvariantCompatible` の不変条件が常に成立してしまう。
2. **モデル拡張時の抜け**: 新しい PartDef を追加したが `Interpretation` に対応する
   case を追加し忘れると、`_ => Unit` に流れる。型エラーが出ない。
3. **Interpretation の健全性証明が困難**: `InterpretationRespects I` を証明するには、
   どの `KerMLType` に対して `Unit` が返るかを調査する必要があり、文字列ベースでは
   網羅性が機械的に確認できない。

---

## 推奨パターン: Tag enum + 網羅的 dispatch

### ステップ 1: ドメイン固有の TypeTag enum を定義

そのサブシステム（または合成単位）で現れる `KerMLType` を全て列挙した
`inductive` を用意する。

```lean
/-- EPS サブシステムに出現する全 KerMLType の識別子. -/
inductive EPSTypeTag where
  | powerSupply
  | load
  | powerPort
  | powerPortConj
  deriving Repr, BEq, DecidableEq
```

**ポイント**:
- `deriving DecidableEq` により、後段の逆引きと証明で `decide` が使える。
- 列挙対象は「このサブシステムで意味論を与えたい型全て」。ポート型、part 型、
  必要なら signal / message 型も含める。

### ステップ 2: enum と KerMLType の埋め込みを定義

enum の各 tag が一意の文字列に対応することを宣言する。

```lean
/-- Tag から KerMLType へ: 文字列は**ここ一箇所だけ**で登場する. -/
def EPSTypeTag.toName : EPSTypeTag → String
  | .powerSupply   => "PowerSupply"
  | .load          => "Load"
  | .powerPort     => "PowerPort"
  | .powerPortConj => "~PowerPort"

def EPSTypeTag.toKerMLType (tag : EPSTypeTag) : KerMLType :=
  { name := some tag.toName }
```

### ステップ 3: 逆引き関数（文字列 → enum）を定義

この関数が「文字列マッチの集約点」。ここだけで `_ => none` のフォールバックを
持ち、呼び出し側は `Option EPSTypeTag` を通して扱う。

```lean
/-- KerMLType.name から EPSTypeTag への逆引き.
    ドメイン外の型は `none` を返す. -/
def EPSTypeTag.fromName : Option String → Option EPSTypeTag
  | some "PowerSupply"  => some .powerSupply
  | some "Load"         => some .load
  | some "PowerPort"    => some .powerPort
  | some "~PowerPort"   => some .powerPortConj
  | _                   => none
```

### ステップ 4: 担体型割当を network 化

各 tag に Lean の担体型を割り当てる関数を、**網羅的 pattern match** で書く。
`_` case を使わず全 tag を明示することで、enum 拡張時に case 漏れが
コンパイラエラーとして検出される。

```lean
/-- 各 tag の担体型. 全ケース網羅(_ case なし). -/
def EPSTypeTag.interp : EPSTypeTag → Type
  | .powerSupply   => Nat
  | .load          => Nat
  | .powerPort     => Nat
  | .powerPortConj => Nat
```

### ステップ 5: Interpretation を合成

`Interpretation` は `KerMLType → Type`。tag への逆引きが成功すれば `.interp`、
失敗（ドメイン外）なら `Unit`（または `Empty`、後述）を返す。

```lean
/-- EPS の Interpretation. 文字列マッチは `fromName` の 1 箇所に閉じ込められており、
    担体型割当は `interp` の網羅的 pattern match で保証される. -/
def EPSNatInterpretation : Interpretation := fun t =>
  match EPSTypeTag.fromName t.name with
  | some tag => tag.interp
  | none     => Unit
```

---

## フォールバック型の選択

ドメイン外の型（`fromName` が `none` を返した場合）に何を割り当てるかは、
**意図的に選ぶ設計判断**である。

| フォールバック | 意味論 | 用途 |
|------------|--------|------|
| `Unit` | 「全てのインスタンスは `()`」 | ドメイン外も参照可能なモデル（従来互換） |
| `Empty` | 「インスタンス不在」 | ドメイン外は使用禁止を型で強制 |
| `PUnit.{u}` | Unit の universe-polymorphic 版 | universe 汎用性が必要な場合 |

**推奨**: Tag enum で「自分のドメインで扱う型」を列挙してあるなら、ドメイン外を
`Empty` にすれば**型レベルで使用を禁止**できる。既存互換のため `Unit` を
使い続ける場合も、その**理由**をコメントで明示する。

```lean
def EPSNatInterpretation : Interpretation := fun t =>
  match EPSTypeTag.fromName t.name with
  | some tag => tag.interp
  | none     =>
    -- Empty にするとドメイン外の型参照で使えなくなる。既存の Architecture で
    -- 他サブシステムと緩く接続する可能性を残すため Unit を採用。
    Unit
```

---

## 合成モデル: 複数サブシステムの Interpretation

複数サブシステム（EPS + AOCS + TCS 等）を合成する場合、各サブシステムの
Tag enum を sum 型で束ねるか、各 Interpretation を `KerMLType.name` で
dispatch する形で合成する。

### パターン A: Sum 型で enum を結合

```lean
inductive SpacecraftTypeTag where
  | eps  (tag : EPSTypeTag)
  | aocs (tag : AOCSTypeTag)
  | tcs  (tag : TCSTypeTag)
  deriving Repr

def SpacecraftTypeTag.toName : SpacecraftTypeTag → String
  | .eps  tag => tag.toName
  | .aocs tag => tag.toName
  | .tcs  tag => tag.toName

def SpacecraftTypeTag.interp : SpacecraftTypeTag → Type
  | .eps  tag => tag.interp
  | .aocs tag => tag.interp
  | .tcs  tag => tag.interp
```

**利点**: 全サブシステムの型空間が 1 つの enum に集約される。命名衝突（例えば
EPS と AOCS 両方に `"Mode"` という型がある）を型レベルで検出できる。

**欠点**: サブシステム追加のたびに合成 enum を更新する必要がある。

### パターン B: Interpretation の `dispatch`

```lean
def SpacecraftInterpretation : Interpretation := fun t =>
  if EPSTypeTag.fromName t.name |>.isSome then
    EPSNatInterpretation t
  else if AOCSTypeTag.fromName t.name |>.isSome then
    AOCSInterpretation t
  else
    Unit
```

**利点**: サブシステム独立性が高い。

**欠点**: 命名衝突が silently 解決される（先に検出された方が勝つ）。
衝突検出には別途 `no_overlap` 補題を証明する必要がある。

---

## 健全性の保証

`InterpretationRespects I`（`soundness` 定理の仮定）を証明する際、Tag パターンを
採用していると induction が tag enum 上で完結する。

```lean
-- 例: EPS 内部の Specialization は全て trivial に reflexive
theorem EPSInterpretationRespects_trivial :
    ∀ tag : EPSTypeTag,
      semanticSpecializes EPSNatInterpretation tag.toKerMLType tag.toKerMLType := by
  intro tag
  exact semanticSpecializes_refl _ _
```

網羅的 pattern match で書かれていれば、`cases tag` で有限個の case を機械的に
潰せる。文字列マッチ版では `t.name` の `Option String` 全体を網羅する必要が
あり、induction 不可能だった。

---

## アンチパターンと対策のまとめ

| アンチパターン | 問題 | 推奨 |
|-------------|------|------|
| `match t.name with ... \| _ => Unit` を `Interpretation` 本体に書く | typo で silent unsoundness | 逆引きを補助関数に分離 + 網羅的 tag pattern |
| `some "Foo"` リテラルを `Interpretation` 内で直接使う | モデル変更で文字列を全ファイル grep する羽目に | `EPSTypeTag.toName` の 1 箇所に集約 |
| ドメイン外を `Unit` にして未使用と偽装 | 他モジュールが誤用してもエラー出ない | `Empty` を検討、または理由を docstring で明示 |
| 複数サブシステムで同名型を別意味で使う | dispatch 順で意味が変わる | Sum 型 enum で命名衝突を型検出 |
| `Interpretation` の健全性を紙で議論 | 拡張時にすぐ壊れる | `cases tag` で機械証明 |

---

## 参考実装

- `Examples/Spacecraft/EPS.lean`: F8 後の `EPSTypeTag` + `EPSNatInterpretation` を
  上記パターンで実装。テストで `EPSTypeTag` の全 tag に対する `interp` が
  rfl で検査される。
- `Examples/Spacecraft/F8Tests.lean`: 受入条件テスト。