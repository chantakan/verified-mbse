import VerifiedMBSE.Behavior.KripkeStructure

/-!
# ProductKripke: Heterogeneous Product of Kripke Structures

任意の `[ToKripke α S₁ D₁]` と `[ToKripke β S₂ D₂]` に対して、2 つの Kripke 構造の
インタリーブ積 `ProductKripke x y` を定義する。本ファイルは **StateMachine 非依存**
で、純粋な Kripke 層の理論のみを扱う。

## B-8 の中核

B-7 までは積状態機械 `ProductStateMachine sm₁ sm₂` が第 1/2 引数とも `StateMachine`
特化であり、`ProductStateMachine psm₁₂ sm₃` のように `ProductKripke` を入れ子に
することができなかった（3 機以上のネスト合成不可能）。

B-8 では `ProductKripke` 型自体を **任意の `ToKripke` インスタンス型を受け取る**
ように一般化する。これにより:

- `ProductKripke sm₁ sm₂ : Type`（StateMachine 同士）
- `ProductKripke (pk : ProductKripke sm₁ sm₂) sm₃ : Type`（3 機ネスト）
- `ProductKripke ct₁ ct₂`（将来の連続時間系 ct_i : ContinuousSystem）

が同じ API で書ける。旧 `ProductStateMachine sm₁ sm₂` は `ProductKripke sm₁ sm₂` の
`abbrev` として `Behavior/Product.lean` で後方互換維持。

## 設計

### `ProductKripke x y` は空構造体

型そのものが「x と y の積を考える」という合意を表現するマーカー。値は重要でなく
`⟨⟩` で構築。将来メタデータ（同期遷移表、ラベル）追加の拡張点として構造体型を保持。

### `ProductKripkeReachable` はインタリーブ積

各ステップは `x` 側または `y` 側のいずれか一方の `step` を消費し、相手側は不変。
同期遷移（両側同時）は扱わない。

### `inv` の保存

`ProductKripkeReachable` 自体は `inv` 保存条件を持たない。代わりに、以下の 2 段階:

1. `fst_reachable` / `snd_reachable` で「積到達可能 → 各成分の到達可能」を示す
2. 各成分の `reachable_inv`（`KripkeStructure` のフィールド公理）を組み合わせて
   `inv_holds` を導く

これにより、`step` に `inv` 保存を直接要求する必要がなく、`KripkeStructure` の
定義が軽量に保たれる（`Transition.preserves` のような型レベル契約は要素側で持つ）。
-/

namespace VerifiedMBSE.Behavior

-- ============================================================
-- §1  ProductKripke 型
-- ============================================================

/-- 任意の `[ToKripke α S₁ D₁]` と `[ToKripke β S₂ D₂]` に対する積マーカー型。

    空構造体。値は `⟨⟩` で構築。型レベルで「x と y の積を考える」という合意のみを
    表現し、意味論は `ProductKripkeReachable` / `ProductKripke.toKripke` で与える。

    明示的な `mk ::` コンストラクタを宣言することで、フィールドなし構造体でも
    Lean のパーサが次の宣言を正しく読めるようにする。 -/
structure ProductKripke
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    (x : α) (y : β) : Type where
  mk ::

-- ============================================================
-- §2  ProductKripkeReachable (Interleaving Semantics)
-- ============================================================

/-- 積 Kripke 構造の到達可能性。**インタリーブ積**として定義する。

    - `init`: 両側の Kripke 構造が到達可能な点 `(s₁, d₁)` / `(s₂, d₂)` から
      スタート。旧 `ProductReachable.init` は StateMachine の初期状態に縛られていたが、
      新版は任意の reachable 点から出発できるため、`fromLeft` / `fromRight` の
      証明が induction 不要になる。
    - `stepLeft` / `stepRight`: 左/右の `(toKripke x/y).step` を 1 ステップ進め、
      相手側は不変。 -/
inductive ProductKripkeReachable
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    (x : α) (y : β) : S₁ × S₂ → D₁ × D₂ → Prop where
  /-- 初期: 両 Kripke 構造の reachable 点からスタート. -/
  | init : ∀ {s₁ : S₁} {s₂ : S₂} {d₁ : D₁} {d₂ : D₂},
      (ToKripke.toKripke x).reachable s₁ d₁ →
      (ToKripke.toKripke y).reachable s₂ d₂ →
      ProductKripkeReachable x y (s₁, s₂) (d₁, d₂)
  /-- 左側 step: x 側が 1 ステップ、y 側は不変. -/
  | stepLeft : ∀ {s₁ : S₁} {s₂ : S₂} {d₁ : D₁} {d₂ : D₂} {s₁' : S₁} {d₁' : D₁},
      ProductKripkeReachable x y (s₁, s₂) (d₁, d₂) →
      (ToKripke.toKripke x).step s₁ d₁ s₁' d₁' →
      ProductKripkeReachable x y (s₁', s₂) (d₁', d₂)
  /-- 右側 step: y 側が 1 ステップ、x 側は不変. -/
  | stepRight : ∀ {s₁ : S₁} {s₂ : S₂} {d₁ : D₁} {d₂ : D₂} {s₂' : S₂} {d₂' : D₂},
      ProductKripkeReachable x y (s₁, s₂) (d₁, d₂) →
      (ToKripke.toKripke y).step s₂ d₂ s₂' d₂' →
      ProductKripkeReachable x y (s₁, s₂') (d₁, d₂')

-- ============================================================
-- §3  Projection Lemmas (fst_reachable / snd_reachable)
-- ============================================================

/-- 射影: 積の到達可能性から左成分の到達可能性を取り出す。

    `stepLeft` ケースでは要素側 `KripkeStructure` の `step_preserves_reachable`
    公理を使い、`stepRight` ケースでは左成分が変化しないので IH をそのまま返す。 -/
theorem ProductKripkeReachable.fst_reachable
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {p : S₁ × S₂} {d : D₁ × D₂}
    (h : ProductKripkeReachable x y p d) :
    (ToKripke.toKripke x).reachable p.1 d.1 := by
  induction h with
  | init hr₁ _hr₂ => exact hr₁
  | stepLeft _hr₀ hstep ih =>
      exact (ToKripke.toKripke x).step_preserves_reachable _ _ _ _ ih hstep
  | stepRight _hr₀ _hstep ih => exact ih

/-- 射影: 積の到達可能性から右成分の到達可能性を取り出す。 -/
theorem ProductKripkeReachable.snd_reachable
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {p : S₁ × S₂} {d : D₁ × D₂}
    (h : ProductKripkeReachable x y p d) :
    (ToKripke.toKripke y).reachable p.2 d.2 := by
  induction h with
  | init _hr₁ hr₂ => exact hr₂
  | stepLeft _hr₀ _hstep ih => exact ih
  | stepRight _hr₀ hstep ih =>
      exact (ToKripke.toKripke y).step_preserves_reachable _ _ _ _ ih hstep

-- ============================================================
-- §4  Safety Theorem (inv_holds)
-- ============================================================

/-- 積の安全性定理: 積到達可能なら両成分の `inv` を満たす。

    `fst_reachable` / `snd_reachable` で各成分の reachable を取り出し、
    要素側 `KripkeStructure` の `reachable_inv` 公理を適用するだけ。
    `ProductKripkeReachable` 自体の induction は不要。 -/
theorem ProductKripkeReachable.inv_holds
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {p : S₁ × S₂} {d : D₁ × D₂}
    (h : ProductKripkeReachable x y p d) :
    (ToKripke.toKripke x).inv p.1 d.1 ∧ (ToKripke.toKripke y).inv p.2 d.2 :=
  ⟨(ToKripke.toKripke x).reachable_inv _ _ h.fst_reachable,
   (ToKripke.toKripke y).reachable_inv _ _ h.snd_reachable⟩

-- ============================================================
-- §5  step_preserves_reachable
-- ============================================================

/-- 積の step が到達可能性を保存する。

    `ProductKripke.toKripke` の `step_preserves_reachable` フィールドに渡す補題。
    インタリーブの disjunction を分解し、各枝で `stepLeft` / `stepRight` コンストラクタを
    適用する。 -/
theorem ProductKripkeReachable.step_preserves_reachable
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β} :
    ∀ (p : S₁ × S₂) (d : D₁ × D₂) (p' : S₁ × S₂) (d' : D₁ × D₂),
      ProductKripkeReachable x y p d →
      (((ToKripke.toKripke x).step p.1 d.1 p'.1 d'.1 ∧ p.2 = p'.2 ∧ d.2 = d'.2)
        ∨ ((ToKripke.toKripke y).step p.2 d.2 p'.2 d'.2 ∧ p.1 = p'.1 ∧ d.1 = d'.1)) →
      ProductKripkeReachable x y p' d' := by
  rintro ⟨s₁, s₂⟩ ⟨d₁, d₂⟩ ⟨s₁', s₂'⟩ ⟨d₁', d₂'⟩ hr hstep
  rcases hstep with
    ⟨hstep₁, rfl, rfl⟩ | ⟨hstep₂, rfl, rfl⟩
  · -- 左 step: s₂ = s₂', d₂ = d₂' は rfl で統合済み
    exact ProductKripkeReachable.stepLeft hr hstep₁
  · -- 右 step: s₁ = s₁', d₁ = d₁' は rfl で統合済み
    exact ProductKripkeReachable.stepRight hr hstep₂

-- ============================================================
-- §6  Lifting Lemmas (fromLeft / fromRight)
-- ============================================================

/-- 持ち上げ: 左側 Kripke 構造の reachable 点から、相手側の NonEmpty を補って
    積の到達可能性を構成する。

    旧 `ProductReachable.fromLeft` は StateMachine の `WellFormed` を要求し
    induction が必要だったが、新 `ProductKripkeReachable.init` が任意の reachable 点から
    始められるため、`init` コンストラクタ一発で証明が済む。 -/
theorem ProductKripkeReachable.fromLeft
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {s₁ : S₁} {d₁ : D₁}
    (hr₁ : (ToKripke.toKripke x).reachable s₁ d₁)
    (hne₂ : (ToKripke.toKripke y).NonEmpty) :
    ∃ (s₂ : S₂) (d₂ : D₂), ProductKripkeReachable x y (s₁, s₂) (d₁, d₂) := by
  obtain ⟨s₂, d₂, hr₂⟩ := hne₂
  exact ⟨s₂, d₂, ProductKripkeReachable.init hr₁ hr₂⟩

/-- 持ち上げ: 右側 Kripke 構造の reachable 点から、相手側の NonEmpty を補って
    積の到達可能性を構成する。 -/
theorem ProductKripkeReachable.fromRight
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {s₂ : S₂} {d₂ : D₂}
    (hr₂ : (ToKripke.toKripke y).reachable s₂ d₂)
    (hne₁ : (ToKripke.toKripke x).NonEmpty) :
    ∃ (s₁ : S₁) (d₁ : D₁), ProductKripkeReachable x y (s₁, s₂) (d₁, d₂) := by
  obtain ⟨s₁, d₁, hr₁⟩ := hne₁
  exact ⟨s₁, d₁, ProductKripkeReachable.init hr₁ hr₂⟩

-- ============================================================
-- §7  ProductKripke.toKripke
-- ============================================================

/-- `ProductKripke x y` を `KripkeStructure (S₁ × S₂) (D₁ × D₂)` として見る。

    `abbrev` なので reducible で、以下の defeq 関係が成立する:
    - `(pk.toKripke).inv p d = (toKripke x).inv p.1 d.1 ∧ (toKripke y).inv p.2 d.2`
    - `(pk.toKripke).reachable p d = ProductKripkeReachable x y p d`
    - `(pk.toKripke).step` = インタリーブ disjunction

    ### `reachable_inv` / `step_preserves_reachable`

    §4 / §5 で証明した `ProductKripkeReachable.inv_holds` /
    `ProductKripkeReachable.step_preserves_reachable` をそのまま代入する。 -/
abbrev ProductKripke.toKripke
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    (_ : ProductKripke x y) : KripkeStructure (S₁ × S₂) (D₁ × D₂) :=
  { inv := fun p d =>
      (ToKripke.toKripke x).inv p.1 d.1 ∧ (ToKripke.toKripke y).inv p.2 d.2
    reachable := ProductKripkeReachable x y
    reachable_inv := fun _ _ hr => ProductKripkeReachable.inv_holds hr
    step := fun p d p' d' =>
      ((ToKripke.toKripke x).step p.1 d.1 p'.1 d'.1 ∧ p.2 = p'.2 ∧ d.2 = d'.2)
      ∨
      ((ToKripke.toKripke y).step p.2 d.2 p'.2 d'.2 ∧ p.1 = p'.1 ∧ d.1 = d'.1)
    step_preserves_reachable := ProductKripkeReachable.step_preserves_reachable }

-- ============================================================
-- §8  ToKripke instance
-- ============================================================

/-- `ProductKripke x y` に対する `ToKripke` instance。

    これにより `Always pk P` / `Eventually pk P` / `Leads pk P Q` が
    `StateMachine` / `ProductStateMachine` と同一 API で書ける。
    3 機以上のネスト合成 (`ProductKripke (pk : ProductKripke ...) sm₃`) も、
    この instance が再帰的に resolve されて機能する。 -/
instance instToKripkeProductKripke
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β} :
    ToKripke (ProductKripke x y) (S₁ × S₂) (D₁ × D₂) where
  toKripke pk := pk.toKripke

-- ============================================================
-- §9  ProductKripke.nonEmpty
-- ============================================================

/-- 両側の NonEmpty から、積の NonEmpty を導く。

    `init` コンストラクタで両側の reachable 点から積到達可能状態を構築できるため、
    induction 不要の自明な証明。 -/
theorem ProductKripke.nonEmpty
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    (pk : ProductKripke x y)
    (hne₁ : (ToKripke.toKripke x).NonEmpty)
    (hne₂ : (ToKripke.toKripke y).NonEmpty) :
    pk.toKripke.NonEmpty := by
  obtain ⟨s₁, d₁, hr₁⟩ := hne₁
  obtain ⟨s₂, d₂, hr₂⟩ := hne₂
  exact ⟨(s₁, s₂), (d₁, d₂), ProductKripkeReachable.init hr₁ hr₂⟩

end VerifiedMBSE.Behavior
