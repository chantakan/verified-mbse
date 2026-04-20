import VerifiedMBSE.Behavior.StateMachine
import VerifiedMBSE.Behavior.StateMachineKripke
import VerifiedMBSE.Behavior.ProductKripke

/-!
# ProductStateMachine: StateMachine 特化層 (ProductKripke の後方互換 abbrev)

B-8 以降、積状態機械の本体は `Behavior/ProductKripke.lean` の `ProductKripke x y`
(任意の `[ToKripke α S₁ D₁]` / `[ToKripke β S₂ D₂]` に対する積マーカー型) に
統一された。

本ファイルは **StateMachine 特化の後方互換 API** を提供する:

1. `productInv`: StateMachine の invariant 連言 (Examples 内の `Reachable` や
   `PartDef.invariant` などで直接参照するため残す)
2. `ProductStateMachine sm₁ sm₂` := `ProductKripke sm₁ sm₂` (abbrev)
3. `ProductReachable sm₁ sm₂` := `ProductKripkeReachable sm₁ sm₂` (abbrev)
4. `ProductStateMachine.initialState` / `.WellFormed` / `.wellFormed_iff` /
   `.nonEmpty`: StateMachine の `initialState` / `WellFormed` を前提にする
   dot notation 補助

## 依存関係

B-7 以前:
```
StateMachine.lean → Product.lean → ProductKripke.lean
```

B-8 以降 (本ファイル):
```
StateMachine.lean → KripkeStructure.lean → ProductKripke.lean → Product.lean
```

依存方向が反転し、`ProductKripke` が純粋 Kripke 層として独立、`Product` は
StateMachine 特化のラッパー層に変わった。既存 Examples の `ProductStateMachine`
呼び出しはすべて **変更なしで動く**（abbrev の defeq 透過性）。

## 歴史的ノート

有限性仮定を避けるため、積状態機械は `StateMachine` を返す形式ではなく独立した
inductive proposition で表現する (旧 `ProductReachable`)。B-8 でこの戦略は維持した
まま、型引数を `StateMachine` 特化から `ToKripke` 型クラスベースに一般化した。
-/

namespace VerifiedMBSE.Behavior

-- ============================================================
-- §1  Product Invariant
-- ============================================================

/-- 積不変条件: 2 つの不変条件の連言。

    `abbrev` とすることで `.1`, `.2` アクセスや `refine ⟨_, _⟩` が透過的に動く。
    `ProductKripke sm₁ sm₂` の `inv` フィールドは `fun p d =>
    (sm₁.toKripke).inv p.1 d.1 ∧ (sm₂.toKripke).inv p.2 d.2` で、これは
    `productInv inv₁ inv₂` と defeq。 -/
abbrev productInv
    {S₁ D₁ : Type} (inv₁ : S₁ → D₁ → Prop)
    {S₂ D₂ : Type} (inv₂ : S₂ → D₂ → Prop) :
    S₁ × S₂ → D₁ × D₂ → Prop :=
  fun p d => inv₁ p.1 d.1 ∧ inv₂ p.2 d.2

-- ============================================================
-- §2  ProductStateMachine (abbrev of ProductKripke)
-- ============================================================

/-- 積状態機械。`ProductKripke sm₁ sm₂` の `abbrev` として後方互換で提供する。

    `abbrev` なので `⟨⟩ : ProductStateMachine sm₁ sm₂` の型推論が `ProductKripke`
    として解決され、`epsMiniPSM : ProductStateMachine epsSM miniSM := ⟨⟩` のような
    既存パターンがそのまま動く。

    `ToKripke` instance は `instToKripkeProductKripke` が自動的に使われる
    (abbrev は instance resolution で透過)。 -/
abbrev ProductStateMachine
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    (sm₁ : StateMachine S₁ D₁ inv₁) (sm₂ : StateMachine S₂ D₂ inv₂) : Type :=
  ProductKripke sm₁ sm₂

/-- 積状態機械の到達可能性。`ProductKripkeReachable sm₁ sm₂` の `abbrev`。

    各コンストラクタ `init` / `stepLeft` / `stepRight` は
    `ProductKripkeReachable` のものがそのまま使える (dot notation 互換)。 -/
abbrev ProductReachable
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    (sm₁ : StateMachine S₁ D₁ inv₁) (sm₂ : StateMachine S₂ D₂ inv₂) :
    S₁ × S₂ → D₁ × D₂ → Prop :=
  ProductKripkeReachable sm₁ sm₂

-- ============================================================
-- §3  StateMachine 特化 API (initialState / WellFormed)
-- ============================================================

/-- 積状態機械の初期状態: 両方の StateMachine の初期状態のペア。

    `ProductKripke` 一般では初期状態の概念がないため、StateMachine 特化で提供する。 -/
def ProductStateMachine.initialState
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    (_ : ProductStateMachine sm₁ sm₂) : S₁ × S₂ :=
  (sm₁.initialState, sm₂.initialState)

/-- 積状態機械の WellFormed: 両方の StateMachine が WellFormed である。

    `ProductKripke` 一般では `NonEmpty` (Kripke 層の弱い条件) しか定義できないが、
    StateMachine に対しては `WellFormed` の形で提供する。`.nonEmpty` で Kripke 層の
    `NonEmpty` に変換可能 (§4 参照)。 -/
def ProductStateMachine.WellFormed
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    (_ : ProductStateMachine sm₁ sm₂) : Prop :=
  sm₁.WellFormed ∧ sm₂.WellFormed

/-- ProductStateMachine.WellFormed は各成分の WellFormed の連言。 -/
theorem ProductStateMachine.wellFormed_iff
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    (psm : ProductStateMachine sm₁ sm₂) :
    psm.WellFormed ↔ sm₁.WellFormed ∧ sm₂.WellFormed :=
  Iff.rfl

-- ============================================================
-- §4  NonEmpty (WellFormed → NonEmpty bridge)
-- ============================================================

/-- sm₁ と sm₂ の両方が `WellFormed` なら、積の Kripke 構造は `NonEmpty`。

    `ProductKripke.nonEmpty` (Kripke 層、両側 NonEmpty を要求) に、
    `WellFormed.nonEmpty` で変換した引数を渡す形で委譲する。

    既存の `FDIRBundle.compose` / `BehavioralSpec.compose` / `SubSystemSpec.compose`
    は `hwf₁ : sm₁.WellFormed` / `hwf₂ : sm₂.WellFormed` を受け取る API のまま
    維持されるため、内部で `ProductStateMachine.nonEmpty psm hwf₁ hwf₂` を呼ぶ
    既存コードがそのまま通る。 -/
theorem ProductStateMachine.nonEmpty
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    (psm : ProductStateMachine sm₁ sm₂)
    (hwf₁ : sm₁.WellFormed) (hwf₂ : sm₂.WellFormed) :
    psm.toKripke.NonEmpty :=
  ProductKripke.nonEmpty psm hwf₁.nonEmpty hwf₂.nonEmpty

end VerifiedMBSE.Behavior
