import VerifiedMBSE.Behavior.StateMachine
import VerifiedMBSE.Behavior.KripkeStructure
import VerifiedMBSE.Behavior.Product

/-!
# ProductStateMachine → KripkeStructure via ToKripke

`ProductStateMachine sm₁ sm₂` に対する `ToKripke` instance を提供する。
これにより `Always psm P` / `Eventually psm P` / `Leads psm P Q` が
StateMachine と同一 API で書ける。

## 設計

`ProductStateMachine sm₁ sm₂` は空構造体 (Product.lean 参照) で、実際の情報は
型パラメータ `sm₁`, `sm₂` に埋め込まれている。よって `ProductStateMachine.toKripke`
は psm 自体の値を使わず、型パラメータから `ProductReachable sm₁ sm₂` を参照する。

`NonEmpty` は、sm₁ と sm₂ それぞれが `WellFormed` なら、`ProductReachable` の
`fromLeft` 経由で合成側の初期到達可能状態を構成できる。
-/

namespace VerifiedMBSE.Behavior

-- ============================================================
-- §1  ProductStateMachine.toKripke
-- ============================================================

/-- ProductStateMachine を KripkeStructure として見る。

    psm は空構造体なので引数として無視 (`_`) し、型パラメータ sm₁, sm₂ から
    `ProductReachable sm₁ sm₂` を reachable 関係として構成する。
    `abbrev` なので `(psm.toKripke).reachable p d` が
    `ProductReachable sm₁ sm₂ p d` に defeq で展開される。 -/
abbrev ProductStateMachine.toKripke
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    (_ : ProductStateMachine sm₁ sm₂) :
    KripkeStructure (S₁ × S₂) (D₁ × D₂) :=
  { reachable := ProductReachable sm₁ sm₂ }

-- ============================================================
-- §2  ToKripke instance
-- ============================================================

/-- ProductStateMachine に対する ToKripke instance。

    これにより `Always psm P` で psm : ProductStateMachine sm₁ sm₂ が渡されると、
    `State = S₁ × S₂, Data = D₁ × D₂` が outParam で決定される。 -/
instance instToKripkeProductStateMachine
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂} :
    ToKripke (ProductStateMachine sm₁ sm₂) (S₁ × S₂) (D₁ × D₂) where
  toKripke psm := psm.toKripke

-- ============================================================
-- §3  Product NonEmpty
-- ============================================================

/-- sm₁ と sm₂ の両方が `WellFormed` なら、積の Kripke 構造は `NonEmpty`。

    sm₁ の初期状態+初期データから `Reachable sm₁` を作り、`fromLeft` で
    積到達可能性に持ち上げる。 -/
theorem ProductStateMachine.nonEmpty
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    (psm : ProductStateMachine sm₁ sm₂)
    (hwf₁ : sm₁.WellFormed) (hwf₂ : sm₂.WellFormed) :
    psm.toKripke.NonEmpty := by
  obtain ⟨d₁, hd₁⟩ := hwf₁
  have hr₁ : Reachable sm₁ sm₁.initialState d₁ := Reachable.init d₁ hd₁
  obtain ⟨s₂, d₂, hp⟩ := ProductReachable.fromLeft hr₁ hwf₂
  exact ⟨(sm₁.initialState, s₂), (d₁, d₂), hp⟩

end VerifiedMBSE.Behavior
