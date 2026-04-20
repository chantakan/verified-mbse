import VerifiedMBSE.Behavior.Temporal
import VerifiedMBSE.Behavior.StateMachineKripke
import VerifiedMBSE.Behavior.ProductKripke
import VerifiedMBSE.Behavior.Product

/-!
# LTL over ProductKripke (Unified via ToKripke)

B-4 以降、積 Kripke 構造上の LTL は `ToKripke` 型クラス経由で統一された
`Always / Eventually / Leads` で書ける。本ファイルは以下を提供する:

1. **後方互換エイリアス** (§1): `Always_prod` / `Eventually_prod` / `Leads_prod` を
   `abbrev` で新 API の別名として残す。既存コードは変更なしで動く。

2. **持ち上げ補題** (§2-§4): 各要素 Kripke 構造の LTL 保証を積に持ち上げる補題
   (`.of_and`, `.of_left`, `.of_right`)。

## B-8c での一般化

B-7 までは型引数が `{sm₁ : StateMachine S₁ D₁ inv₁}` / `{sm₂ : StateMachine S₂ D₂ inv₂}`
の StateMachine 特化で、持ち上げに `sm_i.WellFormed` を要求していた。

B-8c では型引数を `{α β : Type} {S₁ D₁ S₂ D₂ : Type} [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]`
に一般化し、持ち上げ引数は `(ToKripke.toKripke y).NonEmpty` / `(ToKripke.toKripke x).NonEmpty`
に弱化した。これにより:

- `ProductKripke sm₁ sm₂`（= `ProductStateMachine sm₁ sm₂`）での使用は
  `hwf₂.nonEmpty` を渡せばそのまま動作
- `ProductKripke (pk : ProductKripke ...) sm₃`（3 機ネスト合成）でも、
  `pk.toKripke.NonEmpty` を渡すだけで同じ補題を再利用できる

StateMachine 特化の `Always_prod psm P` / `Eventually_prod psm P` / `Leads_prod psm P Q`
は後方互換のため abbrev のシグネチャは維持され、呼び出し側は変更不要。
-/

namespace VerifiedMBSE.Behavior

-- ============================================================
-- §1  Compatibility Aliases
-- ============================================================

/-- 積 Kripke 構造上の Always (後方互換エイリアス)。`Always pk P` と defeq。 -/
abbrev Always_prod
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    (pk : ProductKripke x y)
    (P : S₁ × S₂ → D₁ × D₂ → Prop) : Prop :=
  Always pk P

/-- 積 Kripke 構造上の Eventually (後方互換エイリアス)。`Eventually pk P` と defeq。 -/
abbrev Eventually_prod
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    (pk : ProductKripke x y)
    (P : S₁ × S₂ → D₁ × D₂ → Prop) : Prop :=
  Eventually pk P

/-- 積 Kripke 構造上の Leads (後方互換エイリアス)。`Leads pk P Q` と defeq。 -/
abbrev Leads_prod
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    (pk : ProductKripke x y)
    (P Q : S₁ × S₂ → D₁ × D₂ → Prop) : Prop :=
  Leads pk P Q

-- ============================================================
-- §2  Safety Lifting (Always)
-- ============================================================

/-- Always の積への持ち上げ: 各成分の Always から積の連言 Always を構築。

    `hr.fst_reachable` / `hr.snd_reachable` は `ProductKripkeReachable` の補題。
    要素側の `reachable` が induction hypothesis 経由で供給される。 -/
theorem Always_prod.of_and
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {P₁ : S₁ → D₁ → Prop} {P₂ : S₂ → D₂ → Prop}
    (pk : ProductKripke x y)
    (h₁ : Always x P₁) (h₂ : Always y P₂) :
    Always pk (fun p d => P₁ p.1 d.1 ∧ P₂ p.2 d.2) :=
  fun p d hr =>
    ⟨h₁ p.1 d.1 hr.fst_reachable, h₂ p.2 d.2 hr.snd_reachable⟩

/-- Always の片側持ち上げ (左): x 側の Always から積の左成分 Always を得る。 -/
theorem Always_prod.of_left
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {P₁ : S₁ → D₁ → Prop}
    (pk : ProductKripke x y)
    (h₁ : Always x P₁) :
    Always pk (fun p d => P₁ p.1 d.1) :=
  fun p d hr => h₁ p.1 d.1 hr.fst_reachable

/-- Always の片側持ち上げ (右): y 側の Always から積の右成分 Always を得る。 -/
theorem Always_prod.of_right
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {P₂ : S₂ → D₂ → Prop}
    (pk : ProductKripke x y)
    (h₂ : Always y P₂) :
    Always pk (fun p d => P₂ p.2 d.2) :=
  fun p d hr => h₂ p.2 d.2 hr.snd_reachable

-- ============================================================
-- §3  Detection Lifting (Eventually)
-- ============================================================

/-- Eventually の片側持ち上げ (左): x 側の Eventually から積の左成分 Eventually を得る。

    相手側 (y) の `NonEmpty` で初期データを供給する必要がある。
    `ProductKripkeReachable.fromLeft` が `init` コンストラクタ一発で
    積到達可能状態を構成する。 -/
theorem Eventually_prod.of_left
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {P₁ : S₁ → D₁ → Prop}
    (pk : ProductKripke x y)
    (hne₂ : (ToKripke.toKripke y).NonEmpty)
    (h : Eventually x P₁) :
    Eventually pk (fun p d => P₁ p.1 d.1) := by
  obtain ⟨s₁, d₁, hr₁, hP⟩ := h
  obtain ⟨s₂, d₂, hp⟩ := ProductKripkeReachable.fromLeft hr₁ hne₂
  exact ⟨(s₁, s₂), (d₁, d₂), hp, hP⟩

/-- Eventually の片側持ち上げ (右): y 側の Eventually から積の右成分 Eventually を得る。 -/
theorem Eventually_prod.of_right
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {P₂ : S₂ → D₂ → Prop}
    (pk : ProductKripke x y)
    (hne₁ : (ToKripke.toKripke x).NonEmpty)
    (h : Eventually y P₂) :
    Eventually pk (fun p d => P₂ p.2 d.2) := by
  obtain ⟨s₂, d₂, hr₂, hP⟩ := h
  obtain ⟨s₁, d₁, hp⟩ := ProductKripkeReachable.fromRight hr₂ hne₁
  exact ⟨(s₁, s₂), (d₁, d₂), hp, hP⟩

-- ============================================================
-- §4  Recovery Lifting (Leads)
-- ============================================================

/-- Leads の片側持ち上げ (左): x 側の Leads P₁ Q₁ から、積上で
    `P₁ ∘ fst ⇒ ◇ (Q₁ ∘ fst)` を得る。 -/
theorem Leads_prod.of_left
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {P₁ Q₁ : S₁ → D₁ → Prop}
    (pk : ProductKripke x y)
    (hne₂ : (ToKripke.toKripke y).NonEmpty)
    (h : Leads x P₁ Q₁) :
    Leads pk (fun p d => P₁ p.1 d.1) (fun p d => Q₁ p.1 d.1) := by
  intro p d hr hP
  have hr₁ := hr.fst_reachable
  have hE : Eventually x Q₁ := h p.1 d.1 hr₁ hP
  exact Eventually_prod.of_left pk hne₂ hE

/-- Leads の片側持ち上げ (右): y 側の Leads P₂ Q₂ から、積上で
    `P₂ ∘ snd ⇒ ◇ (Q₂ ∘ snd)` を得る。 -/
theorem Leads_prod.of_right
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    {P₂ Q₂ : S₂ → D₂ → Prop}
    (pk : ProductKripke x y)
    (hne₁ : (ToKripke.toKripke x).NonEmpty)
    (h : Leads y P₂ Q₂) :
    Leads pk (fun p d => P₂ p.2 d.2) (fun p d => Q₂ p.2 d.2) := by
  intro p d hr hP
  have hr₂ := hr.snd_reachable
  have hE : Eventually y Q₂ := h p.2 d.2 hr₂ hP
  exact Eventually_prod.of_right pk hne₁ hE

end VerifiedMBSE.Behavior
