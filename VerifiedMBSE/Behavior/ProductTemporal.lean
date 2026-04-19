import VerifiedMBSE.Behavior.Temporal
import VerifiedMBSE.Behavior.StateMachineKripke
import VerifiedMBSE.Behavior.Product
import VerifiedMBSE.Behavior.ProductKripke

/-!
# LTL over ProductStateMachine (Unified via ToKripke)

B-4 以降、積状態機械上の LTL は `ToKripke` 型クラス経由で統一された
`Always / Eventually / Leads` で書ける。本ファイルは以下を提供する:

1. **後方互換エイリアス**: `Always_prod` / `Eventually_prod` / `Leads_prod` を
   `abbrev` で新 API の別名として残す。既存コードは変更なしで動く。

2. **持ち上げ補題**: 各要素状態機械の LTL 保証を積に持ち上げる補題
   (`.of_and`, `.of_left`, `.of_right`)。return 型は新 API (`Always psm ...`) に
   統一済み。defeq のおかげで `Always_prod psm ...` と書いた proof と互換。

## B-6 で予定の整理

持ち上げ補題の名前空間 `Always_prod.*` / `Eventually_prod.*` / `Leads_prod.*` は
B-6 で `Always.product_*` / `Eventually.product_*` / `Leads.product_*` に rename
予定。現段階では既存 Examples との互換性を優先して現在の名前を維持する。
-/

namespace VerifiedMBSE.Behavior

-- ============================================================
-- §1  Compatibility Aliases
-- ============================================================

/-- 積状態機械上の Always (後方互換)。`Always psm P` と defeq。 -/
abbrev Always_prod
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    (psm : ProductStateMachine sm₁ sm₂)
    (P : S₁ × S₂ → D₁ × D₂ → Prop) : Prop :=
  Always psm P

/-- 積状態機械上の Eventually (後方互換)。`Eventually psm P` と defeq。 -/
abbrev Eventually_prod
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    (psm : ProductStateMachine sm₁ sm₂)
    (P : S₁ × S₂ → D₁ × D₂ → Prop) : Prop :=
  Eventually psm P

/-- 積状態機械上の Leads (後方互換)。`Leads psm P Q` と defeq。 -/
abbrev Leads_prod
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    (psm : ProductStateMachine sm₁ sm₂)
    (P Q : S₁ × S₂ → D₁ × D₂ → Prop) : Prop :=
  Leads psm P Q

-- ============================================================
-- §2  Safety Lifting (Always)
-- ============================================================

/-- Always の積への持ち上げ: 各成分の Always から積の連言 Always を構築。 -/
theorem Always_prod.of_and
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    {P₁ : S₁ → D₁ → Prop} {P₂ : S₂ → D₂ → Prop}
    (psm : ProductStateMachine sm₁ sm₂)
    (h₁ : Always sm₁ P₁) (h₂ : Always sm₂ P₂) :
    Always psm (fun p d => P₁ p.1 d.1 ∧ P₂ p.2 d.2) :=
  fun p d hr =>
    ⟨h₁ p.1 d.1 hr.fst_reachable, h₂ p.2 d.2 hr.snd_reachable⟩

/-- Always の片側持ち上げ (左): sm₁ の Always から積の左成分 Always を得る。 -/
theorem Always_prod.of_left
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    {P₁ : S₁ → D₁ → Prop}
    (psm : ProductStateMachine sm₁ sm₂)
    (h₁ : Always sm₁ P₁) :
    Always psm (fun p d => P₁ p.1 d.1) :=
  fun p d hr => h₁ p.1 d.1 hr.fst_reachable

/-- Always の片側持ち上げ (右): sm₂ の Always から積の右成分 Always を得る。 -/
theorem Always_prod.of_right
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    {P₂ : S₂ → D₂ → Prop}
    (psm : ProductStateMachine sm₁ sm₂)
    (h₂ : Always sm₂ P₂) :
    Always psm (fun p d => P₂ p.2 d.2) :=
  fun p d hr => h₂ p.2 d.2 hr.snd_reachable

-- ============================================================
-- §3  Detection Lifting (Eventually)
-- ============================================================

/-- Eventually の片側持ち上げ (左): sm₁ の Eventually から積の左成分 Eventually を得る。
    相手側 (sm₂) の WellFormed で初期データを供給する必要がある。 -/
theorem Eventually_prod.of_left
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    {P₁ : S₁ → D₁ → Prop}
    (psm : ProductStateMachine sm₁ sm₂)
    (hwf₂ : sm₂.WellFormed)
    (h : Eventually sm₁ P₁) :
    Eventually psm (fun p d => P₁ p.1 d.1) := by
  obtain ⟨s₁, d₁, hr₁, hP⟩ := h
  obtain ⟨s₂, d₂, hp⟩ := ProductReachable.fromLeft hr₁ hwf₂
  exact ⟨(s₁, s₂), (d₁, d₂), hp, hP⟩

/-- Eventually の片側持ち上げ (右): sm₂ の Eventually から積の右成分 Eventually を得る。 -/
theorem Eventually_prod.of_right
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    {P₂ : S₂ → D₂ → Prop}
    (psm : ProductStateMachine sm₁ sm₂)
    (hwf₁ : sm₁.WellFormed)
    (h : Eventually sm₂ P₂) :
    Eventually psm (fun p d => P₂ p.2 d.2) := by
  obtain ⟨s₂, d₂, hr₂, hP⟩ := h
  obtain ⟨s₁, d₁, hp⟩ := ProductReachable.fromRight hr₂ hwf₁
  exact ⟨(s₁, s₂), (d₁, d₂), hp, hP⟩

-- ============================================================
-- §4  Recovery Lifting (Leads)
-- ============================================================

/-- Leads の片側持ち上げ (左): sm₁ の Leads P₁ Q₁ から、積上で
    `P₁ ∘ fst ⇒ ◇ (Q₁ ∘ fst)` を得る。 -/
theorem Leads_prod.of_left
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    {P₁ Q₁ : S₁ → D₁ → Prop}
    (psm : ProductStateMachine sm₁ sm₂)
    (hwf₂ : sm₂.WellFormed)
    (h : Leads sm₁ P₁ Q₁) :
    Leads psm (fun p d => P₁ p.1 d.1) (fun p d => Q₁ p.1 d.1) := by
  intro p d hr hP
  have hr₁ := hr.fst_reachable
  have hE : Eventually sm₁ Q₁ := h p.1 d.1 hr₁ hP
  exact Eventually_prod.of_left psm hwf₂ hE

/-- Leads の片側持ち上げ (右): sm₂ の Leads P₂ Q₂ から、積上で
    `P₂ ∘ snd ⇒ ◇ (Q₂ ∘ snd)` を得る。 -/
theorem Leads_prod.of_right
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    {P₂ Q₂ : S₂ → D₂ → Prop}
    (psm : ProductStateMachine sm₁ sm₂)
    (hwf₁ : sm₁.WellFormed)
    (h : Leads sm₂ P₂ Q₂) :
    Leads psm (fun p d => P₂ p.2 d.2) (fun p d => Q₂ p.2 d.2) := by
  intro p d hr hP
  have hr₂ := hr.snd_reachable
  have hE : Eventually sm₂ Q₂ := h p.2 d.2 hr₂ hP
  exact Eventually_prod.of_right psm hwf₁ hE

end VerifiedMBSE.Behavior
