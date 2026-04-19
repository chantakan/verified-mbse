import VerifiedMBSE.Behavior.Temporal
import VerifiedMBSE.Behavior.StateMachineKripke
import VerifiedMBSE.Behavior.Product

/-!
# LTL over ProductStateMachine

積状態機械上の LTL 演算子 `Always_prod` / `Eventually_prod` / `Leads_prod` と、
各要素状態機械の LTL 保証を積に持ち上げる補題群を提供する。

## Note on Import

`StateMachineKripke` をインポートする理由: 持ち上げ補題 (`Always_prod.of_and` 等)
が引数として `Always sm₁ P₁` (旧 API 形式の呼び出し) を受け取るため、
`StateMachine → KripkeStructure` の coerce 経由で新 LTL API に流れる必要がある。

## B-6 で統合予定

`Always_prod` / `Eventually_prod` / `Leads_prod` / `ProductFDIRBundle` は、
B-6 で `ProductStateMachine.toKripke` を導入し、`Always` / `Eventually` /
`Leads` に統合される予定。本ファイルはそれまでの橋渡しコード。
-/

namespace VerifiedMBSE.Behavior

-- ============================================================
-- §1  Product Temporal Operators
-- ============================================================

/-- 積の Always (□ P): 積のすべての到達可能状態で P が成立する。 -/
def Always_prod
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    (_ : ProductStateMachine sm₁ sm₂)
    (P : S₁ × S₂ → D₁ × D₂ → Prop) : Prop :=
  ∀ p d, ProductReachable sm₁ sm₂ p d → P p d

/-- 積の Eventually (◇ P): P が成立する積の到達可能状態が存在する。 -/
def Eventually_prod
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    (_ : ProductStateMachine sm₁ sm₂)
    (P : S₁ × S₂ → D₁ × D₂ → Prop) : Prop :=
  ∃ p d, ProductReachable sm₁ sm₂ p d ∧ P p d

/-- 積の Leads (P ⇒ ◇ Q): 積で P が成立する任意の到達可能状態から、
    積で Q が成立する状態に到達可能。既存の `Leads` と同様、弱い意味論
    (「どこかで Q」) を採る。 -/
def Leads_prod
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    (psm : ProductStateMachine sm₁ sm₂)
    (P Q : S₁ × S₂ → D₁ × D₂ → Prop) : Prop :=
  Always_prod psm (fun p d => P p d → Eventually_prod psm Q)

-- ============================================================
-- §2  Safety Lifting (Always)
-- ============================================================

/-- Always の積への持ち上げ: 各成分の Always から積の連言 Always を構築。
    射影補題 `fst_reachable` / `snd_reachable` を直接適用するだけ。 -/
theorem Always_prod.of_and
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    {P₁ : S₁ → D₁ → Prop} {P₂ : S₂ → D₂ → Prop}
    (psm : ProductStateMachine sm₁ sm₂)
    (h₁ : Always sm₁ P₁) (h₂ : Always sm₂ P₂) :
    Always_prod psm (fun p d => P₁ p.1 d.1 ∧ P₂ p.2 d.2) :=
  fun p d hr =>
    ⟨h₁ p.1 d.1 hr.fst_reachable, h₂ p.2 d.2 hr.snd_reachable⟩

/-- Always の片側持ち上げ (左): sm₁ の Always から積の左成分に関する Always を得る。 -/
theorem Always_prod.of_left
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    {P₁ : S₁ → D₁ → Prop}
    (psm : ProductStateMachine sm₁ sm₂)
    (h₁ : Always sm₁ P₁) :
    Always_prod psm (fun p d => P₁ p.1 d.1) :=
  fun p d hr => h₁ p.1 d.1 hr.fst_reachable

/-- Always の片側持ち上げ (右): sm₂ の Always から積の右成分に関する Always を得る。 -/
theorem Always_prod.of_right
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    {P₂ : S₂ → D₂ → Prop}
    (psm : ProductStateMachine sm₁ sm₂)
    (h₂ : Always sm₂ P₂) :
    Always_prod psm (fun p d => P₂ p.2 d.2) :=
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
    Eventually_prod psm (fun p d => P₁ p.1 d.1) := by
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
    Eventually_prod psm (fun p d => P₂ p.2 d.2) := by
  obtain ⟨s₂, d₂, hr₂, hP⟩ := h
  obtain ⟨s₁, d₁, hp⟩ := ProductReachable.fromRight hr₂ hwf₁
  exact ⟨(s₁, s₂), (d₁, d₂), hp, hP⟩

-- ============================================================
-- §4  Recovery Lifting (Leads)
-- ============================================================

/-- Leads の片側持ち上げ (左): sm₁ の Leads P₁ Q₁ から、積上で
    `P₁ ∘ fst ⇒ ◇ (Q₁ ∘ fst)` を得る。

    証明のキー: 積で P₁ p.1 d.1 が成立するとき、射影により sm₁ 側で
    Reachable sm₁ p.1 d.1 ∧ P₁ p.1 d.1 が成り立ち、sm₁ の Leads から
    Eventually sm₁ Q₁ を得る。これを `Eventually_prod.of_left` で積へ lift する。 -/
theorem Leads_prod.of_left
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    {P₁ Q₁ : S₁ → D₁ → Prop}
    (psm : ProductStateMachine sm₁ sm₂)
    (hwf₂ : sm₂.WellFormed)
    (h : Leads sm₁ P₁ Q₁) :
    Leads_prod psm (fun p d => P₁ p.1 d.1) (fun p d => Q₁ p.1 d.1) := by
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
    Leads_prod psm (fun p d => P₂ p.2 d.2) (fun p d => Q₂ p.2 d.2) := by
  intro p d hr hP
  have hr₂ := hr.snd_reachable
  have hE : Eventually sm₂ Q₂ := h p.2 d.2 hr₂ hP
  exact Eventually_prod.of_right psm hwf₁ hE

end VerifiedMBSE.Behavior
