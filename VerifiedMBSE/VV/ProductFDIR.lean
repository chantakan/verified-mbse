import VerifiedMBSE.VV.SubSystemSpec
import VerifiedMBSE.Behavior.ProductTemporal

/-!
# FDIRBundle Parallel Composition

積状態機械 `ProductStateMachine sm₁ sm₂` 上の統一 `FDIRBundle` を、
各要素 `FDIRBundle sm₁` / `FDIRBundle sm₂` の並列合成として構築する
`FDIRBundle.compose` を定義する。

## B-6: ProductFDIRBundle との合流

以前は `ProductFDIRBundle` という独立した構造体を並列定義していたが、
B-1 で導入した `ToKripke` 型クラス経由の統一 `Always / Eventually / Leads`
と、B-4 で追加した `ProductStateMachine` に対する `ToKripke` instance により、
`FDIRBundle psm` として `VV/SubSystemSpec.lean` の `FDIRBundle` に合流した。
旧 `ProductFDIRBundle psm F R Sa` は `FDIRBundle psm`（`isFault` 等は**フィールド**）
に置き換える。

## 合成の意味論

- `isFault    := f₁.isFault p.1 ∨ f₂.isFault p.2`   — どちらかが fault
- `isRecovery := f₁.isRecovery p.1 ∨ f₂.isRecovery p.2` — どちらかが recovery
- `isSafe     := f₁.isSafe q.1 ∧ f₂.isSafe q.2`      — 両方 safe

### `isRecovery` に `∨` を採用する設計判断

要件書 F4-2 初稿は `isRecovery := f₁.isRecovery p.1 ∧ f₂.isRecovery p.2`
（両方同時 recovery）としていたが、片方だけ fault が発生した場合、相方は元の
nominal 状態で静止しているため「両方同時に recovery モード」という条件は
一般には到達不能で、要素 `FDIRBundle` の保証だけからは証明不能である。

合成意味論として `∨`（fault を起こした側が recovery すればよい）を採用すると、
`Leads_prod.of_left` / `.of_right` から素直に構成でき、かつ「fault を起こした
側は必ず recovery する」という実用上の要求を満たす。より厳しい recovery 定義
（例: 両方同時 recovery、同期遷移を伴う）が必要なユースケースでは、ユーザ側で
`FDIRBundle psm` を直接構築する設計とした。
-/

namespace VerifiedMBSE.VV

open VerifiedMBSE.Behavior

-- ============================================================
-- §1  FDIRBundle.compose
-- ============================================================

/-- 2 つの `FDIRBundle` の並列合成。

    戻り値は積状態機械 `psm : ProductStateMachine sm₁ sm₂` 上の統一 `FDIRBundle psm`
    （旧 `ProductFDIRBundle` 相当）。

    構成:
    - `safety`    ← `Always_prod.of_and` で両 safety を積の合取にまとめる
    - `detection` ← 左 detection を `Eventually_prod.of_left` で持ち上げ、`Or.inl`
    - `recovery`  ← `Leads_prod.of_left` / `.of_right` で fault 側の recovery を
      選び、`Or.inl` / `Or.inr` で合成 isRecovery にマップ -/
def FDIRBundle.compose
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    (f₁ : FDIRBundle sm₁) (f₂ : FDIRBundle sm₂)
    (psm : ProductStateMachine sm₁ sm₂)
    (hwf₁ : sm₁.WellFormed) (hwf₂ : sm₂.WellFormed) :
    FDIRBundle psm where
  isFault    := fun p => f₁.isFault p.1 ∨ f₂.isFault p.2
  isRecovery := fun p => f₁.isRecovery p.1 ∨ f₂.isRecovery p.2
  isSafe     := fun q => f₁.isSafe q.1 ∧ f₂.isSafe q.2
  safety := Always_prod.of_and psm f₁.safety f₂.safety
  detection := by
    -- 左の detection を持ち上げて Or.inl
    have h := Eventually_prod.of_left (sm₂ := sm₂) psm hwf₂
                (P₁ := fun s _ => f₁.isFault s) f₁.detection
    obtain ⟨p, d, hp, hP⟩ := h
    exact ⟨p, d, hp, Or.inl hP⟩
  recovery := by
    -- 積で fault∨fault が成立する reachable state に対して、該当側の recovery を持ち上げる
    intro p d hr hfault
    cases hfault with
    | inl h₁ =>
        -- 左 fault: f₁.recovery を Leads_prod.of_left で積に持ち上げ、Or.inl
        have hLeads :
            Leads_prod psm
              (fun p' d' => (fun s _ => f₁.isFault s) p'.1 d'.1)
              (fun p' d' => (fun s _ => f₁.isRecovery s) p'.1 d'.1) :=
          Leads_prod.of_left (sm₂ := sm₂) psm hwf₂
            (P₁ := fun s _ => f₁.isFault s)
            (Q₁ := fun s _ => f₁.isRecovery s)
            f₁.recovery
        have hE := hLeads p d hr h₁
        obtain ⟨p', d', hp', hrec⟩ := hE
        exact ⟨p', d', hp', Or.inl hrec⟩
    | inr h₂ =>
        -- 右 fault: 対称
        have hLeads :
            Leads_prod psm
              (fun p' d' => (fun s _ => f₂.isFault s) p'.2 d'.2)
              (fun p' d' => (fun s _ => f₂.isRecovery s) p'.2 d'.2) :=
          Leads_prod.of_right (sm₁ := sm₁) psm hwf₁
            (P₂ := fun s _ => f₂.isFault s)
            (Q₂ := fun s _ => f₂.isRecovery s)
            f₂.recovery
        have hE := hLeads p d hr h₂
        obtain ⟨p', d', hp', hrec⟩ := hE
        exact ⟨p', d', hp', Or.inr hrec⟩

end VerifiedMBSE.VV
