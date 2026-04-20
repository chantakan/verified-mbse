import VerifiedMBSE.VV.SubSystemSpec
import VerifiedMBSE.Behavior.ProductTemporal

/-!
# Parallel Composition of SubSystemSpec / FDIRBundle / BehavioralSpec (B-8c generalized)

積 Kripke 構造 `ProductKripke x y` 上の統一 `FDIRBundle` / `BehavioralSpec` /
`SubSystemSpec` を、各要素の並列合成として構築する `compose` 群を定義する。

## 内容

1. `FDIRBundle.compose` (B-6, B-8c 一般化): 2 つの `FDIRBundle` の合成
2. `BehavioralSpec.compose` (B-7, B-8c 一般化): 2 つの `BehavioralSpec` の合成
3. `SubSystemSpec.compose` (B-7, B-8c 一般化): 2 つの `SubSystemSpec` の合成

## B-6 → B-7 → B-8c の設計変遷

B-6: `ProductFDIRBundle` 独立構造体として合成 API を提供。
B-7: `SubSystemSpec` に `BehavioralSpec`・`FDIRBundle`・`StructuralSpec` を統合し、
     `StateMachine` / `ProductStateMachine` で統一 API 化。合成は 2 機のみ。
B-8c: **型引数を `ToKripke` 型クラスベースに一般化**。これにより:
- `(pk : ProductKripke epsMiniPSM mini2SM)` のような **3 機以上のネスト合成** が可能に
- WellFormed 引数を `NonEmpty` に弱化。StateMachine 呼び出し側は `.nonEmpty` で変換

## 合成の意味論（FDIR 部）

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
`FDIRBundle pk` を直接構築する設計とした。

## 合成 API の粒度

B-8c でも `compose` (2 引数) のみを提供する。N 機合成は型が異なるためリスト
ベースの `foldl` ではなく、**`compose` のネスト** で書く:

```lean
let s₁₂ := SubSystemSpec.compose s₁ s₂ pk₁₂ hne₁ hne₂ [] ...
let s₁₂₃ := SubSystemSpec.compose s₁₂ s₃ pk₁₂₃ s₁₂.behavioral.nonEmpty hne₃ [] ...
```

3 機目以降は `pk₁₂ : ProductKripke x₁ x₂` が **新たな ToKripke 要素** となるため、
NonEmpty は `s₁₂.behavioral.nonEmpty` から供給できる（B-8c のキーとなる一般化）。
将来 B-8d で可変長合成 API を追加する余地あり。
-/

namespace VerifiedMBSE.VV

open VerifiedMBSE.Core
open VerifiedMBSE.Behavior

-- ============================================================
-- §1  FDIRBundle.compose (B-8c generalized)
-- ============================================================

/-- 2 つの `FDIRBundle` の並列合成。

    型引数が `{α β} [ToKripke α S₁ D₁] [ToKripke β S₂ D₂] {x : α} {y : β}` に
    一般化されたため、2 機目以降のネスト合成
    (`FDIRBundle.compose f₁₂ f₃ pk₁₂₃ hne₁₂ hne₃`) も同じ API で書ける。

    戻り値は積 Kripke 構造 `pk : ProductKripke x y` 上の統一 `FDIRBundle pk`。

    構成:
    - `safety`    ← `Always_prod.of_and` で両 safety を積の合取にまとめる
    - `detection` ← 左 detection を `Eventually_prod.of_left` で持ち上げ、`Or.inl`
    - `recovery`  ← `Leads_prod.of_left` / `.of_right` で fault 側の recovery を
      選び、`Or.inl` / `Or.inr` で合成 isRecovery にマップ -/
def FDIRBundle.compose
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    (f₁ : FDIRBundle x) (f₂ : FDIRBundle y)
    (pk : ProductKripke x y)
    (hne₁ : (ToKripke.toKripke x).NonEmpty)
    (hne₂ : (ToKripke.toKripke y).NonEmpty) :
    FDIRBundle pk where
  isFault    := fun p => f₁.isFault p.1 ∨ f₂.isFault p.2
  isRecovery := fun p => f₁.isRecovery p.1 ∨ f₂.isRecovery p.2
  isSafe     := fun q => f₁.isSafe q.1 ∧ f₂.isSafe q.2
  safety := Always_prod.of_and pk f₁.safety f₂.safety
  detection := by
    -- 左の detection を持ち上げて Or.inl
    have h := Eventually_prod.of_left (y := y) pk hne₂
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
            Leads_prod pk
              (fun p' d' => (fun s _ => f₁.isFault s) p'.1 d'.1)
              (fun p' d' => (fun s _ => f₁.isRecovery s) p'.1 d'.1) :=
          Leads_prod.of_left (y := y) pk hne₂
            (P₁ := fun s _ => f₁.isFault s)
            (Q₁ := fun s _ => f₁.isRecovery s)
            f₁.recovery
        have hE := hLeads p d hr h₁
        obtain ⟨p', d', hp', hrec⟩ := hE
        exact ⟨p', d', hp', Or.inl hrec⟩
    | inr h₂ =>
        -- 右 fault: 対称
        have hLeads :
            Leads_prod pk
              (fun p' d' => (fun s _ => f₂.isFault s) p'.2 d'.2)
              (fun p' d' => (fun s _ => f₂.isRecovery s) p'.2 d'.2) :=
          Leads_prod.of_right (x := x) pk hne₁
            (P₂ := fun s _ => f₂.isFault s)
            (Q₂ := fun s _ => f₂.isRecovery s)
            f₂.recovery
        have hE := hLeads p d hr h₂
        obtain ⟨p', d', hp', hrec⟩ := hE
        exact ⟨p', d', hp', Or.inr hrec⟩

-- ============================================================
-- §2  BehavioralSpec.compose (B-8c generalized)
-- ============================================================

/-- 2 つの `BehavioralSpec` の並列合成。

    戻り値は積 Kripke 構造上の `BehavioralSpec pk`。`nonEmpty` は
    `ProductKripke.nonEmpty` で、要素の `NonEmpty` から構築。 -/
def BehavioralSpec.compose
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    (_b₁ : BehavioralSpec x) (_b₂ : BehavioralSpec y)
    (pk : ProductKripke x y)
    (hne₁ : (ToKripke.toKripke x).NonEmpty)
    (hne₂ : (ToKripke.toKripke y).NonEmpty) :
    BehavioralSpec pk where
  nonEmpty := ProductKripke.nonEmpty pk hne₁ hne₂

-- ============================================================
-- §3  SubSystemSpec.compose (B-8c generalized)
-- ============================================================

/-- 2 つの `SubSystemSpec` の並列合成。

    構造・行動・FDIR の各フィールドをそれぞれの要素版合成で埋めた結果を
    返す。戻り値は積 Kripke 構造 `pk` 上の統一 `SubSystemSpec pk`。

    - `structural` ← `StructuralSpec.compose`（`bridge` connectors 付き）
    - `behavioral` ← `BehavioralSpec.compose`
    - `fdir`       ← `FDIRBundle.compose`

    N 機合成は `compose` のネストで実現する（ファイル先頭のモジュール
    ドキュメント参照）。3 機目以降は `s₁₂.behavioral.nonEmpty` が自動的に
    供給可能（B-8c のキーとなる一般化）。 -/
def SubSystemSpec.compose
    {α β : Type} {S₁ D₁ S₂ D₂ : Type}
    [ToKripke α S₁ D₁] [ToKripke β S₂ D₂]
    {x : α} {y : β}
    (spec₁ : SubSystemSpec x) (spec₂ : SubSystemSpec y)
    (pk : ProductKripke x y)
    (hne₁ : (ToKripke.toKripke x).NonEmpty)
    (hne₂ : (ToKripke.toKripke y).NonEmpty)
    (bridge : List Connector)
    (hbridge : ∀ c ∈ bridge,
        c.source.part ∈ spec₁.structural.system.parts ++ spec₂.structural.system.parts ∧
        c.target.part ∈ spec₁.structural.system.parts ++ spec₂.structural.system.parts) :
    SubSystemSpec pk where
  structural :=
    StructuralSpec.compose spec₁.structural spec₂.structural bridge hbridge
  behavioral :=
    BehavioralSpec.compose spec₁.behavioral spec₂.behavioral pk hne₁ hne₂
  fdir :=
    FDIRBundle.compose spec₁.fdir spec₂.fdir pk hne₁ hne₂

end VerifiedMBSE.VV
