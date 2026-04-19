import VerifiedMBSE.Behavior.StateMachine

/-!
# ProductStateMachine and ProductReachable

2 つの StateMachine のインタリーブ積を扱う。積状態機械を専用の `ProductStateMachine`
構造体として定義し、到達可能性を inductive `ProductReachable` で与える。

## Design Decision: Why a Dedicated Type?

既存の `Transition.source : S` は具体値（S の 1 点）なので、`StateMachine` 型の
`transitions : List (Transition ...)` として積状態機械を表現するには、S の全値を
列挙して cross product を作る必要があり、結果として `[Fintype S₁] [Fintype S₂]`
仮定が必須になる。

しかし verified-mbse は連続状態空間（CBF 前方不変性、軌道動力学、ロボティクスの
構成空間、ハイブリッドシステム等）を扱う要求に応えるべく、**有限性仮定を避ける**
方針を採る。したがって積は `StateMachine` を返すのではなく、独立した inductive
proposition で表現する。

既存の `Reachable`/`Always`/`Eventually`/`Leads` はそのまま使え、積用の対応物
(`ProductReachable`/`Always_prod`/`Eventually_prod`/`Leads_prod`) を並行定義する。
-/

namespace VerifiedMBSE.Behavior

-- ============================================================
-- §1  Product Invariant
-- ============================================================

/-- 積不変条件: 2 つの不変条件の連言。

    `abbrev` とすることで `.1`, `.2` アクセスや `refine ⟨_, _⟩` が透過的に動く。 -/
abbrev productInv
    {S₁ D₁ : Type} (inv₁ : S₁ → D₁ → Prop)
    {S₂ D₂ : Type} (inv₂ : S₂ → D₂ → Prop) :
    S₁ × S₂ → D₁ × D₂ → Prop :=
  fun p d => inv₁ p.1 d.1 ∧ inv₂ p.2 d.2

-- ============================================================
-- §2  ProductStateMachine
-- ============================================================

/-- 積状態機械。2 つの StateMachine を型引数に持つ空構造体で、意味論は
    `ProductReachable` の inductive で与える。構造体としては空だが、
    `ProductStateMachine sm₁ sm₂` という型そのものが「sm₁ と sm₂ の積を考える」
    という合意を表現する。将来メタデータ（表示名、同期遷移表等）を追加する余地を
    残すための構造体型。 -/
structure ProductStateMachine
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    (sm₁ : StateMachine S₁ D₁ inv₁) (sm₂ : StateMachine S₂ D₂ inv₂) : Type where

/-- 積状態機械の初期状態: 両方の StateMachine の初期状態のペア。 -/
def ProductStateMachine.initialState
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    (_ : ProductStateMachine sm₁ sm₂) : S₁ × S₂ :=
  (sm₁.initialState, sm₂.initialState)

/-- 積状態機械の WellFormed: 両方の StateMachine が WellFormed である。 -/
def ProductStateMachine.WellFormed
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    (_ : ProductStateMachine sm₁ sm₂) : Prop :=
  sm₁.WellFormed ∧ sm₂.WellFormed

-- ============================================================
-- §3  ProductReachable (Interleaving Semantics)
-- ============================================================

/-- 積状態機械の到達可能性。**インタリーブ積** として定義する: 各ステップは
    sm₁ または sm₂ のいずれか一方の遷移を消費する（同期遷移は将来拡張）。

    設計上、片側の遷移を「持ち上げる」際は相手側の状態・データが不変であることを
    保証するため、stepLeft は sm₂ 成分をそのまま保持し、stepRight は sm₁ 成分を
    そのまま保持する。これにより `productInv` の保存が構造的に証明できる。 -/
inductive ProductReachable
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    (sm₁ : StateMachine S₁ D₁ inv₁) (sm₂ : StateMachine S₂ D₂ inv₂) :
    S₁ × S₂ → D₁ × D₂ → Prop where
  /-- 初期状態: 両方の StateMachine の初期状態で、両方の不変条件を満たすデータ。 -/
  | init : ∀ (d₁ : D₁) (d₂ : D₂),
      inv₁ sm₁.initialState d₁ →
      inv₂ sm₂.initialState d₂ →
      ProductReachable sm₁ sm₂
        (sm₁.initialState, sm₂.initialState) (d₁, d₂)
  /-- 左側の遷移: sm₁ の遷移を実行し sm₂ 側の状態・データは不変。 -/
  | stepLeft : ∀ {s₁ : S₁} {s₂ : S₂} {d₁ : D₁} {d₂ : D₂}
      (t : Transition S₁ D₁ inv₁),
      ProductReachable sm₁ sm₂ (s₁, s₂) (d₁, d₂) →
      t ∈ sm₁.transitions →
      t.source = s₁ →
      t.guard d₁ →
      ProductReachable sm₁ sm₂ (t.target, s₂) (t.effect d₁, d₂)
  /-- 右側の遷移: sm₂ の遷移を実行し sm₁ 側の状態・データは不変。 -/
  | stepRight : ∀ {s₁ : S₁} {s₂ : S₂} {d₁ : D₁} {d₂ : D₂}
      (t : Transition S₂ D₂ inv₂),
      ProductReachable sm₁ sm₂ (s₁, s₂) (d₁, d₂) →
      t ∈ sm₂.transitions →
      t.source = s₂ →
      t.guard d₂ →
      ProductReachable sm₁ sm₂ (s₁, t.target) (d₁, t.effect d₂)

-- ============================================================
-- §4  Product Safety Theorem
-- ============================================================

/-- 積の安全性定理: ProductReachable なら productInv を満たす。
    `Transition.preserves` の type-level 契約と各コンストラクタの「相手側不変」構造から
    直接 induction で証明できる。 -/
theorem ProductReachable.inv_holds
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    {p : S₁ × S₂} {d : D₁ × D₂}
    (h : ProductReachable sm₁ sm₂ p d) :
    productInv inv₁ inv₂ p d := by
  induction h with
  | init d₁ d₂ h₁ h₂ => exact ⟨h₁, h₂⟩
  | stepLeft t _hr _hmem hsrc hguard ih =>
      refine ⟨?_, ih.2⟩
      have h1 := ih.1
      rw [← hsrc] at h1
      exact t.preserves _ hguard h1
  | stepRight t _hr _hmem hsrc hguard ih =>
      refine ⟨ih.1, ?_⟩
      have h2 := ih.2
      rw [← hsrc] at h2
      exact t.preserves _ hguard h2

-- ============================================================
-- §5  Projection Lemmas
-- ============================================================

/-- 射影: 積の到達可能性から左成分の到達可能性を取り出す。

    stepLeft ケースでは既存の `Reachable.step` で 1 ステップ進め、
    stepRight ケースでは左成分が変化しないので帰納法仮説をそのまま使う。 -/
theorem ProductReachable.fst_reachable
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    {p : S₁ × S₂} {d : D₁ × D₂}
    (h : ProductReachable sm₁ sm₂ p d) :
    Reachable sm₁ p.1 d.1 := by
  induction h with
  | init d₁ _d₂ h₁ _h₂ => exact Reachable.init d₁ h₁
  | stepLeft t _hr hmem hsrc hguard ih =>
      exact Reachable.step t ih hmem hsrc hguard
  | stepRight _t _hr _hmem _hsrc _hguard ih => exact ih

/-- 射影: 積の到達可能性から右成分の到達可能性を取り出す。 -/
theorem ProductReachable.snd_reachable
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    {p : S₁ × S₂} {d : D₁ × D₂}
    (h : ProductReachable sm₁ sm₂ p d) :
    Reachable sm₂ p.2 d.2 := by
  induction h with
  | init _d₁ d₂ _h₁ h₂ => exact Reachable.init d₂ h₂
  | stepLeft _t _hr _hmem _hsrc _hguard ih => exact ih
  | stepRight t _hr hmem hsrc hguard ih =>
      exact Reachable.step t ih hmem hsrc hguard

-- ============================================================
-- §6  Lifting Lemmas
-- ============================================================

/-- 持ち上げ: sm₁ の到達可能性を積の到達可能性に持ち上げる。
    片側の trace を積の trace にするには、相手側（sm₂）の WellFormed から
    初期データを供給し、sm₁ 側の遷移は stepLeft で積へ lift する。 -/
theorem ProductReachable.fromLeft
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    {s₁ : S₁} {d₁ : D₁}
    (hr₁ : Reachable sm₁ s₁ d₁)
    (hwf₂ : sm₂.WellFormed) :
    ∃ (s₂ : S₂) (d₂ : D₂), ProductReachable sm₁ sm₂ (s₁, s₂) (d₁, d₂) := by
  induction hr₁ with
  | init d₁₀ h =>
      obtain ⟨d₂₀, h₂⟩ := hwf₂
      exact ⟨sm₂.initialState, d₂₀,
             ProductReachable.init d₁₀ d₂₀ h h₂⟩
  | step t _hr hmem hsrc hguard ih =>
      obtain ⟨s₂, d₂, hp⟩ := ih
      exact ⟨s₂, d₂,
             ProductReachable.stepLeft t hp hmem hsrc hguard⟩

/-- 持ち上げ: sm₂ の到達可能性を積の到達可能性に持ち上げる。 -/
theorem ProductReachable.fromRight
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    {s₂ : S₂} {d₂ : D₂}
    (hr₂ : Reachable sm₂ s₂ d₂)
    (hwf₁ : sm₁.WellFormed) :
    ∃ (s₁ : S₁) (d₁ : D₁), ProductReachable sm₁ sm₂ (s₁, s₂) (d₁, d₂) := by
  induction hr₂ with
  | init d₂₀ h =>
      obtain ⟨d₁₀, h₁⟩ := hwf₁
      exact ⟨sm₁.initialState, d₁₀,
             ProductReachable.init d₁₀ d₂₀ h₁ h⟩
  | step t _hr hmem hsrc hguard ih =>
      obtain ⟨s₁, d₁, hp⟩ := ih
      exact ⟨s₁, d₁,
             ProductReachable.stepRight t hp hmem hsrc hguard⟩

-- ============================================================
-- §7  ProductStateMachine.WellFormed Characterization
-- ============================================================

/-- ProductStateMachine.WellFormed は各成分の WellFormed の連言。 -/
theorem ProductStateMachine.wellFormed_iff
    {S₁ D₁ : Type} {inv₁ : S₁ → D₁ → Prop}
    {S₂ D₂ : Type} {inv₂ : S₂ → D₂ → Prop}
    {sm₁ : StateMachine S₁ D₁ inv₁} {sm₂ : StateMachine S₂ D₂ inv₂}
    (psm : ProductStateMachine sm₁ sm₂) :
    psm.WellFormed ↔ sm₁.WellFormed ∧ sm₂.WellFormed :=
  Iff.rfl

end VerifiedMBSE.Behavior
