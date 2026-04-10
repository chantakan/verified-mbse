import VerifiedMBSE.Core.Component

/-!
# State Machine: Dependently Typed Behavioral Model

Defines `Transition` (with invariant preservation embedded as a type-level proof),
`StateMachine`, the inductive proposition `Reachable`, and the safety theorem
`Reachable.inv_holds`.

## Key Design Decision
Embedding invariant preservation in `Transition.preserves` makes transitions that
violate the invariant unconstructible (type error).
-/

namespace VerifiedMBSE.Behavior

-- ============================================================
-- §1  Transition
-- ============================================================

/-- Transition: 制御状態 S とデータ型 D の上で定義される遷移。
    `preserves` フィールドにより、不変条件保存が型レベルで保証される。 -/
structure Transition (S : Type) (D : Type) (inv : S → D → Prop) where
  /-- 遷移元の制御状態 -/
  source   : S
  /-- 遷移先の制御状態 -/
  target   : S
  /-- ガード条件 -/
  guard    : D → Prop
  /-- エフェクト（データ変換） -/
  effect   : D → D
  /-- 不変条件保存の型レベル契約 -/
  preserves : ∀ d : D, guard d → inv source d → inv target (effect d)

-- ============================================================
-- §2  StateMachine
-- ============================================================

/-- StateMachine: 初期状態と遷移リストから構成される状態機械。 -/
structure StateMachine (S : Type) (D : Type) (inv : S → D → Prop) where
  /-- 初期制御状態 -/
  initialState : S
  /-- 遷移のリスト -/
  transitions  : List (Transition S D inv)

/-- StateMachine の整合性条件：初期状態で不変条件を満たすデータが存在する。 -/
def StateMachine.WellFormed {S D : Type} {inv : S → D → Prop}
    (sm : StateMachine S D inv) : Prop :=
  ∃ d₀ : D, inv sm.initialState d₀

-- ============================================================
-- §3  Reachable（到達可能性）
-- ============================================================

/-- Reachable: 状態機械の到達可能な (制御状態, データ値) の帰納的命題。
    制御状態とデータ値を同時追跡することで inv_holds の帰納法を可能にする。 -/
inductive Reachable {S D : Type} {inv : S → D → Prop}
    (sm : StateMachine S D inv) : S → D → Prop where
  /-- 初期状態は到達可能 -/
  | init : ∀ (d₀ : D), inv sm.initialState d₀ →
           Reachable sm sm.initialState d₀
  /-- 遷移により次の状態に到達可能 -/
  | step : ∀ {s : S} {d : D} (t : Transition S D inv),
           Reachable sm s d →
           t ∈ sm.transitions →
           t.source = s →
           t.guard d →
           Reachable sm t.target (t.effect d)

-- ============================================================
-- §4  安全性定理
-- ============================================================

/-- 安全性定理：到達可能なペアは必ず不変条件を満たす。
    Transition.preserves が型に埋め込まれているため帰納法で直接証明できる。 -/
theorem Reachable.inv_holds {S D : Type} {inv : S → D → Prop}
    {sm : StateMachine S D inv} {s : S} {d : D}
    (h : Reachable sm s d) : inv s d := by
  induction h with
  | init d₀ hd₀ =>
      exact hd₀
  | step t _hr _hmem hsrc hguard ih =>
      rw [← hsrc] at ih
      exact t.preserves _ hguard ih

/-- WellFormed な状態機械の初期状態は不変条件を満たすデータを持つ。 -/
theorem StateMachine.initial_inv_holds {S D : Type} {inv : S → D → Prop}
    {sm : StateMachine S D inv}
    (hwf : sm.WellFormed) :
    ∃ d : D, inv sm.initialState d :=
  hwf

end VerifiedMBSE.Behavior
