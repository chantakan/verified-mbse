import VerifiedMBSE.Behavior.StateMachine
import VerifiedMBSE.Behavior.KripkeStructure

/-!
# StateMachine → KripkeStructure via ToKripke

`StateMachine S D inv` に対する `ToKripke` instance を提供する。
これにより `Always sm P` 等の呼び出しが型クラス resolution 経由で透過的に解決される。

## Coe からの移行理由

`Coe (StateMachine S D inv) (KripkeStructure S D)` instance は、`inv` が α 側のみに
現れるため Lean 4.30 の strict semi-out-params チェックに引っかかる (β = KripkeStructure S D
から `inv` が flow できない)。

`ToKripke` 型クラスは `State` / `Data` のみ `outParam` とし、`α = StateMachine S D inv`
全体に対する instance matching を行うため、`inv` も含めて自然に解決される。

## B-8 での拡張

`KripkeStructure` が `inv` / `step` / `reachable_inv` / `step_preserves_reachable` を
持つようになったため、`StateMachine.toKripke` もこれらを埋める必要がある:

- `inv` = StateMachine の型引数 `inv : S → D → Prop` をそのまま代入 (defeq 成立)
- `reachable_inv` = 既存の `Reachable.inv_holds` の薄いラッパー
- `step` = transition を存在量化した 1 ステップ関係
- `step_preserves_reachable` = `Reachable.step` コンストラクタを呼ぶだけ

`abbrev` のまま維持することで `(sm.toKripke).inv = inv` /
`(sm.toKripke).reachable s d = Reachable sm s d` の defeq が保たれる。
-/

namespace VerifiedMBSE.Behavior

-- ============================================================
-- §1  StateMachine.toKripke
-- ============================================================

/-- StateMachine を KripkeStructure として見る。

    `abbrev` なので reducible で、以下の defeq 関係が成立する:
    - `(sm.toKripke).inv` = `inv` (型引数そのもの)
    - `(sm.toKripke).reachable s d` = `Reachable sm s d`
    - `(sm.toKripke).step s d s' d'` = 遷移の存在量化

    ### step の定義

    `step s d s' d'` は「ある遷移 `t ∈ sm.transitions` が存在して、
    `t.source = s` かつ `t.guard d` が成立し、`t.target = s'` かつ
    `t.effect d = d'` となる」ことを表す。

    ### step_preserves_reachable の証明

    `step` の存在量化を展開すると、対応する `t` と各等式が手に入るので、
    `Reachable.step` コンストラクタをそのまま適用できる。 -/
abbrev StateMachine.toKripke
    {S D : Type} {inv : S → D → Prop}
    (sm : StateMachine S D inv) : KripkeStructure S D :=
  { inv := inv
    reachable := Reachable sm
    reachable_inv := fun _ _ hr => hr.inv_holds
    step := fun s d s' d' =>
      ∃ (t : Transition S D inv),
        t ∈ sm.transitions ∧ t.source = s ∧ t.guard d ∧
        t.target = s' ∧ t.effect d = d'
    step_preserves_reachable := by
      intro s d s' d' hr hstep
      -- 存在量化を開き、等式 `t.target = s'` と `t.effect d = d'` は rfl で統合
      obtain ⟨t, hmem, hsrc, hguard, rfl, rfl⟩ := hstep
      exact Reachable.step t hr hmem hsrc hguard }

-- ============================================================
-- §2  ToKripke instance
-- ============================================================

/-- StateMachine に対する ToKripke instance。

    これにより `Always sm P` で sm : StateMachine S D inv が渡されると、
    `ToKripke (StateMachine S D inv) S D` が resolve され、
    `State = S, Data = D` が outParam で決定される。 -/
instance instToKripkeStateMachine
    {S D : Type} {inv : S → D → Prop} :
    ToKripke (StateMachine S D inv) S D where
  toKripke sm := sm.toKripke

-- ============================================================
-- §3  WellFormed → NonEmpty
-- ============================================================

/-- `sm.WellFormed` から `sm.toKripke.NonEmpty` を導く。 -/
theorem StateMachine.wellFormed_imp_nonEmpty
    {S D : Type} {inv : S → D → Prop}
    {sm : StateMachine S D inv}
    (hwf : sm.WellFormed) :
    sm.toKripke.NonEmpty := by
  obtain ⟨d₀, hd₀⟩ := hwf
  exact ⟨sm.initialState, d₀, Reachable.init d₀ hd₀⟩

/-- ドット記法用のエイリアス: `hwf.nonEmpty`. -/
theorem StateMachine.WellFormed.nonEmpty
    {S D : Type} {inv : S → D → Prop}
    {sm : StateMachine S D inv}
    (hwf : sm.WellFormed) :
    sm.toKripke.NonEmpty :=
  StateMachine.wellFormed_imp_nonEmpty hwf

end VerifiedMBSE.Behavior
