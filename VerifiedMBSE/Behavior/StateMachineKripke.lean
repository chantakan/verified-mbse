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
-/

namespace VerifiedMBSE.Behavior

-- ============================================================
-- §1  StateMachine.toKripke
-- ============================================================

/-- StateMachine を KripkeStructure として見る。

    `abbrev` なので reducible で、`(sm.toKripke).reachable s d` が
    `Reachable sm s d` に defeq で展開される。 -/
abbrev StateMachine.toKripke
    {S D : Type} {inv : S → D → Prop}
    (sm : StateMachine S D inv) : KripkeStructure S D :=
  { reachable := Reachable sm }

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
