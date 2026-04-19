import VerifiedMBSE.Behavior.StateMachine
import VerifiedMBSE.Behavior.StateMachineKripke
import VerifiedMBSE.Behavior.Temporal

/-!
# StateMachine-specific LTL Operators

`Next` (◯ P) と `Until` (P U Q) は具体的な遷移リスト (`sm.transitions`) に
依存するため、`KripkeStructure` ではなく `StateMachine` 固有の演算子として
ここに分離する。

将来 `Next` / `Until` を `KripkeStructure` に持ち上げる場合は、
「ステップ関係」`K.step : State → Data → State → Data → Prop` を
`KripkeStructure` に追加する拡張を行う。現状は StateMachine のみで十分。
-/

namespace VerifiedMBSE.Behavior

-- ============================================================
-- §1  Next (◯)
-- ============================================================

/-- Next (◯ P): 状態 `s`・データ `d` から一歩先の状態で `P` が成立する
    遷移が存在する。遷移リストに依存するため StateMachine 固有。 -/
def Next {S D : Type} {inv : S → D → Prop}
    (sm : StateMachine S D inv)
    (P : S → D → Prop) (s : S) (d : D) : Prop :=
  ∃ t ∈ sm.transitions,
    t.source = s ∧ t.guard d ∧ P t.target (t.effect d)

-- ============================================================
-- §2  Until (P U Q)
-- ============================================================

/-- Until (P U Q): P が保持されている間に Q が成立する状態に到達する。

    `now` ケース: 現在状態で既に Q が成立。
    `later` ケース: P が成立する状態から、遷移を 1 歩進めた先でも Until が
    継続する (帰納的定義)。 -/
inductive Until {S D : Type} {inv : S → D → Prop}
    (sm : StateMachine S D inv)
    (P Q : S → D → Prop) : S → D → Prop where
  | now   : ∀ {s : S} {d : D}, Q s d →
            Until sm P Q s d
  | later : ∀ {s : S} {d : D} (t : Transition S D inv),
            P s d →
            t ∈ sm.transitions →
            t.source = s →
            t.guard d →
            Until sm P Q t.target (t.effect d) →
            Until sm P Q s d

/-- Until P Q → Eventually Q (Reachable 証人が必要)。

    現状態が reachable であるという witness `hr` を使って、Until の帰納に
    沿って到達可能性を伝搬させ、Q が成立する reachable state を構成する。 -/
theorem until_implies_eventually
    {S D : Type} {inv : S → D → Prop}
    {sm : StateMachine S D inv}
    {P Q : S → D → Prop}
    {s : S} {d : D}
    (hr : Reachable sm s d)
    (h : Until sm P Q s d) :
    Eventually sm Q := by
  induction h with
  | now hq =>
      exact ⟨_, _, hr, hq⟩
  | later t _hP hmem hsrc hguard _hU ih =>
      exact ih (Reachable.step t hr hmem hsrc hguard)

end VerifiedMBSE.Behavior
