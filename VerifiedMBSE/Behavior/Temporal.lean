import VerifiedMBSE.Behavior.StateMachine

/-!
# LTL Temporal Operators as Type-Level Propositions

Defines Always (□), Eventually (◇), Next (○), Until (U), and Leads (⇒◇)
as propositions over `Reachable`, and proves basic algebraic laws.
-/

namespace VerifiedMBSE.Behavior

-- ============================================================
-- §1  基本時相演算子
-- ============================================================

/-- Always (□ P): 到達可能な全ての状態で P が成り立つ。 -/
def Always {S D : Type} {inv : S → D → Prop}
    (sm : StateMachine S D inv)
    (P : S → D → Prop) : Prop :=
  ∀ s d, Reachable sm s d → P s d

/-- Eventually (◇ P): P が成り立つ状態に到達可能。 -/
def Eventually {S D : Type} {inv : S → D → Prop}
    (sm : StateMachine S D inv)
    (P : S → D → Prop) : Prop :=
  ∃ s d, Reachable sm s d ∧ P s d

/-- Next (○ P): 現在状態から1ステップで P が成り立つ状態に遷移可能。 -/
def Next {S D : Type} {inv : S → D → Prop}
    (sm : StateMachine S D inv)
    (P : S → D → Prop) (s : S) (d : D) : Prop :=
  ∃ t ∈ sm.transitions,
    t.source = s ∧ t.guard d ∧ P t.target (t.effect d)

/-- Until (P U Q): P が成り立ち続けて最終的に Q が成り立つ。 -/
inductive Until {S D : Type} {inv : S → D → Prop}
    (sm : StateMachine S D inv)
    (P Q : S → D → Prop) : S → D → Prop where
  | now   : ∀ {s d}, Q s d →
            Until sm P Q s d
  | later : ∀ {s d} (t : Transition S D inv),
            P s d →
            t ∈ sm.transitions →
            t.source = s →
            t.guard d →
            Until sm P Q t.target (t.effect d) →
            Until sm P Q s d

/-- Leads (P ⇒ ◇ Q): P が成り立つ全ての到達可能状態から Q に到達可能。 -/
def Leads {S D : Type} {inv : S → D → Prop}
    (sm : StateMachine S D inv)
    (P Q : S → D → Prop) : Prop :=
  Always sm (fun s d => P s d → Eventually sm Q)

-- ============================================================
-- §2  基本代数則
-- ============================================================

/-- □ P ∧ □ Q → □(P ∧ Q) -/
theorem always_and {S D : Type} {inv : S → D → Prop}
    {sm : StateMachine S D inv}
    {P Q : S → D → Prop}
    (hP : Always sm P) (hQ : Always sm Q) :
    Always sm (fun s d => P s d ∧ Q s d) :=
  fun s d hr => ⟨hP s d hr, hQ s d hr⟩

/-- □ P → ◇ P（WellFormed な場合）。 -/
theorem always_implies_eventually {S D : Type} {inv : S → D → Prop}
    {sm : StateMachine S D inv}
    {P : S → D → Prop}
    (hwf : sm.WellFormed)
    (h : Always sm P) :
    Eventually sm P := by
  obtain ⟨d₀, hd₀⟩ := hwf
  exact ⟨sm.initialState, d₀, Reachable.init d₀ hd₀, h sm.initialState d₀ (Reachable.init d₀ hd₀)⟩

/-- Leads P P は自明に成立（到達可能な状態自身が証人）。 -/
theorem always_leads {S D : Type} {inv : S → D → Prop}
    {sm : StateMachine S D inv}
    {P : S → D → Prop} :
    Leads sm P P :=
  fun s d hr hP => ⟨s, d, hr, hP⟩

/-- Until P Q → Eventually Q（到達可能性の証人が必要）。 -/
theorem until_implies_eventually {S D : Type} {inv : S → D → Prop}
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
