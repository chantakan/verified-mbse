import VerifiedMBSE.Behavior.KripkeStructure

/-!
# LTL Temporal Operators via ToKripke Type Class

Always (□), Eventually (◇), Leads (⇒◇) を `ToKripke` 型クラス経由で定義する。
これにより `Always sm P` / `Always psm P` / `Always ct P` のような呼び出しを
StateMachine・積状態機械・連続時間系などに対して同一 API で提供できる。

## ToKripke 経由の dispatch

`Always x P` で `x : α` を渡すと、`ToKripke α State Data` instance が解決され、
`State` / `Data` が `outParam` として決定される。`P : State → Data → Prop` の
形で明示的に elaborate されるため、`fun s d => Q s d` のような lambda の
domain 型が確定し、後続の `omega` や `simp` などが誤動作しない。

## Next と Until について

Next (◯) と Until (P U Q) は具体的な遷移構造 (transitions リスト) に依存する
ため、`KripkeStructure` には含めず `StateMachineLTL.lean` に分離する。
-/

namespace VerifiedMBSE.Behavior

-- ============================================================
-- §1  Basic Temporal Operators
-- ============================================================

/-- Always (□ P): 全ての到達可能な `(s, d)` で `P s d` が成立する。

    `abbrev` かつ型クラス経由のため、`intro s d hr` した際に goal の lambda
    が自動で β 還元される。 -/
abbrev Always {α : Type} {State Data : Type} [ToKripke α State Data]
    (x : α) (P : State → Data → Prop) : Prop :=
  ∀ s d, (ToKripke.toKripke x).reachable s d → P s d

/-- Eventually (◇ P): `P s d` が成立する到達可能な `(s, d)` が存在する。 -/
abbrev Eventually {α : Type} {State Data : Type} [ToKripke α State Data]
    (x : α) (P : State → Data → Prop) : Prop :=
  ∃ s d, (ToKripke.toKripke x).reachable s d ∧ P s d

/-- Leads (P ⇒ ◇ Q): 弱い意味論 (到達可能な P 位置から、到達可能な Q 位置が存在)。 -/
abbrev Leads {α : Type} {State Data : Type} [ToKripke α State Data]
    (x : α) (P Q : State → Data → Prop) : Prop :=
  Always x (fun s d => P s d → Eventually x Q)

-- ============================================================
-- §2  Basic Algebraic Laws
-- ============================================================

/-- □ P ∧ □ Q → □(P ∧ Q). -/
theorem always_and {α : Type} {State Data : Type} [ToKripke α State Data]
    {x : α} {P Q : State → Data → Prop}
    (hP : Always x P) (hQ : Always x Q) :
    Always x (fun s d => P s d ∧ Q s d) :=
  fun s d hr => ⟨hP s d hr, hQ s d hr⟩

/-- NonEmpty + □ P → ◇ P. -/
theorem always_implies_eventually {α : Type} {State Data : Type}
    [ToKripke α State Data]
    {x : α} {P : State → Data → Prop}
    (hne : (ToKripke.toKripke x).NonEmpty) (h : Always x P) :
    Eventually x P := by
  obtain ⟨s, d, hr⟩ := hne
  exact ⟨s, d, hr, h s d hr⟩

/-- Leads P P: 自己反射性。 -/
theorem always_leads {α : Type} {State Data : Type} [ToKripke α State Data]
    {x : α} {P : State → Data → Prop} :
    Leads x P P :=
  fun s d hr hP => ⟨s, d, hr, hP⟩

end VerifiedMBSE.Behavior
