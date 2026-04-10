import VerifiedMBSE.Core.Component

/-!
# HoTT 的コンポーネント等価性

PortEquiv（ポートインターフェース等価性）、ComponentEquiv（コンポーネント等価性）、
Substitutable（代替可能性）、および transport（設計空間での移行）を定義する。

## HoTT との対応
- Equivalence (A ≃ B) → ComponentEquiv
- Univalence (A ≃ B → A = B) → Substitutability principle
- Transport → transport_wellFormed
-/

namespace VerifiedMBSE.Equivalence

open VerifiedMBSE.Core

-- ============================================================
-- §1  インターフェース等価性
-- ============================================================

/-- PortCompatible: 二つのポートが互換（flowType と direction が一致）。 -/
def PortCompatible (p q : PortDef) : Prop :=
  p.flowType = q.flowType ∧ p.feature.direction = q.feature.direction

/-- PortEquiv: 二つのポートリストが構造的に等価。
    HoTT 的には PortBundle(A) ≃ PortBundle(B)。 -/
structure PortEquiv (ports₁ ports₂ : List PortDef) : Prop where
  /-- ポート数が一致 -/
  length_eq : ports₁.length = ports₂.length
  /-- ports₁ → ports₂ の互換対応 -/
  forward : ∀ p ∈ ports₁, ∃ q ∈ ports₂, PortCompatible p q
  /-- ports₂ → ports₁ の互換対応 -/
  backward : ∀ q ∈ ports₂, ∃ p ∈ ports₁, PortCompatible q p

/-- PortEquiv は反射的。 -/
theorem PortEquiv.refl (ports : List PortDef) : PortEquiv ports ports :=
  { length_eq := rfl
    forward   := fun p hp => ⟨p, hp, rfl, rfl⟩
    backward  := fun p hp => ⟨p, hp, rfl, rfl⟩ }

/-- PortEquiv は対称的。 -/
theorem PortEquiv.symm {p₁ p₂ : List PortDef}
    (h : PortEquiv p₁ p₂) : PortEquiv p₂ p₁ :=
  { length_eq := h.length_eq.symm
    forward   := h.backward
    backward  := h.forward }

/-- PortEquiv は推移的。 -/
theorem PortEquiv.trans {p₁ p₂ p₃ : List PortDef}
    (h₁₂ : PortEquiv p₁ p₂) (h₂₃ : PortEquiv p₂ p₃) :
    PortEquiv p₁ p₃ :=
  { length_eq := h₁₂.length_eq.trans h₂₃.length_eq
    forward   := fun p hp => by
      obtain ⟨q, hq, hfq, hdq⟩ := h₁₂.forward p hp
      obtain ⟨r, hr, hfr, hdr⟩ := h₂₃.forward q hq
      exact ⟨r, hr, hfq.trans hfr, hdq.trans hdr⟩
    backward  := fun r hr => by
      obtain ⟨q, hq, hfq, hdq⟩ := h₂₃.backward r hr
      obtain ⟨p, hp, hfp, hdp⟩ := h₁₂.backward q hq
      exact ⟨p, hp, hfq.trans hfp, hdq.trans hdp⟩ }

-- ============================================================
-- §2  コンポーネント等価性
-- ============================================================

/-- ComponentEquiv: 二つの PartDef が等価。
    ポートインターフェースが等価かつ不変条件が同値。 -/
structure ComponentEquiv (a b : PartDef) : Prop where
  /-- ポートインターフェースの等価性 -/
  portEquiv : PortEquiv a.ports b.ports
  /-- 不変条件の同値性 -/
  invariantIff : a.invariant ↔ b.invariant

/-- ComponentEquiv は反射的。 -/
theorem ComponentEquiv.refl (pd : PartDef) : ComponentEquiv pd pd :=
  { portEquiv := PortEquiv.refl pd.ports, invariantIff := Iff.rfl }

/-- ComponentEquiv は対称的。 -/
theorem ComponentEquiv.symm {a b : PartDef}
    (h : ComponentEquiv a b) : ComponentEquiv b a :=
  { portEquiv := h.portEquiv.symm, invariantIff := h.invariantIff.symm }

/-- ComponentEquiv は推移的。 -/
theorem ComponentEquiv.trans {a b c : PartDef}
    (hab : ComponentEquiv a b) (hbc : ComponentEquiv b c) :
    ComponentEquiv a c :=
  { portEquiv := hab.portEquiv.trans hbc.portEquiv
    invariantIff := hab.invariantIff.trans hbc.invariantIff }

-- ============================================================
-- §3  代替可能性
-- ============================================================

/-- Substitutable: A が B に代替可能（upward compatible）。
    ComponentEquiv より弱い条件。 -/
structure Substitutable (a b : PartDef) : Prop where
  /-- b の不変条件は a の不変条件を含意する -/
  invariantStronger : b.invariant → a.invariant
  /-- a の全ポートが b にも存在する -/
  portsSubset : ∀ p ∈ a.ports, ∃ q ∈ b.ports, PortCompatible p q

/-- ComponentEquiv → Substitutable（双方向の特殊ケース）。 -/
theorem ComponentEquiv.toSubstitutable {a b : PartDef}
    (h : ComponentEquiv a b) : Substitutable a b :=
  { invariantStronger := h.invariantIff.mpr
    portsSubset       := h.portEquiv.forward }

/-- Substitutable は推移的。 -/
theorem Substitutable.trans {a b c : PartDef}
    (hab : Substitutable a b) (hbc : Substitutable b c) :
    Substitutable a c :=
  { invariantStronger := fun hc => hab.invariantStronger (hbc.invariantStronger hc)
    portsSubset := fun p hp => by
      obtain ⟨q, hq, hfq, hdq⟩ := hab.portsSubset p hp
      obtain ⟨r, hr, hfr, hdr⟩ := hbc.portsSubset q hq
      exact ⟨r, hr, hfq.trans hfr, hdq.trans hdr⟩ }

-- ============================================================
-- §4  Transport（設計空間での移行）
-- ============================================================

/-- 等価なコンポーネントの置換は不変条件を保存する。
    HoTT の transport: (A = B) → P(A) → P(B) の MBSE 版。 -/
theorem transport_wellFormed
    (sys : System) (a b : PartDef)
    (hmem : a ∈ sys.parts)
    (hequiv : ComponentEquiv a b) :
    (∀ p ∈ sys.parts, p.invariant) → b.invariant := by
  intro hall
  exact hequiv.invariantIff.mp (hall a hmem)

end VerifiedMBSE.Equivalence
