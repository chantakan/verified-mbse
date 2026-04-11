import VerifiedMBSE.Core.Component

/-!
# HoTT-Inspired Component Equivalence

Defines `PortEquiv` (port interface equivalence), `ComponentEquiv` (component equivalence),
`Substitutable` (substitutability), and `transport_wellFormed` (design-space transport).

## Correspondence with HoTT
- Equivalence (A ≃ B) → `ComponentEquiv`
- Univalence (A ≃ B → A = B) → Substitutability principle
- Transport → `transport_wellFormed`
-/

namespace VerifiedMBSE.Equivalence

open VerifiedMBSE.Core

-- ============================================================
-- §1  Interface Equivalence
-- ============================================================

/-- PortCompatible: two ports are compatible (flowType and direction match). -/
def PortCompatible (p q : PortDef) : Prop :=
  p.flowType = q.flowType ∧ p.feature.direction = q.feature.direction

/-- PortEquiv: two port lists are structurally equivalent.
    In HoTT terms, PortBundle(A) ≃ PortBundle(B). -/
structure PortEquiv (ports₁ ports₂ : List PortDef) : Prop where
  /-- Port counts match -/
  length_eq : ports₁.length = ports₂.length
  /-- Forward compatible mapping ports₁ → ports₂ -/
  forward : ∀ p ∈ ports₁, ∃ q ∈ ports₂, PortCompatible p q
  /-- Backward compatible mapping ports₂ → ports₁ -/
  backward : ∀ q ∈ ports₂, ∃ p ∈ ports₁, PortCompatible q p

/-- PortEquiv is reflexive. -/
theorem PortEquiv.refl (ports : List PortDef) : PortEquiv ports ports :=
  { length_eq := rfl
    forward   := fun p hp => ⟨p, hp, rfl, rfl⟩
    backward  := fun p hp => ⟨p, hp, rfl, rfl⟩ }

/-- PortEquiv is symmetric. -/
theorem PortEquiv.symm {p₁ p₂ : List PortDef}
    (h : PortEquiv p₁ p₂) : PortEquiv p₂ p₁ :=
  { length_eq := h.length_eq.symm
    forward   := h.backward
    backward  := h.forward }

/-- PortEquiv is transitive. -/
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
-- §2  Component Equivalence
-- ============================================================

/-- ComponentEquiv: two PartDefs are equivalent.
    Port interfaces are equivalent and invariants are biconditional. -/
structure ComponentEquiv (a b : PartDef) : Prop where
  /-- Port interface equivalence -/
  portEquiv : PortEquiv a.ports b.ports
  /-- Invariant biconditional -/
  invariantIff : a.invariant ↔ b.invariant

/-- ComponentEquiv is reflexive. -/
theorem ComponentEquiv.refl (pd : PartDef) : ComponentEquiv pd pd :=
  { portEquiv := PortEquiv.refl pd.ports, invariantIff := Iff.rfl }

/-- ComponentEquiv is symmetric. -/
theorem ComponentEquiv.symm {a b : PartDef}
    (h : ComponentEquiv a b) : ComponentEquiv b a :=
  { portEquiv := h.portEquiv.symm, invariantIff := h.invariantIff.symm }

/-- ComponentEquiv is transitive. -/
theorem ComponentEquiv.trans {a b c : PartDef}
    (hab : ComponentEquiv a b) (hbc : ComponentEquiv b c) :
    ComponentEquiv a c :=
  { portEquiv := hab.portEquiv.trans hbc.portEquiv
    invariantIff := hab.invariantIff.trans hbc.invariantIff }

-- ============================================================
-- §3  Substitutability
-- ============================================================

/-- Substitutable: A can substitute for B (upward compatible).
    A weaker condition than ComponentEquiv. -/
structure Substitutable (a b : PartDef) : Prop where
  /-- b's invariant implies a's invariant -/
  invariantStronger : b.invariant → a.invariant
  /-- All ports of a exist in b -/
  portsSubset : ∀ p ∈ a.ports, ∃ q ∈ b.ports, PortCompatible p q

/-- ComponentEquiv → Substitutable (special case of bidirectional equivalence). -/
theorem ComponentEquiv.toSubstitutable {a b : PartDef}
    (h : ComponentEquiv a b) : Substitutable a b :=
  { invariantStronger := h.invariantIff.mpr
    portsSubset       := h.portEquiv.forward }

/-- Substitutable is transitive. -/
theorem Substitutable.trans {a b c : PartDef}
    (hab : Substitutable a b) (hbc : Substitutable b c) :
    Substitutable a c :=
  { invariantStronger := fun hc => hab.invariantStronger (hbc.invariantStronger hc)
    portsSubset := fun p hp => by
      obtain ⟨q, hq, hfq, hdq⟩ := hab.portsSubset p hp
      obtain ⟨r, hr, hfr, hdr⟩ := hbc.portsSubset q hq
      exact ⟨r, hr, hfq.trans hfr, hdq.trans hdr⟩ }

-- ============================================================
-- §4  Transport (Design Space Migration)
-- ============================================================

/-- Replacing a component with an equivalent one preserves invariants.
    MBSE version of HoTT transport: (A = B) → P(A) → P(B). -/
theorem transport_wellFormed
    (sys : System) (a b : PartDef)
    (hmem : a ∈ sys.parts)
    (hequiv : ComponentEquiv a b) :
    (∀ p ∈ sys.parts, p.invariant) → b.invariant := by
  intro hall
  exact hequiv.invariantIff.mp (hall a hmem)

end VerifiedMBSE.Equivalence
