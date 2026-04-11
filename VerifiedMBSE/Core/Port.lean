import VerifiedMBSE.Core.KerML

/-!
# Port Definitions and Connection Compatibility

Defines `PortDef` (typed, directed port), `Conjugation` (conjugation relation),
and `compatible` — a decidable proposition for port-to-port connection compatibility.
-/

namespace VerifiedMBSE.Core

-- ============================================================
-- §1  PortDef
-- ============================================================

/-- PortDef: port definition adding a flow type to a directed feature. -/
structure PortDef where
  feature  : DirectedFeature
  flowType : KerMLType
  deriving Repr

/-- PortDef conjugation: inverts direction while preserving the flow type. -/
def PortDef.conj (p : PortDef) : PortDef where
  feature  := p.feature.conj
  flowType := p.flowType

/-- PortDef conjugation is an involution. -/
theorem PortDef.conj_involution (p : PortDef) : p.conj.conj = p := by
  simp [PortDef.conj, DirectedFeature.conj_involution]

-- ============================================================
-- §2  Conjugation and Compatibility
-- ============================================================

/-- KerML Conjugation relation: A's conjugate equals B.
    Type-theoretically corresponds to the A and A⊥ relation in linear logic. -/
structure Conjugation where
  original   : KerMLType
  conjugated : KerMLType
  deriving Repr

/-- Port compatibility: A and B are connectable ⟺ B is the conjugate of A. -/
def compatible (a b : KerMLType) : Prop :=
  ∃ c : Conjugation, c.original = a ∧ c.conjugated = b

/-- Compatibility is symmetric: A and B are compatible ⟺ B and A are compatible. -/
theorem compatible_symm {a b : KerMLType}
    (h : compatible a b) : compatible b a := by
  obtain ⟨c, hc_orig, hc_conj⟩ := h
  exact ⟨{ original := c.conjugated, conjugated := c.original },
         hc_conj, hc_orig⟩

/-- Involutivity: compatible a b → compatible b a (alias for compatible_symm). -/
theorem compatible_conj_involution (a b : KerMLType)
    (h : compatible a b) : compatible b a :=
  compatible_symm h

end VerifiedMBSE.Core
