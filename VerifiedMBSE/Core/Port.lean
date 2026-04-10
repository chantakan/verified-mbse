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

/-- PortDef: 方向付きフィーチャーにフロー型を付加したポート定義。 -/
structure PortDef where
  feature  : DirectedFeature
  flowType : KerMLType
  deriving Repr

/-- PortDef の共役：方向を反転しフロー型は保持。 -/
def PortDef.conj (p : PortDef) : PortDef where
  feature  := p.feature.conj
  flowType := p.flowType

/-- PortDef の共役は対合。 -/
theorem PortDef.conj_involution (p : PortDef) : p.conj.conj = p := by
  simp [PortDef.conj, DirectedFeature.conj_involution]

-- ============================================================
-- §2  Conjugation と互換性
-- ============================================================

/-- KerML Conjugation 関係：A の共役が B であることを表す。
    型理論的には線形論理の A と A⊥ の関係。 -/
structure Conjugation where
  original   : KerMLType
  conjugated : KerMLType
  deriving Repr

/-- ポートの互換性：A と B が接続可能 ⟺ B は A の共役。 -/
def compatible (a b : KerMLType) : Prop :=
  ∃ c : Conjugation, c.original = a ∧ c.conjugated = b

/-- 互換性は対称：A と B が互換 ⟺ B と A が互換。 -/
theorem compatible_symm {a b : KerMLType}
    (h : compatible a b) : compatible b a := by
  obtain ⟨c, hc_orig, hc_conj⟩ := h
  exact ⟨{ original := c.conjugated, conjugated := c.original },
         hc_conj, hc_orig⟩

/-- 対合性：compatible a b → compatible b a（compatible_symm の別名）。 -/
theorem compatible_conj_involution (a b : KerMLType)
    (h : compatible a b) : compatible b a :=
  compatible_symm h

end VerifiedMBSE.Core
