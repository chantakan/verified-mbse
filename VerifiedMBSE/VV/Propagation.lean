import VerifiedMBSE.VV.Evidence

/-!
# Inter-Layer V&V Propagation

Defines `Layer.supports` (inclusion relation between layers) and
`LayerPropagation` (transitive propagation from lower-layer V&V to upper-layer V&V).
-/

namespace VerifiedMBSE.VV

-- ============================================================
-- §1  Layer Inclusion Relation
-- ============================================================

/-- Layer inclusion: a lower layer 'supports' an upper layer. -/
def Layer.supports : Layer → Layer → Prop
  | .component, .subsystem => True
  | .subsystem, .system    => True
  | .component, .system    => True
  | _,          _          => False

/-- supports is transitive. -/
theorem Layer.supports_trans {l1 l2 l3 : Layer}
    (h12 : Layer.supports l1 l2) (h23 : Layer.supports l2 l3) :
    Layer.supports l1 l3 := by
  cases l1 <;> cases l2 <;> cases l3 <;> simp [Layer.supports] at *

/-- supports is irreflexive. -/
theorem Layer.supports_irrefl (l : Layer) : ¬ Layer.supports l l := by
  cases l <;> simp [Layer.supports]

-- ============================================================
-- §2  LayerPropagation
-- ============================================================

/-- LayerPropagation: relation where lower-layer V&V implies upper-layer V&V. -/
structure LayerPropagation where
  lower_layer : Layer
  upper_layer : Layer
  supports    : Layer.supports lower_layer upper_layer
  lower_prop  : Prop
  upper_prop  : Prop
  propagates  : lower_prop → upper_prop

/-- Composition of transitive propagation. -/
def LayerPropagation.compose
    (lp1 : LayerPropagation) (lp2 : LayerPropagation)
    (hchain : lp1.upper_prop → lp2.lower_prop)
    (hsup : Layer.supports lp1.lower_layer lp2.upper_layer) :
    LayerPropagation :=
  { lower_layer := lp1.lower_layer
    upper_layer := lp2.upper_layer
    supports    := hsup
    lower_prop  := lp1.lower_prop
    upper_prop  := lp2.upper_prop
    propagates  := fun h => lp2.propagates (hchain (lp1.propagates h)) }

-- ============================================================
-- §3  Confidence Propagation
-- ============================================================

/-- If all VVRecord validations are trusted, then currentLevel = 1.0. -/
theorem trusted_gives_full_confidence (r : VVRecord)
    (h : r.validation.current = .trusted r.verified) :
    r.validation.currentLevel = 1.0 := by
  simp [ValidationTrace.currentLevel, h, ValidationEvidence.confidenceLevel]

end VerifiedMBSE.VV
