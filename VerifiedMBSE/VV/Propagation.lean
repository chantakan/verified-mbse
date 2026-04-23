import VerifiedMBSE.VV.Evidence

/-!
# Inter-Layer V&V Propagation

Defines `Layer.supports` (an inclusion relation between layers) and
`LayerPropagation` (transitive propagation of V&V results from a lower
layer to an upper layer).

## Depth-based `supports`

`Layer.supports l1 l2` is defined as `l1.depth > l2.depth`:

```
Layer.supports l1 l2 ⟺ l1.depth > l2.depth
```

A single depth comparison gives the relation uniformly across all
eight layers. `supports_trans` and `supports_irrefl` are proved once
via the corresponding properties of `Nat.lt`, with no per-layer case
analysis.
-/

namespace VerifiedMBSE.VV

-- ============================================================
-- §1  Layer Inclusion Relation (depth-based)
-- ============================================================

/-- Layer inclusion: a lower layer "supports" an upper layer.

    Defined by depth comparison: when `l1.depth > l2.depth`, `l1` is
    lower (more decomposed) and supports the V&V of the upper layer
    `l2`. -/
def Layer.supports (l1 l2 : Layer) : Prop :=
  l1.depth > l2.depth

/-- `supports` is decidable via `Nat.lt`. -/
instance (l1 l2 : Layer) : Decidable (Layer.supports l1 l2) :=
  Nat.decLt l2.depth l1.depth

/-- `supports` is transitive, inherited from `Nat.lt`. -/
theorem Layer.supports_trans {l1 l2 l3 : Layer}
    (h12 : Layer.supports l1 l2) (h23 : Layer.supports l2 l3) :
    Layer.supports l1 l3 := by
  -- supports := depth の > 比較 (= < の flip)。明示的に unfold して Nat.lt_trans に渡す。
  -- h12 : l2.depth < l1.depth, h23 : l3.depth < l2.depth から l3.depth < l1.depth。
  unfold Layer.supports at h12 h23 ⊢
  exact Nat.lt_trans h23 h12

/-- `supports` is irreflexive, inherited from `Nat.lt`. -/
theorem Layer.supports_irrefl (l : Layer) : ¬ Layer.supports l l := by
  -- ¬ (l.depth > l.depth) = ¬ (l.depth < l.depth) = Nat.lt_irrefl
  unfold Layer.supports
  exact Nat.lt_irrefl l.depth

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
