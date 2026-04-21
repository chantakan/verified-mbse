import VerifiedMBSE.VV.Evidence

/-!
# Inter-Layer V&V Propagation (F5 generalized)

`Layer.supports` (inclusion relation between layers) と
`LayerPropagation` (transitive propagation from lower-layer V&V to upper-layer V&V)
を定義する。

## F5 での一般化

旧版は 3 階層 (`.component` / `.subsystem` / `.system`) の pattern match で
`supports` を定義していたため、新しい階層（`.assembly`, `.unit`, `.part` 等）を
追加するたびにケースを増やす必要があった。

F5 で `Layer` が `depth` を持つようになったため、`supports` を

```
Layer.supports l1 l2 ⟺ l1.depth > l2.depth
```

という depth 比較ベースに一般化した。これにより 8 階層すべてに対して
`supports` / `supports_trans` / `supports_irrefl` が **同一の証明で成立** する。

後方互換: 旧コードが期待する `supports .component .system` などの判定結果は
そのまま成立する（`.component.depth = 6 > 1 = .system.depth`）。
-/

namespace VerifiedMBSE.VV

-- ============================================================
-- §1  Layer Inclusion Relation (depth-based)
-- ============================================================

/-- Layer inclusion: a lower layer 'supports' an upper layer.

    depth ベースで判定: l1 の depth が l2 より大きければ l1 は下層
    （分解が進んだ側）であり、上層 l2 の V&V を支える。 -/
def Layer.supports (l1 l2 : Layer) : Prop :=
  l1.depth > l2.depth

/-- `supports` は `Nat.lt` 経由で決定可能 (Bool 化できる)。 -/
instance (l1 l2 : Layer) : Decidable (Layer.supports l1 l2) :=
  Nat.decLt l2.depth l1.depth

/-- supports は推移的 (Nat.lt の推移性から直接導出)。 -/
theorem Layer.supports_trans {l1 l2 l3 : Layer}
    (h12 : Layer.supports l1 l2) (h23 : Layer.supports l2 l3) :
    Layer.supports l1 l3 := by
  -- supports := depth の > 比較 (= < の flip)。明示的に unfold して Nat.lt_trans に渡す。
  -- h12 : l2.depth < l1.depth, h23 : l3.depth < l2.depth から l3.depth < l1.depth。
  unfold Layer.supports at h12 h23 ⊢
  exact Nat.lt_trans h23 h12

/-- supports は反反射的 (Nat.lt の反反射性から直接導出)。 -/
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
