import VerifiedMBSE.VV.Evidence

/-!
# レイヤー間の VV 伝播

Layer.supports（レイヤー間の包含関係）と
LayerPropagation（下位 VV → 上位 VV の推移的伝播）を定義する。
-/

namespace VerifiedMBSE.VV

-- ============================================================
-- §1  レイヤーの包含関係
-- ============================================================

/-- レイヤーの包含関係：下位レイヤーが上位レイヤーを「支える」。 -/
def Layer.supports : Layer → Layer → Prop
  | .component, .subsystem => True
  | .subsystem, .system    => True
  | .component, .system    => True
  | _,          _          => False

/-- supports は推移的。 -/
theorem Layer.supports_trans {l1 l2 l3 : Layer}
    (h12 : Layer.supports l1 l2) (h23 : Layer.supports l2 l3) :
    Layer.supports l1 l3 := by
  cases l1 <;> cases l2 <;> cases l3 <;> simp [Layer.supports] at *

/-- supports は反射的でない。 -/
theorem Layer.supports_irrefl (l : Layer) : ¬ Layer.supports l l := by
  cases l <;> simp [Layer.supports]

-- ============================================================
-- §2  LayerPropagation
-- ============================================================

/-- LayerPropagation: 下位レイヤーの VV が成立すれば上位レイヤーの VV も成立する関係。 -/
structure LayerPropagation where
  lower_layer : Layer
  upper_layer : Layer
  supports    : Layer.supports lower_layer upper_layer
  lower_prop  : Prop
  upper_prop  : Prop
  propagates  : lower_prop → upper_prop

/-- 推移的伝播の合成。 -/
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
-- §3  確信度伝播
-- ============================================================

/-- 全 VVRecord の validation が trusted なら currentLevel = 1.0。 -/
theorem trusted_gives_full_confidence (r : VVRecord)
    (h : r.validation.current = .trusted r.verified) :
    r.validation.currentLevel = 1.0 := by
  simp [ValidationTrace.currentLevel, h, ValidationEvidence.confidenceLevel]

end VerifiedMBSE.VV
