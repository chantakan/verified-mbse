import VerifiedMBSE.Core.KerML

/-!
# 特殊化・型付け・再定義・意味論的解釈

Specialization（前順序）、FeatureTyping（代入補題）、Redefinition（型の細化）、
Interpretation（モデル理論的意味論）、および健全性定理を定義する。
-/

namespace VerifiedMBSE.Core

-- ============================================================
-- §1  Specialization（前順序）
-- ============================================================

/-- Specialization: A は B の特殊化 ⟺ A のインスタンスは全て B のインスタンス。 -/
structure Specialization where
  specific : KerMLType
  general  : KerMLType
  deriving Repr

/-- Specialization は反射的。 -/
def Specialization.refl (t : KerMLType) : Specialization where
  specific := t
  general  := t

/-- Specialization は推移的。 -/
def Specialization.trans (s₁ s₂ : Specialization)
    (_h : s₁.general = s₂.specific) : Specialization where
  specific := s₁.specific
  general  := s₂.general

/-- 命題としての特殊化関係。 -/
def specializes (a b : KerMLType) : Prop :=
  ∃ s : Specialization, s.specific = a ∧ s.general = b

/-- specializes は反射的。 -/
theorem specializes_refl (a : KerMLType) : specializes a a :=
  ⟨Specialization.refl a, rfl, rfl⟩

/-- specializes は推移的。 -/
theorem specializes_trans {a b c : KerMLType}
    (hab : specializes a b) (hbc : specializes b c) : specializes a c := by
  obtain ⟨s₁, hs₁s, hs₁g⟩ := hab
  obtain ⟨s₂, hs₂s, hs₂g⟩ := hbc
  exact ⟨Specialization.trans s₁ s₂ (hs₁g.trans hs₂s.symm), hs₁s, hs₂g⟩

/-- Preorder インスタンス。 -/
instance : Preorder KerMLType where
  le         := specializes
  le_refl    := specializes_refl
  le_trans _ _ _ := specializes_trans

-- ============================================================
-- §2  FeatureTyping と代入補題
-- ============================================================

/-- FeatureTyping: フィーチャーに型を割り当てる関係。
    型判断 f : A に対応。 -/
structure FeatureTyping where
  /-- 型付けされるフィーチャー -/
  feature     : Feature
  /-- 割り当てられる型 -/
  featureType : KerMLType
  deriving Repr

/-- TypedFeature: Feature と FeatureTyping の整合性を保証するバンドル。 -/
structure TypedFeature where
  feature : Feature
  typing  : FeatureTyping
  /-- 整合性：typing が同じ feature を参照すること -/
  wf      : typing.feature = feature

/-- 代入補題（Subsumption）による型の拡大（widening）。
    A ≤ B, f : A ⊢ f : B -/
def FeatureTyping.widen (ft : FeatureTyping) (b : KerMLType)
    (_ : ft.featureType ≤ b) : FeatureTyping where
  feature     := ft.feature
  featureType := b

/-- widening はフィーチャー自体を変えない。 -/
theorem FeatureTyping.widen_feature (ft : FeatureTyping) (b : KerMLType)
    (h : ft.featureType ≤ b) :
    (ft.widen b h).feature = ft.feature := rfl

/-- widening の結果の型は指定した b になる。 -/
theorem FeatureTyping.widen_type (ft : FeatureTyping) (b : KerMLType)
    (h : ft.featureType ≤ b) :
    (ft.widen b h).featureType = b := rfl

/-- widening は推移的（coherence）。 -/
theorem FeatureTyping.widen_trans (ft : FeatureTyping) (b c : KerMLType)
    (hab : ft.featureType ≤ b) (hbc : b ≤ c) :
    (ft.widen c (hab.trans hbc)).feature = ((ft.widen b hab).widen c hbc).feature := rfl

-- ============================================================
-- §3  Redefinition（再定義）
-- ============================================================

/-- Redefinition: サブタイプのコンテキストでフィーチャーを再定義する関係。
    型の細化条件 redefining.featureType ≤ redefined.featureType を要求。 -/
structure Redefinition where
  /-- 再定義するフィーチャー（サブタイプ側） -/
  redefining : FeatureTyping
  /-- 再定義されるフィーチャー（スーパータイプ側） -/
  redefined  : FeatureTyping
  /-- 型の細化条件 -/
  typeRefinement : redefining.featureType ≤ redefined.featureType

/-- Redefinition から widen による FeatureTyping を復元する。 -/
def Redefinition.toWidened (r : Redefinition) : FeatureTyping :=
  r.redefining.widen r.redefined.featureType r.typeRefinement

/-- widen 後の型は redefined の型と一致する。 -/
theorem Redefinition.toWidened_type (r : Redefinition) :
    r.toWidened.featureType = r.redefined.featureType := rfl

/-- widen 後もフィーチャー本体は redefining のまま。 -/
theorem Redefinition.toWidened_feature (r : Redefinition) :
    r.toWidened.feature = r.redefining.feature := rfl

/-- Redefinition の推移性。 -/
def Redefinition.trans (r₁ r₂ : Redefinition)
    (h : r₁.redefined.featureType = r₂.redefining.featureType) :
    Redefinition where
  redefining     := r₁.redefining
  redefined      := r₂.redefined
  typeRefinement := r₁.typeRefinement.trans (h ▸ r₂.typeRefinement)

-- ============================================================
-- §4  Interpretation（意味論的解釈）
-- ============================================================

/-- 意味論的解釈：各 KerMLType にキャリア型を割り当てる関数。
    denotational semantics: ⟦ T ⟧_I := I T -/
def Interpretation := KerMLType → Type

/-- 解釈のもとでの外延（extent）。 -/
def extent (I : Interpretation) (T : KerMLType) : Type := I T

/-- 意味論的特殊化：I のもとで A ≤_sem B ⟺ I A → I B の単射が存在。 -/
def semanticSpecializes (I : Interpretation) (a b : KerMLType) : Prop :=
  ∃ f : I a → I b, Function.Injective f

/-- 意味論的特殊化は反射的。 -/
theorem semanticSpecializes_refl (I : Interpretation) (a : KerMLType) :
    semanticSpecializes I a a :=
  ⟨id, Function.injective_id⟩

/-- 意味論的特殊化は推移的。 -/
theorem semanticSpecializes_trans (I : Interpretation) {a b c : KerMLType}
    (hab : semanticSpecializes I a b) (hbc : semanticSpecializes I b c) :
    semanticSpecializes I a c := by
  obtain ⟨f, hf⟩ := hab
  obtain ⟨g, hg⟩ := hbc
  exact ⟨g ∘ f, hg.comp hf⟩

/-- 意味論的特殊化は前順序をなす。 -/
theorem semanticSpecializes_preorder (I : Interpretation) :
    ∀ a b c : KerMLType,
      semanticSpecializes I a b →
      semanticSpecializes I b c →
      semanticSpecializes I a c :=
  fun _ _ _ => semanticSpecializes_trans I

-- ============================================================
-- §5  モデル条件と健全性
-- ============================================================

/-- 単元素解釈（trivial model）。 -/
def trivialInterpretation : Interpretation := fun _ => Unit

/-- 文字列解釈（デバッグ向け）。 -/
def stringInterpretation : Interpretation := fun _ => String

/-- trivial モデルでは特殊化は常に成立。 -/
theorem trivial_semanticSpecializes_all (a b : KerMLType) :
    semanticSpecializes trivialInterpretation a b :=
  ⟨fun _ => (), fun _ _ _ => rfl⟩

/-- 解釈がモデル条件を満たす（全 Specialization を尊重する）。 -/
def InterpretationRespects (I : Interpretation) : Prop :=
  ∀ s : Specialization, semanticSpecializes I s.specific s.general

/-- 健全性定理：構文的特殊化 → 意味論的特殊化。 -/
theorem soundness (I : Interpretation) (hI : InterpretationRespects I)
    {a b : KerMLType} (hab : specializes a b) :
    semanticSpecializes I a b := by
  obtain ⟨s, hs_spec, hs_gen⟩ := hab
  obtain ⟨f, hf⟩ := hI s
  subst hs_spec; subst hs_gen
  exact ⟨f, hf⟩

/-- trivial 解釈はモデル条件を満たす。 -/
theorem trivial_respects : InterpretationRespects trivialInterpretation :=
  fun s => trivial_semanticSpecializes_all s.specific s.general

/-- 健全性の系：trivial モデルでは構文的特殊化は常に意味論的に成立。 -/
theorem soundness_trivial {a b : KerMLType} (hab : specializes a b) :
    semanticSpecializes trivialInterpretation a b :=
  soundness trivialInterpretation trivial_respects hab

end VerifiedMBSE.Core
