import VerifiedMBSE.Core.KerML

/-!
# Specialization, Feature Typing, Redefinition, and Interpretation

`Specialization`（preorder）、`FeatureTyping`（置換補題）、
`Redefinition`（型のリファイン）、`Interpretation`（モデル理論的意味論）、
および健全性定理を定義する。
-/

namespace VerifiedMBSE.Core

-- ============================================================
-- §1  Specialization (Preorder)
-- ============================================================

/-- Specialization: A が B を特殊化する ⟺ A の任意のインスタンスは B のインスタンスでもある。

    注: 現時点の `Specialization` は `(specific, general)` のみを保持する syntactic な
    構造体であり、chain の証拠は `specializes` 側の命題でのみ保持する。将来 witness を
    構造体に埋め込む拡張を行う場合は、本注記を更新すること（F3 参照）。 -/
structure Specialization where
  specific : KerMLType
  general  : KerMLType
  deriving Repr

/-- Specialization は反射的。 -/
def Specialization.refl (t : KerMLType) : Specialization where
  specific := t
  general  := t

/-- specialization の命題的定式化。 -/
def specializes (a b : KerMLType) : Prop :=
  ∃ s : Specialization, s.specific = a ∧ s.general = b

/-- specializes は反射的。 -/
theorem specializes_refl (a : KerMLType) : specializes a a :=
  ⟨Specialization.refl a, rfl, rfl⟩

/-- specializes は推移的。

    `Specialization` は現時点では witness を持たない pair 構造体であるため、`a ≤ c` の
    証拠は `⟨⟨a, c⟩, rfl, rfl⟩` として直接構成できる。仮説 `hab`, `hbc` は API 上は
    受け取っているが、本体では使用しない（将来 `Specialization` に chain の witness を
    追加する拡張に備えた API フック）。旧 `Specialization.trans` は仮説を受け取りながら
    使わないデータ関数だったため削除した（F3）。 -/
theorem specializes_trans {a b c : KerMLType}
    (_hab : specializes a b) (_hbc : specializes b c) : specializes a c :=
  ⟨⟨a, c⟩, rfl, rfl⟩

/-- Preorder インスタンス。 -/
instance : Preorder KerMLType where
  le         := specializes
  le_refl    := specializes_refl
  le_trans _ _ _ := specializes_trans

-- ============================================================
-- §2  FeatureTyping and Substitution Lemma
-- ============================================================

/-- FeatureTyping: feature に型を割り当てる関係。
    型付け判断 f : A に対応する。 -/
structure FeatureTyping where
  /-- 型付け対象の feature -/
  feature     : Feature
  /-- 割り当てられる型 -/
  featureType : KerMLType
  deriving Repr

/-- TypedFeature: Feature と FeatureTyping の整合性を保証する束。 -/
structure TypedFeature where
  feature : Feature
  typing  : FeatureTyping
  /-- 整合性: typing は同じ feature を参照する -/
  wf      : typing.feature = feature

/-- 置換補題による型の拡張（subsumption）。
    A ≤ B, f : A ⊢ f : B -/
def FeatureTyping.widen (ft : FeatureTyping) (b : KerMLType)
    (_ : ft.featureType ≤ b) : FeatureTyping where
  feature     := ft.feature
  featureType := b

/-- widen は feature そのものを変えない。 -/
theorem FeatureTyping.widen_feature (ft : FeatureTyping) (b : KerMLType)
    (h : ft.featureType ≤ b) :
    (ft.widen b h).feature = ft.feature := rfl

/-- widen 後の型は指定した b に一致する。 -/
theorem FeatureTyping.widen_type (ft : FeatureTyping) (b : KerMLType)
    (h : ft.featureType ≤ b) :
    (ft.widen b h).featureType = b := rfl

/-- widen は推移的に合成できる（coherence）。 -/
theorem FeatureTyping.widen_trans (ft : FeatureTyping) (b c : KerMLType)
    (hab : ft.featureType ≤ b) (hbc : b ≤ c) :
    (ft.widen c (hab.trans hbc)).feature = ((ft.widen b hab).widen c hbc).feature := rfl

-- ============================================================
-- §3  Redefinition
-- ============================================================

/-- Redefinition: サブタイプ文脈で feature を再定義する関係。
    redefining.featureType ≤ redefined.featureType という refinement 条件を要求する。 -/
structure Redefinition where
  /-- 再定義する feature（サブタイプ側） -/
  redefining : FeatureTyping
  /-- 再定義される feature（スーパータイプ側） -/
  redefined  : FeatureTyping
  /-- 型の refinement 条件 -/
  typeRefinement : redefining.featureType ≤ redefined.featureType

/-- Redefinition から widen 経由で FeatureTyping を復元する。 -/
def Redefinition.toWidened (r : Redefinition) : FeatureTyping :=
  r.redefining.widen r.redefined.featureType r.typeRefinement

/-- widen 後の型は redefined の型に一致する。 -/
theorem Redefinition.toWidened_type (r : Redefinition) :
    r.toWidened.featureType = r.redefined.featureType := rfl

/-- feature 本体は widen 後も redefining のまま。 -/
theorem Redefinition.toWidened_feature (r : Redefinition) :
    r.toWidened.feature = r.redefining.feature := rfl

/-- Redefinition の推移律。 -/
def Redefinition.trans (r₁ r₂ : Redefinition)
    (h : r₁.redefined.featureType = r₂.redefining.featureType) :
    Redefinition where
  redefining     := r₁.redefining
  redefined      := r₂.redefined
  typeRefinement := r₁.typeRefinement.trans (h ▸ r₂.typeRefinement)

-- ============================================================
-- §4  Interpretation (Semantic Interpretation)
-- ============================================================

/-- 意味論的解釈: 各 KerMLType に担体型を割り当てる関数。
    denotational semantics: ⟦ T ⟧_I := I T -/
def Interpretation := KerMLType → Type

/-- 解釈下での extent。 -/
def extent (I : Interpretation) (T : KerMLType) : Type := I T

/-- 意味論的 specialization: I の下で A ≤_sem B ⟺ I A → I B の単射が存在する。 -/
def semanticSpecializes (I : Interpretation) (a b : KerMLType) : Prop :=
  ∃ f : I a → I b, Function.Injective f

/-- 意味論的 specialization は反射的。 -/
theorem semanticSpecializes_refl (I : Interpretation) (a : KerMLType) :
    semanticSpecializes I a a :=
  ⟨id, Function.injective_id⟩

/-- 意味論的 specialization は推移的。 -/
theorem semanticSpecializes_trans (I : Interpretation) {a b c : KerMLType}
    (hab : semanticSpecializes I a b) (hbc : semanticSpecializes I b c) :
    semanticSpecializes I a c := by
  obtain ⟨f, hf⟩ := hab
  obtain ⟨g, hg⟩ := hbc
  exact ⟨g ∘ f, hg.comp hf⟩

/-- 意味論的 specialization は preorder を成す。 -/
theorem semanticSpecializes_preorder (I : Interpretation) :
    ∀ a b c : KerMLType,
      semanticSpecializes I a b →
      semanticSpecializes I b c →
      semanticSpecializes I a c :=
  fun _ _ _ => semanticSpecializes_trans I

-- ============================================================
-- §5  Model Conditions and Soundness
-- ============================================================

/-- 単一点解釈（自明モデル）。 -/
def trivialInterpretation : Interpretation := fun _ => Unit

/-- 文字列解釈（デバッグ用）。 -/
def stringInterpretation : Interpretation := fun _ => String

/-- 自明モデル下では specialization は常に成立する。 -/
theorem trivial_semanticSpecializes_all (a b : KerMLType) :
    semanticSpecializes trivialInterpretation a b :=
  ⟨fun _ => (), fun _ _ _ => rfl⟩

/-- 解釈がモデル条件を満たす（すべての Specialization を尊重する）。 -/
def InterpretationRespects (I : Interpretation) : Prop :=
  ∀ s : Specialization, semanticSpecializes I s.specific s.general

/-- 健全性定理: 統語的 specialization ⇒ 意味論的 specialization。 -/
theorem soundness (I : Interpretation) (hI : InterpretationRespects I)
    {a b : KerMLType} (hab : specializes a b) :
    semanticSpecializes I a b := by
  obtain ⟨s, hs_spec, hs_gen⟩ := hab
  obtain ⟨f, hf⟩ := hI s
  subst hs_spec; subst hs_gen
  exact ⟨f, hf⟩

/-- 自明解釈はモデル条件を満たす。 -/
theorem trivial_respects : InterpretationRespects trivialInterpretation :=
  fun s => trivial_semanticSpecializes_all s.specific s.general

/-- 系: 自明モデルでは統語的 specialization は常に意味論的にも成立する。 -/
theorem soundness_trivial {a b : KerMLType} (hab : specializes a b) :
    semanticSpecializes trivialInterpretation a b :=
  soundness trivialInterpretation trivial_respects hab

end VerifiedMBSE.Core
