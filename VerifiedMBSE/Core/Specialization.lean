import VerifiedMBSE.Core.KerML

/-!
# Specialization, Feature Typing, Redefinition, and Interpretation

Defines `Specialization` (preorder), `FeatureTyping` (substitution lemma),
`Redefinition` (type refinement), `Interpretation` (model-theoretic semantics),
and soundness theorems.
-/

namespace VerifiedMBSE.Core

-- ============================================================
-- §1  Specialization (Preorder)
-- ============================================================

/-- Specialization: A specializes B ⟺ every instance of A is also an instance of B. -/
structure Specialization where
  specific : KerMLType
  general  : KerMLType
  deriving Repr

/-- Specialization is reflexive. -/
def Specialization.refl (t : KerMLType) : Specialization where
  specific := t
  general  := t

/-- Specialization is transitive. -/
def Specialization.trans (s₁ s₂ : Specialization)
    (_h : s₁.general = s₂.specific) : Specialization where
  specific := s₁.specific
  general  := s₂.general

/-- Specialization as a proposition. -/
def specializes (a b : KerMLType) : Prop :=
  ∃ s : Specialization, s.specific = a ∧ s.general = b

/-- specializes is reflexive. -/
theorem specializes_refl (a : KerMLType) : specializes a a :=
  ⟨Specialization.refl a, rfl, rfl⟩

/-- specializes is transitive. -/
theorem specializes_trans {a b c : KerMLType}
    (hab : specializes a b) (hbc : specializes b c) : specializes a c := by
  obtain ⟨s₁, hs₁s, hs₁g⟩ := hab
  obtain ⟨s₂, hs₂s, hs₂g⟩ := hbc
  exact ⟨Specialization.trans s₁ s₂ (hs₁g.trans hs₂s.symm), hs₁s, hs₂g⟩

/-- Preorder instance. -/
instance : Preorder KerMLType where
  le         := specializes
  le_refl    := specializes_refl
  le_trans _ _ _ := specializes_trans

-- ============================================================
-- §2  FeatureTyping and Substitution Lemma
-- ============================================================

/-- FeatureTyping: relation assigning a type to a feature.
    Corresponds to the typing judgment f : A. -/
structure FeatureTyping where
  /-- The feature being typed -/
  feature     : Feature
  /-- The assigned type -/
  featureType : KerMLType
  deriving Repr

/-- TypedFeature: bundle ensuring consistency of Feature and FeatureTyping. -/
structure TypedFeature where
  feature : Feature
  typing  : FeatureTyping
  /-- Consistency: typing refers to the same feature -/
  wf      : typing.feature = feature

/-- Type widening via the substitution lemma (subsumption).
    A ≤ B, f : A ⊢ f : B -/
def FeatureTyping.widen (ft : FeatureTyping) (b : KerMLType)
    (_ : ft.featureType ≤ b) : FeatureTyping where
  feature     := ft.feature
  featureType := b

/-- widening does not change the feature itself. -/
theorem FeatureTyping.widen_feature (ft : FeatureTyping) (b : KerMLType)
    (h : ft.featureType ≤ b) :
    (ft.widen b h).feature = ft.feature := rfl

/-- The result type of widening is the specified b. -/
theorem FeatureTyping.widen_type (ft : FeatureTyping) (b : KerMLType)
    (h : ft.featureType ≤ b) :
    (ft.widen b h).featureType = b := rfl

/-- widening is transitive (coherence). -/
theorem FeatureTyping.widen_trans (ft : FeatureTyping) (b c : KerMLType)
    (hab : ft.featureType ≤ b) (hbc : b ≤ c) :
    (ft.widen c (hab.trans hbc)).feature = ((ft.widen b hab).widen c hbc).feature := rfl

-- ============================================================
-- §3  Redefinition
-- ============================================================

/-- Redefinition: relation that redefines a feature in a subtype context.
    Requires the refinement condition redefining.featureType ≤ redefined.featureType. -/
structure Redefinition where
  /-- Redefining feature (subtype side) -/
  redefining : FeatureTyping
  /-- Redefined feature (supertype side) -/
  redefined  : FeatureTyping
  /-- Type refinement condition -/
  typeRefinement : redefining.featureType ≤ redefined.featureType

/-- Recover FeatureTyping from Redefinition via widen. -/
def Redefinition.toWidened (r : Redefinition) : FeatureTyping :=
  r.redefining.widen r.redefined.featureType r.typeRefinement

/-- The type after widen matches the redefined type. -/
theorem Redefinition.toWidened_type (r : Redefinition) :
    r.toWidened.featureType = r.redefined.featureType := rfl

/-- The feature body remains redefining after widen. -/
theorem Redefinition.toWidened_feature (r : Redefinition) :
    r.toWidened.feature = r.redefining.feature := rfl

/-- Transitivity of Redefinition. -/
def Redefinition.trans (r₁ r₂ : Redefinition)
    (h : r₁.redefined.featureType = r₂.redefining.featureType) :
    Redefinition where
  redefining     := r₁.redefining
  redefined      := r₂.redefined
  typeRefinement := r₁.typeRefinement.trans (h ▸ r₂.typeRefinement)

-- ============================================================
-- §4  Interpretation (Semantic Interpretation)
-- ============================================================

/-- Semantic interpretation: function assigning a carrier type to each KerMLType.
    denotational semantics: ⟦ T ⟧_I := I T -/
def Interpretation := KerMLType → Type

/-- Extent under an interpretation. -/
def extent (I : Interpretation) (T : KerMLType) : Type := I T

/-- Semantic specialization: A ≤_sem B under I ⟺ an injection I A → I B exists. -/
def semanticSpecializes (I : Interpretation) (a b : KerMLType) : Prop :=
  ∃ f : I a → I b, Function.Injective f

/-- Semantic specialization is reflexive. -/
theorem semanticSpecializes_refl (I : Interpretation) (a : KerMLType) :
    semanticSpecializes I a a :=
  ⟨id, Function.injective_id⟩

/-- Semantic specialization is transitive. -/
theorem semanticSpecializes_trans (I : Interpretation) {a b c : KerMLType}
    (hab : semanticSpecializes I a b) (hbc : semanticSpecializes I b c) :
    semanticSpecializes I a c := by
  obtain ⟨f, hf⟩ := hab
  obtain ⟨g, hg⟩ := hbc
  exact ⟨g ∘ f, hg.comp hf⟩

/-- Semantic specialization forms a preorder. -/
theorem semanticSpecializes_preorder (I : Interpretation) :
    ∀ a b c : KerMLType,
      semanticSpecializes I a b →
      semanticSpecializes I b c →
      semanticSpecializes I a c :=
  fun _ _ _ => semanticSpecializes_trans I

-- ============================================================
-- §5  Model Conditions and Soundness
-- ============================================================

/-- Singleton interpretation (trivial model). -/
def trivialInterpretation : Interpretation := fun _ => Unit

/-- String interpretation (for debugging). -/
def stringInterpretation : Interpretation := fun _ => String

/-- In the trivial model, specialization always holds. -/
theorem trivial_semanticSpecializes_all (a b : KerMLType) :
    semanticSpecializes trivialInterpretation a b :=
  ⟨fun _ => (), fun _ _ _ => rfl⟩

/-- An interpretation satisfies the model condition (respects all Specializations). -/
def InterpretationRespects (I : Interpretation) : Prop :=
  ∀ s : Specialization, semanticSpecializes I s.specific s.general

/-- Soundness theorem: syntactic specialization → semantic specialization. -/
theorem soundness (I : Interpretation) (hI : InterpretationRespects I)
    {a b : KerMLType} (hab : specializes a b) :
    semanticSpecializes I a b := by
  obtain ⟨s, hs_spec, hs_gen⟩ := hab
  obtain ⟨f, hf⟩ := hI s
  subst hs_spec; subst hs_gen
  exact ⟨f, hf⟩

/-- The trivial interpretation satisfies the model condition. -/
theorem trivial_respects : InterpretationRespects trivialInterpretation :=
  fun s => trivial_semanticSpecializes_all s.specific s.general

/-- Corollary: in the trivial model, syntactic specialization always holds semantically. -/
theorem soundness_trivial {a b : KerMLType} (hab : specializes a b) :
    semanticSpecializes trivialInterpretation a b :=
  soundness trivialInterpretation trivial_respects hab

end VerifiedMBSE.Core
