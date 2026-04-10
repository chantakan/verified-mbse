import VerifiedMBSE.Core.Component
import VerifiedMBSE.Core.Specialization

/-!
# PartDef Semantics and ConnectorSemantic

Defines interpretation-based extent of `PartDef`, `PartInstance` (dependent record),
`semanticSpecializes` at the `PartDef` level, and categorical laws for
`ConnectorSemantic` (associativity, identity).
-/

namespace VerifiedMBSE.Core

-- ============================================================
-- §1  PartInstance と extent
-- ============================================================

/-- PortInstance: 解釈 I のもとでのポートのインスタンス型。 -/
def PortInstance (I : Interpretation) (p : PortDef) : Type := I p.flowType

/-- PartInstance: 解釈 I のもとでの PartDef のインスタンス。
    キャリア値と不変条件の証明を持つ依存レコード。 -/
structure PartInstance (I : Interpretation) (pd : PartDef) where
  carrier   : I pd.baseType
  inv_holds : pd.invariant

/-- PartDef の外延：PartInstance の型。 -/
def PartDef.extent (I : Interpretation) (pd : PartDef) : Type := PartInstance I pd

-- ============================================================
-- §2  PartDef レベルの semanticSpecializes
-- ============================================================

/-- PartDef レベルの意味論的特殊化。 -/
def PartDef.semanticSpecializes (I : Interpretation) (pdA pdB : PartDef) : Prop :=
  ∃ f : PartDef.extent I pdA → PartDef.extent I pdB, Function.Injective f

/-- PartDef.semanticSpecializes は反射的。 -/
theorem PartDef.semanticSpecializes_refl (I : Interpretation) (pd : PartDef) :
    PartDef.semanticSpecializes I pd pd :=
  ⟨id, Function.injective_id⟩

/-- PartDef.semanticSpecializes は推移的。 -/
theorem PartDef.semanticSpecializes_trans
    (I : Interpretation) {pdA pdB pdC : PartDef}
    (hAB : PartDef.semanticSpecializes I pdA pdB)
    (hBC : PartDef.semanticSpecializes I pdB pdC) :
    PartDef.semanticSpecializes I pdA pdC := by
  obtain ⟨f, hf⟩ := hAB; obtain ⟨g, hg⟩ := hBC
  exact ⟨g ∘ f, hg.comp hf⟩

/-- 不変条件の継承関係。 -/
def InvariantInheritance (pdA pdB : PartDef) : Prop := pdA.invariant → pdB.invariant

/-- baseType の semanticSpecializes と InvariantInheritance から
    PartDef レベルの semanticSpecializes を導出する。 -/
theorem PartDef.semanticSpecializes_from_base
    (I : Interpretation) (pdA pdB : PartDef)
    (hBase : VerifiedMBSE.Core.semanticSpecializes I pdA.baseType pdB.baseType)
    (hInv  : InvariantInheritance pdA pdB) :
    PartDef.semanticSpecializes I pdA pdB := by
  obtain ⟨f, hf⟩ := hBase
  refine ⟨fun inst => { carrier := f inst.carrier, inv_holds := hInv inst.inv_holds }, ?_⟩
  intro inst₁ inst₂ h
  obtain ⟨c₁, inv₁⟩ := inst₁; obtain ⟨c₂, inv₂⟩ := inst₂
  have hcarrier : f c₁ = f c₂ := congrArg PartInstance.carrier h
  have heq : c₁ = c₂ := hf hcarrier
  subst heq; simp

/-- PartDef レベルの健全性定理。 -/
theorem partDef_soundness
    (I : Interpretation) (hI : InterpretationRespects I)
    (pdA pdB : PartDef)
    (hSyn : specializes pdA.baseType pdB.baseType)
    (hInv : InvariantInheritance pdA pdB) :
    PartDef.semanticSpecializes I pdA pdB :=
  PartDef.semanticSpecializes_from_base I pdA pdB
    (soundness I hI hSyn) hInv

-- ============================================================
-- §3  ConnectorSemantic
-- ============================================================

/-- ConnectorSemantic: コネクタの意味論（値転送関数の型）。 -/
def ConnectorSemantic (I : Interpretation) (c : Connector) : Type :=
  I c.source.port.flowType → I c.target.port.flowType

/-- 直列合成可能性条件。 -/
def Connector.Composable (c1 c2 : Connector) : Prop :=
  c1.target.port.flowType = c2.source.port.flowType

/-- ConnectorSemantic の直列合成。 -/
def ConnectorSemantic.compose
    (I : Interpretation) (c1 c2 : Connector)
    (h : Connector.Composable c1 c2)
    (f1 : ConnectorSemantic I c1)
    (f2 : ConnectorSemantic I c2) :
    I c1.source.port.flowType → I c2.target.port.flowType :=
  fun v => f2 (h ▸ f1 v)

/-- 恒等 ConnectorSemantic（source と target の flowType が等しい場合）。 -/
def ConnectorSemantic.id_of_eq
    (I : Interpretation) (c : Connector)
    (h : c.source.port.flowType = c.target.port.flowType) :
    ConnectorSemantic I c :=
  fun v => h ▸ v

-- ============================================================
-- §4  圏論的性質
-- ============================================================

/-- ConnectorSemantic の結合性。 -/
theorem ConnectorSemantic.compose_assoc
    (I : Interpretation) (c1 c2 c3 : Connector)
    (h12 : Connector.Composable c1 c2)
    (h23 : Connector.Composable c2 c3)
    (f1 : ConnectorSemantic I c1)
    (f2 : ConnectorSemantic I c2)
    (f3 : ConnectorSemantic I c3)
    (v : I c1.source.port.flowType) :
    f3 (h23 ▸ ConnectorSemantic.compose I c1 c2 h12 f1 f2 v) =
    ConnectorSemantic.compose I c2 c3 h23 f2 f3 (h12 ▸ f1 v) := by
  simp [ConnectorSemantic.compose]

/-- 2回の transport と trans の等価性。 -/
private theorem eq_transport_trans
    {α : Type} {P : α → Type}
    {a b c : α} (h1 : a = b) (h2 : b = c) (x : P a) :
    h2 ▸ h1 ▸ x = h1.trans h2 ▸ x := by
  cases h1; rfl

/-- ConnectorSemantic の右単位元律。 -/
theorem ConnectorSemantic.compose_id_right
    (I : Interpretation) (c1 c2 : Connector)
    (h12 : Connector.Composable c1 c2)
    (heq : c2.source.port.flowType = c2.target.port.flowType)
    (f : ConnectorSemantic I c1)
    (v : I c1.source.port.flowType) :
    ConnectorSemantic.compose I c1 c2 h12 f
      (ConnectorSemantic.id_of_eq I c2 heq) v =
    h12.trans heq ▸ f v := by
  simp only [ConnectorSemantic.compose, ConnectorSemantic.id_of_eq]
  exact eq_transport_trans h12 heq (f v)

/-- ConnectorSemantic の左単位元律。 -/
theorem ConnectorSemantic.compose_id_left
    (I : Interpretation) (c1 c2 : Connector)
    (h12 : Connector.Composable c1 c2)
    (heq : c1.source.port.flowType = c1.target.port.flowType)
    (f : ConnectorSemantic I c2)
    (v : I c1.source.port.flowType) :
    ConnectorSemantic.compose I c1 c2 h12
      (ConnectorSemantic.id_of_eq I c1 heq) f v =
    f (heq.trans h12 ▸ v) := by
  simp only [ConnectorSemantic.compose, ConnectorSemantic.id_of_eq]
  congr 1
  exact eq_transport_trans heq h12 v

/-- 単位元律の系：3連結合成の左端が恒等のとき。 -/
theorem ConnectorSemantic.compose_id_left_assoc
    (I : Interpretation) (c1 c2 c3 : Connector)
    (h12 : Connector.Composable c1 c2)
    (h23 : Connector.Composable c2 c3)
    (heq : c1.source.port.flowType = c1.target.port.flowType)
    (f : ConnectorSemantic I c2)
    (g : ConnectorSemantic I c3)
    (v : I c1.source.port.flowType) :
    ConnectorSemantic.compose I c2 c3 h23 f g
      (h12 ▸ ConnectorSemantic.id_of_eq I c1 heq v) =
    ConnectorSemantic.compose I c2 c3 h23 f g (heq.trans h12 ▸ v) := by
  simp only [ConnectorSemantic.id_of_eq]
  congr 1
  exact eq_transport_trans heq h12 v

end VerifiedMBSE.Core
