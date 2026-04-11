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
-- §1  PartInstance and Extent
-- ============================================================

/-- PortInstance: instance type of a port under interpretation I. -/
def PortInstance (I : Interpretation) (p : PortDef) : Type := I p.flowType

/-- PartInstance: instance of a PartDef under interpretation I.
    A dependent record with a carrier value and proof of the invariant. -/
structure PartInstance (I : Interpretation) (pd : PartDef) where
  carrier   : I pd.baseType
  inv_holds : pd.invariant

/-- Extent of a PartDef: the type of PartInstances. -/
def PartDef.extent (I : Interpretation) (pd : PartDef) : Type := PartInstance I pd

-- ============================================================
-- §2  PartDef-Level semanticSpecializes
-- ============================================================

/-- Semantic specialization at the PartDef level. -/
def PartDef.semanticSpecializes (I : Interpretation) (pdA pdB : PartDef) : Prop :=
  ∃ f : PartDef.extent I pdA → PartDef.extent I pdB, Function.Injective f

/-- PartDef.semanticSpecializes is reflexive. -/
theorem PartDef.semanticSpecializes_refl (I : Interpretation) (pd : PartDef) :
    PartDef.semanticSpecializes I pd pd :=
  ⟨id, Function.injective_id⟩

/-- PartDef.semanticSpecializes is transitive. -/
theorem PartDef.semanticSpecializes_trans
    (I : Interpretation) {pdA pdB pdC : PartDef}
    (hAB : PartDef.semanticSpecializes I pdA pdB)
    (hBC : PartDef.semanticSpecializes I pdB pdC) :
    PartDef.semanticSpecializes I pdA pdC := by
  obtain ⟨f, hf⟩ := hAB; obtain ⟨g, hg⟩ := hBC
  exact ⟨g ∘ f, hg.comp hf⟩

/-- Invariant inheritance relation. -/
def InvariantInheritance (pdA pdB : PartDef) : Prop := pdA.invariant → pdB.invariant

/-- Derive PartDef-level semanticSpecializes from
    baseType semanticSpecializes and InvariantInheritance. -/
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

/-- Soundness theorem at the PartDef level. -/
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

/-- ConnectorSemantic: connector semantics (type of value transfer functions). -/
def ConnectorSemantic (I : Interpretation) (c : Connector) : Type :=
  I c.source.port.flowType → I c.target.port.flowType

/-- Serial composability condition. -/
def Connector.Composable (c1 c2 : Connector) : Prop :=
  c1.target.port.flowType = c2.source.port.flowType

/-- Serial composition of ConnectorSemantics. -/
def ConnectorSemantic.compose
    (I : Interpretation) (c1 c2 : Connector)
    (h : Connector.Composable c1 c2)
    (f1 : ConnectorSemantic I c1)
    (f2 : ConnectorSemantic I c2) :
    I c1.source.port.flowType → I c2.target.port.flowType :=
  fun v => f2 (h ▸ f1 v)

/-- Identity ConnectorSemantic (when source and target flowTypes are equal). -/
def ConnectorSemantic.id_of_eq
    (I : Interpretation) (c : Connector)
    (h : c.source.port.flowType = c.target.port.flowType) :
    ConnectorSemantic I c :=
  fun v => h ▸ v

-- ============================================================
-- §4  Categorical Properties
-- ============================================================

/-- Associativity of ConnectorSemantic. -/
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

/-- Equivalence of double transport and trans. -/
private theorem eq_transport_trans
    {α : Type} {P : α → Type}
    {a b c : α} (h1 : a = b) (h2 : b = c) (x : P a) :
    h2 ▸ h1 ▸ x = h1.trans h2 ▸ x := by
  cases h1; rfl

/-- Right identity law of ConnectorSemantic. -/
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

/-- Left identity law of ConnectorSemantic. -/
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

/-- Corollary: when the leftmost connector in a triple composition is identity. -/
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
