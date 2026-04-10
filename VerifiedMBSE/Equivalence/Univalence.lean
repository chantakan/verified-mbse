import VerifiedMBSE.Equivalence.ComponentEquiv

/-!
# Formalization of the Univalence Axiom

Formalizes the HoTT univalence axiom `(A ≃ B) ≃ (A = B)` in the MBSE design space.

Since Lean 4 is not a cubical type theory, full univalence does not hold intrinsically.
Instead, we use a **setoid quotient** to construct the design space `DesignSpace`
as `PartDef / ComponentEquiv`. On this quotient type, the following hold:

- **Sound** (ua): `ComponentEquiv a b → ⟦a⟧ = ⟦b⟧`
- **Complete** (ua⁻¹): `⟦a⟧ = ⟦b⟧ → ComponentEquiv a b`
- **Transport**: `⟦a⟧ = ⟦b⟧ → P ⟦a⟧ → P ⟦b⟧`
- **Path induction**: Induction on the quotient type
- **Fiber**: Lifting of design space points

## References
- HoTT Book §2.10 (Universes and the univalence axiom)
- Setoid model of HoTT (Altenkirch, Boulier, Kaposi, Tabareau 2019)
-/

namespace VerifiedMBSE.Equivalence

open VerifiedMBSE.Core

-- ============================================================
-- §1  Setoid 構造
-- ============================================================

/-- ComponentEquiv は同値関係であることの証明。 -/
theorem componentEquiv_equivalence : Equivalence ComponentEquiv :=
  { refl  := ComponentEquiv.refl
    symm  := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂ }

/-- PartDef 上の Setoid インスタンス。
    ComponentEquiv を等価性関係として用いる。 -/
instance componentSetoid : Setoid PartDef :=
  ⟨ComponentEquiv, componentEquiv_equivalence⟩

-- ============================================================
-- §2  DesignSpace（設計空間 = 商型）
-- ============================================================

/-- DesignSpace: PartDef を ComponentEquiv で割った商型。
    HoTT の universe `U` に対応。等しい要素は互いに代替可能。 -/
def DesignSpace : Type := Quotient componentSetoid

/-- PartDef から DesignSpace への埋め込み。 -/
def DesignSpace.mk (pd : PartDef) : DesignSpace :=
  Quotient.mk componentSetoid pd

/-- 表記: ⟦pd⟧ で DesignSpace.mk pd を表す。 -/
scoped notation "⟦" pd "⟧" => DesignSpace.mk pd

-- ============================================================
-- §3  Univalence（Sound + Complete）
-- ============================================================

/-- ua (Univalence axiom, sound direction):
    ComponentEquiv a b → ⟦a⟧ = ⟦b⟧。
    Setoid quotient では Quotient.sound として自動的に成立する。 -/
theorem ua {a b : PartDef} (h : ComponentEquiv a b) : ⟦a⟧ = ⟦b⟧ :=
  Quotient.sound h

/-- ua_inv (Univalence axiom, complete direction):
    ⟦a⟧ = ⟦b⟧ → ComponentEquiv a b。
    Quotient.exact により成立。 -/
theorem ua_inv {a b : PartDef} (h : ⟦a⟧ = ⟦b⟧) : ComponentEquiv a b :=
  Quotient.exact h

/-- ua と ua_inv は互いに逆写像。
    これが (ComponentEquiv a b) ≃ (⟦a⟧ = ⟦b⟧) の同値性を与える。 -/
theorem ua_iff {a b : PartDef} : ComponentEquiv a b ↔ ⟦a⟧ = ⟦b⟧ :=
  ⟨ua, ua_inv⟩

-- ============================================================
-- §4  Transport（パスに沿った輸送）
-- ============================================================

/-- transport: DesignSpace 上の述語を等号に沿って輸送する。
    HoTT の transport : (p : a = b) → P a → P b の MBSE 版。 -/
theorem transport {P : DesignSpace → Prop}
    {a b : PartDef} (h : ComponentEquiv a b) :
    P ⟦a⟧ → P ⟦b⟧ :=
  ua h ▸ id

/-- transport_symm: 逆方向の輸送。 -/
theorem transport_symm {P : DesignSpace → Prop}
    {a b : PartDef} (h : ComponentEquiv a b) :
    P ⟦b⟧ → P ⟦a⟧ :=
  transport h.symm

/-- transport_refl: 反射的等価性での輸送は恒等写像。 -/
theorem transport_refl {P : DesignSpace → Prop}
    (a : PartDef) (pa : P ⟦a⟧) :
    transport (ComponentEquiv.refl a) pa = pa := by
  simp

-- ============================================================
-- §5  Lift（商型への関数持ち上げ）
-- ============================================================

/-- DesignSpace 上の述語を定義するための lift。
    ComponentEquiv を尊重する述語のみ持ち上げ可能。 -/
def DesignSpace.liftProp (P : PartDef → Prop)
    (resp : ∀ a b : PartDef, ComponentEquiv a b → (P a ↔ P b)) :
    DesignSpace → Prop :=
  Quotient.lift P (fun a b hab => propext (resp a b hab))

/-- liftProp は元の述語と整合する。 -/
theorem DesignSpace.liftProp_mk (P : PartDef → Prop)
    (resp : ∀ a b : PartDef, ComponentEquiv a b → (P a ↔ P b))
    (pd : PartDef) :
    DesignSpace.liftProp P resp ⟦pd⟧ = P pd :=
  rfl

/-- DesignSpace 上の Bool 値関数の lift。 -/
def DesignSpace.liftBool (f : PartDef → Bool)
    (resp : ∀ a b : PartDef, ComponentEquiv a b → f a = f b) :
    DesignSpace → Bool :=
  Quotient.lift f resp

-- ============================================================
-- §6  Path Induction（帰納法原理）
-- ============================================================

/-- DesignSpace 上の帰納法（∀ 量化）。
    HoTT の path induction の MBSE 版。 -/
theorem DesignSpace.ind {P : DesignSpace → Prop}
    (h : ∀ pd : PartDef, P ⟦pd⟧) :
    ∀ d : DesignSpace, P d :=
  Quotient.ind h

/-- DesignSpace 上の二項帰納法。 -/
theorem DesignSpace.ind₂ {P : DesignSpace → DesignSpace → Prop}
    (h : ∀ a b : PartDef, P ⟦a⟧ ⟦b⟧) :
    ∀ d₁ d₂ : DesignSpace, P d₁ d₂ :=
  Quotient.ind (fun a => Quotient.ind (fun b => h a b))

-- ============================================================
-- §7  Fiber（ファイバー）
-- ============================================================

/-- Fiber: 設計空間の点 d の上のファイバー。
    d に等価な全ての具体的 PartDef の集合。
    HoTT の homotopy fiber fib(f, b) = Σ(a:A). f(a) = b。 -/
def Fiber (d : DesignSpace) : Type :=
  { pd : PartDef // ⟦pd⟧ = d }

/-- 各ファイバーは非空（全ての DesignSpace の点は代表元を持つ）。 -/
theorem fiber_nonempty (d : DesignSpace) : Nonempty (Fiber d) :=
  Quotient.inductionOn d (fun pd => ⟨⟨pd, rfl⟩⟩)

/-- ファイバーの任意の2要素は ComponentEquiv。 -/
theorem fiber_equiv {d : DesignSpace}
    (x y : Fiber d) : ComponentEquiv x.val y.val := by
  have hx := x.property
  have hy := y.property
  exact ua_inv (hx.trans hy.symm)

-- ============================================================
-- §8  Groupoid 構造
-- ============================================================

/-- ComponentEquiv は groupoid 構造を持つ（strict category で morphism が invertible）。
    refl = id, trans = comp, symm = inv。 -/
theorem groupoid_left_id {a b : PartDef} (h : ComponentEquiv a b) :
    (ComponentEquiv.refl a).trans h = h := by
  cases h; rfl

theorem groupoid_right_id {a b : PartDef} (h : ComponentEquiv a b) :
    h.trans (ComponentEquiv.refl b) = h := by
  cases h; rfl

theorem groupoid_left_inv {a b : PartDef} (h : ComponentEquiv a b) :
    h.symm.trans h = ComponentEquiv.refl b := by
  cases h; rfl

theorem groupoid_right_inv {a b : PartDef} (h : ComponentEquiv a b) :
    h.trans h.symm = ComponentEquiv.refl a := by
  cases h; rfl

-- ============================================================
-- §9  System レベルの Univalence
-- ============================================================

/-- システム内のコンポーネントを等価なものに置換しても
    設計空間での表現は変わらない。 -/
theorem system_component_ua
    {a b : PartDef} (h : ComponentEquiv a b)
    (f : DesignSpace → Prop) :
    f ⟦a⟧ ↔ f ⟦b⟧ := by
  constructor
  · exact transport h
  · exact transport_symm h

/-- 不変条件は設計空間上で well-defined（ComponentEquiv を尊重）。 -/
theorem invariant_respects_equiv {a b : PartDef}
    (h : ComponentEquiv a b) :
    a.invariant ↔ b.invariant :=
  h.invariantIff

/-- 不変条件の DesignSpace への持ち上げ。 -/
def designInvariant : DesignSpace → Prop :=
  DesignSpace.liftProp
    (fun pd => pd.invariant)
    (fun _ _ h => h.invariantIff)

/-- designInvariant は元の invariant と整合。 -/
theorem designInvariant_mk (pd : PartDef) :
    designInvariant ⟦pd⟧ = pd.invariant :=
  rfl

end VerifiedMBSE.Equivalence
