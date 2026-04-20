import VerifiedMBSE.VV.SubSystemSpec

/-!
# SubSystemVVBundle: Automated VVRecord Construction

Defines `mkComponentRecord` and `SubSystemVVBundle`, which batch-construct
`VVRecord`s from a `SubSystemSpec`.

## B-7: Kripke 一般化

`SubSystemSpec` の Kripke 一般化に伴い、`SubSystemVVBundle` もその型引数を
`x : α` ベースに一般化した。StateMachine 版も ProductStateMachine 版も同じ
`SubSystemVVBundle` 型で扱える。
-/

namespace VerifiedMBSE.VV

open VerifiedMBSE.Core
open VerifiedMBSE.Behavior

-- ============================================================
-- §1  Component-Level VVRecord
-- ============================================================

/-- Helper to construct a component-level VVRecord. -/
def mkComponentRecord
    (subsysName : String) (idx : Nat)
    (pd : PartDef) (proof : pd.invariant) :
    VVRecord :=
  let partName := match pd.baseType.name with
    | some n => n
    | none   => "Anonymous"
  { layer        := .component
    spec_name    := s!"{subsysName}-C{idx}-{partName}-Invariant"
    verification := pd.invariant
    verified     := proof
    validation   := ValidationTrace.init (.trusted proof) }

-- ============================================================
-- §2  SubSystemVVBundle (Kripke-Generalized)
-- ============================================================

/-- SubSystemVVBundle: bundle of VVRecords constructed from a SubSystemSpec.

    B-7 で `SubSystemSpec` が Kripke 一般化されたため、本構造の implicit
    型引数も `{α : Type} {S D : Type} [ToKripke α S D] {x : α}` に変更された。
    StateMachine 版・ProductStateMachine 版の両方に対応する。 -/
structure SubSystemVVBundle
    {α : Type} {S D : Type} [ToKripke α S D]
    {x : α} (spec : SubSystemSpec x) where
  /-- List of component-level VVRecords -/
  componentRecords : List VVRecord
  /-- Additional system-level VVRecords (e.g. power budget) -/
  extraSystemRecords : List VVRecord := []

/-- Get all VVRecords. -/
def SubSystemVVBundle.allRecords
    {α : Type} {S D : Type} [ToKripke α S D]
    {x : α} {spec : SubSystemSpec x}
    (bundle : SubSystemVVBundle spec) :
    List VVRecord :=
  bundle.componentRecords
    ++ [spec.subsystemRecord]
    ++ [spec.safetyRecord, spec.recoveryRecord]
    ++ bundle.extraSystemRecords

/-- Theorem on VVRecord count. -/
theorem SubSystemVVBundle.allRecords_length
    {α : Type} {S D : Type} [ToKripke α S D]
    {x : α} {spec : SubSystemSpec x}
    (bundle : SubSystemVVBundle spec) :
    bundle.allRecords.length =
    bundle.componentRecords.length + 3 + bundle.extraSystemRecords.length := by
  simp [SubSystemVVBundle.allRecords, List.length_append]
  omega

end VerifiedMBSE.VV
