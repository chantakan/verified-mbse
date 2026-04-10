import VerifiedMBSE.VV.SubSystemSpec

/-!
# SubSystemVVBundle: VVRecord バンドルの自動構成

mkComponentRecord と SubSystemVVBundle を定義し、
SubSystemSpec から VVRecord を一括構成する。
-/

namespace VerifiedMBSE.VV

open VerifiedMBSE.Core

-- ============================================================
-- §1  コンポーネントレベル VVRecord
-- ============================================================

/-- コンポーネントレベルの VVRecord を構成するヘルパー。 -/
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
-- §2  SubSystemVVBundle
-- ============================================================

/-- SubSystemVVBundle: SubSystemSpec から構成される VVRecord の束。 -/
structure SubSystemVVBundle
    {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv) where
  /-- コンポーネントレベルの VVRecord リスト -/
  componentRecords : List VVRecord
  /-- 追加のシステムレベル VVRecord（電力バジェット等） -/
  extraSystemRecords : List VVRecord := []

/-- 全 VVRecord を取得。 -/
def SubSystemVVBundle.allRecords
    {S D : Type} {inv : S → D → Prop}
    {spec : SubSystemSpec S D inv}
    (bundle : SubSystemVVBundle spec) :
    List VVRecord :=
  bundle.componentRecords
    ++ [spec.subsystemRecord]
    ++ [spec.safetyRecord, spec.recoveryRecord]
    ++ bundle.extraSystemRecords

/-- VVRecord 数の定理。 -/
theorem SubSystemVVBundle.allRecords_length
    {S D : Type} {inv : S → D → Prop}
    {spec : SubSystemSpec S D inv}
    (bundle : SubSystemVVBundle spec) :
    bundle.allRecords.length =
    bundle.componentRecords.length + 3 + bundle.extraSystemRecords.length := by
  simp [SubSystemVVBundle.allRecords, List.length_append]
  omega

end VerifiedMBSE.VV
