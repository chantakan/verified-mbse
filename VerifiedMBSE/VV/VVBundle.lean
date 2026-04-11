import VerifiedMBSE.VV.SubSystemSpec

/-!
# SubSystemVVBundle: Automated VVRecord Construction

Defines `mkComponentRecord` and `SubSystemVVBundle`, which batch-construct
`VVRecord`s from a `SubSystemSpec`.
-/

namespace VerifiedMBSE.VV

open VerifiedMBSE.Core

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
-- §2  SubSystemVVBundle
-- ============================================================

/-- SubSystemVVBundle: bundle of VVRecords constructed from a SubSystemSpec. -/
structure SubSystemVVBundle
    {S D : Type} {inv : S → D → Prop}
    (spec : SubSystemSpec S D inv) where
  /-- List of component-level VVRecords -/
  componentRecords : List VVRecord
  /-- Additional system-level VVRecords (e.g. power budget) -/
  extraSystemRecords : List VVRecord := []

/-- Get all VVRecords. -/
def SubSystemVVBundle.allRecords
    {S D : Type} {inv : S → D → Prop}
    {spec : SubSystemSpec S D inv}
    (bundle : SubSystemVVBundle spec) :
    List VVRecord :=
  bundle.componentRecords
    ++ [spec.subsystemRecord]
    ++ [spec.safetyRecord, spec.recoveryRecord]
    ++ bundle.extraSystemRecords

/-- Theorem on VVRecord count. -/
theorem SubSystemVVBundle.allRecords_length
    {S D : Type} {inv : S → D → Prop}
    {spec : SubSystemSpec S D inv}
    (bundle : SubSystemVVBundle spec) :
    bundle.allRecords.length =
    bundle.componentRecords.length + 3 + bundle.extraSystemRecords.length := by
  simp [SubSystemVVBundle.allRecords, List.length_append]
  omega

end VerifiedMBSE.VV
