import Examples.Spacecraft.EPS
import Examples.Spacecraft.AOCS
import Examples.Spacecraft.TCS
import Examples.Spacecraft.TTC

/-!
# Satellite: 4 サブシステムから V 字行列を構成し完全性を証明する
-/

open VerifiedMBSE.Core
open VerifiedMBSE.Behavior
open VerifiedMBSE.VV
open VerifiedMBSE.Matrix
open Examples.Spacecraft.EPS
open Examples.Spacecraft.AOCS
open Examples.Spacecraft.TCS
open Examples.Spacecraft.TTC

namespace Examples.Spacecraft.Satellite

-- ============================================================
-- §1  VColumn の構成
-- ============================================================

def epsColumn : VColumn :=
  { subsystem := "EPS", records := epsVVBundle.allRecords }

def aocsColumn : VColumn :=
  { subsystem := "AOCS", records := aocsVVBundle.allRecords }

def tcsColumn : VColumn :=
  { subsystem := "TCS", records := tcsVVBundle.allRecords }

def ttcColumn : VColumn :=
  { subsystem := "TTC", records := ttcVVBundle.allRecords }

-- ============================================================
-- §2  VMatrix
-- ============================================================

/-- 衛星の V 字行列: 4 サブシステム -/
def satelliteVMatrix : VMatrix :=
  { columns := [epsColumn, aocsColumn, tcsColumn, ttcColumn] }

-- ============================================================
-- §3  性質の検証
-- ============================================================

/-- 全カラムが全レイヤーをカバー -/
theorem epsColumn_allLayers : epsColumn.allLayersCovered = true := by native_decide
theorem aocsColumn_allLayers : aocsColumn.allLayersCovered = true := by native_decide
theorem tcsColumn_allLayers : tcsColumn.allLayersCovered = true := by native_decide
theorem ttcColumn_allLayers : ttcColumn.allLayersCovered = true := by native_decide

/-- レコード総数 = 25 -/
theorem satelliteVMatrix_totalRecords :
    satelliteVMatrix.totalRecords = 25 := by native_decide

/-- 全レコードが trusted -/
theorem satelliteVMatrix_fullyTrusted :
    satelliteVMatrix.fullyTrusted = true := by native_decide

-- ============================================================
-- §4  完全性の証明
-- ============================================================

/-- サブシステム完全性 -/
theorem satelliteVMatrix_SubSystemComplete :
    satelliteVMatrix.SubSystemComplete ["EPS", "AOCS", "TCS", "TTC"] := by
  unfold VMatrix.SubSystemComplete
  intro s hs
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact ⟨epsColumn, by simp [satelliteVMatrix], rfl⟩
  · exact ⟨aocsColumn, by simp [satelliteVMatrix], rfl⟩
  · exact ⟨tcsColumn, by simp [satelliteVMatrix], rfl⟩
  · exact ⟨ttcColumn, by simp [satelliteVMatrix], rfl⟩

/-- V 字行列の完全性: サブシステム完全 ∧ 全カラムがレイヤー完全 -/
theorem satelliteVMatrix_Complete :
    satelliteVMatrix.Complete ["EPS", "AOCS", "TCS", "TTC"] := by
  constructor
  · exact satelliteVMatrix_SubSystemComplete
  · intro col hcol
    simp [satelliteVMatrix] at hcol
    rcases hcol with rfl | rfl | rfl | rfl <;>
      refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ============================================================
-- §5  Contract-Based Integration
-- ============================================================

-- EPS-AOCS power contract: EPS guarantees a bounded supply, AOCS assumes it.
-- This is the integration story that is invisible at the subsystem level
-- and becomes a type-level obligation at the system level.

/-- EPS guarantees max 100W consumption on its own bus. -/
def epsGuarantee : Prop := epsModePowerSpec.maxPower ≤ 100

/-- AOCS assumes that its peak consumption (200W) is compatible with the
    allocated bus share. The environment must provide 200W for AOCS. -/
def aocsAssume : Prop := aocsModePowerSpec.maxPower ≤ 200

/-- Contract for EPS: under a nominal bus load assumption, EPS bounds its own
    consumption. -/
def epsContract : Contract :=
  { name      := "EPS power bound"
    assume    := True
    guarantee := epsGuarantee
    valid     := fun _ => by unfold epsGuarantee; decide }

/-- Contract for AOCS: under the bus allocation assumption, AOCS stays within
    its peak consumption envelope. -/
def aocsContract : Contract :=
  { name      := "AOCS power envelope"
    assume    := True
    guarantee := aocsAssume
    valid     := fun _ => by unfold aocsAssume; decide }

/-- Coupling constraint: combined EPS+AOCS peak fits the 500W bus budget.
    This property is not expressible at the subsystem level — it requires
    joint knowledge of both maxPower values. -/
def satelliteBusBudget : CouplingConstraint :=
  { name     := "EPS + AOCS peak ≤ 500W"
    involved := ["EPS", "AOCS"]
    property := epsModePowerSpec.maxPower + aocsModePowerSpec.maxPower ≤ 500
    evidence := by decide }

/-- The satellite modeled as a ContractedSystem. Every contract assumption is
    discharged here; missing any would be a type error. -/
def satelliteContractedSystem : ContractedSystem :=
  { contracts  := [epsContract, aocsContract]
    couplings  := [satelliteBusBudget]
    discharged := by
      intro c hc
      simp [epsContract, aocsContract] at hc
      rcases hc with rfl | rfl <;> trivial }

/-- Integration guarantees: both contract guarantees hold. -/
theorem satellite_integration_guarantees :
    ∀ c ∈ satelliteContractedSystem.contracts, c.guarantee :=
  satelliteContractedSystem.guarantees_hold

-- ============================================================
-- §6  Model Boundary
-- ============================================================

/-- 試験・解析で裏付けられた非形式性質。 -/
def satelliteNonFormalProperties : List NonFormalProperty := [
  { description := "Solar panel efficiency at end-of-life (EOL)"
    kind        := .analyzed
    source      := "Radiation degradation analysis report R-2026-01" },
  { description := "Reaction wheel friction at cold temperatures"
    kind        := .tested
    source      := "Qualification test campaign QT-AOCS-03" }
]

/-- 意図的に形式化しない残留リスク。 -/
def satelliteUnmodeledRisks : List UnmodeledRisk := [
  { description := "Single Event Upset (SEU) in non-redundant memory"
    category    := .physical
    rationale   := "Radiation environment modeling is outside the scope of structural V&V"
    mitigation  := "EDAC memory, periodic scrubbing, watchdog reset" },
  { description := "Operator command sequencing error from ground"
    category    := .human
    rationale   := "Operator behavior is not formalized"
    mitigation  := "Two-person rule, command simulator, uplink authentication" },
  { description := "Third-party firmware in COTS star tracker"
    category    := .software
    rationale   := "Vendor firmware is unavailable for formal analysis"
    mitigation  := "Vendor qualification, plausibility checks on tracker output" }
]

/-- 衛星のモデル境界。F6 により `ModelBoundary satelliteVMatrix` に依存型化
    されたため、他システム用の境界記述を誤って流用するとここで型エラーになる。
    `verifiedCount` は `satelliteVMatrix.totalRecords` から自動導出されるので
    手動同期は不要。 -/
def satelliteModelBoundary : ModelBoundary satelliteVMatrix :=
  { systemName := "Satellite"
    nonFormal  := satelliteNonFormalProperties
    unmodeled  := satelliteUnmodeledRisks }

/-- 健全性: 25 verified + 2 non-formal + 3 unmodeled = 30 tracked items. -/
theorem satelliteModelBoundary_totalItems :
    satelliteModelBoundary.totalItems = 30 := by native_decide

end Examples.Spacecraft.Satellite
