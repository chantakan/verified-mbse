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

end Examples.Spacecraft.Satellite
