import VerifiedMBSE
import Examples.Spacecraft.EPS

/-!
# F1 + F2 受入条件テスト

F1（`ValidationEvidence` をデフォルト引数でパラメータ化）と F2
（`fullyTrusted` の Float 等号依存排除）の受入条件を確認するサニティテスト。

## F1: VVRecord 自動生成の evidence level パラメータ化

`SubSystemSpec.subsystemRecord` / `.safetyRecord` / `.recoveryRecord` は
`ev : ValidationEvidence _ := .trusted _` のデフォルト引数を受け取る形に
なっており、以下の 3 通りの呼び出しが可能:

1. **デフォルト `.trusted`**: `spec.safetyRecord` — 後方互換、既存コード無変更
2. **明示 `.contract`**: `spec.safetyRecord (.contract A h)` — 仮定付き保証
3. **明示 `.confidence`**: `spec.safetyRecord (.confidence 0.7)` — 確率的評価

## F2: fullyTrusted の構造子判別

`VColumn.fullyTrusted` は `ValidationTrace.isTrusted` の inductive 判別を
使用し、Float 等号（`currentLevel == 1.0`）に依存しない。

- 全 `.trusted` レコードの列 → `fullyTrusted = true`
- `.contract` / `.confidence` が混在する列 → `fullyTrusted = false`
- 空列 → `fullyTrusted = true`（`List.all` の空リスト規約）
-/

namespace Examples.Spacecraft.F1F2Tests

open VerifiedMBSE.Core
open VerifiedMBSE.Behavior
open VerifiedMBSE.VV
open VerifiedMBSE.Matrix
open Examples.Spacecraft.EPS

-- ============================================================
-- §1  F1: デフォルト `.trusted` 呼び出し
-- ============================================================

/-- デフォルト引数で safetyRecord を作ると `.trusted` evidence が入る. -/
example : epsSpec.safetyRecord.validation.isTrusted = true := rfl

/-- デフォルト引数で subsystemRecord を作ると `.trusted` evidence が入る. -/
example : epsSpec.subsystemRecord.validation.isTrusted = true := rfl

/-- デフォルト引数で recoveryRecord を作ると `.trusted` evidence が入る. -/
example : epsSpec.recoveryRecord.validation.isTrusted = true := rfl

-- ============================================================
-- §2  F1: 明示 `.contract` 呼び出し
-- ============================================================

/-- `.contract True (fun _ => ...)` で safetyRecord を作れる（仮定付き保証）。
    `True → P` の形で assumption を埋めれば、任意の Prop を仮定に置ける。
    `named argument (ev := ...)` を使うことで期待型からの推論が確実に働く。 -/
def epsSpec_safetyRecord_contract : VVRecord :=
  epsSpec.safetyRecord (ev := .contract True (fun _ => epsSpec.fdir.safety))

/-- `.contract` で作った record は `.trusted` ではない. -/
example : epsSpec_safetyRecord_contract.validation.isTrusted = false := rfl

/-- `.contract` の `currentLevel` は 0.95（Evidence.lean の規約）. -/
example : epsSpec_safetyRecord_contract.validation.currentLevel = 0.95 := rfl

/-- subsystemRecord も `.contract` で作れる. -/
def epsSpec_subsystemRecord_contract : VVRecord :=
  epsSpec.subsystemRecord
    (ev := .contract True (fun _ => epsSpec.structural.wellFormed))

example : epsSpec_subsystemRecord_contract.validation.isTrusted = false := rfl

/-- recoveryRecord も `.contract` で作れる. -/
def epsSpec_recoveryRecord_contract : VVRecord :=
  epsSpec.recoveryRecord
    (ev := .contract True (fun _ => epsSpec.fdir.recovery))

example : epsSpec_recoveryRecord_contract.validation.isTrusted = false := rfl

-- ============================================================
-- §3  F1: 明示 `.confidence` 呼び出し
-- ============================================================

/-- `.confidence 0.7` で safetyRecord を作れる（確率的評価）。 -/
def epsSpec_safetyRecord_confidence : VVRecord :=
  epsSpec.safetyRecord (ev := .confidence 0.7)

example : epsSpec_safetyRecord_confidence.validation.isTrusted = false := rfl

/-- `.confidence` の `currentLevel` は指定値がそのまま返る. -/
example : epsSpec_safetyRecord_confidence.validation.currentLevel = 0.7 := rfl

/-- subsystemRecord も `.confidence` で作れる. -/
def epsSpec_subsystemRecord_confidence : VVRecord :=
  epsSpec.subsystemRecord (ev := .confidence 0.85)

example : epsSpec_subsystemRecord_confidence.validation.isTrusted = false := rfl

-- ============================================================
-- §4  F2: fullyTrusted の判別（mixed-evidence）
-- ============================================================

/-- 全 `.trusted` レコードで構成された列. -/
def allTrustedColumn : VColumn :=
  { subsystem := "EPS"
    records   := [epsSpec.subsystemRecord, epsSpec.safetyRecord, epsSpec.recoveryRecord] }

/-- 全 `.trusted` の列は `fullyTrusted = true`. -/
example : allTrustedColumn.fullyTrusted = true := rfl

/-- `.contract` を含む mixed-evidence の列. -/
def contractMixedColumn : VColumn :=
  { subsystem := "EPS"
    records   := [epsSpec.safetyRecord, epsSpec_safetyRecord_contract] }

/-- mixed-evidence（`.contract` 含む）の列は `fullyTrusted = false`. -/
example : contractMixedColumn.fullyTrusted = false := rfl

/-- `.confidence` を含む mixed-evidence の列. -/
def confidenceMixedColumn : VColumn :=
  { subsystem := "EPS"
    records   := [epsSpec.safetyRecord, epsSpec_safetyRecord_confidence] }

/-- mixed-evidence（`.confidence` 含む）の列は `fullyTrusted = false`. -/
example : confidenceMixedColumn.fullyTrusted = false := rfl

/-- `.contract` と `.confidence` を含む 3 段列. -/
def mixedTripleColumn : VColumn :=
  { subsystem := "EPS"
    records   := [epsSpec.safetyRecord,
                  epsSpec_safetyRecord_contract,
                  epsSpec_safetyRecord_confidence] }

example : mixedTripleColumn.fullyTrusted = false := rfl

/-- `.contract` のみの列は `fullyTrusted = false`. -/
def allContractColumn : VColumn :=
  { subsystem := "EPS"
    records   := [epsSpec_safetyRecord_contract,
                  epsSpec_subsystemRecord_contract,
                  epsSpec_recoveryRecord_contract] }

example : allContractColumn.fullyTrusted = false := rfl

/-- `.confidence` のみの列は `fullyTrusted = false`. -/
def allConfidenceColumn : VColumn :=
  { subsystem := "EPS"
    records   := [epsSpec_safetyRecord_confidence,
                  epsSpec_subsystemRecord_confidence] }

example : allConfidenceColumn.fullyTrusted = false := rfl

/-- 空列は `fullyTrusted = true`（`List.all` の空リスト規約）. -/
def emptyColumn : VColumn :=
  { subsystem := "Empty"
    records   := [] }

example : emptyColumn.fullyTrusted = true := rfl

-- ============================================================
-- §5  F2: Float 等号に依存しないことの原理確認
-- ============================================================

/-- `ValidationEvidence.isTrusted` は `.trusted` のみ true を返す. -/
example : (ValidationEvidence.trusted (show (0 : Nat) = 0 from rfl)).isTrusted = true := rfl

/-- `ValidationEvidence.isTrusted` は `.contract` には false を返す. -/
example : (ValidationEvidence.contract (P := (0 : Nat) = 0) True (fun _ => rfl)).isTrusted = false := rfl

/-- `ValidationEvidence.isTrusted` は `.confidence` には false を返す. -/
example : (ValidationEvidence.confidence (P := (0 : Nat) = 0) 1.0).isTrusted = false := rfl

/-- 重要: 仮に `confidence 1.0` でも `isTrusted = false`。
    これが旧実装 (`currentLevel == 1.0`) との違い。`.confidence 1.0` の Float
    比較は `1.0 == 1.0 = true` なので旧実装では「trusted」と誤判定していたが、
    新実装は**構造子判別**なので `.confidence` である限り必ず false になる. -/
example :
    (ValidationEvidence.confidence (P := (0 : Nat) = 0) 1.0).confidenceLevel = 1.0 ∧
    (ValidationEvidence.confidence (P := (0 : Nat) = 0) 1.0).isTrusted = false := by
  refine ⟨?_, ?_⟩ <;> rfl

end Examples.Spacecraft.F1F2Tests
