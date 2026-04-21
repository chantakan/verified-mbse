import VerifiedMBSE
import Examples.Spacecraft.Satellite

/-!
# F3 + F5 + F6 受入条件テスト

Phase 1 スプリント（F3/F5/F6）の受入条件を機械的に検証するサニティテスト。

## F3: `Specialization.trans` 未使用仮説の除去

データ版 `Specialization.trans` は削除済み。命題版 `specializes_trans` のみ
残っており、`Preorder KerMLType` インスタンスの `le_trans` として使われる。
本節では `specializes` が Preorder として正しく機能することを確認する。

## F5: ECSS-E-ST-10C 準拠の 8 階層化

`Layer` が 8 階層 (mission/system/segment/subsystem/assembly/unit/component/part)
になり、`depth : Layer → Nat` で順序付けされた。`supports` 関係は depth の
`>` 比較で統一され、以前の 3 階層の pattern match から一般化された。

- 旧 3 階層 (`.system`, `.subsystem`, `.component`) は constructor 名不変で後方互換
- depth ベースの supports が旧 3 階層の判定を保持する
- 新階層 (`.mission`, `.segment`, `.assembly`, `.unit`, `.part`) でも推移律が成立

## F6: `ModelBoundary` の VMatrix 型紐付け

`ModelBoundary (vm : VMatrix)` に依存型化され、`verifiedCount` は
`vm.totalRecords` から関数で自動導出される。型レベルで紐付けを確認する。
-/

namespace Examples.Spacecraft.F3F5F6Tests

open VerifiedMBSE.Core
open VerifiedMBSE.VV
open VerifiedMBSE.Matrix
open Examples.Spacecraft.Satellite

-- ============================================================
-- §1  F3: `specializes_trans` と Preorder
-- ============================================================

/-- `specializes_trans` が直接呼び出せる（データ版 `Specialization.trans` は削除済み）。 -/
example (a b c : KerMLType)
    (hab : specializes a b) (hbc : specializes b c) :
    specializes a c :=
  specializes_trans hab hbc

/-- `Preorder KerMLType` の `le_trans` も同じ関数を呼ぶ。 -/
example (a b c : KerMLType)
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  le_trans hab hbc

/-- `specializes_refl` も Preorder の `le_refl` と一致する。 -/
example (a : KerMLType) : a ≤ a := le_refl a

-- ============================================================
-- §2  F5: Layer 8 階層化の確認
-- ============================================================

/-- 新規 5 階層が存在し、`depth` が期待通りに割り当てられている. -/
example : Layer.mission.depth = 0 := rfl
example : Layer.system.depth = 1 := rfl
example : Layer.segment.depth = 2 := rfl
example : Layer.subsystem.depth = 3 := rfl
example : Layer.assembly.depth = 4 := rfl
example : Layer.unit.depth = 5 := rfl
example : Layer.component.depth = 6 := rfl
example : Layer.part.depth = 7 := rfl

/-- DecidableEq があることの確認（pattern match / `==` / `decide` で機能）. -/
example : (Layer.system == Layer.system) = true := rfl
example : (Layer.system == Layer.subsystem) = false := rfl
example : (Layer.mission == Layer.part) = false := rfl

-- ============================================================
-- §3  F5: `supports` が depth ベースで一般化されている
-- ============================================================

/-- 旧 3 階層の supports 判定は保持される（`by decide` で判定可能）. -/
example : Layer.supports .component .subsystem := by decide
example : Layer.supports .subsystem .system    := by decide
example : Layer.supports .component .system    := by decide

/-- 新階層間でも supports が成立する. -/
example : Layer.supports .part .assembly    := by decide
example : Layer.supports .unit .segment     := by decide
example : Layer.supports .subsystem .mission := by decide

/-- 逆向きは成立しない（上層が下層を supports することはない）. -/
example : ¬ Layer.supports .system .component := by decide
example : ¬ Layer.supports .mission .subsystem := by decide

/-- 同層は supports しない（反反射性）. -/
example : ¬ Layer.supports .subsystem .subsystem :=
  Layer.supports_irrefl .subsystem

example : ¬ Layer.supports .assembly .assembly :=
  Layer.supports_irrefl .assembly

/-- 推移律: part < unit < segment で part supports segment. -/
example : Layer.supports .part .segment :=
  Layer.supports_trans
    (show Layer.supports .part .unit    by decide)
    (show Layer.supports .unit .segment by decide)

/-- 推移律: 7 段連鎖 part → mission も成立する（depth ベースなので
    ケース爆発なし）. -/
example : Layer.supports .part .mission := by decide

-- ============================================================
-- §4  F5: `supports` が Decidable
-- ============================================================

/-- Decidable instance により `decide` で判定できる. -/
example : Layer.supports .component .system := by decide

example : ¬ Layer.supports .system .component := by decide

/-- Decidable なので if-then-else でも使える. -/
example :
    (if Layer.supports .part .mission then 1 else 0) = 1 := by decide

-- ============================================================
-- §5  F6: `ModelBoundary` の VMatrix 型紐付け
-- ============================================================

/-- `satelliteModelBoundary` は `ModelBoundary satelliteVMatrix` 型として構築される
    （型レベル紐付け）. -/
example : ModelBoundary satelliteVMatrix := satelliteModelBoundary

/-- `verifiedCount` は `satelliteVMatrix.totalRecords` から自動導出される。
    手動同期不要。 -/
example :
    satelliteModelBoundary.verifiedCount = satelliteVMatrix.totalRecords := rfl

/-- `totalItems` = verified + nonFormal + unmodeled（定義通り）. -/
example :
    satelliteModelBoundary.totalItems =
      satelliteModelBoundary.verifiedCount +
      satelliteModelBoundary.nonFormalCount +
      satelliteModelBoundary.unmodeledCount := rfl

/-- 既存の health check (Satellite.lean §7) と整合する. -/
example : satelliteModelBoundary.totalItems = 30 :=
  satelliteModelBoundary_totalItems

/-- 型レベル紐付けの核: 異なる VMatrix に対する ModelBoundary は別の型を持ち、
    その違いを型システムで検出できる。以下は `satelliteVMatrix` 専用と
    わかるデモ。 -/
def satelliteModelBoundary_selfId :
    ModelBoundary satelliteVMatrix → ModelBoundary satelliteVMatrix :=
  id

example : satelliteModelBoundary_selfId satelliteModelBoundary = satelliteModelBoundary := rfl

end Examples.Spacecraft.F3F5F6Tests
