import VerifiedMBSE
import Examples.Spacecraft.EPS

/-!
# F8 受入条件テスト

`docs/InterpretationPattern.md` の推奨パターンに従って `EPSNatInterpretation` が
リファクタされたことの回帰テスト。

## 確認事項

1. **既存互換**: `EPSNatInterpretation { name := some "PowerSupply" }` などの
   ドメイン内 4 型は、リファクタ前と同じ `Nat` を返す。
2. **EPSTypeTag の網羅性**: `EPSTypeTag` の各 case に対して `.toName` / `.interp`
   が定義され、`fromName` で往復できる（`fromName ∘ toName` が `some` を返す）。
3. **文字列マッチの集約**: 文字列リテラル `"PowerSupply"` 等が `Interpretation`
   の本体に現れず、`EPSTypeTag.toName` / `.fromName` に閉じ込められている。
4. **ドメイン外は `Unit`**: tag に対応しない `KerMLType` は `Unit` を返す。
5. **健全性の機械証明**: `EPSTypeTag` の全 case で Interpretation が正しい型を
   返すことを `cases tag` で機械的に潰せる。
-/

namespace Examples.Spacecraft.F8Tests

open VerifiedMBSE.Core
open VerifiedMBSE.Behavior
open Examples.Spacecraft.EPS

-- ============================================================
-- §1  EPSTypeTag の網羅性と round-trip
-- ============================================================

/-- 各 tag の `toName` が期待通りの文字列を返す. -/
example : EPSTypeTag.powerSupply.toName   = "PowerSupply"  := rfl
example : EPSTypeTag.load.toName          = "Load"         := rfl
example : EPSTypeTag.powerPort.toName     = "PowerPort"    := rfl
example : EPSTypeTag.powerPortConj.toName = "~PowerPort"   := rfl

/-- 各 tag の `toKerMLType` が期待通りの KerMLType を返す. -/
example : EPSTypeTag.powerSupply.toKerMLType = { name := some "PowerSupply" }  := rfl
example : EPSTypeTag.load.toKerMLType        = { name := some "Load" }         := rfl

/-- `fromName ∘ toName` = `some` (round-trip). 全 tag を `cases` で潰す. -/
theorem EPSTypeTag.fromName_toName (tag : EPSTypeTag) :
    EPSTypeTag.fromName (some tag.toName) = some tag := by
  cases tag <;> rfl

-- ============================================================
-- §2  Interpretation の既存互換性
-- ============================================================

/-- ドメイン内 4 型では `Nat` を返す（リファクタ前と同じ挙動）. -/
example : EPSNatInterpretation { name := some "PowerSupply" } = Nat := rfl
example : EPSNatInterpretation { name := some "Load"        } = Nat := rfl
example : EPSNatInterpretation { name := some "PowerPort"   } = Nat := rfl
example : EPSNatInterpretation { name := some "~PowerPort"  } = Nat := rfl

/-- PowerSupply.baseType は `{ name := some "PowerSupply" }` なので、
    `EPSNatInterpretation PowerSupply.baseType = Nat`. これは
    `epsStateMachineComponent : StateMachineComponent EPSNatInterpretation PowerSupply EPSMode epsGlobalInv`
    が型チェックを通るための核心. -/
example : EPSNatInterpretation PowerSupply.baseType = Nat := rfl

example : EPSNatInterpretation Load.baseType = Nat := rfl

-- ============================================================
-- §3  ドメイン外は Unit（フォールバック挙動）
-- ============================================================

/-- 未登録の型名は `Unit`. -/
example : EPSNatInterpretation { name := some "UnknownType" } = Unit := rfl

/-- 空名（KerMLType の name が none）も `Unit`. -/
example : EPSNatInterpretation { name := none } = Unit := rfl

/-- 大文字小文字違い（typo 相当）も `Unit`. リファクタ前のアンチパターンでは
    これが silently Unit に流れていた。新版では `fromName` の中でだけ文字列比較が
    行われ、ドメイン外は Unit を返すことが docstring に明示されている. -/
example : EPSNatInterpretation { name := some "powersupply" } = Unit := rfl
example : EPSNatInterpretation { name := some "Powr Supply" } = Unit := rfl

-- ============================================================
-- §4  EPSTypeTag の case 網羅性（機械証明）
-- ============================================================

/-- 全 tag に対して `interp` が `Nat` を返す（EPS 固有の性質）. -/
theorem EPSTypeTag.interp_is_Nat (tag : EPSTypeTag) :
    tag.interp = Nat := by
  cases tag <;> rfl

/-- `EPSNatInterpretation (tag.toKerMLType) = Nat` が全 tag で成立。
    これは `fromName_toName` の round-trip と `interp_is_Nat` を組み合わせて示す. -/
theorem EPSNatInterpretation_on_tag (tag : EPSTypeTag) :
    EPSNatInterpretation tag.toKerMLType = Nat := by
  cases tag <;> rfl

-- ============================================================
-- §5  DecidableEq: tag の比較が decide で判定できる
-- ============================================================

example : (EPSTypeTag.powerSupply == EPSTypeTag.powerSupply) = true := rfl
example : (EPSTypeTag.powerSupply == EPSTypeTag.load)         = false := rfl

/-- 異なる tag は異なる name を持つ（単射性）. -/
example : EPSTypeTag.powerSupply.toName ≠ EPSTypeTag.load.toName := by
  simp [EPSTypeTag.toName]

example : EPSTypeTag.powerPort.toName ≠ EPSTypeTag.powerPortConj.toName := by
  simp [EPSTypeTag.toName]

-- ============================================================
-- §6  StateMachineComponent 統合が壊れていないことの確認
-- ============================================================

/-- `epsStateMachineComponent` の型自体が OK であれば、Interpretation
    リファクタで StateMachineComponent 接続が壊れていないことの証拠になる. -/
example :
    StateMachineComponent EPSNatInterpretation PowerSupply EPSMode epsGlobalInv :=
  epsStateMachineComponent

end Examples.Spacecraft.F8Tests
