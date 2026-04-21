import VerifiedMBSE
import Examples.Spacecraft.EPS
import Examples.Spacecraft.Integration

/-!
# B-8d 可変長合成 API の受入条件テスト

`SubSystemPayload`・`SubSystemPayload.compose`・`SubSystemPayload.composeMany`
のサニティテスト。

## 検証項目

1. `ofSpec` による payload の構築 (単一 StateMachine / 既存 `SubSystemSpec`)
2. 2 機合成 (`compose`) の結果が既存 `SubSystemSpec.compose` と整合
3. 4 機合成 (`compose` のチェーン) が成立し、name が左結合で展開される
4. `composeMany` のリスト版とチェーン版が同一結果
5. 空リスト / 単機リストの境界動作
6. 合成後の payload から VVRecord 自動生成が機能する
7. `compose_parts_length` 補助補題
-/

namespace Examples.Spacecraft.VariadicComposeTests

open VerifiedMBSE.Core
open VerifiedMBSE.Behavior
open VerifiedMBSE.VV
open Examples.Spacecraft.EPS
open Examples.Spacecraft.Integration

-- ============================================================
-- §1  ofSpec: 既存 SubSystemSpec からの payload 構築
-- ============================================================

/-- EPS spec を payload に wrap できる. -/
def epsPayload : SubSystemPayload := SubSystemPayload.ofSpec epsSpec

/-- Mini spec を payload に wrap できる. -/
def miniPayload : SubSystemPayload := SubSystemPayload.ofSpec miniSpec

/-- Mini2 spec を payload に wrap できる. -/
def mini2Payload : SubSystemPayload := SubSystemPayload.ofSpec mini2Spec

/-- payload の spec.name は元の spec.name と一致する. -/
example : epsPayload.spec.name = "EPS" := rfl

/-- payload の spec.name は元の spec.name と一致する (Mini). -/
example : miniPayload.spec.name = "Mini" := rfl

-- ============================================================
-- §2  2 機合成 (SubSystemPayload.compose)
-- ============================================================

/-- 2 機合成 payload (EPS + Mini). -/
def epsMiniPayload : SubSystemPayload := epsPayload.compose miniPayload

/-- 2 機合成後の name は "EPS+Mini". -/
example : epsMiniPayload.spec.name = "EPS+Mini" := rfl

/-- `compose_name` 補助補題で同じ結論が得られる. -/
example : (epsPayload.compose miniPayload).spec.name = "EPS+Mini" :=
  SubSystemPayload.compose_name epsPayload miniPayload

-- ============================================================
-- §3  4 機合成 (チェーン) + composeMany
-- ============================================================

/-- 4 機合成 (チェーン版): EPS + Mini + Mini2 + Mini. -/
def fourChain : SubSystemPayload :=
  epsPayload.compose miniPayload
    |>.compose mini2Payload
    |>.compose miniPayload

/-- 4 機合成後の name は "EPS+Mini+Mini2+Mini" (左結合). -/
example : fourChain.spec.name = "EPS+Mini+Mini2+Mini" := rfl

/-- 4 機合成 (リスト版 composeMany). -/
def fourList : Option SubSystemPayload :=
  SubSystemPayload.composeMany
    [ epsPayload, miniPayload, mini2Payload, miniPayload ]

/-- リスト版は some にマップされる. -/
example : fourList.isSome = true := rfl

/-- リスト版とチェーン版の合成結果は defeq で一致する. -/
example : fourList = some fourChain := rfl

-- ============================================================
-- §4  境界: 空リスト / 単機リスト
-- ============================================================

/-- 空リストの合成結果は none. -/
example : SubSystemPayload.composeMany [] = none := rfl

/-- 空リストの合成結果は none (補助補題版). -/
example : SubSystemPayload.composeMany [] = none :=
  SubSystemPayload.composeMany_nil

/-- 単機リストの合成結果はその機そのもの (2 機合成は走らない). -/
example : SubSystemPayload.composeMany [epsPayload] = some epsPayload := rfl

/-- 単機リストの合成結果はその機そのもの (補助補題版). -/
example : SubSystemPayload.composeMany [miniPayload] = some miniPayload :=
  SubSystemPayload.composeMany_singleton miniPayload

/-- 2 機リストはチェーン版と一致. -/
example :
    SubSystemPayload.composeMany [epsPayload, miniPayload] =
      some (epsPayload.compose miniPayload) := rfl

/-- 3 機リストはチェーン版と一致. -/
example :
    SubSystemPayload.composeMany [epsPayload, miniPayload, mini2Payload] =
      some ((epsPayload.compose miniPayload).compose mini2Payload) := rfl

-- ============================================================
-- §5  合成後 payload からの VVRecord 自動生成
-- ============================================================

/-- 4 機合成 spec から S1-WellFormed VVRecord が自動生成できる. -/
def fourChain_s1 : VVRecord := fourChain.spec.subsystemRecord

/-- 4 機合成 spec から R1-Safety VVRecord が自動生成できる. -/
def fourChain_r1 : VVRecord := fourChain.spec.safetyRecord

/-- 4 機合成 spec から R3-Recovery VVRecord が自動生成できる. -/
def fourChain_r3 : VVRecord := fourChain.spec.recoveryRecord

/-- S1 record の spec_name は "EPS+Mini+Mini2+Mini-S1-WellFormed". -/
example : fourChain_s1.spec_name = "EPS+Mini+Mini2+Mini-S1-WellFormed" := rfl

/-- R1 record の spec_name は "EPS+Mini+Mini2+Mini-R1-Safety". -/
example : fourChain_r1.spec_name = "EPS+Mini+Mini2+Mini-R1-Safety" := rfl

/-- R3 record の spec_name は "EPS+Mini+Mini2+Mini-R3-Recovery". -/
example : fourChain_r3.spec_name = "EPS+Mini+Mini2+Mini-R3-Recovery" := rfl

/-- デフォルト evidence は `.trusted` で入る (F1 との整合). -/
example : fourChain_r1.validation.isTrusted = true := rfl

-- ============================================================
-- §6  compose_parts_length 補助補題
-- ============================================================

/-- `compose_parts_length`: 右辺は `.system.parts.length` 版
    (既存 `StructuralSpec.compose_parts_length` との整合)。 -/
example :
    (epsPayload.compose miniPayload).spec.structural.parts.length =
      epsPayload.spec.structural.system.parts.length
        + miniPayload.spec.structural.system.parts.length :=
  SubSystemPayload.compose_parts_length epsPayload miniPayload

/-- 具体インスタンスでは `.parts` と `.system.parts` が defeq なので、
    `.parts.length` 版の等式も `rfl` で直接通る (smart constructor の
    `system_eq_parts := rfl` のおかげ)。 -/
example :
    (epsPayload.compose miniPayload).spec.structural.parts.length =
      epsPayload.spec.structural.parts.length
        + miniPayload.spec.structural.parts.length := by
  rfl

/-- Mini (parts = []) + Mini2 (parts = []) の合成では parts.length は 0. -/
example :
    (miniPayload.compose mini2Payload).spec.structural.parts.length = 0 := by
  rfl

-- ============================================================
-- §7  behavioral.nonEmpty の連鎖利用 (B-8c 依存性の回帰テスト)
-- ============================================================

/-- 2 機合成後の behavioral.nonEmpty は取り出せる. -/
example : (ToKripke.toKripke epsMiniPayload.x).NonEmpty :=
  epsMiniPayload.spec.behavioral.nonEmpty

/-- 4 機合成後の behavioral.nonEmpty は取り出せる. -/
example : (ToKripke.toKripke fourChain.x).NonEmpty :=
  fourChain.spec.behavioral.nonEmpty

end Examples.Spacecraft.VariadicComposeTests
