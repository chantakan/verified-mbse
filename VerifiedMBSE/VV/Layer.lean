/-!
# V-Model Design Layers (ECSS-E-ST-10C Compliant, F5)

## 概要

ECSS-E-ST-10C の 7 階層 (mission/system/segment/subsystem/assembly/unit/part) に
プロジェクト固有の `component` を加えた 8 階層。後方互換のため、旧 3 階層
`.system` / `.subsystem` / `.component` は同じ constructor 名を維持する。

## 順序付け: depth ベース

各 Layer に 0〜7 の整数 `depth` を割り当て、`Ord` instance と
`Layer.supports` 関係を depth 比較で統一する。depth が大きいほど下層
（分解が進んだ側）。

| Layer     | depth | 説明 |
|-----------|-------|------|
| mission   | 0     | ミッション全体 |
| system    | 1     | 宇宙機 1 機または地上局全体 |
| segment   | 2     | Space segment / Ground segment 等の大区分 |
| subsystem | 3     | AOCS, EPS, TCS 等 |
| assembly  | 4     | 組立体: アビオ箱、バルブ組 |
| unit      | 5     | ユニット: センサー単体、MCU 単体 |
| component | 6     | コンポーネント: ADC IC、モーター（プロジェクト固有） |
| part      | 7     | 最終部品: 抵抗、ボルト等 |

## 後方互換

旧 3 階層 (`.system`, `.subsystem`, `.component`) を直接参照するコード
（`VColumn.allLayersCovered`, `SubSystemSpec.safetyRecord` の `.layer`,
Examples の `.layer := .system` 等）は、新版でも同じ constructor 名が
そのまま使えるため **無変更でビルド通過** する。

## `Ord` instance の変更点

旧 instance は pattern match で `component < subsystem < system` の順序を
与えていた（未使用だったが、記録のため）。新版は depth の自然順、すなわち
`mission < system < ... < part` の順序になる。dead code 化していたため
影響範囲はない。
-/

namespace VerifiedMBSE.VV

/-- V-model design layer (ECSS-E-ST-10C の 7 階層 + プロジェクト固有 component)。 -/
inductive Layer where
  | mission
  | system
  | segment
  | subsystem
  | assembly
  | unit
  | component
  | part
  deriving Repr, BEq, DecidableEq

/-- 各層の深さ (0 = 最上位 mission、7 = 最下位 part)。

    `supports` 関係と `Ord` instance はこの depth を通して定義される。 -/
def Layer.depth : Layer → Nat
  | .mission   => 0
  | .system    => 1
  | .segment   => 2
  | .subsystem => 3
  | .assembly  => 4
  | .unit      => 5
  | .component => 6
  | .part      => 7

/-- Layer ordering via depth.

    `mission (0) < system (1) < ... < part (7)` の自然順。
    ECSS の階層構造図とも一致する（上位を小さい数値で示す）。 -/
instance : Ord Layer where
  compare a b := compare a.depth b.depth

end VerifiedMBSE.VV
