-- Core: Domain-independent type-theoretic foundations
import VerifiedMBSE.Core.KerML
import VerifiedMBSE.Core.Port
import VerifiedMBSE.Core.Specialization
import VerifiedMBSE.Core.Component
import VerifiedMBSE.Core.Compose
import VerifiedMBSE.Core.Interpretation

-- Behavior: Behavioral models (Kripke-based LTL framework)
import VerifiedMBSE.Behavior.KripkeStructure     -- B-1 新規: LTL 意味論基盤
import VerifiedMBSE.Behavior.StateMachine
import VerifiedMBSE.Behavior.Temporal             -- B-1 書き換え: KripkeStructure 版 Always/Eventually/Leads
import VerifiedMBSE.Behavior.StateMachineKripke  -- B-1 新規: StateMachine → KripkeStructure coerce
import VerifiedMBSE.Behavior.StateMachineLTL     -- B-1 新規: Next / Until (StateMachine 固有)
import VerifiedMBSE.Behavior.FDIR
-- 積状態機械 (B-4 で KripkeStructure ベースに統合予定)
import VerifiedMBSE.Behavior.Product
import VerifiedMBSE.Behavior.ProductTemporal

-- VV: Verification & Validation
import VerifiedMBSE.VV.Layer
import VerifiedMBSE.VV.Evidence
import VerifiedMBSE.VV.SubSystemSpec
import VerifiedMBSE.VV.ProductFDIR
import VerifiedMBSE.VV.VVBundle
import VerifiedMBSE.VV.Power
import VerifiedMBSE.VV.Propagation
import VerifiedMBSE.VV.Contract

-- Matrix: V-matrix construction
import VerifiedMBSE.Matrix.VColumn
import VerifiedMBSE.Matrix.VMatrix
import VerifiedMBSE.Matrix.Query
import VerifiedMBSE.Matrix.ModelBoundary

-- Output: Human-readable output generation
import VerifiedMBSE.Output.Render
import VerifiedMBSE.Output.SysML
import VerifiedMBSE.Output.StateMachineSysML
import VerifiedMBSE.Output.Markdown
import VerifiedMBSE.Output.Terminal

-- Equivalence: HoTT-inspired equivalence (advanced)
import VerifiedMBSE.Equivalence.ComponentEquiv
import VerifiedMBSE.Equivalence.Refinement
import VerifiedMBSE.Equivalence.Abstraction
import VerifiedMBSE.Equivalence.Univalence

/-!
# VerifiedMBSE

A Lean 4 framework that gives SysML v2 / KerML design models a dependent
type-theoretic semantics and guarantees V&V matrix completeness by type
checking.

## Modules

- **Core** — KerML elements, ports, specialization, components, connectors,
  system composition, categorical interpretation.
- **Behavior** — Kripke-based LTL framework. `KripkeStructure` は LTL 演算子
  (`Always` / `Eventually` / `Leads`) の共通意味論基盤で、`StateMachine` /
  `ProductStateMachine` / 連続時間系などが `toKripke` 経由で同一 API を共有
  する。`Next` / `Until` は遷移構造に依存するため `StateMachineLTL` に分離。
  `FDIR`, `Product` (積状態機械の到達可能性), `ProductTemporal` (旧式の
  `Always_prod` 等、B-6 で統合予定) を含む。
- **VV** — `StructuralSpec` / `BehavioralSpec` / `FDIRBundle` / `SubSystemSpec`
  による統合仕様、`ProductFDIRBundle` による並列合成、evidence 付き
  `ValidationTrace`、`ModelBoundary` (B-6 で VMatrix 依存化予定)。
- **Matrix** — `VColumn` / `VMatrix` による V&V マトリクス、完全性定理、
  `VMatrix` に依存型紐付けされた `ModelBoundary`。
- **Output** — SysML v2 テキスト記法、Markdown テーブル、端末表示。
- **Equivalence** — HoTT 風等価性: `ComponentEquiv` / `DesignSpace` (quotient) /
  `ua` / `transport` / `RequirementRefinement` / `AbstractionLevel`。

## Roadmap (F4.5: Kripke Unification)

B-1 (本コミット) で `KripkeStructure` を導入し、LTL API を一本化する基盤を
整備。以降 B-2 (既存 Examples の互換性確認)、B-4 (ProductStateMachine の
Kripke 化)、B-6 (`Always_prod` 等を `Always` に統合)、B-7 (`SubSystemSpec`
の Kripke 一般化 + N機合成) と段階的に進める。
-/
