-- Core: Domain-independent type-theoretic foundations
import VerifiedMBSE.Core.KerML
import VerifiedMBSE.Core.Port
import VerifiedMBSE.Core.Specialization
import VerifiedMBSE.Core.Component
import VerifiedMBSE.Core.Compose
import VerifiedMBSE.Core.Interpretation

-- Behavior: Behavioral models (Kripke-based LTL framework)
import VerifiedMBSE.Behavior.KripkeStructure     -- B-1: LTL 意味論基盤 + ToKripke 型クラス
import VerifiedMBSE.Behavior.StateMachine
import VerifiedMBSE.Behavior.Temporal             -- B-1: ToKripke 経由の Always/Eventually/Leads
import VerifiedMBSE.Behavior.StateMachineKripke  -- B-1: ToKripke instance for StateMachine
import VerifiedMBSE.Behavior.StateMachineLTL     -- B-1: Next / Until (StateMachine 固有)
import VerifiedMBSE.Behavior.FDIR
-- 積状態機械 (B-4 で KripkeStructure ベースに統合)
import VerifiedMBSE.Behavior.Product
import VerifiedMBSE.Behavior.ProductKripke        -- B-4 新規: ToKripke instance for ProductStateMachine
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
- **Behavior** — Unified Kripke-based LTL framework via `ToKripke` type class.
  `KripkeStructure State Data` は LTL 演算子 (`Always` / `Eventually` / `Leads`)
  の共通意味論基盤で、`ToKripke` 型クラスを通して `StateMachine` /
  `ProductStateMachine` / 連続時間系などが同一 API を共有する。`Next` / `Until` は
  遷移構造に依存するため `StateMachineLTL` に分離。`FDIR`, `Product`
  (積状態機械の到達可能性), `ProductKripke` (B-4 新規: 積の ToKripke instance),
  `ProductTemporal` (`Always_prod` 等の後方互換エイリアス + 持ち上げ補題) を含む。
- **VV** — `StructuralSpec` / `BehavioralSpec` / `FDIRBundle` / `SubSystemSpec`
  による統合仕様、`ProductFDIRBundle` による並列合成、evidence 付き
  `ValidationTrace`、`ModelBoundary`。
- **Matrix** — `VColumn` / `VMatrix` による V&V マトリクス、完全性定理、
  `VMatrix` に依存型紐付けされた `ModelBoundary`。
- **Output** — SysML v2 テキスト記法、Markdown テーブル、端末表示。
- **Equivalence** — HoTT 風等価性: `ComponentEquiv` / `DesignSpace` (quotient) /
  `ua` / `transport` / `RequirementRefinement` / `AbstractionLevel`。

## Roadmap (F4.5: Kripke Unification)

B-1 (KripkeStructure + ToKripke 導入)・B-4 (ProductStateMachine 統合) を完了。
以降 B-6 (`ProductFDIRBundle` を `FDIRBundle` に合流)、B-7 (`SubSystemSpec` の
Kripke 一般化 + N機合成) と段階的に進める。
-/
