-- Core: Domain-independent type-theoretic foundations
import VerifiedMBSE.Core.KerML
import VerifiedMBSE.Core.Port
import VerifiedMBSE.Core.Specialization
import VerifiedMBSE.Core.Component
import VerifiedMBSE.Core.Compose
import VerifiedMBSE.Core.Interpretation

-- Behavior: Behavioral models
import VerifiedMBSE.Behavior.StateMachine
import VerifiedMBSE.Behavior.Temporal
import VerifiedMBSE.Behavior.FDIR

-- VV: Verification & Validation
import VerifiedMBSE.VV.Layer
import VerifiedMBSE.VV.Evidence
import VerifiedMBSE.VV.SubSystemSpec
import VerifiedMBSE.VV.VVBundle
import VerifiedMBSE.VV.Power
import VerifiedMBSE.VV.Propagation

-- Matrix: V-matrix construction
import VerifiedMBSE.Matrix.VColumn
import VerifiedMBSE.Matrix.VMatrix
import VerifiedMBSE.Matrix.Query

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

A Lean 4 framework that gives SysML v2 / KerML design models a dependent type-theoretic
semantics and guarantees V&V matrix completeness by type checking.

## Modules

- **Core** — Domain-independent foundations: KerML elements, ports, specialization,
  components, connectors, system composition, and categorical interpretation.
- **Behavior** — State machines with invariant-preserving transitions,
  temporal logic (□, ◇, Until, Leads), and FDIR specification.
- **VV** — Verification & Validation framework: evidence with confidence levels,
  subsystem specifications, power budgets, and layer propagation.
- **Matrix** — V-matrix construction (`VColumn`, `VMatrix`) with `Complete` theorems
  that ensure every requirement has machine-checked evidence.
- **Output** — Human-readable output generation: SysML v2 textual notation,
  Markdown tables, and terminal summaries with confidence bars.
- **Equivalence** — HoTT-inspired equivalence theory: `ComponentEquiv` (setoid),
  `DesignSpace` (quotient type), univalence (`ua`/`ua_inv`), transport, fibers,
  requirement refinement, and abstraction levels.
-/
