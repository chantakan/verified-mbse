-- Core: ドメイン非依存の型理論的基盤
import VerifiedMBSE.Core.KerML
import VerifiedMBSE.Core.Port
import VerifiedMBSE.Core.Specialization
import VerifiedMBSE.Core.Component
import VerifiedMBSE.Core.Compose
import VerifiedMBSE.Core.Interpretation

-- Behavior: 振る舞いモデル
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

-- Matrix: V 字行列
import VerifiedMBSE.Matrix.VColumn
import VerifiedMBSE.Matrix.VMatrix
import VerifiedMBSE.Matrix.Query

-- Output: 人間可読出力
import VerifiedMBSE.Output.Render
import VerifiedMBSE.Output.SysML
import VerifiedMBSE.Output.StateMachineSysML
import VerifiedMBSE.Output.Markdown
import VerifiedMBSE.Output.Terminal

-- Equivalence: HoTT 的等価性（上級者向け）
import VerifiedMBSE.Equivalence.ComponentEquiv
import VerifiedMBSE.Equivalence.Refinement
import VerifiedMBSE.Equivalence.Abstraction
