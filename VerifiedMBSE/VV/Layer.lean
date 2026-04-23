/-!
# V-Model Design Layers (ECSS-E-ST-10C Compliant)

## Overview

Eight layers: the seven ECSS-E-ST-10C layers
(mission, system, segment, subsystem, assembly, unit, part) plus a
project-specific `component` layer inserted between `unit` and `part`.

## Depth-based ordering

Each `Layer` is assigned an integer `depth` in the range `0..7`, and
the `Ord` instance together with the `Layer.supports` relation are
defined uniformly in terms of this `depth`. A larger depth denotes
a lower layer (further decomposition).

| Layer     | depth | Description |
|-----------|-------|-------------|
| mission   | 0     | Overall mission |
| system    | 1     | A single spacecraft or ground station as a whole |
| segment   | 2     | Major divisions such as space segment / ground segment |
| subsystem | 3     | AOCS, EPS, TCS, ... |
| assembly  | 4     | Assemblies: avionics boxes, valve stacks |
| unit      | 5     | Units: individual sensors, a single MCU |
| component | 6     | Components: an ADC IC, a motor (project-specific) |
| part      | 7     | Terminal parts: resistors, bolts, ... |

The `Ord` instance orders layers naturally by depth, so
`mission < system < ... < part`, matching the usual ECSS hierarchy
diagrams where higher levels appear with smaller indices.
-/

namespace VerifiedMBSE.VV

/-- V-model design layer: the seven ECSS-E-ST-10C layers plus a
    project-specific `component` layer. -/
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

/-- Depth of each layer (0 = topmost `mission`, 7 = bottom-most `part`).

    The `supports` relation and the `Ord` instance are both defined in
    terms of this `depth`. -/
def Layer.depth : Layer → Nat
  | .mission   => 0
  | .system    => 1
  | .segment   => 2
  | .subsystem => 3
  | .assembly  => 4
  | .unit      => 5
  | .component => 6
  | .part      => 7

/-- Layer ordering via `depth`.

    Produces the natural order `mission (0) < system (1) < ... < part (7)`,
    in agreement with the usual ECSS hierarchy diagrams (upper layers
    have smaller indices). -/
instance : Ord Layer where
  compare a b := compare a.depth b.depth

end VerifiedMBSE.VV
