import VerifiedMBSE.Core.Port
import VerifiedMBSE.Core.Specialization

/-!
# Component Definitions

Defines `PartDef` (part definition with ports and an invariant), `PortRef` (port reference),
`Connector` (port-to-port connection with compatibility proof),
`System` (composition of parts and connectors), and `WellFormed` conditions.
-/

namespace VerifiedMBSE.Core

-- ============================================================
-- §1  PartDef
-- ============================================================

/-- PartDef: part definition with ports and an invariant. -/
structure PartDef where
  baseType  : KerMLType
  ports     : List PortDef
  invariant : Prop
  deriving Repr

/-- Well-formedness of PartDef: every port's flowType has a specialization relation with baseType. -/
def PartDef.WellFormed (pd : PartDef) : Prop :=
  ∀ p ∈ pd.ports, specializes p.flowType pd.baseType ∨
                  specializes pd.baseType p.flowType

-- ============================================================
-- §2  PortRef and Connector
-- ============================================================

/-- PortRef: reference to a port within a part (with membership proof). -/
structure PortRef where
  part : PartDef
  port : PortDef
  mem  : port ∈ part.ports

/-- Connector: connects two port references with a compatibility proof. -/
structure Connector where
  source     : PortRef
  target     : PortRef
  compatible : VerifiedMBSE.Core.compatible
                 source.port.flowType
                 target.port.flowType

-- ============================================================
-- §3  System
-- ============================================================

/-- System: lists of parts and connectors. -/
structure System where
  parts      : List PartDef
  connectors : List Connector

/-- Well-formedness of System: all connector sources/targets are in parts. -/
def System.WellFormed (sys : System) : Prop :=
  ∀ c ∈ sys.connectors,
    c.source.part ∈ sys.parts ∧ c.target.part ∈ sys.parts

end VerifiedMBSE.Core
