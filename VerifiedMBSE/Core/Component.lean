import VerifiedMBSE.Core.Port
import VerifiedMBSE.Core.Specialization

/-!
# コンポーネント定義

PartDef（パーツ定義）、PortRef（ポート参照）、Connector（接続）、
System（システム合成）と WellFormed 条件を定義する。
-/

namespace VerifiedMBSE.Core

-- ============================================================
-- §1  PartDef
-- ============================================================

/-- PartDef: ポートリストと不変条件を持つパーツ定義。 -/
structure PartDef where
  baseType  : KerMLType
  ports     : List PortDef
  invariant : Prop
  deriving Repr

/-- PartDef の整形式条件：全ポートの flowType が baseType と特殊化関係にある。 -/
def PartDef.WellFormed (pd : PartDef) : Prop :=
  ∀ p ∈ pd.ports, specializes p.flowType pd.baseType ∨
                  specializes pd.baseType p.flowType

-- ============================================================
-- §2  PortRef と Connector
-- ============================================================

/-- PortRef: パーツ内のポートへの参照（所属証明付き）。 -/
structure PortRef where
  part : PartDef
  port : PortDef
  mem  : port ∈ part.ports

/-- Connector: 2つのポート参照を互換性証明付きで接続する。 -/
structure Connector where
  source     : PortRef
  target     : PortRef
  compatible : VerifiedMBSE.Core.compatible
                 source.port.flowType
                 target.port.flowType

-- ============================================================
-- §3  System
-- ============================================================

/-- System: パーツとコネクタのリスト。 -/
structure System where
  parts      : List PartDef
  connectors : List Connector

/-- System の整形式条件：全コネクタの source/target が parts に含まれる。 -/
def System.WellFormed (sys : System) : Prop :=
  ∀ c ∈ sys.connectors,
    c.source.part ∈ sys.parts ∧ c.target.part ∈ sys.parts

end VerifiedMBSE.Core
