/-!
# V-Model Design Layers
-/

namespace VerifiedMBSE.VV

/-- Layer: V 字モデルの設計レイヤー。 -/
inductive Layer where
  | system
  | subsystem
  | component
  deriving Repr, BEq

/-- Layer の順序: component < subsystem < system。 -/
instance : Ord Layer where
  compare a b := match a, b with
    | .component, .subsystem => .lt
    | .component, .system    => .lt
    | .subsystem, .system    => .lt
    | .system,    .subsystem => .gt
    | .system,    .component => .gt
    | .subsystem, .component => .gt
    | _, _                   => .eq

end VerifiedMBSE.VV
