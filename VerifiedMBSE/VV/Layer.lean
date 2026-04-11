/-!
# V-Model Design Layers
-/

namespace VerifiedMBSE.VV

/-- Layer: V-model design layer. -/
inductive Layer where
  | system
  | subsystem
  | component
  deriving Repr, BEq

/-- Layer ordering: component < subsystem < system. -/
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
