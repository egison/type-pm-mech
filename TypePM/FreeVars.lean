import TypePM.Syntax

/-!
# Free solver metavariables

These traversals belong to the ordinary solver syntax and are shared by both
legacy relations and capture-free generalization.
-/

namespace TypePM

mutual

/-- Flexible capability variables occurring in a capability. -/
def Cap.fcv : Cap → List CapVar
  | .any          => []
  | .var a        => [a]
  | .skolem _     => []
  | .con _ caps   => Cap.fcvList caps
  | .prod caps    => Cap.fcvList caps

/-- Flexible capability variables occurring in a list of capabilities. -/
def Cap.fcvList : List Cap → List CapVar
  | []          => []
  | cap :: caps => cap.fcv ++ Cap.fcvList caps

end

mutual

/-- Flexible capability variables occurring anywhere in a two-sorted type. -/
def Ty.fcv : Ty → List CapVar
  | .var _         => []
  | .skolem _      => []
  | .unit          => []
  | .int           => []
  | .bool          => []
  | .data _ tys    => Ty.fcvList tys
  | .prod tys      => Ty.fcvList tys
  | .fn dom cod    => dom.fcv ++ cod.fcv
  | .matcher c ty  => c.fcv ++ ty.fcv
  | .slot c ty     => c.fcv ++ ty.fcv

/-- Flexible capability variables occurring in a list of two-sorted types. -/
def Ty.fcvList : List Ty → List CapVar
  | []        => []
  | ty :: tys => ty.fcv ++ Ty.fcvList tys

end

mutual

/-- Ordinary target-type variables occurring in a two-sorted type. -/
def Ty.ftv : Ty → List TypePM.TyVar
  | .var a         => [a]
  | .skolem _      => []
  | .unit          => []
  | .int           => []
  | .bool          => []
  | .data _ tys    => Ty.ftvList tys
  | .prod tys      => Ty.ftvList tys
  | .fn dom cod    => dom.ftv ++ cod.ftv
  | .matcher _ ty  => ty.ftv
  | .slot _ ty     => ty.ftv

/-- Ordinary target-type variables occurring in a list of two-sorted types. -/
def Ty.ftvList : List Ty → List TypePM.TyVar
  | []        => []
  | ty :: tys => ty.ftv ++ Ty.ftvList tys

end

end TypePM
