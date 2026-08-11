import TypePM.PolyScheme
import TypePM.FreeVars
import TypePM.UniqueVars

/-!
# Generalization into capture-free schemes

Generalization first chooses the ordinary solver metavariables not present in
the environment, then immediately closes them into finite bound indices.  The
chosen names are not retained in the resulting `PolyScheme`.
-/

namespace TypePM

/-- Capability metavariables selected for generalization. -/
def generalizedCapVars (envCaps : List CapVar) (target : Ty) : List CapVar :=
  uniqueVars (target.fcv.filter (fun varId => varId ∉ envCaps))

/-- Ordinary metavariables selected for generalization. -/
def generalizedTyVars (envTys : List TypePM.TyVar)
    (target : Ty) : List TypePM.TyVar :=
  uniqueVars (target.ftv.filter (fun varId => varId ∉ envTys))

/-- Generalize an ordinary type and close the selected metavariables at once. -/
def PolyScheme.generalize (envCaps : List CapVar)
    (envTys : List TypePM.TyVar) (target : Ty) : PolyScheme :=
  PolyScheme.close (generalizedCapVars envCaps target)
    (generalizedTyVars envTys target) target

@[simp] theorem PolyScheme.generalize_capArity
    (envCaps : List CapVar) (envTys : List TypePM.TyVar) (target : Ty) :
    (PolyScheme.generalize envCaps envTys target).capArity =
      (generalizedCapVars envCaps target).length := by
  rfl

@[simp] theorem PolyScheme.generalize_tyArity
    (envCaps : List CapVar) (envTys : List TypePM.TyVar) (target : Ty) :
    (PolyScheme.generalize envCaps envTys target).tyArity =
      (generalizedTyVars envTys target).length := by
  rfl

theorem generalizedCapVars_nodup (envCaps : List CapVar) (target : Ty) :
    (generalizedCapVars envCaps target).Nodup := by
  exact uniqueVars_nodup _

theorem generalizedTyVars_nodup (envTys : List TypePM.TyVar) (target : Ty) :
    (generalizedTyVars envTys target).Nodup := by
  exact uniqueVars_nodup _

/-- A selected capability metavariable is absent from the environment. -/
theorem mem_generalizedCapVars_not_env {envCaps : List CapVar}
    {target : Ty} {varId : CapVar}
    (membership : varId ∈ generalizedCapVars envCaps target) :
    varId ∉ envCaps := by
  exact of_decide_eq_true
    (List.mem_filter.mp (mem_uniqueVars.mp membership)).2

/-- A selected ordinary metavariable is absent from the environment. -/
theorem mem_generalizedTyVars_not_env {envTys : List TypePM.TyVar}
    {target : Ty} {varId : TypePM.TyVar}
    (membership : varId ∈ generalizedTyVars envTys target) :
    varId ∉ envTys := by
  exact of_decide_eq_true
    (List.mem_filter.mp (mem_uniqueVars.mp membership)).2

end TypePM
