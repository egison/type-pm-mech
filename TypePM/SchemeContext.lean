import TypePM.PolyFreeVars
import TypePM.PolySubstitutionLaws

/-!
# Capture-free expression contexts

Expression contexts store canonical `Scheme` values.  Ambient substitution
acts only on free solver metavariables, so context composition inherits the
scheme law without binder masking or a capture condition.
-/

namespace TypePM

/-- Expression scheme context.  The newest binding is stored first. -/
abbrev Context := List (String × Scheme)

namespace Context

/-- Look up an expression scheme. -/
def find? (context : Context) (name : String) : Option Scheme :=
  (List.find? (fun entry => entry.1 == name) context).map Prod.snd

/-- Apply an ambient paired substitution to every free scheme meta. -/
def applySubst (substitution : Subst) (context : Context) : Context :=
  context.map fun entry => (entry.1, entry.2.applyMeta substitution)

/-- Free capability solver metavariables of an expression context. -/
def fcv (context : Context) : List CapVar :=
  context.flatMap fun entry => entry.2.fcv

/-- Free target solver metavariables of an expression context. -/
def ftv (context : Context) : List TypePM.TyVar :=
  context.flatMap fun entry => entry.2.ftv

@[simp] theorem applySubst_id (context : Context) :
    context.applySubst Subst.id = context := by
  induction context with
  | nil => rfl
  | cons entry context ih =>
      cases entry
      simp [Context.applySubst]

theorem applySubst_comp (S₂ S₁ : Subst)
    (crossFixed : (Subst.mk S₂.cap S₁.target).RangeFixed)
    (context : Context) :
    context.applySubst (Subst.comp S₂ S₁) =
      (context.applySubst S₁).applySubst S₂ := by
  induction context with
  | nil => rfl
  | cons entry context ih =>
      cases entry with
      | mk name scheme =>
          simp only [Context.applySubst, List.map_cons]
          rw [Scheme.applyMeta_comp S₂ S₁ crossFixed scheme]
          congr 1

theorem find?_applySubst (substitution : Subst)
    (context : Context) (name : String) :
    (context.applySubst substitution).find? name =
      (context.find? name).map (Scheme.applyMeta substitution) := by
  simp [Context.applySubst, Context.find?, Function.comp_def,
    List.find?_map]

end Context
end TypePM
