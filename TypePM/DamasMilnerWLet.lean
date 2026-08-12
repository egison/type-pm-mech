import TypePM.DamasMilnerW

/-!
# Let boundaries for Damas--Milner Algorithm W completeness

The value and body traversals of an executable `let` meet at a generalized
scheme.  This module isolates the two pieces which are independent of the
recursive completeness proof:

* extending a protected W frame with a residual-realized generalized binding;
* composing the value/body origin and terminal-audit certificates.

The generalization relation is deliberately semantic (`SScheme.RealizedBy`).
It says that every use admitted by the declarative DM scheme is admitted by
the executable scheme after the shared residual has acted on its free
metavariables.  This avoids the false requirement that all polymorphic uses
factor through one fixed total substitution.
-/

namespace TypePM
namespace DM

/-! ## The generalized binding at a let cut -/

/-- The exact relation required when a raw executable binding is put under the
current prevailing substitution before the body traversal starts. -/
structure WLetBindingRel (post prevailing : Subst)
    (algorithmScheme : Scheme) (selectedScheme : SScheme) : Prop where
  capArity : algorithmScheme.capArity = 0
  realizes : selectedScheme.RealizedBy post
    (algorithmScheme.applyMeta prevailing)

/-- Package an already-established semantic realization as a let-binding
relation. -/
theorem WLetBindingRel.ofRealized
    {post prevailing : Subst} {algorithmScheme : Scheme}
    {selectedScheme : SScheme}
    (capArity : algorithmScheme.capArity = 0)
    (realizes : selectedScheme.RealizedBy post
      (algorithmScheme.applyMeta prevailing)) :
    WLetBindingRel post prevailing algorithmScheme selectedScheme :=
  ⟨capArity, realizes⟩

/-- A residual equation for embedded one-sort generalization supplies the
binding relation at identity prevailing state. -/
theorem WLetBindingRel.ofEmbeddedGeneralizationResidual
    {signature : FrozenSig} (signatureClosed : signature.ftv = [])
    {post : Subst}
    {algorithmContext selectedContext : SCtx}
    {algorithmTarget selectedTarget : STy}
    (relation : EmbeddedGeneralizationResidual post signature
      algorithmContext algorithmTarget selectedContext selectedTarget) :
    WLetBindingRel post Subst.id
      (signature.generalize algorithmContext.emb algorithmTarget.emb)
      (SCtx.generalize selectedContext selectedTarget) := by
  refine ⟨?_, ?_⟩
  · rw [DM.generalize_emb signatureClosed]
    rfl
  · intro target instantiation
    simpa using relation.realizedBy instantiation

/-- Extend one residual-related context by the generalized binding selected
at a let boundary. -/
theorem WContextRel.consLetBinding
    {post prevailing : Subst}
    {algorithmContext : Context} {selectedContext : SCtx}
    {name : String} {algorithmScheme : Scheme}
    {selectedScheme : SScheme}
    (binding : WLetBindingRel post prevailing algorithmScheme selectedScheme)
    (tail : WContextRel post
      (algorithmContext.applySubst prevailing) selectedContext) :
    WContextRel post
      (Context.applySubst prevailing
        ((name, algorithmScheme) :: algorithmContext))
      ((name, selectedScheme) :: selectedContext) := by
  change WContextRel post
    ((name, algorithmScheme.applyMeta prevailing) ::
      algorithmContext.applySubst prevailing)
    ((name, selectedScheme) :: selectedContext)
  exact @WContextRel.cons post (algorithmContext.applySubst prevailing)
    selectedContext name (algorithmScheme.applyMeta prevailing) selectedScheme
    binding.capArity binding.realizes tail

/-- Protect the let-body context while retaining every older protected
context and type equation.  The explicit boundedness premise is precisely the
fresh-supply side condition consumed by later variable openings and solver
cuts. -/
theorem WProtectedFrameAt.protectLetBody
    {supply : InferenceBase.FreshSupply} {post prevailing : Subst}
    {frames : List (Context × SCtx)} {frontier : List (Ty × STy)}
    {rawContext : Context} {selectedContext : SCtx}
    {name : String} {algorithmScheme : Scheme}
    {selectedScheme : SScheme}
    (frame : WProtectedFrameAt supply post prevailing frames frontier)
    (outer : WContextRel post
      (rawContext.applySubst prevailing) selectedContext)
    (binding : WLetBindingRel post prevailing algorithmScheme selectedScheme)
    (bounded : Context.BoundedBy supply
      (Context.applySubst prevailing
        ((name, algorithmScheme) :: rawContext))) :
    WProtectedFrameAt supply post prevailing
      ((((name, algorithmScheme) :: rawContext,
          (name, selectedScheme) :: selectedContext)) :: frames) frontier :=
  frame.protect (WContextRel.consLetBinding binding outer) bounded

/-! ## Certified let composition -/

/-- Compose independently certified value and body traversals into the exact
origin/audit certificate for their executable let.  Generalization stability
is intentionally the sole extra premise: it is terminal-sensitive and cannot
be inferred from the two structural child certificates alone. -/
theorem w_let_certified_complete
    {terminal : Subst} {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {name : String} {value body : Expr} {valueTarget : Ty}
    {q₁ : InferenceBase.FreshSupply} {S₁ : Subst} {bodyTarget : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {ledger ledger₁ ledger' : CapabilityOriginLedger}
    {valueRaw : DemandSynth signature q S context value valueTarget q₁ S₁}
    {valueOrigin : DemandSynthOrigin signature valueRaw ledger ledger₁}
    {bodyRaw : DemandSynth signature q₁ S₁
      ((name, signature.generalize (context.applySubst S₁)
        (S₁.apply valueTarget)) :: context) body bodyTarget q' S'}
    {bodyOrigin : DemandSynthOrigin signature bodyRaw ledger₁ ledger'}
    (valueAudit : DemandSynthTerminalAudit terminal signature valueOrigin)
    (bodyAudit : DemandSynthTerminalAudit terminal signature bodyOrigin)
    (facts : DDTerminalAudit.LetFacts terminal signature context valueTarget
      S₁) :
    ∃ (derived : DemandSynth signature q S context (.letE name value body)
          bodyTarget q' S')
      (origin : DemandSynthOrigin signature derived ledger ledger'),
      Nonempty (DemandSynthTerminalAudit terminal signature origin) := by
  let derived : DemandSynth signature q S context (.letE name value body)
      bodyTarget q' S' := DemandSynth.letE valueRaw bodyRaw
  let origin : DemandSynthOrigin signature derived ledger ledger' :=
    DemandSynthOrigin.letE valueOrigin bodyOrigin
  exact ⟨derived, origin,
    ⟨DemandSynthTerminalAudit.letE valueAudit bodyAudit facts⟩⟩

end DM
end TypePM
