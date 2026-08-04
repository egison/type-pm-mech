import TypePM.Source

/-!
# Structural metatheory of the concrete two-sorted source judgments

The theorems in this module expose facts that follow from the actual
`ClauseTy`/`ClausesTy` derivations.  In particular, matcher coverage and
dispatch are not supplied by a runtime interface: they are recovered from
the source `HasTy` derivation for the literal itself.
-/

namespace TypePM

/-! ## Output arities -/

/-- Pointwise expression typing preserves list arity. -/
theorem ExprsTy.length
    {signature : FrozenSig} :
    ∀ {context : Context} {expressions : List Expr} {targets : List Ty},
    ExprsTy signature context expressions targets →
    expressions.length = targets.length := by
  intro context expressions targets typing
  induction expressions generalizing context targets with
  | nil =>
      cases typing
      rfl
  | cons expression expressions ih =>
      cases typing with
      | cons _ tail => simp [ih tail]

/-- Pointwise pattern typing preserves list arity. -/
theorem PatternTys.length
    {signature : FrozenSig} :
    ∀ {context : Context} {parameters : PatternCtx}
      {bindings resultBindings : MonoCtx}
      {patterns : List Pattern} {duals : List Dual},
    PatternTys signature context parameters bindings
      patterns duals resultBindings →
    patterns.length = duals.length := by
  intro context parameters bindings resultBindings patterns duals typing
  induction patterns generalizing context bindings duals with
  | nil =>
      cases typing
      rfl
  | cons pattern patterns ih =>
      cases typing with
      | cons _ tail => simp [ih tail]

/-- A typed clause list contains exactly one evidence tree per clause. -/
theorem ClausesTy.length
    {signature : FrozenSig} :
    ∀ {prevailing : Subst} {context : Context}
      {clauses : List Clause} {capability : Cap} {target : Ty}
      {evidence : List Shape.Evidence},
    ClausesTy signature prevailing context clauses capability target evidence →
    evidence.length = clauses.length := by
  intro prevailing context clauses capability target evidence typing
  induction clauses generalizing prevailing context evidence with
  | nil =>
      cases typing
      rfl
  | cons clause clauses ih =>
      cases typing with
      | cons _ tail => simp [ih tail]

/-- Resolution packaging does not change the clause/evidence arity. -/
theorem ResolvedClausesTy.length
    {signature : FrozenSig} {context : Context}
    {clauses : List Clause} {capability : Cap} {target : Ty}
    {evidence : List Shape.Evidence}
    (typing :
      ResolvedClausesTy signature context clauses capability target evidence) :
    evidence.length = clauses.length := by
  cases typing with
  | ofShared shared => exact shared.length

/-! ## Actual-clause evidence -/

/-- A typed clause's evidence is the result of the concrete checker. -/
theorem ClauseTy.checked
    {signature : FrozenSig} {prevailing : Subst} {context : Context}
    {clause : Clause} {capability : Cap} {target : Ty}
    {evidence : Shape.Evidence}
    (typing :
      ClauseTy signature prevailing context clause capability target evidence) :
    ∃ holes pp next arms ppBindings nextMatchers,
      clause = .mk pp next arms ∧
      ResolvedPPatTy signature prevailing pp target holes ppBindings ∧
      PPatCapsAt signature true pp (holes.map Dual.cap) capability ∧
      decomposeME next holes.length = some nextMatchers ∧
      ExprsTy signature context nextMatchers
        (holes.map fun hole => .slot hole.cap hole.target) ∧
      ArmsTy signature context target ppBindings
        (Ty.listT (prodTy (holes.map Dual.target))) arms ∧
      clauseEvidence signature.toMatcherSig pp (holes.map Dual.cap) =
        some evidence := by
  cases typing with
  | mk hpp hcaps hdecompose hnext harms hcheck =>
      exact
        ⟨_, _, _, _, _, _, rfl, hpp, hcaps, hdecompose, hnext, harms,
          hcheck⟩

/-- The evidence checker consumes exactly the holes exposed by clause typing. -/
theorem ClauseTy.evidence_holeCount
    {signature : FrozenSig} {prevailing : Subst} {context : Context}
    {clause : Clause} {capability : Cap} {target : Ty}
    {evidence : Shape.Evidence}
    (typing :
      ClauseTy signature prevailing context clause capability target evidence) :
    ∃ holes : List Dual,
      (holes.map Dual.cap).length = clause.pp.holeCount := by
  rcases typing.checked with
    ⟨holes, pp, next, arms, ppBindings, nextMatchers,
      rfl, _hpp, _hcaps, _hdecompose, _hnext, _harms, hcheck⟩
  exact ⟨holes, clauseEvidence_holeCount hcheck⟩

/-! ## Coverage is retained by source typing -/

/-- A source-typed matcher literal exposes coverage of its actual clauses. -/
theorem HasTy.matcher_coverage
    {signature : FrozenSig} {context : Context}
    {clauses : List Clause} {capability : Cap} {target : Ty}
    (typing :
      HasTy signature context (.matcher clauses)
        (.matcher capability target)) :
    CoverageOK signature.toMatcherSig clauses capability := by
  exact (typing.matcher_inversion).choose_spec.2.2.2.2.2.2

/-- A source-typed matcher literal has a final catch-all. -/
theorem HasTy.matcher_catchAllLast
    {signature : FrozenSig} {context : Context}
    {clauses : List Clause} {capability : Cap} {target : Ty}
    (typing :
      HasTy signature context (.matcher clauses)
        (.matcher capability target)) :
    CatchAllLast clauses := by
  exact (typing.matcher_inversion).choose_spec.2.2.1

/-- Every source-typed matcher dispatches all required general clauses first. -/
theorem HasTy.matcher_dispatchOK
    {signature : FrozenSig} {context : Context}
    {clauses : List Clause} {capability : Cap} {target : Ty}
    (typing :
      HasTy signature context (.matcher clauses)
        (.matcher capability target)) :
    DispatchOK signature.toMatcherSig clauses capability := by
  exact coverageOK_catchAllLast_dispatchOK _ _ _
    typing.matcher_coverage typing.matcher_catchAllLast

/-- Missing concrete coverage rules out a matcher-literal derivation. -/
theorem noMatcherTyping_of_not_coverage
    {signature : FrozenSig} {context : Context}
    {clauses : List Clause} {capability : Cap} {target : Ty}
    (missing : ¬ CoverageOK signature.toMatcherSig clauses capability) :
    ¬ HasTy signature context (.matcher clauses)
        (.matcher capability target) := by
  intro typing
  exact missing typing.matcher_coverage

/-- The actual evidence list retained by T-MATCHER has source-clause arity. -/
theorem HasTy.matcher_evidence_length
    {signature : FrozenSig} {context : Context}
    {clauses : List Clause} {capability : Cap} {target : Ty}
    (typing :
      HasTy signature context (.matcher clauses)
        (.matcher capability target)) :
    ∃ evidence,
      ResolvedClausesTy signature context clauses capability target evidence ∧
      evidence.length = clauses.length ∧
      Shape.inferShape signature.observability evidence = some capability := by
  rcases typing.matcher_inversion with
    ⟨evidence, hclauses, hshape, _hcatch, _hexhaustive,
      _hppNodup, _harmNodup, _hcoverage⟩
  exact ⟨evidence, hclauses, hclauses.length, hshape⟩

end TypePM
