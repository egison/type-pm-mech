import TypePM.DemandTypingInferenceCompletenessValidatorAudit
import TypePM.DemandTypingInferenceCompletenessContextBisimulation
import TypePM.SourceSubstitution

/-!
# Equivariance of terminal-audit facts

The DD terminal substitution and the executable terminal prevailing
substitution are mutually factoring solved forms, but need not be literally
equal.  This module isolates the semantic reason that the three terminal
audits can nevertheless be consumed by the executable validator:

* pattern-constructor compatibility and matcher finalization are covariant
  under a variable-valued capability post;
* let stability is transported by the normalized-scheme and canonical-
  generalization bisimulations already maintained by completeness.

The lemmas here mention neither an inference-success oracle nor a typing
derivation.  They are algebraic transport boundaries for the final
completeness composition.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessValidatorEquivariance

open Inference
open DemandTypingInferenceCompletenessStateMutual
open DemandTypingInferenceCompletenessContextBisimulation
open DemandTypingInferenceCompletenessLocalRenaming
open DemandTypingInferenceCompletenessGeneralizationEquivariance

/-! ## Capability-normalization algebra -/

/-- The total pure representative of a scoped two-sort renaming is globally
variable-valued in the capability sort. -/
noncomputable def LocalRenamingOn.pureVariablePost
    {forward reverse : Subst} {capScope : List CapVar}
    {targetScope : List TypePM.TyVar}
    (certificate : LocalRenamingOn forward reverse capScope targetScope) :
    VariablePost
      (DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.pureSubst
        certificate) where
  capVariable := fun varId => ⟨certificate.capImage varId, rfl⟩

/-- Terminal primitive-hole normalization commutes with a later
capability-variable post. -/
theorem terminalHoleCaps_seq
    (post terminal : Subst) (rawHoleLists : List (List Dual)) :
    terminalHoleCaps (Subst.seq post terminal) rawHoleLists =
      (terminalHoleCaps terminal rawHoleLists).map
        (Cap.applyList post.cap) := by
  simp only [terminalHoleCaps, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro holes _membership
  rw [Cap.applyList_eq_map]
  rw [List.map_map]
  apply List.map_congr_left
  intro dual _dualMembership
  rw [Dual.applySubst_seq]
  cases dual
  rfl

/-- Collected actual-clause evidence is covariant under a pointwise
capability renaming. -/
theorem collectClauseEvidence_applyRen_of_success
    (rename : CapVar → CapVar) (signature : FrozenMatcherSig) :
    ∀ {clauses : List Clause} {holeLists : List (List Cap)}
      {evidence : List Shape.Evidence},
      collectClauseEvidence signature clauses holeLists = some evidence →
      collectClauseEvidence signature clauses
          (holeLists.map (Cap.applyRenList rename)) =
        some (Shape.Evidence.applyRenList rename evidence) := by
  intro clauses holeLists evidence success
  induction clauses generalizing holeLists evidence with
  | nil =>
      cases holeLists <;> simp [collectClauseEvidence] at success ⊢
      subst evidence
      rfl
  | cons clause clauses induction =>
      cases holeLists with
      | nil => simp [collectClauseEvidence] at success
      | cons holes holeLists =>
          cases headEq : clauseEvidence signature clause.pp holes with
          | none => simp [collectClauseEvidence, headEq] at success
          | some head =>
              cases tailEq : collectClauseEvidence signature clauses holeLists with
              | none =>
                  simp [collectClauseEvidence, headEq, tailEq] at success
              | some tail =>
                  have equality : head :: tail = evidence := by
                    simpa [collectClauseEvidence, headEq, tailEq] using success
                  subst evidence
                  have renamedHead := clauseEvidence_applyRen_of_success
                    rename headEq
                  have renamedTail := induction tailEq
                  simp [collectClauseEvidence, renamedHead, renamedTail,
                    Shape.Evidence.applyRenList]

/-- Mapping every finite-choice candidate maps every generated choice. -/
theorem Cap.mem_applyRenList
    (rename : CapVar → CapVar) {capability : Cap} :
    ∀ {capabilities : List Cap}, capability ∈ capabilities →
      capability.applyRen rename ∈ Cap.applyRenList rename capabilities
  | [], membership => nomatch membership
  | head :: tail, membership => by
      simp only [List.mem_cons] at membership
      simp only [Cap.applyRenList, List.mem_cons]
      exact membership.elim (fun equal => Or.inl (congrArg (Cap.applyRen rename) equal))
        (Or.inr ∘ Cap.mem_applyRenList rename)

theorem Cap.applyRenList_take
    (rename : CapVar → CapVar) (count : Nat) :
    ∀ capabilities : List Cap,
      (Cap.applyRenList rename capabilities).take count =
        Cap.applyRenList rename (capabilities.take count)
  | [] => by simp [Cap.applyRenList]
  | head :: tail => by
      cases count with
      | zero => rfl
      | succ count =>
          simp only [Cap.applyRenList, List.take_succ_cons, List.cons.injEq]
          exact ⟨trivial, Cap.applyRenList_take rename count tail⟩

theorem Cap.applyRenList_drop
    (rename : CapVar → CapVar) (count : Nat) :
    ∀ capabilities : List Cap,
      (Cap.applyRenList rename capabilities).drop count =
        Cap.applyRenList rename (capabilities.drop count)
  | [] => by simp [Cap.applyRenList]
  | head :: tail => by
      cases count with
      | zero => rfl
      | succ count => exact Cap.applyRenList_drop rename count tail

theorem mem_capChoices_map
    (rename : CapVar → CapVar) {candidates : List Cap} {count : Nat}
    {choice : List Cap}
    (membership : choice ∈ capChoices candidates count) :
    Cap.applyRenList rename choice ∈
      capChoices (Cap.applyRenList rename candidates) count := by
  induction count generalizing choice with
  | zero =>
      simp [capChoices] at membership ⊢
      subst choice
      rfl
  | succ count induction =>
      simp only [capChoices] at membership ⊢
      rcases List.mem_flatMap.mp membership with
        ⟨capability, capabilityMem, restMem⟩
      rcases List.mem_map.mp restMem with ⟨rest, restChoice, rfl⟩
      apply List.mem_flatMap.mpr
      refine ⟨capability.applyRen rename,
        ?_, ?_⟩
      · exact Cap.mem_applyRenList rename capabilityMem
      exact List.mem_map.mpr
        ⟨Cap.applyRenList rename rest, induction restChoice, rfl⟩

mutual

/-- A successful primitive-pattern capability check remains successful after
pointwise capability renaming. -/
theorem ppatCapsAtCheck_applyRen_of_success
    (rename : CapVar → CapVar) (signature : FrozenSig) :
    ∀ (atRoot : Bool) (pattern : PPat) (holes : List Cap) (outer : Cap),
      ppatCapsAtCheck signature atRoot pattern holes outer = true →
      ppatCapsAtCheck signature atRoot pattern
        (Cap.applyRenList rename holes) (outer.applyRen rename) = true
  | false, .hole, holes, outer, checked => by
      cases holes with
      | nil => simp [ppatCapsAtCheck] at checked
      | cons hole rest =>
          cases rest with
          | cons another more => simp [ppatCapsAtCheck] at checked
          | nil =>
              have equal : hole = outer := by
                exact of_decide_eq_true (by
                  simpa [ppatCapsAtCheck] using checked)
              subst outer
              simp [ppatCapsAtCheck, Cap.applyRenList]
  | true, .hole, holes, outer, checked => by
      cases holes with
      | nil => simp [ppatCapsAtCheck] at checked
      | cons hole rest =>
          cases rest with
          | cons another more => simp [ppatCapsAtCheck] at checked
          | nil => simp [ppatCapsAtCheck, Cap.applyRenList]
  | atRoot, .wild, holes, outer, checked => by
      have empty : holes = [] := by
        exact of_decide_eq_true (by simpa [ppatCapsAtCheck] using checked)
      subst holes
      simp [ppatCapsAtCheck, Cap.applyRenList]
  | atRoot, .pval name, holes, outer, checked => by
      have empty : holes = [] := by
        exact of_decide_eq_true (by simpa [ppatCapsAtCheck] using checked)
      subst holes
      simp [ppatCapsAtCheck, Cap.applyRenList]
  | atRoot, .ctor name patterns, holes, outer, checked => by
      simp only [ppatCapsAtCheck] at checked ⊢
      split at checked
      · contradiction
      · rename_i entry lookup
        rcases List.any_eq_true.mp checked with
          ⟨children, choiceMem, childChecked⟩
        simp only [Bool.and_eq_true] at childChecked
        apply List.any_eq_true.mpr
        refine ⟨Cap.applyRenList rename children, ?_, ?_⟩
        · have mapped := mem_capChoices_map rename choiceMem
          simpa [Cap.applyRenList, Cap.applyRen] using mapped
        · rw [Bool.and_eq_true]
          exact ⟨ppatCapsListCheck_applyRen_of_success rename signature
              patterns holes children childChecked.1,
            capCompatibleCheck_complete
              ((capCompatibleCheck_sound childChecked.2).applyRen rename)⟩
  | atRoot, .tuple patterns, holes, outer, checked => by
      cases outer <;> try simp [ppatCapsAtCheck] at checked
      case prod children =>
        simpa [ppatCapsAtCheck, Cap.applyRen] using
          ppatCapsListCheck_applyRen_of_success rename signature patterns holes
            children checked

/-- List-form covariance of the primitive-pattern capability checker. -/
theorem ppatCapsListCheck_applyRen_of_success
    (rename : CapVar → CapVar) (signature : FrozenSig) :
    ∀ (patterns : List PPat) (holes children : List Cap),
      ppatCapsListCheck signature patterns holes children = true →
      ppatCapsListCheck signature patterns (Cap.applyRenList rename holes)
        (Cap.applyRenList rename children) = true
  | [], holes, children, checked => by
      simp only [ppatCapsListCheck, Bool.and_eq_true,
        decide_eq_true_eq] at checked ⊢
      rcases checked with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  | pattern :: patterns, holes, child :: children, checked => by
      simp only [ppatCapsListCheck, Bool.and_eq_true, Cap.applyRenList]
        at checked ⊢
      rw [Cap.applyRenList_take, Cap.applyRenList_drop]
      exact ⟨ppatCapsAtCheck_applyRen_of_success rename signature false pattern
          (holes.take pattern.holeCount) child checked.1,
        ppatCapsListCheck_applyRen_of_success rename signature patterns
          (holes.drop pattern.holeCount) children checked.2⟩
  | _ :: _, _, [], checked => by simp [ppatCapsListCheck] at checked

end

/-- The full clause-capability validator fold is covariant under pointwise
capability renaming. -/
theorem clauseCapsListCheck_applyRen_of_success
    (rename : CapVar → CapVar) (signature : FrozenSig) :
    ∀ {clauses : List Clause} {holeLists : List (List Cap)} {capability : Cap},
      clauseCapsListCheck signature capability clauses holeLists = true →
      clauseCapsListCheck signature (capability.applyRen rename) clauses
        (holeLists.map (Cap.applyRenList rename)) = true
  | [], [], capability, _ => rfl
  | clause :: clauses, holes :: holeLists, capability, checked => by
      simp only [clauseCapsListCheck, Bool.and_eq_true, List.map_cons]
        at checked ⊢
      exact ⟨ppatCapsAtCheck_applyRen_of_success rename signature true clause.pp
          holes capability checked.1,
        clauseCapsListCheck_applyRen_of_success rename signature checked.2⟩
  | [], _ :: _, _, checked
  | _ :: _, [], _, checked => by simp [clauseCapsListCheck] at checked

/-- Source-order clause capability alignment is covariant under every
variable-valued capability post. -/
theorem ClauseCapsList.transport
    {signature : FrozenSig} {post : Subst}
    (postVariable : VariablePost post) :
    ∀ {clauses : List Clause} {holeLists : List (List Cap)} {capability : Cap},
      ClauseCapsList signature clauses holeLists capability →
      ClauseCapsList signature clauses
        (holeLists.map (Cap.applyList post.cap))
        (capability.apply post.cap) := by
  intro clauses holeLists capability typing
  induction typing with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons (PPatCapsAt.transport postVariable head) induction

/-- The executable arm checker is complete for the extensionally identical
`ArmExhaustive` predicate. -/
theorem armExhaustiveCheck_complete
    {signature : FrozenSig} {clauses : List Clause} {target : Ty}
    (exhaustive : ArmExhaustive signature clauses target) :
    armExhaustiveCheck signature clauses target = true := by
  exact List.all_eq_true.mpr exhaustive

/-! ## Pattern-constructor audit transport -/

/-- A pattern-constructor terminal fact survives a variable-valued
capability suffix. -/
theorem DDTerminalAudit.PatternCtorFacts.transportVariablePost
    {terminal post : Subst} (postVariable : VariablePost post)
    {observable : Shape.Observability}
    {entry : PatternCtorScheme observable} {duals : List Dual}
    {capability : Cap}
    (facts : DDTerminalAudit.PatternCtorFacts terminal entry duals capability) :
    DDTerminalAudit.PatternCtorFacts (Subst.seq post terminal) entry duals
      capability := by
  constructor
  have renamed := facts.compatible.applyRen postVariable.capRen
  rw [← postVariable.applyCapList_eq_applyRenList,
    ← postVariable.applyCap_eq_applyRen] at renamed
  change entry.CapCompatible
    ((duals.map (Dual.applySubst (Subst.seq post terminal))).map Dual.cap)
    (capability.apply (CapSubst.comp post.cap terminal.cap))
  rw [Dual.map_applySubst_seq, Dual.map_cap_applySubst, Cap.apply_comp]
  exact renamed

/-- Scoped-renaming specialization using its total pure representative. -/
theorem DDTerminalAudit.PatternCtorFacts.transportLocalRenaming
    {terminal forward reverse : Subst} {capScope : List CapVar}
    {targetScope : List TypePM.TyVar}
    (certificate : LocalRenamingOn forward reverse capScope targetScope)
    {observable : Shape.Observability}
    {entry : PatternCtorScheme observable} {duals : List Dual}
    {capability : Cap}
    (facts : DDTerminalAudit.PatternCtorFacts terminal entry duals capability) :
    DDTerminalAudit.PatternCtorFacts
      (Subst.seq
        (DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.pureSubst
          certificate) terminal) entry duals capability :=
  TypePM.DemandTypingInferenceCompletenessValidatorEquivariance.DDTerminalAudit.PatternCtorFacts.transportVariablePost
    (LocalRenamingOn.pureVariablePost certificate) facts

/-! ## Matcher audit transport -/

/-- Every matcher terminal fact survives a variable-valued capability suffix
when the frozen signature uses the target-insensitive core arm checker. -/
theorem DDTerminalAudit.MatcherFacts.transportVariablePost
    {terminal post : Subst} (postVariable : VariablePost post)
    {signature : FrozenSig}
    (armBasic : signature.armExhaustive = basicArmExhaustive)
    {clauses : List Clause} {rawHoleLists : List (List Dual)}
    {rawCapability : Cap} {rawTarget : Ty}
    (facts : DDTerminalAudit.MatcherFacts terminal signature clauses
      rawHoleLists rawCapability rawTarget) :
    DDTerminalAudit.MatcherFacts (Subst.seq post terminal) signature clauses
      rawHoleLists rawCapability rawTarget := by
  rcases facts.valid with
    ⟨evidence, collected, inferred, clauseCaps, arms, coverage⟩
  let oldHoles := terminalHoleCaps terminal rawHoleLists
  let newHoles := terminalHoleCaps (Subst.seq post terminal) rawHoleLists
  have holesEq : newHoles = oldHoles.map (Cap.applyList post.cap) := by
    simpa [newHoles, oldHoles] using
      terminalHoleCaps_seq post terminal rawHoleLists
  have holesRen : oldHoles.map (Cap.applyList post.cap) =
      oldHoles.map (Cap.applyRenList postVariable.capRen) := by
    apply List.map_congr_left
    intro holes _membership
    exact postVariable.applyCapList_eq_applyRenList holes
  have collected' : collectClauseEvidence signature.toMatcherSig clauses
      newHoles = some (Shape.Evidence.applyRenList postVariable.capRen evidence) := by
    rw [holesEq, holesRen]
    exact collectClauseEvidence_applyRen_of_success
      postVariable.capRen signature.toMatcherSig collected
  have inferred' : Shape.inferShape signature.observability
      (Shape.Evidence.applyRenList postVariable.capRen evidence) =
      some (rawCapability.apply (Subst.seq post terminal).cap) := by
    have moved := Shape.inferShape_applyRen_of_success postVariable.capRen
      signature.observability inferred
    rw [← postVariable.applyCap_eq_applyRen] at moved
    change _ = some
      (rawCapability.apply (CapSubst.comp post.cap terminal.cap))
    rw [Cap.apply_comp]
    exact moved
  have clauseCapsMoved := clauseCapsListCheck_applyRen_of_success
    postVariable.capRen signature clauseCaps
  have clauseCaps' : clauseCapsListCheck signature
      (rawCapability.apply (Subst.seq post terminal).cap) clauses newHoles = true := by
    rw [holesEq, holesRen]
    change clauseCapsListCheck signature
      (rawCapability.apply (CapSubst.comp post.cap terminal.cap)) clauses
        (oldHoles.map (Cap.applyRenList postVariable.capRen)) = true
    rw [Cap.apply_comp, postVariable.applyCap_eq_applyRen]
    exact clauseCapsMoved
  have exhaustive := armExhaustiveCheck_sound arms
  have exhaustive' := exhaustive.transport_basic armBasic
    (resultTarget := (Subst.seq post terminal).apply rawTarget)
  have arms' : armExhaustiveCheck signature clauses
      ((Subst.seq post terminal).apply rawTarget) = true := by
    exact armExhaustiveCheck_complete exhaustive'
  have coverageTyping := coverageCheck_sound coverage
  have coverageMoved := coverageTyping.applyRen postVariable.capRen
  rw [← postVariable.applyCap_eq_applyRen] at coverageMoved
  have coverage' : coverageCheck signature.toMatcherSig clauses
      (rawCapability.apply (Subst.seq post terminal).cap) = true := by
    apply coverageCheck_complete
    change CoverageOK signature.toMatcherSig clauses
      (rawCapability.apply (CapSubst.comp post.cap terminal.cap))
    rw [Cap.apply_comp]
    exact coverageMoved
  exact ⟨Shape.Evidence.applyRenList postVariable.capRen evidence,
    by simpa [newHoles] using collected', inferred',
    clauseCaps', arms', coverage'⟩

/-- Scoped-renaming specialization of complete matcher-finalization
equivariance. -/
theorem DDTerminalAudit.MatcherFacts.transportLocalRenaming
    {terminal forward reverse : Subst} {capScope : List CapVar}
    {targetScope : List TypePM.TyVar}
    (certificate : LocalRenamingOn forward reverse capScope targetScope)
    {signature : FrozenSig}
    (armBasic : signature.armExhaustive = basicArmExhaustive)
    {clauses : List Clause} {rawHoleLists : List (List Dual)}
    {rawCapability : Cap} {rawTarget : Ty}
    (facts : DDTerminalAudit.MatcherFacts terminal signature clauses
      rawHoleLists rawCapability rawTarget) :
    DDTerminalAudit.MatcherFacts
      (Subst.seq
        (DemandTypingInferenceCompletenessGeneralizationEquivariance.LocalRenamingOn.pureSubst
          certificate) terminal) signature clauses rawHoleLists
      rawCapability rawTarget :=
  TypePM.DemandTypingInferenceCompletenessValidatorEquivariance.DDTerminalAudit.MatcherFacts.transportVariablePost
    (LocalRenamingOn.pureVariablePost certificate) armBasic facts

/-! ## Let-audit elimination through scheme bisimulation -/

/-- Let stability does not require equality of terminal substitutions.  A
normalized correspondence for the locally generalized scheme and the
canonical final generalization correspondence are exactly sufficient. -/
theorem DDTerminalAudit.LetFacts.stable_of_bisimulation
    {terminal : Subst} {signature : FrozenSig} {rawContext : Context}
    {rawTarget : Ty} {valueSubst : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    {relation : StateBisimulation ledger terminal state}
    {executableLocal executableFinal : Scheme}
    (facts : DDTerminalAudit.LetFacts terminal signature rawContext rawTarget
      valueSubst)
    (localSchemes : NormalizedSchemeBisimulation relation
      (signature.generalize (rawContext.applySubst valueSubst)
        (valueSubst.apply rawTarget)) executableLocal)
    (final : GeneralizationBisimulation relation
      (signature.generalize (rawContext.applySubst terminal)
        (terminal.apply rawTarget)) executableFinal) :
    executableLocal.applyMeta state.prevailing = executableFinal := by
  calc
    executableLocal.applyMeta state.prevailing =
        ((signature.generalize (rawContext.applySubst valueSubst)
          (valueSubst.apply rawTarget)).applyMeta terminal).applyMeta
            relation.reverse := localSchemes.reverse
    _ = (signature.generalize (rawContext.applySubst terminal)
          (terminal.apply rawTarget)).applyMeta relation.reverse := by
        rw [facts.stable]
    _ = executableFinal := final.reverse.symm

/-- Common same-source-context specialization: mutual state correspondence,
signature closedness, and raw-target correspondence construct the final
generalization transport internally. -/
theorem DDTerminalAudit.LetFacts.stable_of_sameContext
    {terminal : Subst} {signature : FrozenSig} {rawContext : Context}
    {declarativeTarget executableTarget : Ty} {valueSubst : Subst}
    {ledger : CapabilityOriginLedger} {state : InferState}
    {relation : StateBisimulation ledger terminal state}
    {executableLocal : Scheme}
    (facts : DDTerminalAudit.LetFacts terminal signature rawContext
      declarativeTarget valueSubst)
    (signatureClosed : signature.SchemesClosed)
    (targets : TyBisimulation relation declarativeTarget executableTarget)
    (localSchemes : NormalizedSchemeBisimulation relation
      (signature.generalize (rawContext.applySubst valueSubst)
        (valueSubst.apply declarativeTarget)) executableLocal) :
    executableLocal.applyMeta state.prevailing =
      signature.generalize (rawContext.applySubst state.prevailing)
        (state.prevailing.apply executableTarget) := by
  apply DDTerminalAudit.LetFacts.stable_of_bisimulation facts localSchemes
  exact GeneralizationBisimulation.ofBisimulation
    (ContextBisimulation.same relation rawContext) signature signatureClosed
    targets

end DemandTypingInferenceCompletenessValidatorEquivariance
end TypePM
