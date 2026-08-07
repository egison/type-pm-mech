import TypePM.Source

/-!
# Origin-sensitive capability substitutions

Capability variables with the same syntactic shape need not admit the same
post-substitutions.  Variables owned by a frozen signature are rigid, variables
exported by an existing matcher producer may only be renamed, and variables
local to a constructor or primitive instantiation may still be structurally
specialized before that producer is frozen.

This module records that distinction in a finite, first-match ledger.  Variables
absent from the ledger are rigid by default.  A rename-only variable may only be
renamed to a variable that is itself non-structural.  The image condition is
what makes admissibility closed under sequential substitution: a later post can
never structurally expand the intermediate image of a rename-only variable.

The paired-post judgment deliberately leaves the target component unrestricted.
`Subst.seq` already applies a later capability action inside an earlier target
range, while the capability ledger controls exactly which such actions are
allowed.
-/

namespace TypePM

/-- The substitution policy attached to one capability variable. -/
inductive CapabilityOrigin where
  /-- A signature-owned or otherwise rigid variable is fixed pointwise. -/
  | rigid
  /-- An exported producer variable may only be mapped to another frozen variable. -/
  | renameOnly
  /-- A local, not-yet-exported variable may receive an arbitrary capability. -/
  | structuralFlexible
deriving Repr, DecidableEq, BEq

namespace CapabilityOrigin

/-- Freeze one origin, preserving rigid and already rename-only variables. -/
def freeze : CapabilityOrigin → CapabilityOrigin
  | .rigid => .rigid
  | .renameOnly => .renameOnly
  | .structuralFlexible => .renameOnly

/-- Freezing an origin always removes structural flexibility. -/
theorem freeze_ne_structuralFlexible (origin : CapabilityOrigin) :
    origin.freeze ≠ .structuralFlexible := by
  cases origin <;> simp [freeze]

end CapabilityOrigin

/-- A finite, first-match capability-origin ledger. -/
abbrev CapabilityOriginLedger := List (CapVar × CapabilityOrigin)

namespace CapabilityOriginLedger

/-- Look up an origin, treating every unlisted variable as rigid. -/
def originOf : CapabilityOriginLedger → CapVar → CapabilityOrigin
  | [], _ => .rigid
  | (candidate, origin) :: rest, varId =>
      if candidate = varId then origin else originOf rest varId

/-- Override an origin by placing it at the shadowing head of the ledger. -/
def setOrigin
    (ledger : CapabilityOriginLedger) (varId : CapVar)
    (origin : CapabilityOrigin) : CapabilityOriginLedger :=
  (varId, origin) :: ledger

/-- Override one common origin for a finite batch of capability variables. -/
def setOrigins
    (ledger : CapabilityOriginLedger) (varIds : List CapVar)
    (origin : CapabilityOrigin) : CapabilityOriginLedger :=
  match varIds with
  | [] => ledger
  | varId :: rest => (ledger.setOrigins rest origin).setOrigin varId origin

/-- Mark a capability variable as locally structurally flexible. -/
def markStructuralFlexible
    (ledger : CapabilityOriginLedger) (varId : CapVar) :
    CapabilityOriginLedger :=
  ledger.setOrigin varId .structuralFlexible

/-- Freeze one capability variable at the rename-only export boundary. -/
def freezeVar
    (ledger : CapabilityOriginLedger) (varId : CapVar) :
    CapabilityOriginLedger :=
  ledger.setOrigin varId .renameOnly

/-- Freeze every explicitly recorded structurally flexible origin. -/
def freezeAll : CapabilityOriginLedger → CapabilityOriginLedger
  | [] => []
  | (varId, origin) :: rest =>
      (varId, origin.freeze) :: freezeAll rest

@[simp]
theorem originOf_setOrigin_same
    (ledger : CapabilityOriginLedger) (varId : CapVar)
    (origin : CapabilityOrigin) :
    (ledger.setOrigin varId origin).originOf varId = origin := by
  simp [setOrigin, originOf]

@[simp]
theorem originOf_setOrigin_of_ne
    (ledger : CapabilityOriginLedger) (updated queried : CapVar)
    (different : updated ≠ queried) (origin : CapabilityOrigin) :
    (ledger.setOrigin updated origin).originOf queried =
      ledger.originOf queried := by
  simp [setOrigin, originOf, different]

/-- Every member of a batch receives the common overriding origin. -/
theorem originOf_setOrigins_of_mem
    (ledger : CapabilityOriginLedger) (varIds : List CapVar)
    (varId : CapVar) (origin : CapabilityOrigin)
    (membership : varId ∈ varIds) :
    (ledger.setOrigins varIds origin).originOf varId = origin := by
  induction varIds generalizing ledger with
  | nil => contradiction
  | cons head rest inductionHypothesis =>
      simp only [List.mem_cons] at membership
      rcases membership with same | membership
      · subst head
        simp [setOrigins]
      · by_cases same : head = varId
        · subst head
          simp [setOrigins]
        · rw [setOrigins,
            originOf_setOrigin_of_ne _ head varId same]
          exact inductionHypothesis ledger membership

@[simp]
theorem originOf_markStructuralFlexible_same
    (ledger : CapabilityOriginLedger) (varId : CapVar) :
    (ledger.markStructuralFlexible varId).originOf varId =
      .structuralFlexible := by
  simp [markStructuralFlexible]

@[simp]
theorem originOf_markStructuralFlexible_of_ne
    (ledger : CapabilityOriginLedger) (updated queried : CapVar)
    (different : updated ≠ queried) :
    (ledger.markStructuralFlexible updated).originOf queried =
      ledger.originOf queried := by
  simp [markStructuralFlexible, different]

@[simp]
theorem originOf_freezeVar_same
    (ledger : CapabilityOriginLedger) (varId : CapVar) :
    (ledger.freezeVar varId).originOf varId = .renameOnly := by
  simp [freezeVar]

@[simp]
theorem originOf_freezeVar_of_ne
    (ledger : CapabilityOriginLedger) (updated queried : CapVar)
    (different : updated ≠ queried) :
    (ledger.freezeVar updated).originOf queried = ledger.originOf queried := by
  simp [freezeVar, different]

@[simp]
theorem originOf_freezeAll
    (ledger : CapabilityOriginLedger) (varId : CapVar) :
    ledger.freezeAll.originOf varId = (ledger.originOf varId).freeze := by
  induction ledger with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      rcases entry with ⟨candidate, origin⟩
      by_cases same : candidate = varId
      · simp [freezeAll, originOf, same]
      · simp [freezeAll, originOf, same, inductionHypothesis]

/-- A ledger is frozen when it contains no structurally flexible variable. -/
def Frozen (ledger : CapabilityOriginLedger) : Prop :=
  ∀ varId, ledger.originOf varId ≠ .structuralFlexible

/-- Freezing one variable removes structural flexibility at that variable. -/
theorem freezeVar_not_structuralFlexible
    (ledger : CapabilityOriginLedger) (varId : CapVar) :
    (ledger.freezeVar varId).originOf varId ≠ .structuralFlexible := by
  simp

/-- A non-structural override preserves a frozen ledger. -/
theorem Frozen.setOrigin
    {ledger : CapabilityOriginLedger} (frozen : ledger.Frozen)
    (varId : CapVar) (origin : CapabilityOrigin)
    (nonStructural : origin ≠ .structuralFlexible) :
    (ledger.setOrigin varId origin).Frozen := by
  intro queried
  by_cases same : varId = queried
  · subst queried
    simpa using nonStructural
  · rw [originOf_setOrigin_of_ne ledger varId queried same]
    exact frozen queried

/-- Freezing one variable preserves an already frozen ledger. -/
theorem Frozen.freezeVar
    {ledger : CapabilityOriginLedger} (frozen : ledger.Frozen)
    (varId : CapVar) :
    (ledger.freezeVar varId).Frozen := by
  exact frozen.setOrigin varId .renameOnly (by simp)

/-- Freezing the entire ledger produces a frozen ledger. -/
theorem frozen_freezeAll (ledger : CapabilityOriginLedger) :
    ledger.freezeAll.Frozen := by
  intro varId
  rw [originOf_freezeAll]
  exact CapabilityOrigin.freeze_ne_structuralFlexible _

end CapabilityOriginLedger

/--
An origin-sensitive admissible capability post.

The extra origin check on a rename-only image is essential for closure under
composition.  Without it, an earlier post could rename a frozen producer to a
structurally flexible variable and a later post could then expand that image.
-/
def AdmissibleCapPost
    (ledger : CapabilityOriginLedger) (post : CapSubst) : Prop :=
  ∀ varId,
    match ledger.originOf varId with
    | .rigid => post varId = .var varId
    | .renameOnly =>
        ∃ image,
          post varId = .var image ∧
            ledger.originOf image ≠ .structuralFlexible
    | .structuralFlexible => True

/-- Check origin admissibility on an explicit finite support.  Variables
outside `supportVars` are handled by the accompanying `SupportWithin`
certificate, so this traversal is executable despite substitutions being
represented as total functions. -/
def admissibleCapPostCheck
    (ledger : CapabilityOriginLedger) (post : CapSubst)
    (supportVars : List CapVar) : Bool :=
  supportVars.all fun varId =>
    match ledger.originOf varId with
    | .rigid => decide (post varId = .var varId)
    | .renameOnly =>
        match post varId with
        | .var image =>
            decide (ledger.originOf image ≠ .structuralFlexible)
        | _ => false
    | .structuralFlexible => true

/-- A paired post whose capability component respects the origin ledger. -/
structure AdmissiblePost
    (ledger : CapabilityOriginLedger) (post : Subst) : Prop where
  cap : AdmissibleCapPost ledger post.cap

namespace AdmissibleCapPost

/-- The pointwise finite check implies the origin policy at the checked
variable. -/
private theorem checkAt_sound
    {ledger : CapabilityOriginLedger} {post : CapSubst} {varId : CapVar}
    (checked :
      (match ledger.originOf varId with
       | .rigid => decide (post varId = .var varId)
       | .renameOnly =>
           match post varId with
           | .var image =>
               decide (ledger.originOf image ≠ .structuralFlexible)
           | _ => false
       | .structuralFlexible => true) = true) :
    match ledger.originOf varId with
    | .rigid => post varId = .var varId
    | .renameOnly =>
        ∃ image,
          post varId = .var image ∧
            ledger.originOf image ≠ .structuralFlexible
    | .structuralFlexible => True := by
  cases origin : ledger.originOf varId with
  | rigid =>
      simpa [origin] using checked
  | renameOnly =>
      cases imageEquation : post varId with
      | any => simp [origin, imageEquation] at checked
      | var image =>
          have imageSafeCheck :
              decide (ledger.originOf image ≠ .structuralFlexible) = true := by
            simpa [origin, imageEquation] using checked
          exact ⟨image, rfl, of_decide_eq_true imageSafeCheck⟩
      | skolem name => simp [origin, imageEquation] at checked
      | con name children => simp [origin, imageEquation] at checked
      | prod components => simp [origin, imageEquation] at checked
  | structuralFlexible =>
      trivial

/-- Passing the executable check on a certified finite support is sound for
the semantic, whole-substitution admissibility judgment. -/
theorem check_sound
    {ledger : CapabilityOriginLedger} {post : CapSubst}
    {supportVars : List CapVar}
    (support : post.SupportWithin supportVars)
    (checked : admissibleCapPostCheck ledger post supportVars = true) :
    AdmissibleCapPost ledger post := by
  intro varId
  by_cases member : varId ∈ supportVars
  · apply checkAt_sound
    exact (List.all_eq_true.mp checked) varId member
  · have fixed := support varId member
    rw [fixed]
    cases origin : ledger.originOf varId with
    | rigid => rfl
    | renameOnly =>
        exact ⟨varId, rfl, by simp [origin]⟩
    | structuralFlexible => trivial

/-- Eliminate admissibility at a rigid variable. -/
theorem rigid
    {ledger : CapabilityOriginLedger} {post : CapSubst} {varId : CapVar}
    (admissible : AdmissibleCapPost ledger post)
    (origin : ledger.originOf varId = .rigid) :
    post varId = .var varId := by
  simpa [AdmissibleCapPost, origin] using admissible varId

/-- Eliminate admissibility at a rename-only variable. -/
theorem renameOnly
    {ledger : CapabilityOriginLedger} {post : CapSubst} {varId : CapVar}
    (admissible : AdmissibleCapPost ledger post)
    (origin : ledger.originOf varId = .renameOnly) :
    ∃ image,
      post varId = .var image ∧
        ledger.originOf image ≠ .structuralFlexible := by
  simpa [AdmissibleCapPost, origin] using admissible varId

/-- A rename-only variable always has a variable-valued image. -/
theorem renameOnly_variable
    {ledger : CapabilityOriginLedger} {post : CapSubst} {varId : CapVar}
    (admissible : AdmissibleCapPost ledger post)
    (origin : ledger.originOf varId = .renameOnly) :
    ∃ image, post varId = .var image := by
  rcases admissible.renameOnly origin with ⟨image, equation, _safe⟩
  exact ⟨image, equation⟩

/-- Identity respects every origin ledger. -/
theorem id (ledger : CapabilityOriginLedger) :
    AdmissibleCapPost ledger CapSubst.id := by
  intro varId
  cases origin : ledger.originOf varId with
  | rigid => rfl
  | renameOnly =>
      exact ⟨varId, rfl, by simp [origin]⟩
  | structuralFlexible => trivial

/-- Origin-sensitive admissibility is closed under capability composition. -/
theorem comp
    {ledger : CapabilityOriginLedger} {later earlier : CapSubst}
    (laterAdmissible : AdmissibleCapPost ledger later)
    (earlierAdmissible : AdmissibleCapPost ledger earlier) :
    AdmissibleCapPost ledger (CapSubst.comp later earlier) := by
  intro varId
  cases origin : ledger.originOf varId with
  | rigid =>
      have earlierFixed := earlierAdmissible.rigid origin
      have laterFixed := laterAdmissible.rigid origin
      simp [CapSubst.comp, earlierFixed, laterFixed, Cap.apply]
  | renameOnly =>
      rcases earlierAdmissible.renameOnly origin with
        ⟨middle, earlierEquation, middleSafe⟩
      cases middleOrigin : ledger.originOf middle with
      | rigid =>
          have laterEquation := laterAdmissible.rigid middleOrigin
          exact ⟨middle, by
            simp [CapSubst.comp, earlierEquation, laterEquation, Cap.apply],
            by simp [middleOrigin]⟩
      | renameOnly =>
          rcases laterAdmissible.renameOnly middleOrigin with
            ⟨image, laterEquation, imageSafe⟩
          exact ⟨image, by
            simp [CapSubst.comp, earlierEquation, laterEquation, Cap.apply],
            imageSafe⟩
      | structuralFlexible =>
          exact False.elim (middleSafe middleOrigin)
  | structuralFlexible => trivial

/--
Freeze one ledger entry once the current post already gives it an admissible
rename-only image.  Constraints at every other entry are preserved because the
updated origin is non-structural.
-/
theorem freezeVar
    {ledger : CapabilityOriginLedger} {post : CapSubst} {varId : CapVar}
    (admissible : AdmissibleCapPost ledger post)
    (imageAtFrozen :
      ∃ image,
        post varId = .var image ∧
          (ledger.freezeVar varId).originOf image ≠
            .structuralFlexible) :
    AdmissibleCapPost (ledger.freezeVar varId) post := by
  intro queried
  by_cases same : varId = queried
  · subst queried
    simpa only [CapabilityOriginLedger.originOf_freezeVar_same] using
      imageAtFrozen
  · rw [CapabilityOriginLedger.originOf_freezeVar_of_ne
      ledger varId queried same]
    cases origin : ledger.originOf queried with
    | rigid => exact admissible.rigid origin
    | renameOnly =>
        rcases admissible.renameOnly origin with
          ⟨image, equation, imageSafe⟩
        refine ⟨image, equation, ?_⟩
        by_cases imageIsFrozen : varId = image
        · subst image
          simp
        · rw [CapabilityOriginLedger.originOf_freezeVar_of_ne
              ledger varId image imageIsFrozen]
          exact imageSafe
    | structuralFlexible => trivial

/-- Admissibility at a frozen entry exposes its rename-only image. -/
theorem at_freezeVar
    {ledger : CapabilityOriginLedger} {post : CapSubst} {varId : CapVar}
    (admissible : AdmissibleCapPost (ledger.freezeVar varId) post) :
    ∃ image,
      post varId = .var image ∧
        (ledger.freezeVar varId).originOf image ≠ .structuralFlexible := by
  exact admissible.renameOnly (by simp)

/--
Freeze an entire admissible post once every structurally flexible entry has a
variable-valued image.  Every image is safe in the resulting frozen ledger.
-/
theorem freezeAll
    {ledger : CapabilityOriginLedger} {post : CapSubst}
    (admissible : AdmissibleCapPost ledger post)
    (structuralVariable :
      ∀ varId,
        ledger.originOf varId = .structuralFlexible →
          ∃ image, post varId = .var image) :
    AdmissibleCapPost ledger.freezeAll post := by
  intro varId
  rw [CapabilityOriginLedger.originOf_freezeAll]
  cases origin : ledger.originOf varId with
  | rigid => exact admissible.rigid origin
  | renameOnly =>
      rcases admissible.renameOnly origin with ⟨image, equation, _imageSafe⟩
      exact ⟨image, equation,
        CapabilityOriginLedger.frozen_freezeAll ledger image⟩
  | structuralFlexible =>
      rcases structuralVariable varId origin with ⟨image, equation⟩
      exact ⟨image, equation,
        CapabilityOriginLedger.frozen_freezeAll ledger image⟩

/-- On a frozen ledger every admissible capability post is variable-valued. -/
theorem variable_of_frozen
    {ledger : CapabilityOriginLedger} {post : CapSubst}
    (admissible : AdmissibleCapPost ledger post)
    (frozen : ledger.Frozen) :
    ∀ varId, ∃ image, post varId = .var image := by
  intro varId
  cases origin : ledger.originOf varId with
  | rigid => exact ⟨varId, admissible.rigid origin⟩
  | renameOnly => exact admissible.renameOnly_variable origin
  | structuralFlexible => exact False.elim (frozen varId origin)

end AdmissibleCapPost

namespace AdmissiblePost

/-- Paired identity is admissible for every origin ledger. -/
theorem id (ledger : CapabilityOriginLedger) :
    AdmissiblePost ledger Subst.id :=
  { cap := AdmissibleCapPost.id ledger }

/-- Admissible paired posts are closed under cross-sort-aware sequencing. -/
theorem seq
    {ledger : CapabilityOriginLedger} {later earlier : Subst}
    (laterAdmissible : AdmissiblePost ledger later)
    (earlierAdmissible : AdmissiblePost ledger earlier) :
    AdmissiblePost ledger (Subst.seq later earlier) := by
  constructor
  change AdmissibleCapPost ledger
    (CapSubst.comp later.cap earlier.cap)
  exact AdmissibleCapPost.comp laterAdmissible.cap earlierAdmissible.cap

/-- Lift the one-variable freeze bridge to paired substitutions. -/
theorem freezeVar
    {ledger : CapabilityOriginLedger} {post : Subst} {varId : CapVar}
    (admissible : AdmissiblePost ledger post)
    (imageAtFrozen :
      ∃ image,
        post.cap varId = .var image ∧
          (ledger.freezeVar varId).originOf image ≠
            .structuralFlexible) :
    AdmissiblePost (ledger.freezeVar varId) post :=
  { cap := admissible.cap.freezeVar imageAtFrozen }

/-- Lift whole-ledger freezing to paired substitutions. -/
theorem freezeAll
    {ledger : CapabilityOriginLedger} {post : Subst}
    (admissible : AdmissiblePost ledger post)
    (structuralVariable :
      ∀ varId,
        ledger.originOf varId = .structuralFlexible →
          ∃ image, post.cap varId = .var image) :
    AdmissiblePost ledger.freezeAll post :=
  { cap := admissible.cap.freezeAll structuralVariable }

/-- A frozen origin ledger recovers the existing global `VariablePost` boundary. -/
theorem toVariablePost_of_frozen
    {ledger : CapabilityOriginLedger} {post : Subst}
    (admissible : AdmissiblePost ledger post)
    (frozen : ledger.Frozen) :
    VariablePost post :=
  { capVariable := admissible.cap.variable_of_frozen frozen }

/-- Admissibility after whole-ledger freezing meets `VariablePost`. -/
theorem toVariablePost_of_freezeAll
    {ledger : CapabilityOriginLedger} {post : Subst}
    (admissible : AdmissiblePost ledger.freezeAll post) :
    VariablePost post :=
  admissible.toVariablePost_of_frozen
    (CapabilityOriginLedger.frozen_freezeAll ledger)

/--
An admissible post whose flexible entries are already variable-valued can cross
the existing global variable-post boundary by freezing its ledger.
-/
theorem toVariablePost_after_freezeAll
    {ledger : CapabilityOriginLedger} {post : Subst}
    (admissible : AdmissiblePost ledger post)
    (structuralVariable :
      ∀ varId,
        ledger.originOf varId = .structuralFlexible →
          ∃ image, post.cap varId = .var image) :
    VariablePost post :=
  (admissible.freezeAll structuralVariable).toVariablePost_of_freezeAll

end AdmissiblePost

/-! ## Two-phase constructor posts -/

/--
A constructor-local structural phase followed by a frozen export phase.

Keeping the two substitutions as separate fields prevents the local structural
instantiation from being mistaken for one global `VariablePost`.  Only the
residual phase is judged against the fully frozen ledger.
-/
structure PhasedPost
    (ledger : CapabilityOriginLedger) (total : Subst) where
  localPost : Subst
  residualPost : Subst
  localAdmissible : AdmissiblePost ledger localPost
  residualAdmissible : AdmissiblePost ledger.freezeAll residualPost
  totalEquation : total = Subst.seq residualPost localPost

namespace PhasedPost

/-- Extensional equality for the two components of a paired substitution. -/
theorem subst_ext
    {left right : Subst}
    (capEquation : left.cap = right.cap)
    (targetEquation : left.target = right.target) :
    left = right := by
  cases left with
  | mk leftCap leftTarget =>
      cases right with
      | mk rightCap rightTarget =>
          cases capEquation
          cases targetEquation
          rfl

/-- Sequential paired substitution is associative. -/
theorem seq_assoc (latest middle earliest : Subst) :
    Subst.seq latest (Subst.seq middle earliest) =
      Subst.seq (Subst.seq latest middle) earliest := by
  apply subst_ext
  · funext varId
    change
      ((earliest.cap varId).apply middle.cap).apply latest.cap =
        (earliest.cap varId).apply
          (CapSubst.comp latest.cap middle.cap)
    exact (Cap.apply_comp latest.cap middle.cap (earliest.cap varId)).symm
  · funext varId
    change
      latest.apply (middle.apply (earliest.target varId)) =
        (Subst.seq latest middle).apply (earliest.target varId)
    exact (Subst.seq_apply latest middle (earliest.target varId)).symm

/-- The stored total acts by the local phase and then the residual phase. -/
theorem total_apply
    {ledger : CapabilityOriginLedger} {total : Subst}
    (phased : PhasedPost ledger total) (target : Ty) :
    total.apply target =
      phased.residualPost.apply (phased.localPost.apply target) := by
  calc
    total.apply target =
        (Subst.seq phased.residualPost phased.localPost).apply target :=
      congrArg (fun post => post.apply target) phased.totalEquation
    _ = phased.residualPost.apply (phased.localPost.apply target) :=
      Subst.seq_apply phased.residualPost phased.localPost target

/-- Capability application follows the same local-then-residual order. -/
theorem total_apply_cap
    {ledger : CapabilityOriginLedger} {total : Subst}
    (phased : PhasedPost ledger total) (capability : Cap) :
    capability.apply total.cap =
      (capability.apply phased.localPost.cap).apply
        phased.residualPost.cap := by
  calc
    capability.apply total.cap =
        capability.apply
          (Subst.seq phased.residualPost phased.localPost).cap :=
      congrArg (fun post => capability.apply post.cap) phased.totalEquation
    _ = (capability.apply phased.localPost.cap).apply
          phased.residualPost.cap :=
      Cap.apply_comp phased.residualPost.cap phased.localPost.cap capability

/-- The completely inactive two-phase post. -/
def id (ledger : CapabilityOriginLedger) :
    PhasedPost ledger Subst.id where
  localPost := Subst.id
  residualPost := Subst.id
  localAdmissible := AdmissiblePost.id ledger
  residualAdmissible := AdmissiblePost.id ledger.freezeAll
  totalEquation := by
    apply subst_ext
    · funext varId
      rfl
    · funext varId
      rfl

/-- Only the residual/export phase must satisfy the global variable boundary. -/
theorem residualVariable
    {ledger : CapabilityOriginLedger} {total : Subst}
    (phased : PhasedPost ledger total) :
    VariablePost phased.residualPost := by
  exact AdmissiblePost.toVariablePost_of_freezeAll
    (ledger := ledger) phased.residualAdmissible

/--
Append one more frozen residual action.  The local structural phase is retained,
while residual admissibility is closed by `AdmissiblePost.seq`.
-/
def seqResidual
    {ledger : CapabilityOriginLedger} {total : Subst}
    (phased : PhasedPost ledger total) (later : Subst)
    (laterAdmissible : AdmissiblePost ledger.freezeAll later) :
    PhasedPost ledger (Subst.seq later total) where
  localPost := phased.localPost
  residualPost := Subst.seq later phased.residualPost
  localAdmissible := phased.localAdmissible
  residualAdmissible :=
    AdmissiblePost.seq laterAdmissible phased.residualAdmissible
  totalEquation := by
    calc
      Subst.seq later total =
          Subst.seq later
            (Subst.seq phased.residualPost phased.localPost) :=
        congrArg (fun earlier => Subst.seq later earlier)
          phased.totalEquation
      _ = Subst.seq (Subst.seq later phased.residualPost)
            phased.localPost :=
        seq_assoc later phased.residualPost phased.localPost

/-- The extended residual remains a `VariablePost`. -/
theorem seqResidual_residualVariable
    {ledger : CapabilityOriginLedger} {total later : Subst}
    (phased : PhasedPost ledger total)
    (laterAdmissible : AdmissiblePost ledger.freezeAll later) :
    VariablePost (phased.seqResidual later laterAdmissible).residualPost :=
  (phased.seqResidual later laterAdmissible).residualVariable

end PhasedPost

/-! ## Minimal ledger regressions -/

namespace CapabilityOriginRegression

def sampleLedger : CapabilityOriginLedger :=
  [(0, .renameOnly), (1, .structuralFlexible)]

def renameZeroToOne : CapSubst :=
  fun varId => if varId = (0 : CapVar) then .var 1 else .var varId

def renameZeroToOnePost : Subst :=
  .mk renameZeroToOne TySubst.id

/-- A rename-only producer cannot be redirected to a still-flexible local
variable, since a later post could then strengthen it structurally. -/
theorem renameOnly_to_structuralFlexible_rejected :
    ¬ AdmissibleCapPost sampleLedger renameZeroToOne := by
  intro admissible
  have atZero := admissible (0 : CapVar)
  simp [sampleLedger, CapabilityOriginLedger.originOf,
    renameZeroToOne] at atZero
  exact (by decide : (0 : CapVar) ≠ (1 : CapVar)) atZero

/-- Once the local ledger is frozen, the same variable rename is admissible
and crosses the legacy global `VariablePost` boundary. -/
theorem rename_after_freezeAll_variable :
    VariablePost renameZeroToOnePost := by
  have admissible :
      AdmissiblePost sampleLedger.freezeAll renameZeroToOnePost := by
    constructor
    intro varId
    by_cases zero : varId = (0 : CapVar)
    · subst varId
      exact ⟨1, by simp [renameZeroToOnePost, renameZeroToOne], by
        simp [sampleLedger, CapabilityOriginLedger.originOf,
          CapabilityOriginLedger.freezeAll, CapabilityOrigin.freeze]⟩
    · by_cases one : varId = (1 : CapVar)
      · subst varId
        exact ⟨1, by simp [renameZeroToOnePost, renameZeroToOne], by
          simp [sampleLedger, CapabilityOriginLedger.originOf,
            CapabilityOriginLedger.freezeAll, CapabilityOrigin.freeze]⟩
      · have zero' : (0 : CapVar) ≠ varId := Ne.symm zero
        have one' : (1 : CapVar) ≠ varId := Ne.symm one
        simp [sampleLedger, CapabilityOriginLedger.originOf,
          CapabilityOriginLedger.freezeAll, CapabilityOrigin.freeze,
          renameZeroToOnePost, renameZeroToOne, zero, zero', one']
  exact admissible.toVariablePost_of_freezeAll

end CapabilityOriginRegression

end TypePM
