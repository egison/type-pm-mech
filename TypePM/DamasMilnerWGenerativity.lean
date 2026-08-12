import TypePM.DamasMilnerWGenerativeTransport

/-!
# A finite stack of local generativity obligations

Nested W constructors protect control metavariables across recursive calls.
Each entry remembers the supply and raw context at one enclosing expression.
The frame says that every target on the shared continuation frontier is
old-free at every remembered entry.  Exact ordinary cuts transport the whole
finite stack pointwise.
-/

namespace TypePM
namespace DM

/-- A local generativity obligation protects only the explicitly registered
raw-coordinate tokens.  In particular it never quantifies over the ambient
continuation frontier, whose older entries need not be owned by this local
context. -/
structure GenerativitySurfaceObligation : Type where
  floor : InferenceBase.FreshSupply
  owner : Context
  /-- Paired continuation entries.  These satisfy the retained disjunction
  and executable-frontier membership, but need not be old-free. -/
  continuation : List (Ty × STy)
  /-- Constructor control metavariables.  These are old-free at the owner but
  need not satisfy the retained disjunction at an older floor. -/
  protectedOld : List Ty := []

def GenerativitySurfaceFrameAt
    (obligations : List GenerativitySurfaceObligation)
    (current : Subst) : Prop :=
  ∀ obligation ∈ obligations, ∀ raw ∈ obligation.protectedOld,
    OldFreeInContextAt obligation.floor
      (obligation.owner.applySubst current) (current.apply raw)

/-- Every protected paired token remains on the continuation surface, with
its raw coordinate evolved by the current substitution. -/
def GenerativitySurfaceMembersAt
    (obligations : List GenerativitySurfaceObligation)
    (current : Subst) (frontier : List (Ty × STy)) : Prop :=
  ∀ obligation ∈ obligations, ∀ pair ∈ obligation.continuation,
    (current.apply pair.1, pair.2) ∈ frontier

/-- A protected surface retains the let-registration disjunction at the
entry represented by its owning obligation. -/
def GenerativitySurfaceRetainedAt
    (obligations : List GenerativitySurfaceObligation)
    (current : Subst) : Prop :=
  ∀ obligation ∈ obligations,
    RetainedOldOrContextAt obligation.floor
      (obligation.owner.applySubst current) current obligation.continuation

def GenerativitySurfaceContextsAt
    (obligations : List GenerativitySurfaceObligation)
    (current : Subst) (active : Context) : Prop :=
  ∀ obligation ∈ obligations,
    OldContextCoveredAt obligation.floor
      (obligation.owner.applySubst current) active

def GenerativitySurfaceValid (supply : InferenceBase.FreshSupply)
    (rawContext : Context)
    (obligations : List GenerativitySurfaceObligation) : Prop :=
  ∀ obligation ∈ obligations,
    SupplyExtends obligation.floor supply ∧
      ProvenanceContextSuffix obligation.owner rawContext

def GenerativitySurfaceObligation.current
    (supply : InferenceBase.FreshSupply) (owner : Context)
    (surface : List Ty := []) : GenerativitySurfaceObligation :=
  ⟨supply, owner, [], surface⟩

/-- Sound paired entry constructor used by the final mutual completeness
driver. -/
def GenerativitySurfaceObligation.currentPaired
    (supply : InferenceBase.FreshSupply) (owner : Context)
    (surface : List (Ty × STy)) : GenerativitySurfaceObligation :=
  ⟨supply, owner, surface, []⟩

def GenerativitySurfaceObligation.protectPair (pair : Ty × STy)
    (obligation : GenerativitySurfaceObligation) :
    GenerativitySurfaceObligation :=
  { obligation with continuation := pair :: obligation.continuation }

def GenerativitySurfaceObligations.protectPair (pair : Ty × STy)
    (obligations : List GenerativitySurfaceObligation) :
    List GenerativitySurfaceObligation :=
  obligations.map (GenerativitySurfaceObligation.protectPair pair)

theorem GenerativitySurfaceFrameAt.nil (current : Subst) :
    GenerativitySurfaceFrameAt [] current := by
  simp [GenerativitySurfaceFrameAt]

theorem GenerativitySurfaceMembersAt.nil (current : Subst)
    (frontier : List (Ty × STy)) :
    GenerativitySurfaceMembersAt [] current frontier := by
  simp [GenerativitySurfaceMembersAt]

theorem GenerativitySurfaceRetainedAt.nil (current : Subst) :
    GenerativitySurfaceRetainedAt [] current := by
  simp [GenerativitySurfaceRetainedAt]

theorem GenerativitySurfaceRetainedAt.registerCurrent
    {obligations : List GenerativitySurfaceObligation} {current : Subst}
    {supply : InferenceBase.FreshSupply} {owner : Context}
    {surface : List (Ty × STy)}
    (head : RetainedOldOrContextAt supply (owner.applySubst current)
      current surface)
    (tail : GenerativitySurfaceRetainedAt obligations current) :
    GenerativitySurfaceRetainedAt
      (GenerativitySurfaceObligation.currentPaired supply owner surface ::
        obligations) current := by
  intro obligation member
  rcases List.mem_cons.mp member with rfl | old
  · exact head
  · exact tail obligation old

theorem GenerativitySurfaceMembersAt.registerCurrent
    {obligations : List GenerativitySurfaceObligation} {current : Subst}
    {supply : InferenceBase.FreshSupply} {owner : Context}
    {surface frontier : List (Ty × STy)}
    (head : ∀ pair ∈ surface, (current.apply pair.1, pair.2) ∈ frontier)
    (tail : GenerativitySurfaceMembersAt obligations current frontier) :
    GenerativitySurfaceMembersAt
      (GenerativitySurfaceObligation.currentPaired supply owner surface ::
        obligations) current frontier := by
  intro obligation member pair pairMember
  rcases List.mem_cons.mp member with rfl | old
  · exact head pair pairMember
  · exact tail obligation old pair pairMember

theorem GenerativitySurfaceRetainedAt.registerCurrentOfBounded
    {obligations : List GenerativitySurfaceObligation} {current : Subst}
    {supply : InferenceBase.FreshSupply} {owner : Context}
    {surface : List (Ty × STy)}
    (bounded : ∀ pair ∈ surface, (current.apply pair.1).BoundedBy supply)
    (tail : GenerativitySurfaceRetainedAt obligations current) :
    GenerativitySurfaceRetainedAt
      (GenerativitySurfaceObligation.currentPaired supply owner surface ::
        obligations) current := by
  apply GenerativitySurfaceRetainedAt.registerCurrent _ tail
  constructor
  · intro pair member varId free
    exact Or.inl ((bounded pair member).caps varId free)
  · intro pair member varId free
    exact Or.inl ((bounded pair member).targets varId free)

theorem GenerativitySurfaceRetainedAt.protectPair
    {obligations : List GenerativitySurfaceObligation} {current : Subst}
    {pair : Ty × STy}
    (head : ∀ obligation ∈ obligations,
      RetainedOldOrContextAt obligation.floor
        (obligation.owner.applySubst current) current [pair])
    (tail : GenerativitySurfaceRetainedAt obligations current) :
    GenerativitySurfaceRetainedAt
      (GenerativitySurfaceObligations.protectPair pair obligations) current := by
  intro obligation member
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  constructor
  · intro candidate candidateMember varId free
    rcases List.mem_cons.mp candidateMember with rfl | previous
    · exact (head old oldMember).caps candidate List.mem_cons_self varId free
    · exact (tail old oldMember).caps candidate previous varId free
  · intro candidate candidateMember varId free
    rcases List.mem_cons.mp candidateMember with rfl | previous
    · exact (head old oldMember).targets candidate List.mem_cons_self varId free
    · exact (tail old oldMember).targets candidate previous varId free

theorem GenerativitySurfaceMembersAt.protectPair
    {obligations : List GenerativitySurfaceObligation} {current : Subst}
    {frontier : List (Ty × STy)} {pair : Ty × STy}
    (head : (current.apply pair.1, pair.2) ∈ frontier)
    (tail : GenerativitySurfaceMembersAt obligations current frontier) :
    GenerativitySurfaceMembersAt
      (GenerativitySurfaceObligations.protectPair pair obligations)
      current frontier := by
  intro obligation member candidate candidateMember
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  rcases List.mem_cons.mp candidateMember with rfl | previous
  · exact head
  · exact tail old oldMember candidate previous

theorem GenerativitySurfaceRetainedAt.unprotectPair
    {obligations : List GenerativitySurfaceObligation} {current : Subst}
    {pair : Ty × STy}
    (retained : GenerativitySurfaceRetainedAt
      (GenerativitySurfaceObligations.protectPair pair obligations) current) :
    GenerativitySurfaceRetainedAt obligations current := by
  intro obligation member
  have protectedResult := retained (obligation.protectPair pair)
    (List.mem_map.mpr ⟨obligation, member, rfl⟩)
  exact protectedResult.of_subset (by
    intro candidate candidateMember
    exact List.mem_cons_of_mem _ candidateMember)

theorem GenerativitySurfaceMembersAt.unprotectPair
    {obligations : List GenerativitySurfaceObligation} {current : Subst}
    {frontier : List (Ty × STy)} {pair : Ty × STy}
    (members : GenerativitySurfaceMembersAt
      (GenerativitySurfaceObligations.protectPair pair obligations)
      current frontier) :
    GenerativitySurfaceMembersAt obligations current frontier := by
  intro obligation member candidate candidateMember
  exact members (obligation.protectPair pair)
    (List.mem_map.mpr ⟨obligation, member, rfl⟩) candidate
    (List.mem_cons_of_mem _ candidateMember)

theorem GenerativitySurfaceRetainedAt.of_obligations_subset
    {larger smaller : List GenerativitySurfaceObligation} {current : Subst}
    (retained : GenerativitySurfaceRetainedAt larger current)
    (subset : ∀ obligation, obligation ∈ smaller → obligation ∈ larger) :
    GenerativitySurfaceRetainedAt smaller current := by
  intro obligation member
  exact retained obligation (subset obligation member)

theorem GenerativitySurfaceMembersAt.of_obligations_subset
    {larger smaller : List GenerativitySurfaceObligation} {current : Subst}
    {frontier : List (Ty × STy)}
    (members : GenerativitySurfaceMembersAt larger current frontier)
    (subset : ∀ obligation, obligation ∈ smaller → obligation ∈ larger) :
    GenerativitySurfaceMembersAt smaller current frontier := by
  intro obligation member pair pairMember
  exact members obligation (subset obligation member) pair pairMember

theorem GenerativitySurfaceContextsAt.nil (current : Subst)
    (active : Context) : GenerativitySurfaceContextsAt [] current active := by
  simp [GenerativitySurfaceContextsAt]

theorem GenerativitySurfaceValid.nil (supply : InferenceBase.FreshSupply)
    (rawContext : Context) : GenerativitySurfaceValid supply rawContext [] := by
  simp [GenerativitySurfaceValid]

/-- Register an empty local surface.  Unlike the former full-frontier frame,
this constructor has no ownership premise for unrelated continuation types. -/
theorem GenerativitySurfaceFrameAt.registerEmpty
    {obligations : List GenerativitySurfaceObligation} {current : Subst}
    (frame : GenerativitySurfaceFrameAt obligations current)
    (supply : InferenceBase.FreshSupply) (owner : Context) :
    GenerativitySurfaceFrameAt
      (GenerativitySurfaceObligation.current supply owner :: obligations)
      current := by
  intro obligation member raw rawMember
  rcases List.mem_cons.mp member with rfl | old
  · simp [GenerativitySurfaceObligation.current] at rawMember
  · exact frame obligation old raw rawMember

theorem GenerativitySurfaceFrameAt.registerPaired
    {obligations : List GenerativitySurfaceObligation} {current : Subst}
    (frame : GenerativitySurfaceFrameAt obligations current)
    (supply : InferenceBase.FreshSupply) (owner : Context)
    (surface : List (Ty × STy)) :
    GenerativitySurfaceFrameAt
      (GenerativitySurfaceObligation.currentPaired supply owner surface ::
        obligations) current := by
  intro obligation member raw rawMember
  rcases List.mem_cons.mp member with rfl | old
  · simp [GenerativitySurfaceObligation.currentPaired] at rawMember
  · exact frame obligation old raw rawMember

theorem GenerativitySurfaceContextsAt.registerCurrent
    {obligations : List GenerativitySurfaceObligation} {current : Subst}
    {owner : Context}
    (contexts : GenerativitySurfaceContextsAt obligations current
      (owner.applySubst current))
    (supply : InferenceBase.FreshSupply) :
    GenerativitySurfaceContextsAt
      (GenerativitySurfaceObligation.current supply owner :: obligations)
      current (owner.applySubst current) := by
  intro obligation member
  rcases List.mem_cons.mp member with rfl | old
  · exact OldContextCoveredAt.refl supply (owner.applySubst current)
  · exact contexts obligation old

theorem GenerativitySurfaceContextsAt.registerCurrentPaired
    {obligations : List GenerativitySurfaceObligation} {current : Subst}
    {owner : Context}
    (contexts : GenerativitySurfaceContextsAt obligations current
      (owner.applySubst current))
    (supply : InferenceBase.FreshSupply) (surface : List (Ty × STy)) :
    GenerativitySurfaceContextsAt
      (GenerativitySurfaceObligation.currentPaired supply owner surface ::
        obligations) current (owner.applySubst current) := by
  intro obligation member
  rcases List.mem_cons.mp member with rfl | old
  · exact OldContextCoveredAt.refl supply (owner.applySubst current)
  · exact contexts obligation old

theorem GenerativitySurfaceValid.registerCurrent
    {obligations : List GenerativitySurfaceObligation}
    {supply : InferenceBase.FreshSupply} {rawContext : Context}
    (valid : GenerativitySurfaceValid supply rawContext obligations) :
    GenerativitySurfaceValid supply rawContext
      (GenerativitySurfaceObligation.current supply rawContext :: obligations) := by
  intro obligation member
  rcases List.mem_cons.mp member with rfl | old
  · exact ⟨SupplyExtends.refl _, ProvenanceContextSuffix.refl _⟩
  · exact valid obligation old

theorem GenerativitySurfaceValid.registerCurrentPaired
    {obligations : List GenerativitySurfaceObligation}
    {supply : InferenceBase.FreshSupply} {rawContext : Context}
    (valid : GenerativitySurfaceValid supply rawContext obligations)
    (surface : List (Ty × STy)) :
    GenerativitySurfaceValid supply rawContext
      (GenerativitySurfaceObligation.currentPaired supply rawContext surface ::
        obligations) := by
  intro obligation member
  rcases List.mem_cons.mp member with rfl | old
  · exact ⟨SupplyExtends.refl _, ProvenanceContextSuffix.refl _⟩
  · exact valid obligation old

theorem GenerativitySurfaceValid.monoSupply
    {earlier later : InferenceBase.FreshSupply} {rawContext : Context}
    {obligations : List GenerativitySurfaceObligation}
    (valid : GenerativitySurfaceValid earlier rawContext obligations)
    (extension : SupplyExtends earlier later) :
    GenerativitySurfaceValid later rawContext obligations := by
  intro obligation member
  exact ⟨(valid obligation member).1.trans extension,
    (valid obligation member).2⟩

theorem GenerativitySurfaceValid.consActive
    {supply : InferenceBase.FreshSupply} {rawContext : Context}
    {obligations : List GenerativitySurfaceObligation}
    (valid : GenerativitySurfaceValid supply rawContext obligations)
    (name : String) (scheme : Scheme) :
    GenerativitySurfaceValid supply ((name, scheme) :: rawContext)
      obligations := by
  intro obligation member
  exact ⟨(valid obligation member).1,
    (valid obligation member).2.consActive name scheme⟩

/-- Add one raw-coordinate token to an existing head obligation. -/
theorem GenerativitySurfaceFrameAt.registerHeadToken
    {head : GenerativitySurfaceObligation}
    {obligations : List GenerativitySurfaceObligation} {current : Subst}
    {raw : Ty}
    (token : OldFreeInContextAt head.floor
      (head.owner.applySubst current) (current.apply raw))
    (frame : GenerativitySurfaceFrameAt (head :: obligations) current) :
    GenerativitySurfaceFrameAt
      ({ head with protectedOld := raw :: head.protectedOld } :: obligations)
      current := by
  intro obligation member candidate candidateMember
  rcases List.mem_cons.mp member with rfl | old
  · rcases List.mem_cons.mp candidateMember with rfl | previous
    · exact token
    · exact frame head List.mem_cons_self candidate previous
  · exact frame obligation (List.mem_cons_of_mem _ old) candidate candidateMember

/-- Compatibility adapter for raw-only structural clients.  New solver and
let code uses `protectPair`, which retains the selected coordinate. -/
def GenerativitySurfaceObligation.protectToken (raw : Ty)
    (obligation : GenerativitySurfaceObligation) :
    GenerativitySurfaceObligation :=
  { obligation with protectedOld := raw :: obligation.protectedOld }

def GenerativitySurfaceObligations.protectToken (raw : Ty)
    (obligations : List GenerativitySurfaceObligation) :
    List GenerativitySurfaceObligation :=
  obligations.map (GenerativitySurfaceObligation.protectToken raw)

theorem GenerativitySurfaceFrameAt.protectToken
    {obligations : List GenerativitySurfaceObligation} {current : Subst}
    {raw : Ty}
    (target : ∀ obligation ∈ obligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst current) (current.apply raw))
    (frame : GenerativitySurfaceFrameAt obligations current) :
    GenerativitySurfaceFrameAt
      (GenerativitySurfaceObligations.protectToken raw obligations) current := by
  intro obligation member candidate candidateMember
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  rcases List.mem_cons.mp candidateMember with rfl | previous
  · exact target old oldMember
  · exact frame old oldMember candidate previous

theorem GenerativitySurfaceFrameAt.unprotectToken
    {obligations : List GenerativitySurfaceObligation} {current : Subst}
    {raw : Ty}
    (frame : GenerativitySurfaceFrameAt
      (GenerativitySurfaceObligations.protectToken raw obligations) current) :
    GenerativitySurfaceFrameAt obligations current := by
  intro obligation member candidate candidateMember
  exact frame (obligation.protectToken raw)
    (List.mem_map.mpr ⟨obligation, member, rfl⟩) candidate
    (List.mem_cons_of_mem _ candidateMember)

theorem GenerativitySurfaceContextsAt.protectToken
    {obligations : List GenerativitySurfaceObligation} {current : Subst}
    {active : Context} {raw : Ty}
    (contexts : GenerativitySurfaceContextsAt obligations current active) :
    GenerativitySurfaceContextsAt
      (GenerativitySurfaceObligations.protectToken raw obligations)
      current active := by
  intro obligation member
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  exact contexts old oldMember

theorem GenerativitySurfaceContextsAt.unprotectToken
    {obligations : List GenerativitySurfaceObligation} {current : Subst}
    {active : Context} {raw : Ty}
    (contexts : GenerativitySurfaceContextsAt
      (GenerativitySurfaceObligations.protectToken raw obligations)
      current active) :
    GenerativitySurfaceContextsAt obligations current active := by
  intro obligation member
  exact contexts (obligation.protectToken raw)
    (List.mem_map.mpr ⟨obligation, member, rfl⟩)

theorem GenerativitySurfaceValid.protectToken
    {obligations : List GenerativitySurfaceObligation}
    {supply : InferenceBase.FreshSupply} {rawContext : Context} {raw : Ty}
    (valid : GenerativitySurfaceValid supply rawContext obligations) :
    GenerativitySurfaceValid supply rawContext
      (GenerativitySurfaceObligations.protectToken raw obligations) := by
  intro obligation member
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  exact valid old oldMember

theorem GenerativitySurfaceValid.unprotectToken
    {obligations : List GenerativitySurfaceObligation}
    {supply : InferenceBase.FreshSupply} {rawContext : Context} {raw : Ty}
    (valid : GenerativitySurfaceValid supply rawContext
      (GenerativitySurfaceObligations.protectToken raw obligations)) :
    GenerativitySurfaceValid supply rawContext obligations := by
  intro obligation member
  exact valid (obligation.protectToken raw)
    (List.mem_map.mpr ⟨obligation, member, rfl⟩)

theorem GenerativitySurfaceRetainedAt.protectToken
    {obligations : List GenerativitySurfaceObligation} {current : Subst}
    {raw : Ty}
    (retained : GenerativitySurfaceRetainedAt obligations current) :
    GenerativitySurfaceRetainedAt
      (GenerativitySurfaceObligations.protectToken raw obligations) current := by
  intro obligation member
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  exact retained old oldMember

theorem GenerativitySurfaceRetainedAt.unprotectToken
    {obligations : List GenerativitySurfaceObligation} {current : Subst}
    {raw : Ty}
    (retained : GenerativitySurfaceRetainedAt
      (GenerativitySurfaceObligations.protectToken raw obligations) current) :
    GenerativitySurfaceRetainedAt obligations current := by
  intro obligation member
  exact retained (obligation.protectToken raw)
    (List.mem_map.mpr ⟨obligation, member, rfl⟩)

theorem GenerativitySurfaceMembersAt.protectToken
    {obligations : List GenerativitySurfaceObligation} {current : Subst}
    {frontier : List (Ty × STy)} {raw : Ty}
    (members : GenerativitySurfaceMembersAt obligations current frontier) :
    GenerativitySurfaceMembersAt
      (GenerativitySurfaceObligations.protectToken raw obligations)
      current frontier := by
  intro obligation member pair pairMember
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  exact members old oldMember pair pairMember

theorem GenerativitySurfaceMembersAt.unprotectToken
    {obligations : List GenerativitySurfaceObligation} {current : Subst}
    {frontier : List (Ty × STy)} {raw : Ty}
    (members : GenerativitySurfaceMembersAt
      (GenerativitySurfaceObligations.protectToken raw obligations)
      current frontier) :
    GenerativitySurfaceMembersAt obligations current frontier := by
  intro obligation member pair pairMember
  exact members (obligation.protectToken raw)
    (List.mem_map.mpr ⟨obligation, member, rfl⟩) pair pairMember

theorem GenerativitySurfaceFrameAt.of_obligations_subset
    {larger smaller : List GenerativitySurfaceObligation} {current : Subst}
    (frame : GenerativitySurfaceFrameAt larger current)
    (subset : ∀ obligation, obligation ∈ smaller → obligation ∈ larger) :
    GenerativitySurfaceFrameAt smaller current := by
  intro obligation member raw rawMember
  exact frame obligation (subset obligation member) raw rawMember

theorem GenerativitySurfaceFrameAt.token
    {obligations : List GenerativitySurfaceObligation} {current : Subst}
    {obligation : GenerativitySurfaceObligation} {raw : Ty}
    (frame : GenerativitySurfaceFrameAt obligations current)
    (obligationMember : obligation ∈ obligations)
    (rawMember : raw ∈ obligation.protectedOld) :
    OldFreeInContextAt obligation.floor
      (obligation.owner.applySubst current) (current.apply raw) :=
  frame obligation obligationMember raw rawMember

theorem GenerativitySurfaceFrameAt.applyOriginSafeExactPairedMGU
    {obligations : List GenerativitySurfaceObligation}
    {current delta : Subst} {left right : Ty}
    (frame : GenerativitySurfaceFrameAt obligations current)
    (leftOld : ∀ obligation ∈ obligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst current) left)
    (rightOld : ∀ obligation ∈ obligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst current) right)
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (leftCapFree : left.fcv = []) (rightCapFree : right.fcv = []) :
    GenerativitySurfaceFrameAt obligations (Subst.seq delta current) := by
  intro obligation obligationMember raw rawMember
  have singleton : ProtectedOldFreeAt obligation.floor
      (obligation.owner.applySubst current) [(current.apply raw, STy.int)] :=
    ProtectedOldFreeAt.cons
      (frame obligation obligationMember raw rawMember)
      (ProtectedOldFreeAt.nil _ _)
  obtain ⟨_, transported⟩ :=
    (OldContextCoveredAt.refl obligation.floor
      (obligation.owner.applySubst current))
      |>.applyOriginSafeExactPairedMGU_and_protected singleton
        (leftOld obligation obligationMember)
        (rightOld obligation obligationMember) exact leftCapFree rightCapFree
  have result := transported (delta.apply (current.apply raw), STy.int)
    List.mem_cons_self
  simpa only [Context.applySubst_seq, Subst.seq_apply] using result

theorem GenerativitySurfaceContextsAt.applyOriginSafeExactPairedMGU
    {obligations : List GenerativitySurfaceObligation}
    {current delta : Subst} {active : Context} {left right : Ty}
    (contexts : GenerativitySurfaceContextsAt obligations current active)
    (leftOld : ∀ obligation ∈ obligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst current) left)
    (rightOld : ∀ obligation ∈ obligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst current) right)
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (leftCapFree : left.fcv = []) (rightCapFree : right.fcv = []) :
    GenerativitySurfaceContextsAt obligations (Subst.seq delta current)
      (active.applySubst delta) := by
  intro obligation member
  simpa only [Context.applySubst_seq] using
    (contexts obligation member).applyOriginSafeExactPairedMGU_and_protected
      (ProtectedOldFreeAt.nil obligation.floor active)
      (leftOld obligation member) (rightOld obligation member) exact
      leftCapFree rightCapFree |>.1

theorem GenerativitySurfaceRetainedAt.applyOriginSafeExactPairedMGU
    {obligations : List GenerativitySurfaceObligation}
    {current delta : Subst} {left right : Ty}
    (retained : GenerativitySurfaceRetainedAt obligations current)
    (leftOld : ∀ obligation ∈ obligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst current) left)
    (rightOld : ∀ obligation ∈ obligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst current) right)
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (leftCapFree : left.fcv = []) (rightCapFree : right.fcv = []) :
    GenerativitySurfaceRetainedAt obligations (Subst.seq delta current) := by
  intro obligation member
  have transported := (retained obligation member)
    |>.applyOriginSafeExactPairedMGU_of_endpointsOld
      (leftOld obligation member) (rightOld obligation member) exact
      leftCapFree rightCapFree
  simpa only [Context.applySubst_seq] using transported

theorem GenerativitySurfaceMembersAt.applyOriginSafeExactPairedMGU
    {obligations : List GenerativitySurfaceObligation}
    {current delta : Subst} {frontier : List (Ty × STy)}
    (members : GenerativitySurfaceMembersAt obligations current frontier) :
    GenerativitySurfaceMembersAt obligations (Subst.seq delta current)
      (frontier.map fun pair => (delta.apply pair.1, pair.2)) := by
  intro obligation obligationMember pair pairMember
  apply List.mem_map.mpr
  exact ⟨(current.apply pair.1, pair.2),
    members obligation obligationMember pair pairMember, by
      simp only [Subst.seq_apply]⟩

/-- Paired continuation state transported as one unit through an exact
ordinary cut. -/
structure GenerativityPairedStateAt
    (obligations : List GenerativitySurfaceObligation)
    (current : Subst) (frontier : List (Ty × STy)) : Prop where
  retained : GenerativitySurfaceRetainedAt obligations current
  members : GenerativitySurfaceMembersAt obligations current frontier

theorem GenerativityPairedStateAt.applyOriginSafeExactPairedMGU
    {obligations : List GenerativitySurfaceObligation}
    {current delta : Subst} {frontier : List (Ty × STy)}
    {left right : Ty}
    (state : GenerativityPairedStateAt obligations current frontier)
    (leftOld : ∀ obligation ∈ obligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst current) left)
    (rightOld : ∀ obligation ∈ obligations,
      OldFreeInContextAt obligation.floor
        (obligation.owner.applySubst current) right)
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (leftCapFree : left.fcv = []) (rightCapFree : right.fcv = []) :
    GenerativityPairedStateAt obligations (Subst.seq delta current)
      (frontier.map fun pair => (delta.apply pair.1, pair.2)) :=
  ⟨state.retained.applyOriginSafeExactPairedMGU leftOld rightOld exact
      leftCapFree rightCapFree,
    state.members.applyOriginSafeExactPairedMGU⟩

/-! ## Legacy full-frontier formulation

The definitions below are kept temporarily while downstream constructor
modules migrate to the surface-indexed API above.  They must not be used by
new completeness proofs: registering a new obligation against an arbitrary
old frontier is false in general. -/

abbrev GenerativityObligation := InferenceBase.FreshSupply × Context

def GenerativityObligationsValid (supply : InferenceBase.FreshSupply)
    (rawContext : Context) (obligations : List GenerativityObligation) : Prop :=
  ∀ obligation ∈ obligations,
    SupplyExtends obligation.1 supply ∧
      ProvenanceContextSuffix obligation.2 rawContext

theorem GenerativityObligationsValid.nil (supply : InferenceBase.FreshSupply)
    (rawContext : Context) : GenerativityObligationsValid supply rawContext [] := by
  simp [GenerativityObligationsValid]

theorem GenerativityObligationsValid.consCurrent
    {supply : InferenceBase.FreshSupply} {rawContext : Context}
    {obligations : List GenerativityObligation}
    (valid : GenerativityObligationsValid supply rawContext obligations) :
    GenerativityObligationsValid supply rawContext
      ((supply, rawContext) :: obligations) := by
  intro obligation member
  rcases List.mem_cons.mp member with rfl | old
  · exact ⟨SupplyExtends.refl _, ProvenanceContextSuffix.refl _⟩
  · exact valid obligation old

theorem GenerativityObligationsValid.monoSupply
    {earlier later : InferenceBase.FreshSupply} {rawContext : Context}
    {obligations : List GenerativityObligation}
    (valid : GenerativityObligationsValid earlier rawContext obligations)
    (extension : SupplyExtends earlier later) :
    GenerativityObligationsValid later rawContext obligations := by
  intro obligation member
  exact ⟨(valid obligation member).1.trans extension,
    (valid obligation member).2⟩

theorem GenerativityObligationsValid.consActive
    {supply : InferenceBase.FreshSupply} {rawContext : Context}
    {obligations : List GenerativityObligation}
    (valid : GenerativityObligationsValid supply rawContext obligations)
    (name : String) (scheme : Scheme) :
    GenerativityObligationsValid supply ((name, scheme) :: rawContext)
      obligations := by
  intro obligation member
  exact ⟨(valid obligation member).1,
    (valid obligation member).2.consActive name scheme⟩

def GenerativityFrameAt (obligations : List GenerativityObligation)
    (current : Subst) (frontier : List (Ty × STy)) : Prop :=
  ∀ obligation ∈ obligations,
    ProtectedOldFreeAt obligation.1 (obligation.2.applySubst current) frontier

def GenerativityContextFrameAt (obligations : List GenerativityObligation)
    (current : Subst) (active : Context) : Prop :=
  ∀ obligation ∈ obligations,
    OldContextCoveredAt obligation.1
      (obligation.2.applySubst current) active

theorem GenerativityContextFrameAt.nil (current : Subst) (active : Context) :
    GenerativityContextFrameAt [] current active := by
  simp [GenerativityContextFrameAt]

theorem GenerativityContextFrameAt.cons
    {obligations : List GenerativityObligation} {current : Subst}
    {active : Context} {obligation : GenerativityObligation}
    (head : OldContextCoveredAt obligation.1
      (obligation.2.applySubst current) active)
    (tail : GenerativityContextFrameAt obligations current active) :
    GenerativityContextFrameAt (obligation :: obligations) current active := by
  intro candidate member
  rcases List.mem_cons.mp member with rfl | old
  · exact head
  · exact tail candidate old

theorem GenerativityContextFrameAt.applyOriginSafeExactPairedMGU
    {obligations : List GenerativityObligation} {current delta : Subst}
    {active : Context} {left right : Ty}
    (contexts : GenerativityContextFrameAt obligations current active)
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (leftCapFree : left.fcv = []) (rightCapFree : right.fcv = [])
    (leftOld : ∀ obligation ∈ obligations,
      OldFreeInContextAt obligation.1
        (obligation.2.applySubst current) left)
    (rightOld : ∀ obligation ∈ obligations,
      OldFreeInContextAt obligation.1
        (obligation.2.applySubst current) right) :
    GenerativityContextFrameAt obligations (Subst.seq delta current)
      (active.applySubst delta) := by
  intro obligation member
  simpa only [Context.applySubst_seq] using
    ((contexts obligation member).applyOriginSafeExactPairedMGU_and_protected
      (ProtectedOldFreeAt.nil obligation.1 active)
      (leftOld obligation member) (rightOld obligation member) exact
      leftCapFree rightCapFree).1

theorem GenerativityFrameAt.nil (current : Subst)
    (frontier : List (Ty × STy)) :
    GenerativityFrameAt [] current frontier := by
  simp [GenerativityFrameAt]

theorem GenerativityFrameAt.cons
    {obligations : List GenerativityObligation} {current : Subst}
    {frontier : List (Ty × STy)} {obligation : GenerativityObligation}
    (head : ProtectedOldFreeAt obligation.1
      (obligation.2.applySubst current) frontier)
    (tail : GenerativityFrameAt obligations current frontier) :
    GenerativityFrameAt (obligation :: obligations) current frontier := by
  intro candidate member
  rcases List.mem_cons.mp member with rfl | old
  · exact head
  · exact tail candidate old

theorem GenerativityFrameAt.tail
    {obligations : List GenerativityObligation} {current : Subst}
    {frontier : List (Ty × STy)} {obligation : GenerativityObligation}
    (frame : GenerativityFrameAt (obligation :: obligations) current frontier) :
    GenerativityFrameAt obligations current frontier := by
  intro candidate member
  exact frame candidate (List.mem_cons_of_mem _ member)

theorem GenerativityFrameAt.of_obligations_subset
    {larger smaller : List GenerativityObligation} {current : Subst}
    {frontier : List (Ty × STy)}
    (frame : GenerativityFrameAt larger current frontier)
    (subset : ∀ obligation, obligation ∈ smaller → obligation ∈ larger) :
    GenerativityFrameAt smaller current frontier := by
  intro obligation member
  exact frame obligation (subset obligation member)

theorem GenerativityFrameAt.of_frontier_subset
    {obligations : List GenerativityObligation} {current : Subst}
    {larger smaller : List (Ty × STy)}
    (frame : GenerativityFrameAt obligations current larger)
    (subset : ∀ pair, pair ∈ smaller → pair ∈ larger) :
    GenerativityFrameAt obligations current smaller := by
  intro obligation member
  exact (frame obligation member).of_subset subset

theorem GenerativityFrameAt.consFreshTarget
    {obligations : List GenerativityObligation} {current : Subst}
    {frontier : List (Ty × STy)} {varId : TyVar} {selected : STy}
    (frame : GenerativityFrameAt obligations current frontier)
    (fresh : ∀ obligation ∈ obligations, obligation.1.nextTy ≤ varId) :
    GenerativityFrameAt obligations current
      ((.var varId, selected) :: frontier) := by
  intro obligation member
  exact (frame obligation member).cons
    (OldFreeInContextAt.var obligation.1 _ varId (fresh obligation member))

theorem GenerativityFrameAt.consFn
    {obligations : List GenerativityObligation} {current : Subst}
    {frontier : List (Ty × STy)} {domain codomain : Ty} {selected : STy}
    (frame : GenerativityFrameAt obligations current frontier)
    (domainOld : ∀ obligation ∈ obligations,
      OldFreeInContextAt obligation.1 (obligation.2.applySubst current) domain)
    (codomainOld : ∀ obligation ∈ obligations,
      OldFreeInContextAt obligation.1 (obligation.2.applySubst current) codomain) :
    GenerativityFrameAt obligations current
      ((.fn domain codomain, selected) :: frontier) := by
  intro obligation member
  exact (frame obligation member).cons
    (OldFreeInContextAt.fn (domainOld obligation member)
      (codomainOld obligation member))

theorem GenerativityFrameAt.applyOriginSafeExactPairedMGU
    {obligations : List GenerativityObligation} {current delta : Subst}
    {frontier : List (Ty × STy)} {left right : Ty}
    (frame : GenerativityFrameAt obligations current frontier)
    (leftOld : ∀ obligation ∈ obligations,
      OldFreeInContextAt obligation.1
        (obligation.2.applySubst current) left)
    (rightOld : ∀ obligation ∈ obligations,
      OldFreeInContextAt obligation.1
        (obligation.2.applySubst current) right)
    (exact : OriginSafeExactPairedMGU [] left right delta)
    (leftCapFree : left.fcv = []) (rightCapFree : right.fcv = []) :
    GenerativityFrameAt obligations (Subst.seq delta current)
      (frontier.map fun pair => (delta.apply pair.1, pair.2)) := by
  intro obligation member
  obtain ⟨_context, protectedFinal⟩ :=
    (OldContextCoveredAt.refl obligation.1
      (obligation.2.applySubst current)).applyOriginSafeExactPairedMGU_and_protected
      (frame obligation member) (leftOld obligation member)
      (rightOld obligation member) exact leftCapFree rightCapFree
  simpa only [Context.applySubst_seq] using protectedFinal

theorem GenerativityFrameAt.target
    {obligations : List GenerativityObligation} {current : Subst}
    {frontier : List (Ty × STy)} {obligation : GenerativityObligation}
    {algorithm : Ty} {selected : STy}
    (frame : GenerativityFrameAt obligations current frontier)
    (obligationMember : obligation ∈ obligations)
    (targetMember : (algorithm, selected) ∈ frontier) :
    OldFreeInContextAt obligation.1
      (obligation.2.applySubst current) algorithm :=
  frame obligation obligationMember _ targetMember

end DM
end TypePM
