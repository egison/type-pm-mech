import TypePM.PolyScheme

/-!
# Executable equality for capture-free schemes

The payload of a `Scheme` is indexed by its two binder arities, so Lean cannot
derive equality for it directly.  We erase only those indices into an
ordinary code datatype.  Bound variables retain their numeric `Fin` value;
the arities stored beside the payload make this encoding lossless.
-/

namespace TypePM

namespace SchemeEquality

private inductive CapCode where
  | any
  | mvar   : CapVar → CapCode
  | bound  : Nat → CapCode
  | skolem : Nat → CapCode
  | con    : String → List CapCode → CapCode
  | prod   : List CapCode → CapCode

private inductive TyCode where
  | mvar   : TypePM.TyVar → TyCode
  | bound  : Nat → TyCode
  | skolem : Nat → TyCode
  | unit
  | int
  | bool
  | data    : String → List TyCode → TyCode
  | prod    : List TyCode → TyCode
  | fn      : TyCode → TyCode → TyCode
  | matcher : CapCode → TyCode → TyCode
  | slot    : CapCode → TyCode → TyCode

mutual

private def CapCode.eqb : CapCode → CapCode → Bool
  | .any, .any => true
  | .mvar left, .mvar right => left == right
  | .bound left, .bound right => left == right
  | .skolem left, .skolem right => left == right
  | .con leftName leftChildren, .con rightName rightChildren =>
      leftName == rightName && CapCode.eqbList leftChildren rightChildren
  | .prod left, .prod right => CapCode.eqbList left right
  | _, _ => false

private def CapCode.eqbList : List CapCode → List CapCode → Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      left.eqb right && CapCode.eqbList lefts rights
  | _, _ => false

end


mutual

private theorem CapCode.eqb_eq_true :
    ∀ (left right : CapCode), CapCode.eqb left right = true ↔ left = right
  | .any, right => by cases right <;> simp [CapCode.eqb]
  | .mvar _, right => by cases right <;> simp [CapCode.eqb]
  | .bound _, right => by cases right <;> simp [CapCode.eqb]
  | .skolem _, right => by cases right <;> simp [CapCode.eqb]
  | .con _ _, right => by
      cases right <;> simp [CapCode.eqb, CapCode.eqbList_eq_true]
  | .prod _, right => by
      cases right <;> simp [CapCode.eqb, CapCode.eqbList_eq_true]

private theorem CapCode.eqbList_eq_true :
    ∀ left right, CapCode.eqbList left right = true ↔ left = right
  | [], right => by cases right <;> simp [CapCode.eqbList]
  | _ :: _, right => by
      cases right with
      | nil => simp [CapCode.eqbList]
      | cons head tail =>
          simp only [CapCode.eqbList, Bool.and_eq_true]
          rw [CapCode.eqb_eq_true, CapCode.eqbList_eq_true]
          simp

end


mutual

private def TyCode.eqb : TyCode → TyCode → Bool
  | .mvar left, .mvar right => left == right
  | .bound left, .bound right => left == right
  | .skolem left, .skolem right => left == right
  | .unit, .unit => true
  | .int, .int => true
  | .bool, .bool => true
  | .data leftName leftChildren, .data rightName rightChildren =>
      leftName == rightName && TyCode.eqbList leftChildren rightChildren
  | .prod left, .prod right => TyCode.eqbList left right
  | .fn leftDomain leftCodomain, .fn rightDomain rightCodomain =>
      leftDomain.eqb rightDomain && leftCodomain.eqb rightCodomain
  | .matcher leftCap leftTarget, .matcher rightCap rightTarget =>
      leftCap.eqb rightCap && leftTarget.eqb rightTarget
  | .slot leftCap leftTarget, .slot rightCap rightTarget =>
      leftCap.eqb rightCap && leftTarget.eqb rightTarget
  | _, _ => false

private def TyCode.eqbList : List TyCode → List TyCode → Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      left.eqb right && TyCode.eqbList lefts rights
  | _, _ => false

end


mutual

private theorem TyCode.eqb_eq_true :
    ∀ (left right : TyCode), TyCode.eqb left right = true ↔ left = right
  | .mvar _, right => by cases right <;> simp [TyCode.eqb]
  | .bound _, right => by cases right <;> simp [TyCode.eqb]
  | .skolem _, right => by cases right <;> simp [TyCode.eqb]
  | .unit, right => by cases right <;> simp [TyCode.eqb]
  | .int, right => by cases right <;> simp [TyCode.eqb]
  | .bool, right => by cases right <;> simp [TyCode.eqb]
  | .data _ _, right => by
      cases right <;> simp [TyCode.eqb, TyCode.eqbList_eq_true]
  | .prod _, right => by
      cases right <;> simp [TyCode.eqb, TyCode.eqbList_eq_true]
  | .fn _ _, right => by
      cases right <;> simp [TyCode.eqb, TyCode.eqb_eq_true]
  | .matcher _ _, right => by
      cases right <;>
        simp [TyCode.eqb, CapCode.eqb_eq_true, TyCode.eqb_eq_true]
  | .slot _ _, right => by
      cases right <;>
        simp [TyCode.eqb, CapCode.eqb_eq_true, TyCode.eqb_eq_true]

private theorem TyCode.eqbList_eq_true :
    ∀ left right, TyCode.eqbList left right = true ↔ left = right
  | [], right => by cases right <;> simp [TyCode.eqbList]
  | _ :: _, right => by
      cases right with
      | nil => simp [TyCode.eqbList]
      | cons head tail =>
          simp only [TyCode.eqbList, Bool.and_eq_true]
          rw [TyCode.eqb_eq_true, TyCode.eqbList_eq_true]
          simp

end

private def encodeCap {capArity : Nat} : PolyCap capArity → CapCode
  | .any => .any
  | .mvar varId => .mvar varId
  | .bound index => .bound index.val
  | .skolem name => .skolem name
  | .con name children => .con name (children.map encodeCap)
  | .prod components => .prod (components.map encodeCap)

private def encodeTy {capArity tyArity : Nat} :
    PolyTy capArity tyArity → TyCode
  | .mvar varId => .mvar varId
  | .bound index => .bound index.val
  | .skolem name => .skolem name
  | .unit => .unit
  | .int => .int
  | .bool => .bool
  | .data name children => .data name (children.map encodeTy)
  | .prod components => .prod (components.map encodeTy)
  | .fn domain codomain => .fn (encodeTy domain) (encodeTy codomain)
  | .matcher capability target =>
      .matcher (encodeCap capability) (encodeTy target)
  | .slot capability target =>
      .slot (encodeCap capability) (encodeTy target)

mutual

private def decodeCap (capArity : Nat) : CapCode → Option (PolyCap capArity)
  | .any => some .any
  | .mvar varId => some (.mvar varId)
  | .bound value =>
      if bounded : value < capArity then
        some (.bound ⟨value, bounded⟩)
      else
        none
  | .skolem name => some (.skolem name)
  | .con name children =>
      match decodeCaps capArity children with
      | some decoded => some (.con name decoded)
      | none => none
  | .prod components =>
      match decodeCaps capArity components with
      | some decoded => some (.prod decoded)
      | none => none

private def decodeCaps (capArity : Nat) :
    List CapCode → Option (List (PolyCap capArity))
  | [] => some []
  | capability :: capabilities =>
      match decodeCap capArity capability, decodeCaps capArity capabilities with
      | some decoded, some rest => some (decoded :: rest)
      | _, _ => none

end

mutual

private theorem decodeCap_encode {capArity : Nat} :
    ∀ capability : PolyCap capArity,
      decodeCap capArity (encodeCap capability) = some capability
  | .any => by simp [encodeCap, decodeCap]
  | .mvar _ => by simp [encodeCap, decodeCap]
  | .bound index => by
      simp [encodeCap, decodeCap, index.isLt]
  | .skolem _ => by simp [encodeCap, decodeCap]
  | .con name children => by
      simp [encodeCap, decodeCap, decodeCaps_encode children]
  | .prod components => by
      simp [encodeCap, decodeCap, decodeCaps_encode components]

private theorem decodeCaps_encode {capArity : Nat} :
    ∀ capabilities : List (PolyCap capArity),
      decodeCaps capArity (capabilities.map encodeCap) = some capabilities
  | [] => rfl
  | capability :: capabilities => by
      simp [decodeCaps, decodeCap_encode capability,
        decodeCaps_encode capabilities]

end

mutual

private def decodeTy (capArity tyArity : Nat) :
    TyCode → Option (PolyTy capArity tyArity)
  | .mvar varId => some (.mvar varId)
  | .bound value =>
      if bounded : value < tyArity then
        some (.bound ⟨value, bounded⟩)
      else
        none
  | .skolem name => some (.skolem name)
  | .unit => some .unit
  | .int => some .int
  | .bool => some .bool
  | .data name children =>
      match decodeTys capArity tyArity children with
      | some decoded => some (.data name decoded)
      | none => none
  | .prod components =>
      match decodeTys capArity tyArity components with
      | some decoded => some (.prod decoded)
      | none => none
  | .fn domain codomain =>
      match decodeTy capArity tyArity domain,
          decodeTy capArity tyArity codomain with
      | some decodedDomain, some decodedCodomain =>
          some (.fn decodedDomain decodedCodomain)
      | _, _ => none
  | .matcher capability target =>
      match decodeCap capArity capability,
          decodeTy capArity tyArity target with
      | some decodedCapability, some decodedTarget =>
          some (.matcher decodedCapability decodedTarget)
      | _, _ => none
  | .slot capability target =>
      match decodeCap capArity capability,
          decodeTy capArity tyArity target with
      | some decodedCapability, some decodedTarget =>
          some (.slot decodedCapability decodedTarget)
      | _, _ => none

private def decodeTys (capArity tyArity : Nat) :
    List TyCode → Option (List (PolyTy capArity tyArity))
  | [] => some []
  | target :: targets =>
      match decodeTy capArity tyArity target,
          decodeTys capArity tyArity targets with
      | some decoded, some rest => some (decoded :: rest)
      | _, _ => none

end

mutual

private theorem decodeTy_encode {capArity tyArity : Nat} :
    ∀ target : PolyTy capArity tyArity,
      decodeTy capArity tyArity (encodeTy target) = some target
  | .mvar _ => by simp [encodeTy, decodeTy]
  | .bound index => by
      simp [encodeTy, decodeTy, index.isLt]
  | .skolem _ => by simp [encodeTy, decodeTy]
  | .unit => by simp [encodeTy, decodeTy]
  | .int => by simp [encodeTy, decodeTy]
  | .bool => by simp [encodeTy, decodeTy]
  | .data name children => by
      simp [encodeTy, decodeTy, decodeTys_encode children]
  | .prod components => by
      simp [encodeTy, decodeTy, decodeTys_encode components]
  | .fn domain codomain => by
      simp [encodeTy, decodeTy, decodeTy_encode domain,
        decodeTy_encode codomain]
  | .matcher capability target => by
      simp [encodeTy, decodeTy, decodeCap_encode capability,
        decodeTy_encode target]
  | .slot capability target => by
      simp [encodeTy, decodeTy, decodeCap_encode capability,
        decodeTy_encode target]

private theorem decodeTys_encode {capArity tyArity : Nat} :
    ∀ targets : List (PolyTy capArity tyArity),
      decodeTys capArity tyArity (targets.map encodeTy) = some targets
  | [] => rfl
  | target :: targets => by
      simp [decodeTys, decodeTy_encode target, decodeTys_encode targets]

end

private theorem encodeTy_injective {capArity tyArity : Nat} :
    Function.Injective (@encodeTy capArity tyArity) := by
  intro left right equality
  have decoded := congrArg (decodeTy capArity tyArity) equality
  exact Option.some.inj (by simpa only [decodeTy_encode] using decoded)

private def schemeEqb (left right : Scheme) : Bool :=
  left.capArity == right.capArity &&
    left.tyArity == right.tyArity &&
    (encodeTy left.body).eqb (encodeTy right.body)

private theorem schemeEqb_eq_true (left right : Scheme) :
    schemeEqb left right = true ↔ left = right := by
  cases left with
  | mk leftCap leftTy leftBody =>
      cases right with
      | mk rightCap rightTy rightBody =>
          constructor
          · intro checked
            simp only [schemeEqb, Bool.and_eq_true,
              beq_iff_eq] at checked
            rcases checked with ⟨⟨capEquality, tyEquality⟩,
              bodyCodeEquality⟩
            subst rightCap
            subst rightTy
            have bodyEquality : leftBody = rightBody :=
              encodeTy_injective
                ((TyCode.eqb_eq_true _ _).mp bodyCodeEquality)
            subst rightBody
            rfl
          · intro equality
            cases equality
            simp [schemeEqb, TyCode.eqb_eq_true]

end SchemeEquality

instance : BEq Scheme where
  beq := SchemeEquality.schemeEqb

instance : LawfulBEq Scheme where
  eq_of_beq equality :=
    (SchemeEquality.schemeEqb_eq_true _ _).mp equality
  rfl := (SchemeEquality.schemeEqb_eq_true _ _).mpr rfl

instance : DecidableEq Scheme :=
  instDecidableEqOfLawfulBEq

end TypePM
