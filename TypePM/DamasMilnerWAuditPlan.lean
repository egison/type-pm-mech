import TypePM.DamasMilnerWLetStability

/-!
# Deferred terminal audits for Damas--Milner W

A child traversal cannot be audited only at its local terminal: an enclosing
application, tuple, or fix may append solver steps.  `WSynthAuditPlan` records
the finite let cuts occurring in an already-built origin tree and constructs
the proof-relevant terminal audit once stability at the eventual root
terminal is supplied.
-/

namespace TypePM
namespace DM

/-- Restrict pointwise stability to a sublist. -/
theorem PendingLetStability.of_subset
    {signature : FrozenSig} {terminal : Subst}
    {larger smaller : List PendingLetCut}
    (stable : PendingLetStability signature terminal larger)
    (subset : ∀ cut, cut ∈ smaller → cut ∈ larger) :
    PendingLetStability signature terminal smaller := by
  intro cut member
  exact stable cut (subset cut member)

/-- A deferred audit for one fixed raw synthesis/origin pair. -/
structure WSynthAuditPlan
    (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {expression : Expr} {target : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DemandSynth signature q S context expression target q' S'}
    {origin : DemandSynthOrigin signature raw [] []} : Type where
  cuts : List PendingLetCut
  build : ∀ terminal,
    PendingLetStability signature terminal cuts →
      Nonempty (DemandSynthTerminalAudit terminal signature origin)

/-- Deferred terminal audit for one checking origin. -/
structure WCheckAuditPlan
    (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {expression : Expr} {expected : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DemandCheck signature q S context expression expected q' S'}
    {origin : DemandCheckOrigin signature raw [] []} : Type where
  cuts : List PendingLetCut
  build : ∀ terminal,
    PendingLetStability signature terminal cuts →
      Nonempty (DemandCheckTerminalAudit terminal signature origin)

/-- Deferred terminal audit for a chronological synthesis list. -/
structure WSynthsAuditPlan
    (signature : FrozenSig)
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {expressions : List Expr} {targets : List Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DemandSynths signature q S context expressions targets q' S'}
    {origin : DemandSynthsOrigin signature raw [] []} : Type where
  cuts : List PendingLetCut
  build : ∀ terminal,
    PendingLetStability signature terminal cuts →
      Nonempty (DemandSynthsTerminalAudit terminal signature origin)

/-- Package an origin whose terminal audit is independent of pending let
stability (variables, literals, and any other terminal-insensitive leaf). -/
def WSynthAuditPlan.noCuts
    {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {expression : Expr} {target : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {raw : DemandSynth signature q S context expression target q' S'}
    {origin : DemandSynthOrigin signature raw [] []}
    (audit : ∀ terminal,
      Nonempty (DemandSynthTerminalAudit terminal signature origin)) :
    WSynthAuditPlan signature (origin := origin) where
  cuts := []
  build := by
    intro terminal _stable
    exact audit terminal

/-- Literal leaves contain no terminal-sensitive boundary. -/
def WSynthAuditPlan.lit
    {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {value : Int}
    {origin : DemandSynthOrigin signature
      (DemandSynth.lit (q := q) (S := S) (value := value) (Γ := context))
      [] []} :
    WSynthAuditPlan signature (origin := origin) where
  cuts := []
  build := by
    intro terminal _stable
    exact ⟨DemandSynthTerminalAudit.lit.transportOrigin⟩

/-- Lambda merely wraps its body's deferred audit. -/
def WSynthAuditPlan.lam
    {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {name : String} {body : Expr} {bodyTarget : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {bodyRaw : DemandSynth signature { q with nextTy := q.nextTy + 1 } S
      ((name, Scheme.mono (.var q.nextTy)) :: context) body bodyTarget q' S'}
    {bodyOrigin : DemandSynthOrigin signature bodyRaw [] []}
    (bodyPlan : WSynthAuditPlan signature (origin := bodyOrigin)) :
    WSynthAuditPlan signature
      (origin := DemandSynthOrigin.lam bodyOrigin) where
  cuts := bodyPlan.cuts
  build := by
    intro terminal stable
    obtain ⟨bodyAudit⟩ := bodyPlan.build terminal stable
    exact ⟨DemandSynthTerminalAudit.lam bodyAudit⟩

/-- An ordinary checking boundary adds no let cut. -/
def WSynthAuditPlan.check
    {signature : FrozenSig}
    {q q' : InferenceBase.FreshSupply} {S S' terminalSubst : Subst}
    {context : Context} {expression : Expr} {rawTarget expected : Ty}
    {synth : DemandSynth signature q S context expression rawTarget q'
      terminalSubst}
    {synthOrigin : DemandSynthOrigin signature synth [] []}
    {aligned : DemandAlignWithLedger [] terminalSubst rawTarget expected S'}
    (plan : WSynthAuditPlan signature (origin := synthOrigin)) :
    WCheckAuditPlan signature
      (origin := DemandCheckOrigin.mk synthOrigin aligned) where
  cuts := plan.cuts
  build := by
    intro terminal stable
    obtain ⟨audit⟩ := plan.build terminal stable
    exact ⟨DemandCheckTerminalAudit.mk (aligned := aligned) audit⟩

/-- Application concatenates the function and checking-child cut lists and
wraps their eventual-terminal audits structurally. -/
def WSynthAuditPlan.app
    {signature : FrozenSig}
    {q q₁ q' : InferenceBase.FreshSupply} {S S₁ S₂ S' : Subst}
    {context : Context} {function argument : Expr} {functionTarget : Ty}
    {functionRaw : DemandSynth signature q S context function functionTarget
      q₁ S₁}
    {functionOrigin : DemandSynthOrigin signature functionRaw [] []}
    {aligned : DemandAlignTypesWithLedger [] S₁ functionTarget
      (.fn (.var q₁.nextTy) (.var (q₁.nextTy + 1))) S₂}
    {argumentRaw : DemandCheck signature
      { q₁ with nextTy := q₁.nextTy + 2 } S₂ context argument
      (.var q₁.nextTy) q' S'}
    {argumentOrigin : DemandCheckOrigin signature argumentRaw [] []}
    (functionPlan : WSynthAuditPlan signature (origin := functionOrigin))
    (argumentPlan : WCheckAuditPlan signature (origin := argumentOrigin)) :
    WSynthAuditPlan signature
      (origin := DemandSynthOrigin.app functionOrigin aligned argumentOrigin) where
  cuts := functionPlan.cuts ++ argumentPlan.cuts
  build := by
    intro terminal stable
    have functionStable : PendingLetStability signature terminal
        functionPlan.cuts := stable.of_subset (by
      intro cut member
      exact List.mem_append_left _ member)
    have argumentStable : PendingLetStability signature terminal
        argumentPlan.cuts := stable.of_subset (by
      intro cut member
      exact List.mem_append_right _ member)
    obtain ⟨functionAudit⟩ := functionPlan.build terminal functionStable
    obtain ⟨argumentAudit⟩ := argumentPlan.build terminal argumentStable
    exact ⟨DemandSynthTerminalAudit.app
      (aligned := aligned) functionAudit argumentAudit⟩

/-- Empty chronological list. -/
def WSynthsAuditPlan.nil
    {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context} :
    WSynthsAuditPlan signature
      (origin := DemandSynthsOrigin.nil (q := q) (S := S)
        (context := context) (ledger := [])) where
  cuts := []
  build := by
    intro terminal _stable
    exact ⟨DemandSynthsTerminalAudit.nil⟩

/-- Chronological cons concatenates the let cuts found in the head and tail. -/
def WSynthsAuditPlan.cons
    {signature : FrozenSig}
    {q q₁ q' : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {context : Context} {expression : Expr} {expressions : List Expr}
    {target : Ty} {targets : List Ty}
    {head : DemandSynth signature q S context expression target q₁ S₁}
    {headOrigin : DemandSynthOrigin signature head [] []}
    {tail : DemandSynths signature q₁ S₁ context expressions targets q' S'}
    {tailOrigin : DemandSynthsOrigin signature tail [] []}
    (headPlan : WSynthAuditPlan signature (origin := headOrigin))
    (tailPlan : WSynthsAuditPlan signature (origin := tailOrigin)) :
    WSynthsAuditPlan signature
      (origin := DemandSynthsOrigin.cons headOrigin tailOrigin) where
  cuts := headPlan.cuts ++ tailPlan.cuts
  build := by
    intro terminal stable
    have headStable : PendingLetStability signature terminal
        headPlan.cuts := stable.of_subset (by
      intro cut member
      exact List.mem_append_left _ member)
    have tailStable : PendingLetStability signature terminal
        tailPlan.cuts := stable.of_subset (by
      intro cut member
      exact List.mem_append_right _ member)
    obtain ⟨headAudit⟩ := headPlan.build terminal headStable
    obtain ⟨tailAudit⟩ := tailPlan.build terminal tailStable
    exact ⟨DemandSynthsTerminalAudit.cons headAudit tailAudit⟩

/-- Tuple synthesis is a structural wrapper around its chronological list. -/
def WSynthAuditPlan.tuple
    {signature : FrozenSig}
    {q q' : InferenceBase.FreshSupply} {S S' : Subst}
    {context : Context} {expressions : List Expr} {targets : List Ty}
    {children : DemandSynths signature q S context expressions targets q' S'}
    {childrenOrigin : DemandSynthsOrigin signature children [] []}
    (childrenPlan : WSynthsAuditPlan signature (origin := childrenOrigin)) :
    WSynthAuditPlan signature
      (origin := DemandSynthOrigin.tuple childrenOrigin) where
  cuts := childrenPlan.cuts
  build := by
    intro terminal stable
    obtain ⟨childrenAudit⟩ := childrenPlan.build terminal stable
    exact ⟨DemandSynthTerminalAudit.tuple childrenAudit⟩

/-- Direct-self fix is a structural wrapper around its body plus one ordinary
alignment, neither of which introduces a new let cut. -/
def WSynthAuditPlan.fix
    {signature : FrozenSig}
    {q q₁ : InferenceBase.FreshSupply} {S S₁ S' : Subst}
    {context : Context} {self argument : String} {body : Expr}
    {bodyTarget : Ty}
    {bodyRaw : DemandSynth signature { q with nextTy := q.nextTy + 2 } S
      ((argument, Scheme.mono (.var q.nextTy)) ::
        (self, Scheme.mono
          (.fn (.var q.nextTy) (.var (q.nextTy + 1)))) :: context)
      body bodyTarget q₁ S₁}
    {bodyOrigin : DemandSynthOrigin signature bodyRaw [] []}
    {distinct : self ≠ argument} {direct : DirectSelf.Holds self body}
    {nonMatcher : NonMatcherBody body}
    {aligned : DemandAlignTypesWithLedger [] S₁ bodyTarget
      (.var (q.nextTy + 1)) S'}
    (bodyPlan : WSynthAuditPlan signature (origin := bodyOrigin)) :
    WSynthAuditPlan signature
      (origin := DemandSynthOrigin.fix distinct direct nonMatcher bodyOrigin
        aligned) where
  cuts := bodyPlan.cuts
  build := by
    intro terminal stable
    obtain ⟨bodyAudit⟩ := bodyPlan.build terminal stable
    exact ⟨DemandSynthTerminalAudit.fix
      (distinct := distinct) (direct := direct) (nonMatcher := nonMatcher)
      (aligned := aligned) bodyAudit⟩

/-- Let composition adds its own cut to the union of the two child plans.
At the eventual terminal, the common stability premise supplies both child
audits and exactly the `LetFacts` payload of the new origin node. -/
def WSynthAuditPlan.letE
    {signature : FrozenSig}
    {q : InferenceBase.FreshSupply} {S : Subst} {context : Context}
    {name : String} {value body : Expr} {valueTarget : Ty}
    {q₁ : InferenceBase.FreshSupply} {S₁ : Subst} {bodyTarget : Ty}
    {q' : InferenceBase.FreshSupply} {S' : Subst}
    {valueRaw : DemandSynth signature q S context value valueTarget q₁ S₁}
    {valueOrigin : DemandSynthOrigin signature valueRaw [] []}
    {bodyRaw : DemandSynth signature q₁ S₁
      ((name, signature.generalize (context.applySubst S₁)
        (S₁.apply valueTarget)) :: context) body bodyTarget q' S'}
    {bodyOrigin : DemandSynthOrigin signature bodyRaw [] []}
    (valuePlan : WSynthAuditPlan signature (origin := valueOrigin))
    (bodyPlan : WSynthAuditPlan signature (origin := bodyOrigin)) :
    WSynthAuditPlan signature
      (origin := DemandSynthOrigin.letE valueOrigin bodyOrigin) where
  cuts := valuePlan.cuts ++
    ⟨context, valueTarget, S₁⟩ :: bodyPlan.cuts
  build := by
    intro terminal stable
    have valueStable : PendingLetStability signature terminal
        valuePlan.cuts := stable.of_subset (by
      intro cut member
      exact List.mem_append_left _ member)
    have bodyStable : PendingLetStability signature terminal
        bodyPlan.cuts := stable.of_subset (by
      intro cut member
      exact List.mem_append_right valuePlan.cuts
        (List.mem_cons_of_mem _ member))
    have currentMember :
        (⟨context, valueTarget, S₁⟩ : PendingLetCut) ∈
          valuePlan.cuts ++
            ⟨context, valueTarget, S₁⟩ :: bodyPlan.cuts :=
      List.mem_append_right _ List.mem_cons_self
    obtain ⟨valueAudit⟩ := valuePlan.build terminal valueStable
    obtain ⟨bodyAudit⟩ := bodyPlan.build terminal bodyStable
    have facts := stable.letFacts currentMember
    exact ⟨DemandSynthTerminalAudit.letE valueAudit bodyAudit facts⟩

end DM
end TypePM
