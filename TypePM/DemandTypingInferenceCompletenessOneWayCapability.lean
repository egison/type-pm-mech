import TypePM.CapMatch

/-!
# Post-composition laws for the one-way capability matcher

A one-way witness keeps its producer fixed, so it is not itself invariant
under an arbitrary later renaming.  Chronological transport needs the related
absorption law: once the matcher has replaced consumer leaves by producer
subtrees, every later post sees the same result whether that replacement is
replayed or not.
-/

namespace TypePM
namespace DemandTypingInferenceCompletenessOneWayCapability

mutual

theorem demandMatches_comp
    (later earlier : CapSubst) :
    ∀ {producer consumer : Cap},
      DemandMatches earlier producer consumer →
        DemandMatches (CapSubst.comp later earlier)
          (producer.apply later) consumer
  | producer, .any, _ => by
      cases producer <;> simp only [DemandMatches]
  | producer, .var varId, matched => by
      cases producer <;>
        simp only [DemandMatches, CapSubst.comp, Cap.apply] at matched ⊢
      all_goals
        exact congrArg (fun capability : Cap => capability.apply later) matched
  | producer, .skolem _, matched => by
      cases producer <;> simp only [DemandMatches] at matched ⊢
      exact matched
  | producer, .con _ _, matched => by
      cases producer <;> simp only [DemandMatches] at matched ⊢
      exact ⟨matched.1,
        demandMatchesList_comp later earlier matched.2⟩
  | producer, .prod _, matched => by
      cases producer <;> simp only [DemandMatches] at matched ⊢
      exact demandMatchesList_comp later earlier matched

theorem demandMatchesList_comp
    (later earlier : CapSubst) :
    ∀ {producers consumers : List Cap},
      DemandMatchesList earlier producers consumers →
        DemandMatchesList (CapSubst.comp later earlier)
          (Cap.applyList later producers) consumers
  | [], [], _ => trivial
  | _ :: _, _ :: _, matched =>
      ⟨demandMatches_comp later earlier matched.1,
        demandMatchesList_comp later earlier matched.2⟩
  | [], _ :: _, matched => False.elim matched
  | _ :: _, [], matched => False.elim matched

end

mutual

theorem demandMatches_reflect_comp
    (forward reverse later : CapSubst) :
    ∀ {producer consumer : Cap},
      consumer = (consumer.apply forward).apply reverse →
      DemandMatches later producer (consumer.apply forward) →
      DemandMatches (CapSubst.comp later forward) producer consumer
  | producer, .any, _, _ => by cases producer <;> trivial
  | producer, .var varId, inverse, matched => by
      cases imageEquation : forward varId with
      | any => simp [Cap.apply, imageEquation] at inverse
      | var image =>
          rw [show (Cap.var varId).apply forward = .var image by
            simpa only [Cap.apply] using imageEquation] at matched
          have matchedEq : later image = producer := by
            simpa only [DemandMatches] using matched
          simpa only [DemandMatches, CapSubst.comp, imageEquation, Cap.apply]
            using matchedEq
      | skolem _ => simp [Cap.apply, imageEquation] at inverse
      | con _ _ => simp [Cap.apply, imageEquation] at inverse
      | prod _ => simp [Cap.apply, imageEquation] at inverse
  | producer, .skolem _, _, matched => by
      cases producer <;> simp only [Cap.apply, DemandMatches] at matched ⊢
      exact matched
  | producer, .con _ consumers, inverse, matched => by
      cases producer <;> simp only [Cap.apply, DemandMatches] at matched ⊢
      have inverseList : consumers =
          Cap.applyList reverse (Cap.applyList forward consumers) := by
        simpa only [Cap.apply, Cap.con.injEq, true_and] using inverse
      exact ⟨matched.1,
        demandMatchesList_reflect_comp forward reverse later inverseList
          matched.2⟩
  | producer, .prod consumers, inverse, matched => by
      cases producer <;> simp only [Cap.apply, DemandMatches] at matched ⊢
      have inverseList : consumers =
          Cap.applyList reverse (Cap.applyList forward consumers) := by
        simpa only [Cap.apply, Cap.prod.injEq] using inverse
      exact demandMatchesList_reflect_comp forward reverse later inverseList
        matched

theorem demandMatchesList_reflect_comp
    (forward reverse later : CapSubst) :
    ∀ {producers consumers : List Cap},
      consumers = Cap.applyList reverse (Cap.applyList forward consumers) →
      DemandMatchesList later producers
        (Cap.applyList forward consumers) →
      DemandMatchesList (CapSubst.comp later forward) producers consumers
  | [], [], _, _ => trivial
  | _ :: _, [], _, matched => False.elim matched
  | [], _ :: _, _, matched => False.elim matched
  | producer :: producers, consumer :: consumers, inverse, matched => by
      simp only [Cap.applyList, List.cons.injEq] at inverse matched ⊢
      exact ⟨demandMatches_reflect_comp forward reverse later inverse.1
          matched.1,
        demandMatchesList_reflect_comp forward reverse later inverse.2
          matched.2⟩

end

theorem oneWayAt_forward_postDemand
    {forward reverse declarativeCap : CapSubst}
    {declarativeProducer executableProducer : Cap}
    {declarativeConsumer executableConsumer : Cap}
    (producerForward :
      declarativeProducer = executableProducer.apply forward)
    (consumerForward :
      declarativeConsumer = executableConsumer.apply forward)
    (consumerReverse :
      executableConsumer = declarativeConsumer.apply reverse)
    (oneWay : OneWayAt declarativeCap declarativeProducer
      declarativeConsumer) :
    DemandMatches (CapSubst.comp declarativeCap forward)
      (executableProducer.apply
        (CapSubst.comp declarativeCap forward)) executableConsumer := by
  have inverse : executableConsumer =
      (executableConsumer.apply forward).apply reverse := by
    rw [← consumerForward, ← consumerReverse]
  have transported := demandMatches_reflect_comp forward reverse
    declarativeCap inverse (by simpa [consumerForward] using oneWay.2.2)
  have producerStable : executableProducer.apply
      (CapSubst.comp declarativeCap forward) = declarativeProducer := by
    rw [Cap.apply_comp, ← producerForward, oneWay.2.1]
  simpa only [producerStable] using transported

theorem capMatchRestricted_absorbed
    {producer consumer : Cap} {bindings : CapMatch.Bindings}
    (matched : CapMatch.matchCap producer consumer = some bindings)
    (later : CapSubst)
    (laterDemand :
      DemandMatches later (producer.apply later) consumer) :
    later = CapSubst.comp later
      (bindings.toSubstWithin consumer.fcv) := by
  let exact := bindings.toSubstWithin consumer.fcv
  have exactOneWay : OneWayAt exact producer consumer :=
    CapMatch.matchCap_restricted_sound matched
  have composedDemand :
      DemandMatches (CapSubst.comp later exact)
        (producer.apply later) consumer :=
    demandMatches_comp later exact exactOneWay.2.2
  funext varId
  by_cases member : varId ∈ consumer.fcv
  · exact demandMatches_unique_on_consumer later
      (CapSubst.comp later exact) (producer.apply later) consumer
        laterDemand composedDemand varId member
  · change later varId = (exact varId).apply later
    rw [exactOneWay.1 varId member]
    rfl

end DemandTypingInferenceCompletenessOneWayCapability
end TypePM
