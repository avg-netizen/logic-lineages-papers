module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalInputDecisionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalInputDecisionProof
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations
open FiniteObservationBits ConfinedStructuralInterpretation TypedValueEnvironment
open SourceConstructorIteration TypedObservationAccess RecursiveComparison OriginalInputDecision

theorem wrongTypeRejection : OriginalInputDecisionTargets.WrongTypeRejection := by
  intro Symbol inst arity I above dec h
  have hn : ¬ Accepted I I.sourceType (emptyWorld I) (rootObservation I) := by
    intro ha
    exact h ha.2.2.1.symm
  refine ⟨?_,?_,?_,?_⟩
  · exact TypedObservationAccessProof.rejectedFalse Symbol inst arity I I.sourceType
      (emptyWorld I) false _ (rootObservation I) hn
  · exact TypedObservationAccessProof.rejectedFalse Symbol inst arity I I.sourceType
      (emptyWorld I) true _ (rootObservation I) hn
  · intro hw
    exact h (RecursiveComparisonProof.weakTypeSoundness Symbol arity above I.context _ _ hw)
  · intro hs
    exact h (RecursiveComparisonProof.strictTypeSoundness Symbol arity above I.context _ _ hs)

theorem rootReadAdequacy : OriginalInputDecisionTargets.RootReadAdequacy := by
  intro Symbol inst arity I above dec
  by_cases h : I.sourceType=I.targetType
  · let o : ObservationAt I I.sourceType (emptyWorld I) :=
      ⟨rootObservation I,Source.SourceOpenedObservationsProof.openedRootMembership
        Symbol arity I.context I.targetType I.target (budget I) le_rfl,rfl,h.symm⟩
    have H := RelationalSyntaxProof.actualIdentityAdequacy Symbol inst arity I above dec
      (emptyWorld I) I.sourceType (inputSource I) o
    rcases I with ⟨Gamma,sigma,tau,s,t⟩
    dsimp at h
    subst tau
    exact H
  · have H := wrongTypeRejection Symbol inst arity I above dec h
    exact ⟨⟨by rw [H.1]; simp,fun hw => (H.2.2.1 hw).elim⟩,
      ⟨by rw [H.2.1]; simp,fun hs => (H.2.2.2 hs).elim⟩⟩

def originalComparisonsDecidable : OriginalInputDecisionTargets.OriginalComparisonsDecidable := by
  intro Symbol inst arity I above dec
  have H := rootReadAdequacy Symbol inst arity I above dec
  exact ⟨if h : compare I above false=true then isTrue (H.1.mp h)
      else isFalse (fun hw => h (H.1.mpr hw)),
    if h : compare I above true=true then isTrue (H.2.mp h)
      else isFalse (fun hs => h (H.2.mpr hs))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalInputDecisionProof
