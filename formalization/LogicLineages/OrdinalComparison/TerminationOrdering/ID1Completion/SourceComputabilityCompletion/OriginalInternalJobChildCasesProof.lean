module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildTagCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalInternalJobChildCasesTargets
open OriginalInternalJobChildCasesContextProof (consumerWeaken)
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof (orCases arityOneTags arityTwoTags)
theorem firstOneCases : ActualCases true 1 := by
 intro body alpha Delta H M W role typ raw cell parameter c gamma psi ha hp harity hj next
 apply orCases (arityOneTags raw harity)
 · intro Theta inc ht
   exact OriginalInternalJobChildTagCasesProof.lambdaFirst H M W role typ raw cell parameter c gamma psi ht
    (weakenProof ha inc) (weakenProof hp inc) (weakenProof hj inc)
    (consumerWeaken H M W (numeral 0) role typ raw cell parameter c gamma psi next Theta inc)
 · intro Theta inc ht
   exact OriginalInternalJobChildTagCasesProof.ordinaryFirst H M W role typ raw cell parameter c gamma psi ht
    (weakenProof ha inc) (weakenProof hp inc) (weakenProof hj inc)
    (consumerWeaken H M W (numeral 0) role typ raw cell parameter c gamma psi next Theta inc)
theorem firstTwoCases : ActualCases true 2 := by
 intro body alpha Delta H M W role typ raw cell parameter c gamma psi ha hp harity hj next
 apply orCases (arityTwoTags raw harity)
 · intro Theta inc ht
   exact OriginalInternalJobChildTagCasesProof.applicationFirst H M W role typ raw cell parameter c gamma psi ht
    (weakenProof ha inc) (weakenProof hp inc) (weakenProof hj inc)
    (consumerWeaken H M W (numeral 0) role typ raw cell parameter c gamma psi next Theta inc)
 · intro Theta inc ht
   apply orCases ht
   · intro Xi inc2 ht2
     have incl : ∀ p ∈ Delta, p ∈ Xi := fun p h => inc2 p (inc p h)
     exact OriginalInternalJobChildTagCasesProof.numberedFirst H M W role typ raw cell parameter c gamma psi ht2
      (weakenProof ha incl) (weakenProof hp incl) (weakenProof hj incl)
      (consumerWeaken H M W (numeral 0) role typ raw cell parameter c gamma psi next Xi incl)
   · intro Xi inc2 ht2
     have incl : ∀ p ∈ Delta, p ∈ Xi := fun p h => inc2 p (inc p h)
     exact OriginalInternalJobChildTagCasesProof.consFirst H M W role typ raw cell parameter c gamma psi ht2
      (weakenProof ha incl) (weakenProof hp incl) (weakenProof hj incl)
      (consumerWeaken H M W (numeral 0) role typ raw cell parameter c gamma psi next Xi incl)
theorem secondCases : ActualCases false 2 := by
 intro body alpha Delta H M W role typ raw cell parameter c gamma psi ha hp harity hj next
 apply orCases (arityTwoTags raw harity)
 · intro Theta inc ht
   exact OriginalInternalJobChildTagCasesProof.applicationSecond H M W role typ raw cell parameter c gamma psi ht
    (weakenProof ha inc) (weakenProof hp inc) (weakenProof hj inc)
    (consumerWeaken H M W (numeral 1) role typ raw cell parameter c gamma psi next Theta inc)
 · intro Theta inc ht
   apply orCases ht
   · intro Xi inc2 ht2
     have incl : ∀ p ∈ Delta, p ∈ Xi := fun p h => inc2 p (inc p h)
     exact OriginalInternalJobChildTagCasesProof.numberedSecond H M W role typ raw cell parameter c gamma psi ht2
      (weakenProof ha incl) (weakenProof hp incl) (weakenProof hj incl)
      (consumerWeaken H M W (numeral 1) role typ raw cell parameter c gamma psi next Xi incl)
   · intro Xi inc2 ht2
     have incl : ∀ p ∈ Delta, p ∈ Xi := fun p h => inc2 p (inc p h)
     exact OriginalInternalJobChildTagCasesProof.consSecond H M W role typ raw cell parameter c gamma psi ht2
      (weakenProof ha incl) (weakenProof hp incl) (weakenProof hj incl)
      (consumerWeaken H M W (numeral 1) role typ raw cell parameter c gamma psi next Xi incl)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildCasesProof
