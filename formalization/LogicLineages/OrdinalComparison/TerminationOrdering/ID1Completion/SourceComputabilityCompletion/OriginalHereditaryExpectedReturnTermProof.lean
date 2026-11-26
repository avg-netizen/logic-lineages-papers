module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnDeletionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnAssemblySupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepTermProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnTermProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedAuxiliaryCoding NumberedMultisetNumeric
open OriginalHereditaryAgendaDefinitions OriginalHereditaryExpectedDefinitions OriginalHereditarySettledObserverDefinitions
open OriginalHereditaryExpectedReturnSupportProof OriginalHereditaryExpectedReturnAssemblySupportProof
open OriginalHereditaryExpectedReturnRowProof OriginalHereditaryWorkBound OriginalHereditaryFiniteObserver
open OriginalHereditaryTypedJobDecorationProof OriginalHereditaryVisitScheduler

theorem termReturnExpected (R : Program 2) {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
 (c : Nat) (q : Packed (Fin n) arity Gamma) (values agenda old : List Nat)
 (hv : List.Forall₂ (Expected arity R c) (jobs c (termJob q)) values) :
 evaluate (OriginalHereditaryReturnStep.step R) (List.Vector.ofFn ![
   stateNumber (OriginalHereditaryRuntimeWork.frameNumber c (.returning (termJob q)) :: agenda)
     (values.reverse ++ old)]) = stateNumber agenda (settledValue R c ⟨Gamma,q⟩ :: old) := by
 let Q := family R (OriginalHereditaryNativeBoundDefinitions.weight ⟨Gamma,q⟩)
 let childValues := OriginalHereditaryReturnStep.termChildren Q c q
 let deletionValues := (deletionsFrom (termCode q.2) [] Gamma).map (rawValue Q q.1 c)
 have hc := OriginalHereditaryExpectedReturnChildrenProof.termChildrenExpected (c:=c) R q
 have hd := OriginalHereditaryExpectedReturnDeletionProof.termDeletionsExpected (c:=c) R q
   (children Gamma (termCode q.2)).length (by rw [OriginalHereditaryTypedJobChildrenProof.childrenLength])
 have hall : List.Forall₂ (Expected arity R c) (jobs c (termJob q)) (childValues ++ deletionValues) := by
   rw [jobs,successors,decorateAppend]
   simpa only [Nat.zero_add,termJob,childValues,deletionValues,Q] using appendRelation hc hd
 have he := valuesUnique arity R c _ values _ hv hall
 rw [he,List.reverse_append,List.append_assoc,termFrame Q c q]
 have hlen : deletionValues.length = Gamma.length := by
   simp only [deletionValues,List.length_map,OriginalHereditaryWorkBoundProof.deletionsLength]
 have hr := OriginalHereditaryReturnStepTermProof.termReturn R Q n arity Gamma c q deletionValues agenda old hlen
 have hu := OriginalHereditarySettledObserverProof.unfolding R n arity c ⟨Gamma,q⟩
 rw [rowsAt Q c q] at hu
 simp only [OriginalHereditaryFiniteStability.value] at hu
 simp only [OriginalHereditaryResultStack.stack,List.append_assoc] at hr
 rw [← hu] at hr
 exact hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnTermProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnTermProof
