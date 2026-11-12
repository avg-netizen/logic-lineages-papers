module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnArgumentsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnAssemblySupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepArgumentsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnArgumentsReturnProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedAuxiliaryCoding NumberedMultisetNumeric
open OriginalHereditaryAgendaDefinitions OriginalHereditaryExpectedDefinitions OriginalHereditarySettledObserverDefinitions
open OriginalHereditaryExpectedReturnSupportProof OriginalHereditaryExpectedReturnAssemblySupportProof
open OriginalHereditaryWorkBound OriginalHereditaryFiniteObserver
open OriginalHereditaryTypedJobDecorationProof OriginalHereditaryVisitScheduler

theorem argumentsReturnExpected (R : Program 2) {n : Nat} {arity : Fin n → Nat} {Gamma types : List Ty}
 (c : Nat) (args : AuxArguments (Fin n) arity Gamma types) (values agenda old : List Nat)
 (hv : List.Forall₂ (Expected arity R c) (jobs c (argumentJob args)) values) :
 evaluate (OriginalHereditaryReturnStep.step R) (List.Vector.ofFn ![
   stateNumber (OriginalHereditaryRuntimeWork.frameNumber c (.returning (argumentJob args)) :: agenda)
     (values.reverse ++ old)]) = stateNumber agenda (numbersNumber (argumentValues R c args) :: old) := by
 let Q := family R (argumentDepth args)
 rw [jobs,successors,decorateAppend] at hv
 obtain ⟨cv,dv,he,hc,hd⟩ := splitAppend _ _ _ values hv
 have hc' := OriginalHereditaryExpectedReturnArgumentsProof.argumentChildrenExpected (c:=c) R args
   (argumentDepth args) (fun q hq => OriginalHereditaryExpectedJointDepthProof.memberWeight args q hq)
 have hcv := valuesUnique arity R c _ cv _ hc hc'
 subst cv
 have hlen : dv.length = Gamma.length := by
   have hh := relationLength hd
   rw [decorateLength,OriginalHereditaryWorkBoundProof.deletionsLength] at hh
   exact hh.symm
 rw [he,List.reverse_append,List.append_assoc,argumentFrame Q c args]
 have hr := OriginalHereditaryReturnStepArgumentsProof.argumentsReturn R Q n arity Gamma types c args dv agenda old hlen
 rw [OriginalHereditaryExpectedJointDepthProof.argumentsJointDepth R n arity Gamma types c args
   (argumentDepth args) (Nat.le_refl _)] at hr
 simp only [OriginalHereditaryResultStack.stack,List.append_assoc] at hr
 exact hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnArgumentsReturnProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnArgumentsReturnProof
