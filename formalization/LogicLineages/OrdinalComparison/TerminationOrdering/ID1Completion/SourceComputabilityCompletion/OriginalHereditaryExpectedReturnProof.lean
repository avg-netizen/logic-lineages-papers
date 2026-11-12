module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnTermProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnArgumentsReturnProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedAuxiliaryCoding NumberedMultisetNumeric
open OriginalHereditaryAgendaDefinitions OriginalHereditaryExpectedDefinitions OriginalHereditarySettledObserverDefinitions
open OriginalHereditaryExpectedReturnSupportProof OriginalHereditaryTypedJobDefinitions

theorem localReturn : OriginalHereditaryExpectedReturnTargets.LocalReturn := by
 intro R n arity c a values agenda old ha hv
 rcases a with ⟨role,typ,Gamma,code⟩
 change CoreTyped arity role typ Gamma code at ha
 cases ha with
 | term q =>
   exact ⟨settledValue R c ⟨Gamma,⟨_,q⟩⟩,expectedTerm R c ⟨_,q⟩,
     OriginalHereditaryExpectedReturnTermProof.termReturnExpected R c ⟨_,q⟩ values agenda old hv⟩
 | arguments args =>
   exact ⟨numbersNumber (argumentValues R c args),expectedArguments R c args,
     OriginalHereditaryExpectedReturnArgumentsReturnProof.argumentsReturnExpected R c args values agenda old hv⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnProof
