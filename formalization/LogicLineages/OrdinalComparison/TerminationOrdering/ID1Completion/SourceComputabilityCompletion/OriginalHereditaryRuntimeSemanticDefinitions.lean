module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeIterationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeSemanticDefinitions
open OriginalHereditaryAgendaDefinitions
/-- State encoding for actual frames and actual numeric completed values. -/
def state {n : Nat} (c : Nat) (agenda : List (Frame n)) (values : List Nat) :=
 OriginalHereditaryVisitScheduler.stateNumber (agenda.map (OriginalHereditaryRuntimeWork.frameNumber c)) values

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeSemanticDefinitions
