module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedAgendaDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedAgendaTargets
open OriginalHereditaryAgendaDefinitions OriginalHereditaryTypedJobDefinitions
open OriginalHereditaryTypedAgendaDefinitions
def StepPreservation : Prop := ∀ n (arity : Fin n → Nat) c (source target : List (Frame n)),
 Step c source target → AgendaTyped arity source → AgendaTyped arity target
def TracePreservation : Prop := ∀ n (arity : Fin n → Nat) c count (source target : List (Frame n)),
 Trace c count source target → AgendaTyped arity source → AgendaTyped arity target
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedAgendaTargets
