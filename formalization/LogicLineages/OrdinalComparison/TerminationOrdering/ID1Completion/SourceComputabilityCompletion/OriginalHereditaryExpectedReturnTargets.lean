module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryAgendaDefinitions OriginalHereditaryExpectedDefinitions
/-- Actual completed successor values in the literal native expansion order.
The Program is the unchanged return step; the Expected relation is proof-only.
No assertion that the complete evaluator has already computed these values. -/
def LocalReturn : Prop := ∀ R n (arity : Fin n → Nat) c (a : Job n)
 (values agenda old : List Nat),
 OriginalHereditaryTypedJobDefinitions.Typed arity a →
 List.Forall₂ (Expected arity R c) (jobs c a) values →
 ∃ v, Expected arity R c a v ∧
   evaluate (OriginalHereditaryReturnStep.step R) (List.Vector.ofFn ![
     OriginalHereditaryVisitScheduler.stateNumber
       (OriginalHereditaryRuntimeWork.frameNumber c (.returning a) :: agenda)
       (values.reverse ++ old)]) =
     OriginalHereditaryVisitScheduler.stateNumber agenda (v :: old)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnTargets
