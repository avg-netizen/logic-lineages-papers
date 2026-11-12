module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeSemanticTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeCorrectnessTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryAgendaDefinitions OriginalHereditaryExpectedDefinitions
open OriginalHereditaryRuntimeSemanticDefinitions OriginalHereditaryRuntimeIterationDefinitions
/-- Concrete semantic subtree execution, without a local-return premise. -/
def ExactExecution : Prop := ∀ (R : Program 2) n (arity : Fin n → Nat) c (a : Job n)
 (suffix : List (Frame n)) (old : List Nat),
 OriginalHereditaryTypedJobDefinitions.Typed arity a →
 ∃ value, Expected arity R c a value ∧
 evaluate (run R) (List.Vector.ofFn ![2 * OriginalHereditaryWorkBound.totalWork a.core,
   state c (.visit a :: suffix) old]) = state c suffix (value :: old)
/-- Fixed-budget actual Program execution returns an Expected value and preserves
the old stack exactly. Empty-work padding does not change any result data. -/
def BudgetExecution : Prop := ∀ (R : Program 2) n (arity : Fin n → Nat) c (a : Job n)
 (old : List Nat), OriginalHereditaryTypedJobDefinitions.Typed arity a →
 ∃ value, Expected arity R c a value ∧
 evaluate (run R) (List.Vector.ofFn ![fuel a,state c [.visit a] old]) =
   state (n:=n) c [] (value :: old)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeCorrectnessTargets
