module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeSemanticDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeSemanticTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryAgendaDefinitions OriginalHereditaryExpectedDefinitions
open OriginalHereditaryRuntimeSemanticDefinitions OriginalHereditaryRuntimeIterationDefinitions
/-- Conditional semantic subtree execution, with arbitrary agenda suffix and old
stack. The exact local semantic return supplier is explicit until discharged. -/
def DepthExecution : Prop := OriginalHereditaryExpectedReturnTargets.LocalReturn →
 ∀ (R : Program 2) n (arity : Fin n → Nat) c depth (a : Job n)
 (suffix : List (Frame n)) (old : List Nat),
 OriginalHereditaryTypedJobDefinitions.Typed arity a → FrontierTerminal depth a →
 ∃ value, Expected arity R c a value ∧
 (tick R)^[2 * OriginalHereditaryWorkBound.visits depth a.core]
   (state c (.visit a :: suffix) old) = state c suffix (value :: old)
/-- Actual PR run at exact subtree visit/return count; still conditional on
LocalReturn, not an assumed global result invariant. -/
def ExactExecution : Prop := OriginalHereditaryExpectedReturnTargets.LocalReturn →
 ∀ (R : Program 2) n (arity : Fin n → Nat) c (a : Job n)
 (suffix : List (Frame n)) (old : List Nat),
 OriginalHereditaryTypedJobDefinitions.Typed arity a →
 ∃ value, Expected arity R c a value ∧
 evaluate (run R) (List.Vector.ofFn ![2 * OriginalHereditaryWorkBound.totalWork a.core,
   state c (.visit a :: suffix) old]) = state c suffix (value :: old)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeSemanticTargets
