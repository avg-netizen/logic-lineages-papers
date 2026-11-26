module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeIterationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeIterationTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryAgendaDefinitions OriginalHereditaryRuntimeWork
open OriginalHereditaryRuntimeIterationDefinitions
/-- All numeric inputs, including malformed states. -/
def Calibration : Prop := ∀ R count state,
 evaluate (run R) (List.Vector.ofFn ![count,state]) = (tick R)^[count] state
/-- Work only. Results can be arbitrary numeric data. -/
def TraceWork : Prop := ∀ (R : Program 2) n (arity : Fin n → Nat) c count
 (before after : List (Frame n)) state,
 TypedAgenda arity before → Trace c count before after →
 (Nat.unpair state).1 = agendaNumber c before →
 (Nat.unpair ((tick R)^[count] state)).1 = agendaNumber c after
/-- A fixed coarse PR iteration count empties the work agenda of a typed root.
No correctness of the remaining result stack or primitive-operation cost is asserted. -/
def Completion : Prop := ∀ (R : Program 2) n (arity : Fin n → Nat) c
 (a : Job n) result,
 OriginalHereditaryTypedJobDefinitions.Typed arity a →
 (Nat.unpair (evaluate (run R) (List.Vector.ofFn ![fuel a,
   Nat.pair (agendaNumber c [.visit a]) result]))).1 = 0

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeIterationTargets
