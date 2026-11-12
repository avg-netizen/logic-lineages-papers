module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeIterationDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual numeric primitive recursion; inputs [count, encoded runtime state]. -/
def run (R : Program 2) : Program 2 :=
 InternalNumericIteration.repeatProgram (OriginalHereditaryCombinedStep.step R)
def tick (R : Program 2) (state : Nat) :=
 evaluate (OriginalHereditaryCombinedStep.step R) (List.Vector.ofFn ![state])
def fuel {n : Nat} (a : OriginalHereditaryAgendaDefinitions.Job n) :=
 2 * OriginalHereditaryWorkBound.budget (OriginalHereditaryWorkBound.weight a.core + 2)
   (OriginalHereditaryWorkBound.weight a.core)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeIterationDefinitions
