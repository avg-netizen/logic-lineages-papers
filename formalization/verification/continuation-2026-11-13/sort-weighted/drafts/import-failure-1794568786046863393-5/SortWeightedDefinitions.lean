module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Proof-side weighted fold over the ORIGINAL numeric list codec. The sort,
insertion, evaluator, and selected source tuples are not replaced. -/
def step {k : Nat} (F : Program (k + 1)) : Program (k + 2) :=
 .composition InternalArithmeticPrograms.addition
   ![.composition F (Fin.cons (.projection 0) (fun i : Fin k => .projection i.succ.succ)),.projection 1]
def weighted {k : Nat} (F : Program (k + 1)) : Program (k + 1) :=
 InternalRawListRecursion.listRec (InternalRawListRecursion.zero : Program k) (step F)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedDefinitions
