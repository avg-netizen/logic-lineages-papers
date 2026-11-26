module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMinimum.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.LengthAlignedPrimary
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Concrete count supplier using exactly the selected pool's literal raw-list
length. This changes only a new chosen tuple, not any prior accepted program. -/
def countOfPool (P : Program 2) : Program 2 :=
  .composition OriginalContextInsertion.length (fun _ : Fin 1 => P)
/-- Same original invalid-seed guard and original singleton reachability run. -/
def primary (T P : Program 2) (E : Program 3) : Program 2 :=
  TransparentPrimary.primary T (countOfPool P) P E
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.LengthAlignedPrimary
