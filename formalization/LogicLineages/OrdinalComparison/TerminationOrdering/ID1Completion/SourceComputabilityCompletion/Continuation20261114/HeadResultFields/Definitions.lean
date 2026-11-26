module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadResult.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadResultFields
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Guarded raw metadata extraction followed by the actual result-type AST. -/
def result (V : Program 3) (target : Bool) : Program 3 :=
  .composition OriginalHeadResult.headResult (fun _ : Fin 1 => TransparentMetadataFields.head V target)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadResultFields
