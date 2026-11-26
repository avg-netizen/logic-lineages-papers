module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport
/-- Original unary extraction is instantiated at the unused parameter zero. -/
def leftEntries : Program 2 := .composition ArgumentEntriesRecursor.extract ![.projection 0,constant 2 0]
def rightEntries : Program 2 := .composition ArgumentEntriesRecursor.extract ![.projection 1,constant 2 0]
def leftList : Program 2 := .composition InternalEqualityTest.predecessor (fun _ : Fin 1 => leftEntries)
def rightList : Program 2 := .composition InternalEqualityTest.predecessor (fun _ : Fin 1 => rightEntries)
def compare : Program 2 := .composition ArgumentCountComparison.permutation ![leftList,rightList]
/-- Both original Option extractions must succeed. None=0, Some list=code+1. -/
def check : Program 2 := InternalAcceptance.branch leftEntries (constant 2 0)
  (InternalAcceptance.branch rightEntries (constant 2 0) compare)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation
