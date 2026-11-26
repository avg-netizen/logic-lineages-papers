module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrependTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrefix
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Inputs [head, recursively lifted suffix path, original path]. -/
def step : Program 3 := .composition OriginalNumericListSortExchangePathPrepend.mapPath ![.projection 1,.projection 0]
/-- Inputs [numeric prefix, original certified path]. Original list recursion
lifts the tail first, then the head, preserving prefix order. -/
def mapPrefix : Program 2 := InternalRawListRecursion.listRec (.projection 0) step
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrefix
