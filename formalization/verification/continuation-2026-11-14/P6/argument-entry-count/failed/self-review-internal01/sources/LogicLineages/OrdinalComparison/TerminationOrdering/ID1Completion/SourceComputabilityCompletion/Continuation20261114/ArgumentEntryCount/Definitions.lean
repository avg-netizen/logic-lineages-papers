module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesRecursor.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport
/-- Original countPrimitive fold step inputs [head,tailCount,needle]. -/
def step : Program 3 := InternalAcceptance.branch (sameOf (.projection 0) (.projection 2))
  (.projection 1) (succOf (.projection 1))
/-- Input [numeric list,needle], the exact original right-fold counter. -/
def count : Program 2 := InternalRawListRecursion.listRec (constant 1 0) step
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount
