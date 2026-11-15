module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.StatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Nat recursion step inputs [index,previous]. Keep index as a genuine
singleton entry, including index0; zero is not a missing Option payload. -/
def singleton : Program 2 := .composition InternalListCodec.consCode
  ![.projection 0,InternalAcceptance.constantZero 2]
/-- Append at the right, so enumeration is ascending, not reversed. -/
def step : Program 2 := .composition InternalApplicationValidityStackAppend.append
  ![.projection 1,singleton]
/-- Literal ascending range, with empty-list0 at bound0. Every Nat bound is
valid; there is no typed decoder, filter, or malformed-bound fallback. -/
def range : Program 1 := .recursion (InternalAcceptance.constantZero 0) step
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange
