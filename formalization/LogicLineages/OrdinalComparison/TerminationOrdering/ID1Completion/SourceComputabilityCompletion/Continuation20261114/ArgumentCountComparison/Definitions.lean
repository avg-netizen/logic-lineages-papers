module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport
/-- Step inputs [candidate,tailTruth,leftList,rightList], original multiplicity test. -/
def leftCount : Program 4 := .composition ArgumentEntryCount.count ![.projection 2,.projection 0]
def rightCount : Program 4 := .composition ArgumentEntryCount.count ![.projection 3,.projection 0]
def step : Program 4 := InternalAcceptance.branch (sameOf leftCount rightCount)
  (constant 4 0) (.projection 1)
/-- Inputs [candidates,leftList,rightList], literal bounded universal fold. -/
def allCounts : Program 3 := InternalRawListRecursion.listRec (constant 2 1) step
/-- Original bounded domain is left ++ right, not a sorted or deduplicated replacement. -/
def permutation : Program 2 := .composition allCounts
  ![InternalApplicationValidityStackAppend.append,.projection 0,.projection 1]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison
