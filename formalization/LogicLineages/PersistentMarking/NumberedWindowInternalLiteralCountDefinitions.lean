module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCount
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open SourceComputabilityCompletion.OriginalRawSyntaxTransport

/-- Literal transcription of Nov14 ArgumentEntryCount.step. -/
def entryStep : Program 3 := InternalAcceptance.branch (sameOf (.projection 0) (.projection 2))
  (.projection 1) (succOf (.projection 1))

def entryCount : Program 2 := InternalRawListRecursion.listRec (constant 1 0) entryStep

/-- Literal transcription of Nov14 ArgumentCountComparison; every occurrence
of the actual appended candidate tape is checked, with no deduplication. -/
def leftCount : Program 4 := .composition entryCount ![.projection 2,.projection 0]
def rightCount : Program 4 := .composition entryCount ![.projection 3,.projection 0]
def step : Program 4 := InternalAcceptance.branch (sameOf leftCount rightCount)
  (constant 4 0) (.projection 1)
def allCounts : Program 3 := InternalRawListRecursion.listRec (constant 2 1) step
def permutation : Program 2 := .composition allCounts
  ![InternalApplicationValidityStackAppend.append,.projection 0,.projection 1]

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCount
