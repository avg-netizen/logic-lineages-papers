module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilder
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
/-- Auxiliary builder only: [numeric packed-cell prefix,original raw suffix].
Each cell retains its literal type/raw-child pair. No runtime tuple is changed. -/
def step : Program 3 := .composition OriginalRawSyntaxTransport.consConstructor
 ![leftOf (.projection 0),rightOf (.projection 0),.projection 1]
def build : Program 2 := InternalRawListRecursion.listRec (.projection 0) step
/-- Fixed R/parameter, preserving the cell's literal type even for arbitrary codes. -/
def cell (R : Program 2) : Program 2 := pairOf (leftOf (.projection 0))
 (.composition R ![.projection 0,.projection 1])
def mapped (R : Program 2) : Program 2 := InternalListMap.map (cell R)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilder
