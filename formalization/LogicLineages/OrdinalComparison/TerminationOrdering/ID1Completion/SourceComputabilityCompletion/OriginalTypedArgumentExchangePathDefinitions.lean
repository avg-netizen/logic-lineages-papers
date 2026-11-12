module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangePath
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Original paired path entry and unchanged runtime parameter. -/
def observedVertex (R : Program 2) : Program 2 := .composition (OriginalTypedArgumentObservations.argumentObservations R)
 ![leftOf (.projection 0),.projection 1]
def numericCertificate (R : Program 2) : Program 2 := .composition (OriginalTypedArgumentExchange.translate R)
 ![rightOf (.projection 0),.projection 1]
def entryMap (R : Program 2) : Program 2 := pairOf (observedVertex R) (numericCertificate R)
/-- Original numeric map, retaining order and the same parameter at every entry. -/
def mapPath (R : Program 2) : Program 2 := InternalListMap.map (entryMap R)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangePath
