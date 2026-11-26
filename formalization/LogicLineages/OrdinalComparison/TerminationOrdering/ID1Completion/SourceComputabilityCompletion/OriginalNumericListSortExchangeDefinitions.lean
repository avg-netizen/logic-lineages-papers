module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortPrefixTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchange
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Inputs [source,target,certificate]. The certificate is the literal nested
pair (front,(x,(y,tail))). Numeric-list codes and pair decoding are total.
The checker does not inspect sort output, an observer, a source predicate,
or a native permutation decision. -/
def front : Program 3 := leftOf (.projection 2)
def payload : Program 3 := rightOf (.projection 2)
def first : Program 3 := leftOf payload
def rest : Program 3 := rightOf payload
def second : Program 3 := leftOf rest
def tail : Program 3 := rightOf rest
def afterSecond : Program 3 := consOf second tail
def afterFirst : Program 3 := consOf first tail
def firstSecond : Program 3 := consOf first afterSecond
def secondFirst : Program 3 := consOf second afterFirst
def sourceEndpoint : Program 3 := .composition InternalApplicationValidityStackAppend.append ![front,firstSecond]
def targetEndpoint : Program 3 := .composition InternalApplicationValidityStackAppend.append ![front,secondFirst]
def sourceMatch : Program 3 := OriginalRawSyntaxTransport.sameOf (.projection 0) sourceEndpoint
def targetMatch : Program 3 := OriginalRawSyntaxTransport.sameOf (.projection 1) targetEndpoint
def edge : Program 3 := InternalAcceptance.conjunction sourceMatch targetMatch
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchange
