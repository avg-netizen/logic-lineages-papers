module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchange
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
/-- Standalone raw swap certificate: pair(packed-cell prefix,pair(Q,pair(R,rawTail))).
No original source acceptance predicate or selected runtime tuple is replaced. -/
def frontOf {k : Nat} (c : Program k) : Program k := leftOf c
def payloadOf {k : Nat} (c : Program k) : Program k := rightOf c
def firstOf {k : Nat} (c : Program k) : Program k := leftOf (payloadOf c)
def restOf {k : Nat} (c : Program k) : Program k := rightOf (payloadOf c)
def secondOf {k : Nat} (c : Program k) : Program k := leftOf (restOf c)
def tailOf {k : Nat} (c : Program k) : Program k := rightOf (restOf c)
def rawCons {k : Nat} (packed tail : Program k) : Program k :=
 .composition OriginalRawSyntaxTransport.consConstructor ![leftOf packed,rightOf packed,tail]
def sourceSuffix : Program 3 := rawCons (firstOf (.projection 2))
 (rawCons (secondOf (.projection 2)) (tailOf (.projection 2)))
def targetSuffix : Program 3 := rawCons (secondOf (.projection 2))
 (rawCons (firstOf (.projection 2)) (tailOf (.projection 2)))
def sourceEndpoint : Program 3 := .composition OriginalTypedArgumentPrefixBuilder.build
 ![frontOf (.projection 2),sourceSuffix]
def targetEndpoint : Program 3 := .composition OriginalTypedArgumentPrefixBuilder.build
 ![frontOf (.projection 2),targetSuffix]
def sourceMatch : Program 3 := OriginalRawSyntaxTransport.sameOf (.projection 0) sourceEndpoint
def targetMatch : Program 3 := OriginalRawSyntaxTransport.sameOf (.projection 1) targetEndpoint
def edge : Program 3 := InternalAcceptance.conjunction sourceMatch targetMatch
/-- Numeric certificate translation, inputs [raw certificate,unchanged parameter]. -/
def translatedFront (R : Program 2) : Program 2 := .composition (OriginalTypedArgumentPrefixBuilder.mapped R)
 ![frontOf (.projection 0),.projection 1]
def translatedFirst (R : Program 2) : Program 2 := .composition (OriginalTypedArgumentPrefixBuilder.cell R)
 ![firstOf (.projection 0),.projection 1]
def translatedSecond (R : Program 2) : Program 2 := .composition (OriginalTypedArgumentPrefixBuilder.cell R)
 ![secondOf (.projection 0),.projection 1]
def translatedTail (R : Program 2) : Program 2 := .composition (OriginalTypedArgumentObservations.argumentObservations R)
 ![tailOf (.projection 0),.projection 1]
def translatedRest (R : Program 2) : Program 2 := pairOf (translatedSecond R) (translatedTail R)
def translatedPayload (R : Program 2) : Program 2 := pairOf (translatedFirst R) (translatedRest R)
def translate (R : Program 2) : Program 2 := pairOf (translatedFront R) (translatedPayload R)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchange
