module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLiteralEndpointDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Context membership at the literal original left(parameter), not a selected tuple alias. -/
def memberAt (M : Program 2) : Program 2 :=
 .composition M ![.projection 0,leftOf (.projection 1)]
def endpoint (H G : Program 1) (M W : Program 2) : Program 6 :=
 InternalParameterizedStructuralEndpointGuard.endpoint
  (OriginalUniverseDecoder.source H G M W) (OriginalTypedDecoder.target H G) (memberAt M)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLiteralEndpointDefinitions
