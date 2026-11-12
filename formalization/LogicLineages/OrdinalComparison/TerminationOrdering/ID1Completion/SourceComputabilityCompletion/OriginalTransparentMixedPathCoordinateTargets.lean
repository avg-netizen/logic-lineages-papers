module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathRunTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathCoordinateTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Coordinate-level equations for the SAME mixed refined leaf; no global tuple retention.
The transition graph is derived, not assumed. All path/live coordinates are literal graphs. -/
def ActualLambdaEquivalence : Prop := ∀ (source : Program 2) (oldStep : Program 4) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter childS childT childCert childParam d e context gamma extended code head tail state next out : OTerm alpha),
 Nonempty (Derivation body Delta (OriginalTransparentLambdaStep.LambdaHop source s t cert parameter childS childT childCert childParam d e context gamma extended)) →
 Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.path code s t cert parameter)) →
 Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.path tail childS childT childCert childParam)) →
 Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live state s t cert parameter)) →
 Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live next childS childT childCert childParam)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)) →
 Nonempty (Derivation body Delta ((graph4 (OriginalTransparentMixedPathDefinitions.refined source oldStep) out s t cert parameter).iff
  (graph4 (OriginalTransparentMixedPathDefinitions.refined source oldStep) out childS childT childCert childParam)))

def ActualApplicationEquivalence : Prop := ∀ (source : Program 2) (oldStep : Program 4) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter childS childT childCert arg d e arrow code head tail state next out : OTerm alpha),
 Nonempty (Derivation body Delta (OriginalTransparentMixedPathInternalDefinitions.ApplicationHop source s t cert parameter childS childT childCert arg d e arrow)) →
 Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.path code s t cert parameter)) →
 Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.path tail childS childT childCert parameter)) →
 Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live state s t cert parameter)) →
 Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live next childS childT childCert parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)) →
 Nonempty (Derivation body Delta ((graph4 (OriginalTransparentMixedPathDefinitions.refined source oldStep) out s t cert parameter).iff
  (graph4 (OriginalTransparentMixedPathDefinitions.refined source oldStep) out childS childT childCert parameter)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathCoordinateTargets
