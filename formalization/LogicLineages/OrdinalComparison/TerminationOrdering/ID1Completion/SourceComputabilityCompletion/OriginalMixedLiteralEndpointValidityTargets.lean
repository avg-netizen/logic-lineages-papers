module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLiteralEndpointDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathInternalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLiteralEndpointValidityTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SourceComputabilityFormulaSupportProof (numeral)
/-- Literal decoder endpoint supporting law. Actual source constructors and the exact
target-function source graph are explicit; no selected-tuple equality or final wrapper is claimed. -/
def ActualEndpointFromTargetSource : Prop := ∀ (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter fn targetFn childCert arg d e arrow fp ap : OTerm alpha),
 Nonempty (Derivation body Delta (InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg s)) →
 Nonempty (Derivation body Delta (OriginalTransparentMixedPathInternalDefinitions.ApplicationHop
  (OriginalUniverseDecoder.source H G M W) s t cert parameter fn targetFn childCert arg d e arrow)) →
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) targetFn parameter)) →
 Nonempty (Derivation body Delta (InternalParameterizedApplicationStepChecker.endpointGraph
  (OriginalMixedLiteralEndpointDefinitions.endpoint H G M W) (numeral 1) d e fn targetFn arg parameter))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLiteralEndpointValidityTargets
