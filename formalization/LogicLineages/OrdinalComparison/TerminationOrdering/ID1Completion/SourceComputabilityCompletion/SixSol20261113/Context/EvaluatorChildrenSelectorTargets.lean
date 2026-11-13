module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSelectorTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaTraversalInternal
/-- Pure literal selector wiring: no source, evaluator or native calibration
premise. Original unary traversal fields feed original binary root selectors. -/
def ActualApplication : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
 (Delta : List (Formula alpha)) (parent parameter domain codomain fn arg : OTerm alpha),
 Nonempty (Derivation body Delta (ApplicationFields parent domain codomain fn arg)) →
 Nonempty (Derivation body Delta
   (graph2 OriginalRootObservation.tag (numeral 2) parent parameter ⊓
    (graph2 OriginalRootObservation.functionPacked fn parent parameter ⊓
     graph2 OriginalRootObservation.argumentPacked arg parent parameter)))
/-- The body is the actual repacked codomain/body selector and the extended
parameter is exactly the existing childParameter output. No typedness premise. -/
def ActualLambda : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
 (Delta : List (Formula alpha)) (parent parameter domain codomain child bodyParameter : OTerm alpha),
 Nonempty (Derivation body Delta (LambdaFields parent domain codomain child parameter bodyParameter)) →
 Nonempty (Derivation body Delta
   (graph2 OriginalRootObservation.tag (numeral 1) parent parameter ⊓
    (graph2 OriginalRootObservation.bodyPacked child parent parameter ⊓
     graph2 OriginalRootObservation.childParameter bodyParameter parent parameter)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSelectorTargets
