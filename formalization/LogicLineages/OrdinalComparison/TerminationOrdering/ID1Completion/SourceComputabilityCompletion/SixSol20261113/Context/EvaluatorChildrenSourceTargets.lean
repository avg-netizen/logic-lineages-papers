module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSourceTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalLambdaTraversalInternal
/-- Child source admission from the unchanged original source checker and
literal total application selectors. No child validity is assumed. -/
def ActualApplication : Prop := ∀ (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (parent parameter domain codomain fn arg : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) parent parameter)) →
 Nonempty (Derivation body Delta (ApplicationFields parent domain codomain fn arg)) →
 Nonempty (Derivation body Delta
   (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) fn parameter ⊓
    graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) arg parameter))
/-- Original lambda child source at the actual childParameter selector result.
No caller-supplied context decomposition, calibration or child source premise. -/
def ActualLambda : Prop := ∀ (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (parent parameter domain codomain child bodyParameter : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) parent parameter)) →
 Nonempty (Derivation body Delta (LambdaFields parent domain codomain child parameter bodyParameter)) →
 Nonempty (Derivation body Delta
   (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) child bodyParameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSourceTargets
