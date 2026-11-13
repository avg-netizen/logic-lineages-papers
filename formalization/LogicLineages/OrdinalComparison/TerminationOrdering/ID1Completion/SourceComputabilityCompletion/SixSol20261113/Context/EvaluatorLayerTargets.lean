module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorLayerTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- The original computed-fuel evaluator unfolds to the original observation
layer on genuinely source-admitted inputs. The SAME R, packed term and parameter
occur throughout. No framed content, recursive correctness, desired output,
semantic row, or fuel bound is assumed. This is an internal graph iff, not a
native calibration or a newly defined evaluator. -/
def ActualSourceUnfolding : Prop := ∀ (R : Program 2) (H G : Program 1) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (packed parameter out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)) →
  Nonempty (Derivation body Delta
    ((graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) out packed parameter).iff
      (graph2 (OriginalHereditaryObservationLayer.layer R (OriginalHereditaryEvaluatorDefinitions.evaluator R)) out packed parameter)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorLayerTargets
