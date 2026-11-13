module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalFiniteBlocks (block)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Source admission alone discharges exact subtree completion. The actual
computed-fuel completed program fixes output; no fuel bound, empty-state,
result geometry, or semantic content supplier is assumed. -/
def ActualComputedSingleton : Prop := ∀ (R : Program 2) (body : Positive (Fin 1))
 (H G : Program 1) (M W : Program 2) (alpha : Type) (Delta : List (Formula alpha))
 (packed parameter output : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)) →
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.completed R) output packed parameter)) →
 Nonempty (Derivation body Delta (ComputedStackDefinitions.SingletonResult R packed parameter output))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackTargets
