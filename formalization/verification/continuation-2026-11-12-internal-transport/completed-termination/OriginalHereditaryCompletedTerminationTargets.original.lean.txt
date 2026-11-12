module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySourceRootCompletionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryCompletedTerminationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Source-valid inputs have empty completed work at the literal computed fuel.
No assertion about the returned result content is included. -/
def ActualCompletedTermination : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (H G : Program 1) (M W : Program 2)
 (alpha : Type) (Delta : List (Formula alpha)) (packed parameter output : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)) →
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.completed R) output packed parameter)) →
 Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty output))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryCompletedTerminationTargets
