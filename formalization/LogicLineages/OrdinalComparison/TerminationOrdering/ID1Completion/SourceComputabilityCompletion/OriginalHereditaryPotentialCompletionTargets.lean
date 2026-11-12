module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open OriginalHereditaryPotentialCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Eventual concrete endpoint, intentionally separate from staged implication. -/
def ActualCompletion (R : Program 2) (H : Program 1) (M W : Program 2) : Prop :=
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (c B fuel input work results before output : OTerm alpha),
 Nonempty (Derivation body Delta (Entry R H M W c B fuel input work results before output)) →
 Nonempty (Derivation body Delta (Empty output))
def ConditionalCompletion : Prop := ∀ (R : Program 2) (H : Program 1) (M W : Program 2),
 StepLaw R H M W → ActualCompletion R H M W
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionTargets
