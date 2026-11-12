module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobExpansionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalHereditaryInternalAgenda OriginalHereditaryInternalJobRow
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def Expansion : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (H : Program 1) (M W : Program 2) (c B parent row : OTerm alpha),
 Nonempty (Derivation body Delta (Job H M W c B parent)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion row parent)) →
 Nonempty (Derivation body Delta (Jobs H M W c B row))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobExpansionTargets
