module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalHereditaryInternalAgenda OriginalHereditaryInternalJobRow
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def Tagged : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (H : Program 1) (M W : Program 2) (c B row tagged : OTerm alpha),
 Nonempty (Derivation body Delta (Jobs H M W c B row)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryVisitScheduler.tagVisits tagged row)) →
 Nonempty (Derivation body Delta (Agenda H M W c B tagged))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowTargets
