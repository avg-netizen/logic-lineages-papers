module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangePathDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangePathTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Sound translation of the standalone raw swap path. This does not extract
paths from original BASE acceptance, and does not invoke native reflection. -/
def ActualTranslation : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type)
 (Delta : List (Formula alpha)) (path source target parameter observedSource observedTarget mapped : OTerm alpha),
 Nonempty (Derivation body Delta (InternalPathChecker.pathGraph OriginalTypedArgumentExchange.edge source target path)) →
 Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations R) observedSource source parameter)) →
 Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations R) observedTarget target parameter)) →
 Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentExchangePath.mapPath R) mapped path parameter)) →
 Nonempty (Derivation body Delta (InternalPathChecker.pathGraph OriginalNumericListSortExchange.edge observedSource observedTarget mapped))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangePathTargets
