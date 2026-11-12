module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Sound translation of the explicit standalone raw swap checker. No native
permutation, original BASE acceptance or source-validity reflection is used. -/
def ActualTranslation : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type)
 (Delta : List (Formula alpha)) (source target certificate parameter observedSource observedTarget numericCertificate : OTerm alpha),
 Nonempty (Derivation body Delta (graph3 OriginalTypedArgumentExchange.edge (suc z) source target certificate)) →
 Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations R) observedSource source parameter)) →
 Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations R) observedTarget target parameter)) →
 Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentExchange.translate R) numericCertificate certificate parameter)) →
 Nonempty (Derivation body Delta (graph3 OriginalNumericListSortExchange.edge (suc z) observedSource observedTarget numericCertificate))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeTargets
