module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackDeletionRowTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackSlotsTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackOldSuffixTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
def Children0 : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (count row reversed old stack : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count row)) →
 Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse reversed row)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append stack reversed old)) →
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryResultStackProgram.oldSuffix old z count stack))
def Children1 : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (count row reversed old stack suffix value : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count row)) →
 Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse reversed row)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append stack reversed suffix)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode suffix value old)) →
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryResultStackProgram.oldSuffix old (suc z) count stack))
def Children2 : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (count row reversed old stack suffix tail first second : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count row)) →
 Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse reversed row)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append stack reversed suffix)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode suffix second tail)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tail first old)) →
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryResultStackProgram.oldSuffix old (suc (suc z)) count stack))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackOldSuffixTargets
