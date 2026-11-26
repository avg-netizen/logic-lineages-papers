module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseLengthInvolutionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackPartitionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackDeletionRowTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
/-- Actual original row length and reversal plus stack append suffice.
No front, reverse-back, or desired selector output premise is supplied. -/
def ActualRestoration : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
 (Delta : List (Formula alpha)) (children count row reversed suffix stack : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count row)) →
 Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse reversed row)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append stack reversed suffix)) →
 Nonempty (Derivation body Delta
  (graph3 OriginalHereditaryResultStackProgram.deletionRow row children count stack))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackDeletionRowTargets
