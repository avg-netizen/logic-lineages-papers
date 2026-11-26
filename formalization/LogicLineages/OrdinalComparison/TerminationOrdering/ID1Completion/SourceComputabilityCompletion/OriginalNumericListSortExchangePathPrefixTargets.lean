module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrefixDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrefixTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalNumericListSortExchange
/-- Actual full numeric-prefix lifting, retaining the original append and
path checker graphs. No source or native permutation reflection. -/
def ActualPrefix : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (front source target path newSource newTarget mapped : OTerm alpha),
 Nonempty (Derivation body Delta (InternalPathChecker.pathGraph edge source target path)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append newSource front source)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append newTarget front target)) →
 Nonempty (Derivation body Delta (graph2 OriginalNumericListSortExchangePathPrefix.mapPrefix mapped front path)) →
 Nonempty (Derivation body Delta (InternalPathChecker.pathGraph edge newSource newTarget mapped))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrefixTargets
