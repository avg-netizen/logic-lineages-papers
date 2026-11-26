module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalNumericListSort OriginalNumericListSortExchange
/-- Soundness of the actual original finite-path checker instantiated with
the explicit numeric adjacent-exchange edge. No source exchange calibration,
native permutation completeness, or permutation predicate is assumed. -/
def AcceptedPathPreservesSort : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
 (source target certificate left right : OTerm alpha),
 Nonempty (Derivation body [] ((InternalPathChecker.pathGraph edge source target certificate ⊓
   (graph1 sort left source ⊓ graph1 sort right target)).imp (equal left right)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathTargets
