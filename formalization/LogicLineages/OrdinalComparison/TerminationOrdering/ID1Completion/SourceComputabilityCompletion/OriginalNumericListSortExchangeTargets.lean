module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalNumericListSort OriginalNumericListSortExchange
open SourceComputabilityFormulaSupportProof (numeral)
/-- Soundness of the literal common-prefix adjacent-exchange certificate.
This says nothing about native List.Perm completeness or typed source BASE. -/
def AcceptedEdgePreservesSort : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
 (source target certificate left right : OTerm alpha),
 Nonempty (Derivation body [] ((graph3 edge (numeral 1) source target certificate ⊓
   (graph1 sort left source ⊓ graph1 sort right target)).imp (equal left right)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeTargets
