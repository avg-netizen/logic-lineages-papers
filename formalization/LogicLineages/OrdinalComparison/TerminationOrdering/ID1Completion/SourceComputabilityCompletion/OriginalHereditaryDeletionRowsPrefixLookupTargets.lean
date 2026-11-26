module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsPrefixSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsPrefixLookupTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalHereditaryDeletionRowsPrefixSyntaxProof (fields)
/-- Actual bounded prefix lookup is preserved by literal numeric append.
The only premises are length, range, append and original lookup graphs. -/
def PrefixLookup : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (count front cutoff suffix out value : OTerm alpha),
 Nonempty (Derivation body Delta ((fields count front cutoff suffix out value).imp
   (graph2 InternalRawListRecursion.lookup value cutoff out)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsPrefixLookupTargets
