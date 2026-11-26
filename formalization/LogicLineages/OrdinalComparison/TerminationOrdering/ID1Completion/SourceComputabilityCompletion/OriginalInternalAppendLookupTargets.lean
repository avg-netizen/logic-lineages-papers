module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalContextInsertion OriginalInternalAppendLookup
def ActualSplit : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (frontCount front suffix joined count index value : OTerm alpha),
 Nonempty (Derivation body Delta (lengthGraph frontCount front)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined front suffix)) →
 Nonempty (Derivation body Delta (lengthGraph count joined)) →
 Nonempty (Derivation body Delta (Below index count)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value index joined)) →
 Nonempty (Derivation body Delta (Result frontCount front suffix index value))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupTargets
