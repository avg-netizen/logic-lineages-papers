module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortPrefixDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortPrefixTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalNumericListSort OriginalNumericListSortPrefixDefinitions
/-- Actual equal sorted suffixes remain equal after the SAME actual numeric
prefix is appended. No native/permutation/sorted-list assumption. -/
def PrefixCongruence : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
 (front tailA tailB left right a b outA outB : OTerm alpha),
 Nonempty (Derivation body [] ((fields front tailA tailB left right a b outA outB).imp (equal outA outB)))
/-- One actual adjacent exchange under an arbitrary common numeric prefix.
This is not reflection of an arbitrary native List.Perm or source exchange. -/
def PrefixAdjacentSwap : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
 (front tail x y tailY tailX xy yx left right outA outB : OTerm alpha),
 Nonempty (Derivation body []
 ((graph2 InternalListCodec.consCode tailY y tail ⊓
 (graph2 InternalListCodec.consCode xy x tailY ⊓
 (graph2 InternalListCodec.consCode tailX x tail ⊓
 (graph2 InternalListCodec.consCode yx y tailX ⊓
 (graph2 InternalApplicationValidityStackAppend.append left front xy ⊓
 (graph2 InternalApplicationValidityStackAppend.append right front yx ⊓
 (graph1 sort outA left ⊓ graph1 sort outB right))))))).imp (equal outA outB)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortPrefixTargets
