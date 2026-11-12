module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortInternalTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAlgebraTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalNumericListSort
/-- Every actual insertion state retains its original numeric list as left coordinate. -/
def OriginalCoordinate : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (raw x state : OTerm alpha),
 Nonempty (Derivation body [] ((graph2 insertState state raw x).imp (graph1 InternalUnpair.left raw state)))
/-- Two actual insertions commute on every numeric list, without sortedness,
native decoding, comparison oracle, or permutation premise. Duplicates retained. -/
def InsertCommutation : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
 (raw x y firstX firstY left right : OTerm alpha),
 Nonempty (Derivation body []
 ((graph2 insert firstX raw x ⊓ (graph2 insert left firstX y ⊓
 (graph2 insert firstY raw y ⊓ graph2 insert right firstY x))).imp (equal left right)))
/-- Literal adjacent-swap generator, not arbitrary coded permutation reflection. -/
def AdjacentSwap : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
 (tail x y tailY tailX xy yx left right : OTerm alpha),
 Nonempty (Derivation body []
 ((graph2 InternalListCodec.consCode tailY y tail ⊓
 (graph2 InternalListCodec.consCode xy x tailY ⊓
 (graph2 InternalListCodec.consCode tailX x tail ⊓
 (graph2 InternalListCodec.consCode yx y tailX ⊓
 (graph1 sort left xy ⊓ graph1 sort right yx))))).imp (equal left right)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAlgebraTargets
