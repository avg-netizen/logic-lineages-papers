module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalIndexedPrefixTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookup
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open InternalAdditionLawsProof (add)
open OriginalContextInsertion
/-- Genuine suffix index/length witnesses, retaining the original index equation. -/
def tailFields {alpha : Type} (frontCount suffix index value suffixIndex suffixCount : OTerm alpha) : Formula alpha :=
 eqn index (add frontCount suffixIndex) ⊓ (lengthGraph suffixCount suffix ⊓
 (Below suffixIndex suffixCount ⊓ graph2 InternalRawListRecursion.lookup value suffixIndex suffix))
def tailMatrix {alpha : Type} (frontCount suffix index value : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
 tailFields (frontCount.relabel Sum.inl) (suffix.relabel Sum.inl) (index.relabel Sum.inl)
   (value.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
def Tail {alpha : Type} (frontCount suffix index value : OTerm alpha) : Formula alpha :=
 InternalFiniteBlocks.block (k := 2) (tailMatrix frontCount suffix index value)
def Result {alpha : Type} (frontCount front suffix index value : OTerm alpha) : Formula alpha :=
 (Below index frontCount ⊓ graph2 InternalRawListRecursion.lookup value index front) ⊔
 Tail frontCount suffix index value
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookup
