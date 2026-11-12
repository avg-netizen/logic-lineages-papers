module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortCommutationCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortCommutationQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalTypedDecoderTransportLogicalProof (notRename)
open OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof (binaryVectorRename)
open OriginalNumericListSort
open OriginalNumericListSortCommutationDefinitions OriginalNumericListSortCommutationSyntaxProof OriginalNumericListSortCommutationCoreProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem advanceAt3 (raw head tail x y firstX firstY left right tx ty tl : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw x y firstX firstY left right)))
 (hxy : Nonempty (Derivation body Delta (ltF x y)))
 (hhx : Nonempty (Derivation body Delta (ltF head x)))
 (htx : Nonempty (Derivation body Delta (graph2 insert tx tail x)))
 (hty : Nonempty (Derivation body Delta (graph2 insert ty tail y)))
 (htl : Nonempty (Derivation body Delta (graph2 insert tl tx y)))
 : Nonempty (Derivation body Delta (equal left right)) := by
 apply programCases insert ![ty,x] _
 intro beta rho Theta tr hrho htr
 rw [binaryVectorRename] at htr
 rw [equalRename]
 have hi' := renameInto hi rho Theta hrho
 simp only [belowRawRename] at hi'
 have hc' := renameInto hc rho Theta hrho
 simp only [graph2Rename] at hc'
 have hf' := renameInto hf rho Theta hrho
 simp only [fields,conjunctionRename,graph2Rename] at hf'
 have hxy' := renameInto hxy rho Theta hrho
 simp only [orderRename] at hxy'
 have hhx' := renameInto hhx rho Theta hrho
 simp only [orderRename] at hhx'
 have htx' := renameInto htx rho Theta hrho
 simp only [graph2Rename] at htx'
 have hty' := renameInto hty rho Theta hrho
 simp only [graph2Rename] at hty'
 have htl' := renameInto htl rho Theta hrho
 simp only [graph2Rename] at htl'
 exact strictAdvance (raw.relabel rho) (head.relabel rho) (tail.relabel rho) (x.relabel rho) (y.relabel rho) (firstX.relabel rho) (firstY.relabel rho) (left.relabel rho) (right.relabel rho) (tx.relabel rho) (ty.relabel rho) (tl.relabel rho) tr hi' hc' hf' hxy' hhx' htx' hty' htl' htr

theorem advanceAt2 (raw head tail x y firstX firstY left right tx ty : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw x y firstX firstY left right)))
 (hxy : Nonempty (Derivation body Delta (ltF x y)))
 (hhx : Nonempty (Derivation body Delta (ltF head x)))
 (htx : Nonempty (Derivation body Delta (graph2 insert tx tail x)))
 (hty : Nonempty (Derivation body Delta (graph2 insert ty tail y)))
 : Nonempty (Derivation body Delta (equal left right)) := by
 apply programCases insert ![tx,y] _
 intro beta rho Theta tl hrho htl
 rw [binaryVectorRename] at htl
 rw [equalRename]
 have hi' := renameInto hi rho Theta hrho
 simp only [belowRawRename] at hi'
 have hc' := renameInto hc rho Theta hrho
 simp only [graph2Rename] at hc'
 have hf' := renameInto hf rho Theta hrho
 simp only [fields,conjunctionRename,graph2Rename] at hf'
 have hxy' := renameInto hxy rho Theta hrho
 simp only [orderRename] at hxy'
 have hhx' := renameInto hhx rho Theta hrho
 simp only [orderRename] at hhx'
 have htx' := renameInto htx rho Theta hrho
 simp only [graph2Rename] at htx'
 have hty' := renameInto hty rho Theta hrho
 simp only [graph2Rename] at hty'
 exact advanceAt3 (raw.relabel rho) (head.relabel rho) (tail.relabel rho) (x.relabel rho) (y.relabel rho) (firstX.relabel rho) (firstY.relabel rho) (left.relabel rho) (right.relabel rho) (tx.relabel rho) (ty.relabel rho) tl hi' hc' hf' hxy' hhx' htx' hty' htl

theorem advanceAt1 (raw head tail x y firstX firstY left right tx : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw x y firstX firstY left right)))
 (hxy : Nonempty (Derivation body Delta (ltF x y)))
 (hhx : Nonempty (Derivation body Delta (ltF head x)))
 (htx : Nonempty (Derivation body Delta (graph2 insert tx tail x)))
 : Nonempty (Derivation body Delta (equal left right)) := by
 apply programCases insert ![tail,y] _
 intro beta rho Theta ty hrho hty
 rw [binaryVectorRename] at hty
 rw [equalRename]
 have hi' := renameInto hi rho Theta hrho
 simp only [belowRawRename] at hi'
 have hc' := renameInto hc rho Theta hrho
 simp only [graph2Rename] at hc'
 have hf' := renameInto hf rho Theta hrho
 simp only [fields,conjunctionRename,graph2Rename] at hf'
 have hxy' := renameInto hxy rho Theta hrho
 simp only [orderRename] at hxy'
 have hhx' := renameInto hhx rho Theta hrho
 simp only [orderRename] at hhx'
 have htx' := renameInto htx rho Theta hrho
 simp only [graph2Rename] at htx'
 exact advanceAt2 (raw.relabel rho) (head.relabel rho) (tail.relabel rho) (x.relabel rho) (y.relabel rho) (firstX.relabel rho) (firstY.relabel rho) (left.relabel rho) (right.relabel rho) (tx.relabel rho) ty hi' hc' hf' hxy' hhx' htx' hty

theorem advanceAt0 (raw head tail x y firstX firstY left right : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw x y firstX firstY left right)))
 (hxy : Nonempty (Derivation body Delta (ltF x y)))
 (hhx : Nonempty (Derivation body Delta (ltF head x)))
 : Nonempty (Derivation body Delta (equal left right)) := by
 apply programCases insert ![tail,x] _
 intro beta rho Theta tx hrho htx
 rw [binaryVectorRename] at htx
 rw [equalRename]
 have hi' := renameInto hi rho Theta hrho
 simp only [belowRawRename] at hi'
 have hc' := renameInto hc rho Theta hrho
 simp only [graph2Rename] at hc'
 have hf' := renameInto hf rho Theta hrho
 simp only [fields,conjunctionRename,graph2Rename] at hf'
 have hxy' := renameInto hxy rho Theta hrho
 simp only [orderRename] at hxy'
 have hhx' := renameInto hhx rho Theta hrho
 simp only [orderRename] at hhx'
 exact advanceAt1 (raw.relabel rho) (head.relabel rho) (tail.relabel rho) (x.relabel rho) (y.relabel rho) (firstX.relabel rho) (firstY.relabel rho) (left.relabel rho) (right.relabel rho) tx hi' hc' hf' hxy' hhx' htx

theorem stopAfter (raw head tail x y firstX firstY left right : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw x y firstX firstY left right)))
 (hxy : Nonempty (Derivation body Delta (ltF x y)))
 (hnx : Nonempty (Derivation body Delta (ltF head x).not))
 (hhy : Nonempty (Derivation body Delta (ltF head y))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 apply programCases insert ![tail,y] _
 intro beta rho Theta inserted hrho hy
 rw [binaryVectorRename] at hy
 rw [equalRename]
 have hc' := renameInto hc rho Theta hrho
 have hf' := renameInto hf rho Theta hrho
 have hxy' := renameInto hxy rho Theta hrho
 have hnx' := renameInto hnx rho Theta hrho
 have hhy' := renameInto hhy rho Theta hrho
 simp only [graph2Rename] at hc'
 simp only [fields,conjunctionRename,graph2Rename] at hf'
 simp only [orderRename] at hxy' hhy'
 simp only [notRename,orderRename] at hnx'
 exact strictStopAfter (raw.relabel rho) (head.relabel rho) (tail.relabel rho)
   (x.relabel rho) (y.relabel rho) (firstX.relabel rho) (firstY.relabel rho)
   (left.relabel rho) (right.relabel rho) inserted hc' hf' hxy' hnx' hhy' hy

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortCommutationQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortCommutationQueryProof
