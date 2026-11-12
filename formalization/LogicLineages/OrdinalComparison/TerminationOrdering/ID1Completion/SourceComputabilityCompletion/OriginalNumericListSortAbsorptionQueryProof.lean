module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAbsorptionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAbsorptionQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof (unaryVectorRename binaryVectorRename)
open OriginalNumericListSort
open OriginalNumericListSortAbsorptionDefinitions OriginalNumericListSortAbsorptionSyntaxProof OriginalNumericListSortAbsorptionCoreProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem afterAt3 (raw head tail x inserted sorted left right ti ts tl : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw x inserted sorted left right)))
 (hlt : Nonempty (Derivation body Delta (ltF head x)))
 (hti : Nonempty (Derivation body Delta (graph2 insert ti tail x)))
 (hts : Nonempty (Derivation body Delta (graph1 sort ts tail)))
 (htl : Nonempty (Derivation body Delta (graph1 sort tl ti)))
 : Nonempty (Derivation body Delta (equal left right)) := by
 apply programCases insert ![ts,x] _
 intro beta rho Theta tr hrho htr
 rw [binaryVectorRename] at htr
 rw [equalRename]
 have hi' := renameInto hi rho Theta hrho
 simp only [belowRawRename] at hi'
 have hc' := renameInto hc rho Theta hrho
 simp only [graph2Rename] at hc'
 have hf' := renameInto hf rho Theta hrho
 simp only [fields,conjunctionRename,graph1Rename,graph2Rename] at hf'
 have hlt' := renameInto hlt rho Theta hrho
 simp only [orderRename] at hlt'
 have hti' := renameInto hti rho Theta hrho
 simp only [graph2Rename] at hti'
 have hts' := renameInto hts rho Theta hrho
 simp only [graph1Rename] at hts'
 have htl' := renameInto htl rho Theta hrho
 simp only [graph1Rename] at htl'
 exact afterCore (raw.relabel rho) (head.relabel rho) (tail.relabel rho) (x.relabel rho) (inserted.relabel rho) (sorted.relabel rho) (left.relabel rho) (right.relabel rho) (ti.relabel rho) (ts.relabel rho) (tl.relabel rho) tr hi' hc' hf' hlt' hti' hts' htl' htr

theorem afterAt2 (raw head tail x inserted sorted left right ti ts : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw x inserted sorted left right)))
 (hlt : Nonempty (Derivation body Delta (ltF head x)))
 (hti : Nonempty (Derivation body Delta (graph2 insert ti tail x)))
 (hts : Nonempty (Derivation body Delta (graph1 sort ts tail)))
 : Nonempty (Derivation body Delta (equal left right)) := by
 apply programCases sort ![ti] _
 intro beta rho Theta tl hrho htl
 rw [unaryVectorRename] at htl
 rw [equalRename]
 have hi' := renameInto hi rho Theta hrho
 simp only [belowRawRename] at hi'
 have hc' := renameInto hc rho Theta hrho
 simp only [graph2Rename] at hc'
 have hf' := renameInto hf rho Theta hrho
 simp only [fields,conjunctionRename,graph1Rename,graph2Rename] at hf'
 have hlt' := renameInto hlt rho Theta hrho
 simp only [orderRename] at hlt'
 have hti' := renameInto hti rho Theta hrho
 simp only [graph2Rename] at hti'
 have hts' := renameInto hts rho Theta hrho
 simp only [graph1Rename] at hts'
 exact afterAt3 (raw.relabel rho) (head.relabel rho) (tail.relabel rho) (x.relabel rho) (inserted.relabel rho) (sorted.relabel rho) (left.relabel rho) (right.relabel rho) (ti.relabel rho) (ts.relabel rho) tl hi' hc' hf' hlt' hti' hts' htl

theorem afterAt1 (raw head tail x inserted sorted left right ti : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw x inserted sorted left right)))
 (hlt : Nonempty (Derivation body Delta (ltF head x)))
 (hti : Nonempty (Derivation body Delta (graph2 insert ti tail x)))
 : Nonempty (Derivation body Delta (equal left right)) := by
 apply programCases sort ![tail] _
 intro beta rho Theta ts hrho hts
 rw [unaryVectorRename] at hts
 rw [equalRename]
 have hi' := renameInto hi rho Theta hrho
 simp only [belowRawRename] at hi'
 have hc' := renameInto hc rho Theta hrho
 simp only [graph2Rename] at hc'
 have hf' := renameInto hf rho Theta hrho
 simp only [fields,conjunctionRename,graph1Rename,graph2Rename] at hf'
 have hlt' := renameInto hlt rho Theta hrho
 simp only [orderRename] at hlt'
 have hti' := renameInto hti rho Theta hrho
 simp only [graph2Rename] at hti'
 exact afterAt2 (raw.relabel rho) (head.relabel rho) (tail.relabel rho) (x.relabel rho) (inserted.relabel rho) (sorted.relabel rho) (left.relabel rho) (right.relabel rho) (ti.relabel rho) ts hi' hc' hf' hlt' hti' hts

theorem afterAt0 (raw head tail x inserted sorted left right : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw x inserted sorted left right)))
 (hlt : Nonempty (Derivation body Delta (ltF head x)))
 : Nonempty (Derivation body Delta (equal left right)) := by
 apply programCases insert ![tail,x] _
 intro beta rho Theta ti hrho hti
 rw [binaryVectorRename] at hti
 rw [equalRename]
 have hi' := renameInto hi rho Theta hrho
 simp only [belowRawRename] at hi'
 have hc' := renameInto hc rho Theta hrho
 simp only [graph2Rename] at hc'
 have hf' := renameInto hf rho Theta hrho
 simp only [fields,conjunctionRename,graph1Rename,graph2Rename] at hf'
 have hlt' := renameInto hlt rho Theta hrho
 simp only [orderRename] at hlt'
 exact afterAt1 (raw.relabel rho) (head.relabel rho) (tail.relabel rho) (x.relabel rho) (inserted.relabel rho) (sorted.relabel rho) (left.relabel rho) (right.relabel rho) ti hi' hc' hf' hlt' hti

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAbsorptionQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAbsorptionQueryProof
