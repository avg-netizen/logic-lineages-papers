module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionSuccessorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof InternalSquareRootArithmeticSupportProof
open InternalListCodecSupportProof InternalSourceInversionSupportProof
open InternalBetaTotalityProof (addHyp)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open OriginalContextInsertionSupportProof
open OriginalContextTwoDeletionInductionSyntaxProof hiding rowInstantiate rowSuccessor
open OriginalClassContextAllPositionObserver (deleteAt)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/- Actual length and in-range cutoff force a nonempty original context. -/
open OriginalContextTwoDeletionQueryProof OriginalContextTwoDeletionCoreProof
open OriginalTypedDecoderTransportLogicalProof (iffForward)
theorem successorValues (gamma count head tail i j a b upper lower left right ut dt lt rt tc : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row i)))
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hf : Nonempty (Derivation body Delta (fields gamma count (suc i) (suc j) a b upper lower left right)))
    (hc0 : Nonempty (Derivation body Delta (consGraph upper head ut)))
    (hd0 : Nonempty (Derivation body Delta (graph2 deleteAt ut (suc j) tail)))
    (hc1 : Nonempty (Derivation body Delta (consGraph lower head dt)))
    (hd1 : Nonempty (Derivation body Delta (graph2 deleteAt dt i tail)))
    (hc2 : Nonempty (Derivation body Delta (consGraph left head lt)))
    (hd2 : Nonempty (Derivation body Delta (graph2 deleteAt lt i ut)))
    (hc3 : Nonempty (Derivation body Delta (consGraph right head rt)))
    (hd3 : Nonempty (Derivation body Delta (graph2 deleteAt rt j dt)))
    (hlen : Nonempty (Derivation body Delta (lengthGraph tc tail)))
    : Nonempty (Derivation body Delta (result (suc i) (suc j) a b upper lower left right)) := by
  obtain ⟨heCount⟩ := lengthConsRecover gamma head tail count tc hc (andLeft hf) hlen
  have hsmall := OriginalContextInsertionBelowCoreProof.successorStrict i (suc j) (andLeft (andRight hf))
  obtain ⟨hb⟩ := andLeft (andRight (andRight hf))
  have hbound := OriginalContextInsertionBelowCoreProof.successorStrict (suc j) tc
    ⟨orderRight (suc (suc j)) heCount hb⟩
  have ha := iffForward (OriginalAllPositionContextDeleteDropProof.lookupConsIff gamma head tail i a hc)
    (andLeft (andRight (andRight (andRight hf))))
  have hb' := iffForward (OriginalAllPositionContextDeleteDropProof.lookupConsIff gamma head tail (suc j) b hc)
    (andLeft (andRight (andRight (andRight (andRight hf)))))
  have htail := rowApply tail tc i j a b ut dt lt rt hrow
    (andIntro hlen (andIntro hsmall (andIntro hbound (andIntro ha
      (andIntro hb' (andIntro hd0 (andIntro hd2 (andIntro hd1 hd3))))))))
  exact successorResult head upper ut lower dt left lt right rt i j a b hc0 hc1 hc2 hc3 htail

theorem successorAt4 (gamma count head tail i j a b upper lower left right ut dt lt rt : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row i)))
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hf : Nonempty (Derivation body Delta (fields gamma count (suc i) (suc j) a b upper lower left right)))
    (hc0 : Nonempty (Derivation body Delta (consGraph upper head ut)))
    (hd0 : Nonempty (Derivation body Delta (graph2 deleteAt ut (suc j) tail)))
    (hc1 : Nonempty (Derivation body Delta (consGraph lower head dt)))
    (hd1 : Nonempty (Derivation body Delta (graph2 deleteAt dt i tail)))
    (hc2 : Nonempty (Derivation body Delta (consGraph left head lt)))
    (hd2 : Nonempty (Derivation body Delta (graph2 deleteAt lt i ut)))
    (hc3 : Nonempty (Derivation body Delta (consGraph right head rt)))
    (hd3 : Nonempty (Derivation body Delta (graph2 deleteAt rt j dt)))
    : Nonempty (Derivation body Delta (result (suc i) (suc j) a b upper lower left right)) := by
  apply programCases OriginalContextInsertion.length (Fin.cons tail Fin.elim0) _
  intro beta rho Theta tc hrho hlen
  simp only [consTermRename,emptyRename] at hlen
  simp only [resultRename,sucRelabel]
  have hrow' := renameInto hrow rho Theta hrho
  have hc' := renameInto hc rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  have hc0' := renameInto hc0 rho Theta hrho
  have hd0' := renameInto hd0 rho Theta hrho
  have hc1' := renameInto hc1 rho Theta hrho
  have hd1' := renameInto hd1 rho Theta hrho
  have hc2' := renameInto hc2 rho Theta hrho
  have hd2' := renameInto hd2 rho Theta hrho
  have hc3' := renameInto hc3 rho Theta hrho
  have hd3' := renameInto hd3 rho Theta hrho
  rw [rowRename] at hrow'
  rw [consGraphRename] at hc'
  simp only [fieldsRename,sucRelabel] at hf'
  simp only [consGraphRename,graph2Rename,sucRelabel] at hc0' hd0' hc1' hd1' hc2' hd2' hc3' hd3'
  exact successorValues (gamma.relabel rho) (count.relabel rho) (head.relabel rho) (tail.relabel rho) (i.relabel rho) (j.relabel rho) (a.relabel rho) (b.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) (ut.relabel rho) (dt.relabel rho) (lt.relabel rho) (rt.relabel rho) tc hrow' hc' hf' hc0' hd0' hc1' hd1' hc2' hd2' hc3' hd3' hlen

theorem successorAt3 (gamma count head tail i j a b upper lower left right ut dt lt : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row i)))
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hf : Nonempty (Derivation body Delta (fields gamma count (suc i) (suc j) a b upper lower left right)))
    (hc0 : Nonempty (Derivation body Delta (consGraph upper head ut)))
    (hd0 : Nonempty (Derivation body Delta (graph2 deleteAt ut (suc j) tail)))
    (hc1 : Nonempty (Derivation body Delta (consGraph lower head dt)))
    (hd1 : Nonempty (Derivation body Delta (graph2 deleteAt dt i tail)))
    (hc2 : Nonempty (Derivation body Delta (consGraph left head lt)))
    (hd2 : Nonempty (Derivation body Delta (graph2 deleteAt lt i ut)))
    : Nonempty (Derivation body Delta (result (suc i) (suc j) a b upper lower left right)) := by
  apply consDeletionCases lower head dt right j _ hc1 (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight hf))))))))
  intro beta rho Theta rt hrho hc3 hd3
  simp only [resultRename,sucRelabel]
  have hrow' := renameInto hrow rho Theta hrho
  have hc' := renameInto hc rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  have hc0' := renameInto hc0 rho Theta hrho
  have hd0' := renameInto hd0 rho Theta hrho
  have hc1' := renameInto hc1 rho Theta hrho
  have hd1' := renameInto hd1 rho Theta hrho
  have hc2' := renameInto hc2 rho Theta hrho
  have hd2' := renameInto hd2 rho Theta hrho
  rw [rowRename] at hrow'
  rw [consGraphRename] at hc'
  simp only [fieldsRename,sucRelabel] at hf'
  simp only [consGraphRename,graph2Rename,sucRelabel] at hc0' hd0' hc1' hd1' hc2' hd2'
  exact successorAt4 (gamma.relabel rho) (count.relabel rho) (head.relabel rho) (tail.relabel rho) (i.relabel rho) (j.relabel rho) (a.relabel rho) (b.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) (ut.relabel rho) (dt.relabel rho) (lt.relabel rho) rt hrow' hc' hf' hc0' hd0' hc1' hd1' hc2' hd2' hc3 hd3

theorem successorAt2 (gamma count head tail i j a b upper lower left right ut dt : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row i)))
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hf : Nonempty (Derivation body Delta (fields gamma count (suc i) (suc j) a b upper lower left right)))
    (hc0 : Nonempty (Derivation body Delta (consGraph upper head ut)))
    (hd0 : Nonempty (Derivation body Delta (graph2 deleteAt ut (suc j) tail)))
    (hc1 : Nonempty (Derivation body Delta (consGraph lower head dt)))
    (hd1 : Nonempty (Derivation body Delta (graph2 deleteAt dt i tail)))
    : Nonempty (Derivation body Delta (result (suc i) (suc j) a b upper lower left right)) := by
  apply consDeletionCases upper head ut left i _ hc0 (andLeft (andRight (andRight (andRight (andRight (andRight (andRight hf)))))))
  intro beta rho Theta lt hrho hc2 hd2
  simp only [resultRename,sucRelabel]
  have hrow' := renameInto hrow rho Theta hrho
  have hc' := renameInto hc rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  have hc0' := renameInto hc0 rho Theta hrho
  have hd0' := renameInto hd0 rho Theta hrho
  have hc1' := renameInto hc1 rho Theta hrho
  have hd1' := renameInto hd1 rho Theta hrho
  rw [rowRename] at hrow'
  rw [consGraphRename] at hc'
  simp only [fieldsRename,sucRelabel] at hf'
  simp only [consGraphRename,graph2Rename,sucRelabel] at hc0' hd0' hc1' hd1'
  exact successorAt3 (gamma.relabel rho) (count.relabel rho) (head.relabel rho) (tail.relabel rho) (i.relabel rho) (j.relabel rho) (a.relabel rho) (b.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) (ut.relabel rho) (dt.relabel rho) lt hrow' hc' hf' hc0' hd0' hc1' hd1' hc2 hd2

theorem successorAt1 (gamma count head tail i j a b upper lower left right ut : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row i)))
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hf : Nonempty (Derivation body Delta (fields gamma count (suc i) (suc j) a b upper lower left right)))
    (hc0 : Nonempty (Derivation body Delta (consGraph upper head ut)))
    (hd0 : Nonempty (Derivation body Delta (graph2 deleteAt ut (suc j) tail)))
    : Nonempty (Derivation body Delta (result (suc i) (suc j) a b upper lower left right)) := by
  apply consDeletionCases gamma head tail lower i _ hc (andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight hf))))))))
  intro beta rho Theta dt hrho hc1 hd1
  simp only [resultRename,sucRelabel]
  have hrow' := renameInto hrow rho Theta hrho
  have hc' := renameInto hc rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  have hc0' := renameInto hc0 rho Theta hrho
  have hd0' := renameInto hd0 rho Theta hrho
  rw [rowRename] at hrow'
  rw [consGraphRename] at hc'
  simp only [fieldsRename,sucRelabel] at hf'
  simp only [consGraphRename,graph2Rename,sucRelabel] at hc0' hd0'
  exact successorAt2 (gamma.relabel rho) (count.relabel rho) (head.relabel rho) (tail.relabel rho) (i.relabel rho) (j.relabel rho) (a.relabel rho) (b.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) (ut.relabel rho) dt hrow' hc' hf' hc0' hd0' hc1 hd1


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionSuccessorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionSuccessorProof
