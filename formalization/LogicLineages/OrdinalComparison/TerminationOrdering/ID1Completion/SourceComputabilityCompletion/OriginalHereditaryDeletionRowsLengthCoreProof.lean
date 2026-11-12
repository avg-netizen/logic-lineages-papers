module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteDropProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthCoreProof
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
open OriginalHereditaryDeletionRowsLengthSyntaxProof hiding rowInstantiate rowSuccessor
open OriginalClassContextAllPositionObserver (deleteAt)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroCore (front value singleton out : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields z front value singleton out))) :
    Nonempty (Derivation body Delta (lengthGraph (suc z) out)) := by
  have he := lengthZeroRecover front (andLeft hf)
  have ha := headTransport InternalApplicationValidityStackAppend.append out front z
    (Fin.cons singleton Fin.elim0) he (andRight (andRight hf))
  obtain ⟨ho⟩ := InternalApplicationValidityStackAppendListProof.appendZeroRecover out singleton ha
  have hl := lengthCons singleton value z z (andLeft (andRight hf)) lengthZero
  exact headTransport length (suc z) singleton out Fin.elim0 ⟨symm ho⟩ hl

theorem succCore (count front value singleton out : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row count)))
    (hf : Nonempty (Derivation body Delta (fields (suc count) front value singleton out))) :
    Nonempty (Derivation body Delta (lengthGraph (suc (suc count)) out)) := by
  apply nonzeroCases front _ (successorLengthNonzero count front (andLeft hf))
  intro beta j Theta head tail hj hc
  simp only [lengthRename,sucRelabel]
  have hf' := renameInto hf j Theta hj
  simp only [fieldsRename,sucRelabel] at hf'
  have hr' := renameInto hrow j Theta hj
  rw [rowRename] at hr'
  have htlen := successorLengthTail (front.relabel j) head tail (count.relabel j) hc (andLeft hf')
  apply programCases InternalApplicationValidityStackAppend.append
    (Fin.cons tail (Fin.cons (singleton.relabel j) Fin.elim0)) _
  intro beta' k Xi tailOut hk ht
  simp only [lengthRename,sucRelabel]
  have hf'' := renameInto hf' k Xi hk
  simp only [fieldsRename,sucRelabel] at hf''
  have hc' := renameInto hc k Xi hk
  rw [consGraphRename] at hc'
  have htl := renameInto htlen k Xi hk
  rw [lengthRename] at htl
  have hr'' := renameInto hr' k Xi hk
  rw [rowRename] at hr''
  simp only [consTermRename,emptyRename] at ht
  have htail := rowApply ((count.relabel j).relabel k) (tail.relabel k)
    ((value.relabel j).relabel k) ((singleton.relabel j).relabel k) tailOut hr''
    (andIntro htl (andIntro (andLeft (andRight hf'')) ht))
  have hout := InternalApplicationValidityStackAppendListProof.consForward
    ((front.relabel j).relabel k) (head.relabel k) (tail.relabel k)
    ((singleton.relabel j).relabel k) tailOut ((out.relabel j).relabel k)
    hc' ht (andRight (andRight hf''))
  exact lengthCons ((out.relabel j).relabel k) (head.relabel k) tailOut
    (suc ((count.relabel j).relabel k)) hout htail

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthCoreProof
