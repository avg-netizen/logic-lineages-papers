module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionOutputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalFoldUnaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalStructuralNodeSizeInternalMachineExpansionProof
open OriginalStructuralNodeSizeInternalMachineCompletionInductionProof OriginalStructuralNodeSizeInternalMachineCompletionUnaryProof
open OriginalStructuralNodeSizeInternalMachineCompletionRunProof OriginalStructuralNodeSizeInternalMachineCompletionOutputProof
open OriginalRawSyntaxTransportInternalConstructorBoundsProof
open OriginalLambdaTraversalInternalPayloadArithmeticProof (lambdaCount)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem unaryBackward (d k raw child childK childOut out : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (UnaryFields raw k child childK)))
    (hchild : Nonempty (Derivation positive Delta (graph3 (OriginalStructuralNodeSizeInternalMachineCompletion.fold) childOut d childK child)))
    (hr : Nonempty (Derivation positive Delta (graph3 (OriginalStructuralNodeSizeInternalAlgebraProof.rebuild) out raw childOut z))) :
    Nonempty (Derivation positive Delta (graph3 (OriginalStructuralNodeSizeInternalMachineCompletion.fold) out d k raw)) := by
  apply completionAtFoldCases d childK child childOut _ hchild (hasCompletion d childK child)
  intro beta j Theta count hj hcb hcc
  rw [graph3Rename]
  have hf' := renameInto hf j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [unaryFieldsRename] at hf'
  simp only [graph3Rename,zRelabel] at hr'
  exact completionFold (d.relabel j) (k.relabel j) (raw.relabel j) (suc (suc count)) (out.relabel j)
    (lambdaCount (raw.relabel j) (child.relabel j) count
      (unaryChildBound (raw.relabel j) (child.relabel j) (andLeft hf') (andLeft (andRight hf'))) hcb)
    (unaryComplete (d.relabel j) (k.relabel j) (raw.relabel j) (child.relabel j)
      (childK.relabel j) count (childOut.relabel j) (out.relabel j) hf' hr' hcc)

theorem unaryForward (d k raw child childK childOut out : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (UnaryFields raw k child childK)))
    (hchild : Nonempty (Derivation positive Delta (graph3 (OriginalStructuralNodeSizeInternalMachineCompletion.fold) childOut d childK child)))
    (ho : Nonempty (Derivation positive Delta (graph3 (OriginalStructuralNodeSizeInternalMachineCompletion.fold) out d k raw))) :
    Nonempty (Derivation positive Delta (graph3 (OriginalStructuralNodeSizeInternalAlgebraProof.rebuild) out raw childOut z)) := by
  apply programCases (OriginalStructuralNodeSizeInternalAlgebraProof.rebuild) (Fin.cons raw (Fin.cons childOut (Fin.cons z Fin.elim0))) _
  intro beta j Theta produced hj hp
  simp only [graph3Rename,zRelabel]
  simp only [consTermRename,emptyRename,zRelabel] at hp
  have hf' := renameInto hf j Theta hj
  have hchild' := renameInto hchild j Theta hj
  have ho' := renameInto ho j Theta hj
  rw [unaryFieldsRename] at hf'
  rw [graph3Rename] at hchild' ho'
  have hfold := unaryBackward (d.relabel j) (k.relabel j) (raw.relabel j) (child.relabel j)
    (childK.relabel j) (childOut.relabel j) produced hf' hchild' hp
  exact outputTransport (OriginalStructuralNodeSizeInternalAlgebraProof.rebuild) produced (out.relabel j)
    ![raw.relabel j,childOut.relabel j,z]
    (valueUnique (OriginalStructuralNodeSizeInternalMachineCompletion.fold) produced (out.relabel j) ![d.relabel j,k.relabel j,raw.relabel j] hfold ho') hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalFoldUnaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalFoldUnaryProof
