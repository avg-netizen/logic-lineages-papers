module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionOutputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldUnaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransportInternalMachineExpansionProof
open OriginalRawSyntaxTransportInternalMachineCompletionInductionProof OriginalRawSyntaxTransportInternalMachineCompletionUnaryProof
open OriginalRawSyntaxTransportInternalMachineCompletionRunProof OriginalRawSyntaxTransportInternalMachineCompletionOutputProof
open OriginalRawSyntaxTransportInternalConstructorBoundsProof
open OriginalLambdaTraversalInternalPayloadArithmeticProof (lambdaCount)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem unaryBackward (mode : Mode) (d k raw child childK childOut out : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (UnaryFields raw k child childK)))
    (hchild : Nonempty (Derivation positive Delta (graph3 (fold mode) childOut d childK child)))
    (hr : Nonempty (Derivation positive Delta (graph3 (rebuild mode) out raw childOut z))) :
    Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw)) := by
  apply completionAtFoldCases mode d childK child childOut _ hchild (hasCompletion mode d childK child)
  intro beta j Theta count hj hcb hcc
  rw [graph3Rename]
  have hf' := renameInto hf j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [unaryFieldsRename] at hf'
  simp only [graph3Rename,zRelabel] at hr'
  exact completionFold mode (d.relabel j) (k.relabel j) (raw.relabel j) (suc (suc count)) (out.relabel j)
    (lambdaCount (raw.relabel j) (child.relabel j) count
      (unaryChildBound (raw.relabel j) (child.relabel j) (andLeft hf') (andLeft (andRight hf'))) hcb)
    (unaryComplete mode (d.relabel j) (k.relabel j) (raw.relabel j) (child.relabel j)
      (childK.relabel j) count (childOut.relabel j) (out.relabel j) hf' hr' hcc)

theorem unaryForward (mode : Mode) (d k raw child childK childOut out : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (UnaryFields raw k child childK)))
    (hchild : Nonempty (Derivation positive Delta (graph3 (fold mode) childOut d childK child)))
    (ho : Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw))) :
    Nonempty (Derivation positive Delta (graph3 (rebuild mode) out raw childOut z)) := by
  apply programCases (rebuild mode) (Fin.cons raw (Fin.cons childOut (Fin.cons z Fin.elim0))) _
  intro beta j Theta produced hj hp
  simp only [graph3Rename,zRelabel]
  simp only [consTermRename,emptyRename,zRelabel] at hp
  have hf' := renameInto hf j Theta hj
  have hchild' := renameInto hchild j Theta hj
  have ho' := renameInto ho j Theta hj
  rw [unaryFieldsRename] at hf'
  rw [graph3Rename] at hchild' ho'
  have hfold := unaryBackward mode (d.relabel j) (k.relabel j) (raw.relabel j) (child.relabel j)
    (childK.relabel j) (childOut.relabel j) produced hf' hchild' hp
  exact outputTransport (rebuild mode) produced (out.relabel j)
    ![raw.relabel j,childOut.relabel j,z]
    (valueUnique (fold mode) produced (out.relabel j) ![d.relabel j,k.relabel j,raw.relabel j] hfold ho') hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldUnaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldUnaryProof
