module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackPartitionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteDropProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteFrontProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackPartitionCoreProof
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
open OriginalResultStackPartitionSyntaxProof hiding rowInstantiate rowSuccessor
open OriginalClassContextAllPositionObserver (deleteAt)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroCore (initialList suffix joined : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields z initialList suffix joined))) :
 Nonempty (Derivation body Delta (outputs z initialList suffix joined)) := by
 have he := lengthZeroRecover initialList (andLeft hf)
 have happ := headTransport InternalApplicationValidityStackAppend.append joined initialList z ![suffix] he (andRight hf)
 have hj := InternalApplicationValidityStackAppendListProof.appendZeroRecover joined suffix happ
 have hfront := OriginalAllPositionContextDeleteBaseProof.frontZero (body:=body) (Delta:=Delta) joined
 have hfront' := outputTransport OriginalClassContextAllPositionObserver.front z initialList ![z,joined]
   (by obtain ⟨he⟩ := he; exact ⟨symm he⟩) hfront
 have hdrop := outputTransport InternalRawListRecursion.drop joined suffix ![z,joined] hj
   (InternalRawListRecursionSupportProof.dropZero joined)
 exact andIntro hfront' hdrop

theorem succCore (count initialList suffix joined : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (row count)))
 (hf : Nonempty (Derivation body Delta (fields (suc count) initialList suffix joined))) :
 Nonempty (Derivation body Delta (outputs (suc count) initialList suffix joined)) := by
 apply nonzeroCases initialList _ (successorLengthNonzero count initialList (andLeft hf))
 intro beta j Theta head tail hj hc
 simp only [outputsRename,sucRelabel]
 have hf' := renameInto hf j Theta hj
 simp only [fieldsRename,sucRelabel] at hf'
 have hr' := renameInto hr j Theta hj
 rw [rowRename] at hr'
 have hl := successorLengthTail (initialList.relabel j) head tail (count.relabel j) hc (andLeft hf')
 apply programCases InternalApplicationValidityStackAppend.append (Fin.cons tail (Fin.cons (suffix.relabel j) Fin.elim0)) _
 intro gamma k Xi tailJoined hk happ
 simp only [outputsRename,sucRelabel]
 have hf'' := renameInto hf' k Xi hk
 simp only [fieldsRename,sucRelabel] at hf''
 have hr'' := renameInto hr' k Xi hk
 rw [rowRename] at hr''
 have hc' := renameInto hc k Xi hk
 rw [consGraphRename] at hc'
 have hl' := renameInto hl k Xi hk
 rw [lengthRename] at hl'
 have happ' : Nonempty (Derivation body Xi (graph2 InternalApplicationValidityStackAppend.append tailJoined
     (tail.relabel k) ((suffix.relabel j).relabel k))) := by
   simpa only [graph2,consTermRename,emptyRename] using happ
 have hout := InternalApplicationValidityStackAppendListProof.consForward
   ((initialList.relabel j).relabel k) (head.relabel k) (tail.relabel k)
   ((suffix.relabel j).relabel k) tailJoined ((joined.relabel j).relabel k) hc' happ' (andRight hf'')
 have ih := rowApply ((count.relabel j).relabel k) (tail.relabel k)
   ((suffix.relabel j).relabel k) tailJoined hr'' (andIntro hl' happ')
 have hfront := OriginalAllPositionContextDeleteFrontProof.frontCons
   ((joined.relabel j).relabel k) (head.relabel k) tailJoined ((count.relabel j).relabel k)
   (tail.relabel k) ((initialList.relabel j).relabel k) hout (andLeft ih) hc'
 have hdrop := OriginalAllPositionContextDeleteDropProof.dropConsBackward
   ((joined.relabel j).relabel k) (head.relabel k) tailJoined ((count.relabel j).relabel k)
   ((suffix.relabel j).relabel k) hout (andRight ih)
 exact andIntro hfront hdrop

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackPartitionCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackPartitionCoreProof
