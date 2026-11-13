module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixQuery
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackPartitionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixCore
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalAdditionLawsProof (add leftZero leftSuccessor)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalContextInsertion OriginalContextInsertionLengthProof
open OriginalContextInsertionSyntaxProof hiding andIntro andLeft andRight
open OriginalContextInsertionSupportProof (successorLengthNonzero successorLengthTail)
open CountedPrefixSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem zeroCore (remaining code front suffix : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields z remaining code front suffix))) :
 Nonempty (Derivation body Delta (outputs z remaining code front suffix)) := by
 have hl := outputTransport length (add z remaining) remaining (Fin.cons code Fin.elim0)
   ⟨leftZero remaining⟩ (andLeft hf)
 have hz := OriginalAllPositionContextDeleteBaseProof.frontZero (body := body) (Delta := Delta) code
 have hefront := valueUnique OriginalClassContextAllPositionObserver.front z front
   (Fin.cons z (Fin.cons code Fin.elim0)) hz (andLeft (andRight hf))
 have hesuffix := valueUnique InternalRawListRecursion.drop code suffix
   (Fin.cons z (Fin.cons code Fin.elim0)) (InternalRawListRecursionSupportProof.dropZero code)
   (andRight (andRight hf))
 have hfrontLength := headTransport length z z front Fin.elim0 hefront lengthZero
 have hsuffixLength := headTransport length remaining code suffix Fin.elim0 hesuffix hl
 have ha := InternalApplicationValidityStackAppendListProof.appendZeroValue (body := body) (Gamma := Delta) suffix
 have hao := outputTransport InternalApplicationValidityStackAppend.append suffix code
   (Fin.cons z (Fin.cons suffix Fin.elim0)) (by obtain ⟨he⟩ := hesuffix; exact ⟨symm he⟩) ha
 have happ := headTransport InternalApplicationValidityStackAppend.append code z front
   (Fin.cons suffix Fin.elim0) hefront hao
 exact andIntro hfrontLength (andIntro hsuffixLength happ)
theorem atCons (count remaining code front suffix head tail taken dropped candidate : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (row count)))
 (hf : Nonempty (Derivation body Delta (fields (suc count) remaining code front suffix)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
 (ht : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.front taken count tail)))
 (hd : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.drop dropped count tail)))
 (hn : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode candidate head taken))) :
 Nonempty (Derivation body Delta (outputs (suc count) remaining code front suffix)) := by
 have hlen := outputTransport length (add (suc count) remaining) (suc (add count remaining))
   (Fin.cons code Fin.elim0) ⟨leftSuccessor count remaining⟩ (andLeft hf)
 have htailLength := successorLengthTail code head tail (add count remaining) hc hlen
 have hfront := OriginalAllPositionContextDeleteFrontProof.frontCons code head tail count taken candidate hc ht hn
 have hefront := valueUnique OriginalClassContextAllPositionObserver.front candidate front
   (Fin.cons (suc count) (Fin.cons code Fin.elim0)) hfront (andLeft (andRight hf))
 have hdrop := OriginalAllPositionContextDeleteDropProof.dropConsBackward code head tail count dropped hc hd
 have hesuffix := valueUnique InternalRawListRecursion.drop dropped suffix
   (Fin.cons (suc count) (Fin.cons code Fin.elim0)) hdrop (andRight (andRight hf))
 have htailDrop := outputTransport InternalRawListRecursion.drop dropped suffix
   (Fin.cons count (Fin.cons tail Fin.elim0)) hesuffix hd
 have ih := rowApply count remaining tail taken suffix hr (andIntro htailLength (andIntro ht htailDrop))
 have hcLength := lengthCons candidate head taken count hn (andLeft ih)
 have hfLength := headTransport length (suc count) candidate front Fin.elim0 hefront hcLength
 have hca := InternalApplicationValidityStackAppendListProof.consBackward candidate head taken suffix tail code
   hn (andRight (andRight ih)) hc
 have happ := headTransport InternalApplicationValidityStackAppend.append code candidate front
   (Fin.cons suffix Fin.elim0) hefront hca
 exact andIntro hfLength (andIntro (andLeft (andRight ih)) happ)
theorem succCore (count remaining code front suffix : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (row count)))
 (hf : Nonempty (Derivation body Delta (fields (suc count) remaining code front suffix))) :
 Nonempty (Derivation body Delta (outputs (suc count) remaining code front suffix)) := by
 have hlen := outputTransport length (add (suc count) remaining) (suc (add count remaining))
   (Fin.cons code Fin.elim0) ⟨leftSuccessor count remaining⟩ (andLeft hf)
 apply nonzeroCases code _ (successorLengthNonzero (add count remaining) code hlen)
 intro beta j Theta head tail hinc hc
 simp only [outputsRename,sucRelabel]
 have hf' := renameInto hf j Theta hinc
 simp only [fieldsRename,sucRelabel] at hf'
 have hr' := renameInto hr j Theta hinc
 rw [rowRename] at hr'
 apply CountedPrefixQuery.tailPieces (count.relabel j) tail head _
 intro gamma k Xi taken dropped candidate hinc2 ht hd hn
 simp only [outputsRename,sucRelabel]
 have hf'' := renameInto hf' k Xi hinc2
 simp only [fieldsRename,sucRelabel] at hf''
 have hr'' := renameInto hr' k Xi hinc2
 rw [rowRename] at hr''
 have hc' := renameInto hc k Xi hinc2
 rw [graph2Rename] at hc'
 exact atCons ((count.relabel j).relabel k) ((remaining.relabel j).relabel k)
   ((code.relabel j).relabel k) ((front.relabel j).relabel k) ((suffix.relabel j).relabel k)
   (head.relabel k) (tail.relabel k) taken dropped candidate hr'' hf'' hc' ht hd hn
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixCore
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixCore
