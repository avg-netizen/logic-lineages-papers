module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupLiftProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalIndexedPrefixProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixZeroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel)
open InternalTagArithmeticSupportProof
open InternalAdditionLawsProof (add leftZero)
open InternalListCodecSupportProof (consGraph consGraphRename)
open InternalOriginalOrderSyntaxProof (orderRename)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open OriginalInternalAppendLookup OriginalInternalAppendLookupSyntaxProof OriginalInternalAppendLookupBindingProof
open OriginalInternalAppendLookupLiftProof
open InternalQuotientComparisonProof (orRight)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroCore (front suffix joined count index value : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields z front suffix joined count index value))) :
 Nonempty (Derivation body Delta (Result z front suffix index value)) := by
 have hz := lengthZeroRecover front (InternalApplicationStepPeelSupportProof.andLeft hf)
 have happ := headTransport InternalApplicationValidityStackAppend.append joined front z (Fin.cons suffix Fin.elim0)
   hz (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight hf))
 have hs := OriginalHereditaryInternalFinitePrefixZeroProof.zeroSuffix suffix joined count index value happ
   (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hf))) (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hf))))
 have ht := tailIntro z suffix index value index count
   (InternalApplicationStepPeelSupportProof.andIntro ⟨symm (leftZero index)⟩
     (InternalApplicationStepPeelSupportProof.andIntro hs.1 (InternalApplicationStepPeelSupportProof.andIntro (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hf)))) hs.2)))
 obtain ⟨ht⟩ := ht
 exact ⟨orRight ht⟩

theorem atCons (frontCount front suffix joined count index value head tail tailJoined : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row frontCount)))
 (hf : Nonempty (Derivation body Delta (fields (suc frontCount) front suffix joined count index value)))
 (hc : Nonempty (Derivation body Delta (consGraph front head tail)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append tailJoined tail suffix))) :
 Nonempty (Derivation body Delta (Result (suc frontCount) front suffix index value)) := by
 have hjoined := InternalApplicationValidityStackAppendListProof.consForward front head tail suffix tailJoined joined
   hc ht (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight hf))
 apply OriginalInternalIndexedPrefixProof.boundedCons body alpha Delta joined head tailJoined count index value _
   hjoined (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hf))) (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hf))))
   (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hf))))
 · intro Theta inc hindex hvalue
   exact firstAt frontCount front head tail suffix index value (weakenProof hc inc) hindex hvalue
 · intro beta j Theta pred tailCount hj hindex hlength hbound hlookup
   have hi' := renameInto hi j Theta hj
   rw [rowRename] at hi'
   have hc' := renameInto hc j Theta hj
   rw [consGraphRename] at hc'
   have ht' := renameInto ht j Theta hj
   rw [graph2Rename] at ht'
   have hf' := renameInto hf j Theta hj
   simp only [fieldsRename,sucRelabel] at hf'
   have htailLength := OriginalContextInsertionSupportProof.successorLengthTail
     (front.relabel j) (head.relabel j) (tail.relabel j) (frontCount.relabel j) hc' (InternalApplicationStepPeelSupportProof.andLeft hf')
   have hr := rowApply (frontCount.relabel j) (tail.relabel j) (suffix.relabel j) (tailJoined.relabel j)
     tailCount pred (value.relabel j) hi'
     (InternalApplicationStepPeelSupportProof.andIntro htailLength (InternalApplicationStepPeelSupportProof.andIntro ht' (InternalApplicationStepPeelSupportProof.andIntro hlength (InternalApplicationStepPeelSupportProof.andIntro hbound hlookup))))
   simp only [resultRename,sucRelabel]
   exact liftResult (frontCount.relabel j) (front.relabel j) (head.relabel j) (tail.relabel j) (suffix.relabel j)
     (index.relabel j) pred (value.relabel j) hc' hindex hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupCoreProof
