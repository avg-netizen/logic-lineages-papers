module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupLiftProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalIndexedPrefixProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixZeroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupQueryProof
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

open InternalAcceptanceSupportProof (programCases)
open InternalRecursionGraphStepSyntaxProof
open OriginalInternalAppendLookupCoreProof

theorem consQuery (frontCount front suffix joined count index value head tail : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row frontCount)))
 (hf : Nonempty (Derivation body Delta (fields (suc frontCount) front suffix joined count index value)))
 (hc : Nonempty (Derivation body Delta (consGraph front head tail))) :
 Nonempty (Derivation body Delta (Result (suc frontCount) front suffix index value)) := by
 apply programCases InternalApplicationValidityStackAppend.append (Fin.cons tail (Fin.cons suffix Fin.elim0)) _
 intro beta j Theta tailJoined hj ht
 simp only [consTermRename,emptyRename] at ht
 have hi' := renameInto hi j Theta hj
 rw [rowRename] at hi'
 have hf' := renameInto hf j Theta hj
 simp only [fieldsRename,sucRelabel] at hf'
 have hc' := renameInto hc j Theta hj
 rw [consGraphRename] at hc'
 simp only [resultRename,sucRelabel]
 exact atCons (frontCount.relabel j) (front.relabel j) (suffix.relabel j) (joined.relabel j)
   (count.relabel j) (index.relabel j) (value.relabel j) (head.relabel j) (tail.relabel j) tailJoined
   hi' hf' hc' ht

theorem succCore (frontCount front suffix joined count index value : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row frontCount)))
 (hf : Nonempty (Derivation body Delta (fields (suc frontCount) front suffix joined count index value))) :
 Nonempty (Derivation body Delta (Result (suc frontCount) front suffix index value)) := by
 apply nonzeroCases front _ (OriginalContextInsertionSupportProof.successorLengthNonzero frontCount front
   (InternalApplicationStepPeelSupportProof.andLeft hf))
 intro beta j Theta head tail hj hc
 have hi' := renameInto hi j Theta hj
 rw [rowRename] at hi'
 have hf' := renameInto hf j Theta hj
 simp only [fieldsRename,sucRelabel] at hf'
 simp only [resultRename,sucRelabel]
 exact consQuery (frontCount.relabel j) (front.relabel j) (suffix.relabel j) (joined.relabel j)
   (count.relabel j) (index.relabel j) (value.relabel j) head tail hi' hf' hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupQueryProof
