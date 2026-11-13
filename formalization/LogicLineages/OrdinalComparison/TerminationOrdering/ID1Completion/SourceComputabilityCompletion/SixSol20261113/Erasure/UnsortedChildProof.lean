module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.UnsortedChildTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListSumBoundStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentDirectProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.UnsortedChildProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel)
open InternalOriginalOrderSyntaxProof (orderRename)
open InternalUnpairReverseBoundsArithmeticProof (weakTrans)
open InternalSquareRootArithmeticSupportProof (strictWeakTrans)
open InternalOriginalPairingOrderArithmeticProof (weakStrictTrans)
open InternalPairingSumBounds (weakBound)
open SourceComputabilityFormulaSupportProof (numeral)
open ObservationDescentDefinitions ObservationDescentPairProof ObservationDescentSelectorProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atSum (raw sorted count index value total : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph1 OriginalNumericListSort.sort sorted raw)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count raw)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below index count)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value index raw)))
 (ht : Nonempty (Derivation body Delta (graph1 ListSumBoundDefinitions.sum total raw))) :
 Nonempty (Derivation body Delta (weakBound value sorted)) := by
 have hst := SortWeightedSortProof.actualSort 0 (.projection (0 : Fin 1)) body alpha Delta raw sorted total Fin.elim0 hs ht
 exact weakTrans value total sorted
   (ListEntryBoundProof.actualEntryBound body alpha Delta raw count index value total hl hb hv ht)
   (ListSumBoundProof.actualSumBound body alpha Delta sorted total hst)

theorem actualSortedEntryBound : UnsortedChildTargets.ActualSortedEntryBound := by
 intro body alpha Delta raw sorted count index value hs hl hb hv
 apply programCases ListSumBoundDefinitions.sum (Fin.cons raw Fin.elim0) _
 intro beta j Theta total hj ht
 simp only [weakBound,InternalLessThan.strictLess,orderRename,sucRelabel]
 simp only [consTermRename,emptyRename] at ht
 have hs' := renameInto hs j Theta hj
 have hl' := renameInto hl j Theta hj
 have hb' := renameInto hb j Theta hj
 have hv' := renameInto hv j Theta hj
 rw [graph1Rename] at hs'
 rw [OriginalContextInsertionSyntaxProof.lengthRename] at hl'
 simp only [OriginalContextInsertion.Below,orderRename] at hb'
 rw [graph2Rename] at hv'
 exact atSum (raw.relabel j) (sorted.relabel j) (count.relabel j) (index.relabel j)
   (value.relabel j) total hs' hl' hb' hv' ht

theorem positiveBase (kind : UnsortedChildDefinitions.BaseSlot) (root payload : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing root
   (numeral (UnsortedChildDefinitions.tag kind)) payload))) :
 Nonempty (Derivation body Delta (InternalLessThan.strictLess payload root)) := by
 cases kind with
 | ordinary => exact ObservationDescentDirectProof.positivePayload (numeral 3) payload root hr
 | numbered => exact ObservationDescentDirectProof.positivePayload (numeral 4) payload root hr

theorem actualUnsortedChildDescent : UnsortedChildTargets.ActualUnsortedChildDescent := by
 intro kind body alpha Delta out base inner recursive rows payload raw sorted count index typed typ child ho hi hr hsel hs hl hb hv hp
 have hts := actualSortedEntryBound body alpha Delta raw sorted count index typed hs hl hb hv
 have hsp := actualSelectorBound (listPath (UnsortedChildDefinitions.slot kind)) body alpha Delta payload sorted hsel
 have hcp := weakTrans child typed payload (pairRightBound typed typ child hp)
   (weakTrans typed sorted payload hts hsp)
 exact strictWeakTrans child recursive out
   (weakStrictTrans child payload recursive hcp (positiveBase kind recursive payload hr))
   (envelope out base inner recursive rows ho hi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.UnsortedChildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.UnsortedChildProof
