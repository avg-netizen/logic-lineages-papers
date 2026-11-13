module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentDirectProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentLookupProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentProof
open ObservationDescentDefinitions ObservationDescentPairProof ObservationDescentSelectorProof
open InternalUnpairReverseBoundsArithmeticProof (weakTrans)
open InternalSquareRootArithmeticSupportProof (strictWeakTrans)
theorem actualStoredChildDescent : ObservationDescentTargets.ActualStoredChildDescent := by
 intro slot body alpha Delta out base inner recursive rows tag payload list count index typed typ child ho hi hr hs hl hb hv hp
 have hcl := ObservationDescentLookupProof.actualTypedLookupDescent body alpha Delta list count index typed typ child hl hb hv hp
 have hlp := actualSelectorBound (listPath slot) body alpha Delta payload list hs
 have hpr := pairRightBound recursive tag payload hr
 have hro := envelope out base inner recursive rows ho hi
 exact strictWeakTrans child list out hcl
   (weakTrans list payload out hlp (weakTrans payload recursive out hpr hro))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentProof
