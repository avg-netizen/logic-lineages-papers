module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.LambdaContextDeletionTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.LambdaContextDeletionProof
open InternalApplicationStepPeelSupportProof (andIntro)
theorem actualMetadata : LambdaContextDeletionTargets.ActualMetadata := by
 intro body alpha Delta gamma deleted childGamma childDeleted domain cutoff erasedType count hc hcd hl hb hv hd
 have hs := OriginalPositionStructuralKeyLambdaContextProof.shiftedLookupAndDeletion
   gamma deleted childGamma childDeleted domain cutoff erasedType hc hcd hv hd
 exact andIntro (OriginalContextInsertionLengthProof.lengthCons childGamma domain gamma count hc hl)
   (andIntro (InternalRecursionGraphExtensionSupportProof.successorOrder cutoff count hb)
     (andIntro hs.1 hs.2))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.LambdaContextDeletionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.LambdaContextDeletionProof
