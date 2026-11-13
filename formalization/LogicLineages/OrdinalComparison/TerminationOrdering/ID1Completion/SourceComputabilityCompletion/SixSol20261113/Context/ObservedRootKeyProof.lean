module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootTraversalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootKeyTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootKeyProof
 theorem actualRootKeyPreservation : ObservedRootKeyTargets.ActualRootKeyPreservation := by
  intro p H G W P body alpha Delta out input typ parameter mark
  exact ObservedRootTraversalProof.actualOriginalStructuralTraversalKeyFinal
    (Erasure.ObservedPut.prepared p H G W) H G W P body alpha Delta out input typ parameter mark
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootKeyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootKeyProof
