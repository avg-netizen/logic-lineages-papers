module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservedPutTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutPreparationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalRetentionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservedPutRetentionProof
theorem actualRetention : ObservedPut.ActualRetention := by
  intro n arity p H G W P hp hH hG hW hP
  have hprepared := PutPreparationProof.actualPutPreparation n arity p H G W P hp hH hG hW hP
  exact ⟨hprepared,OriginalAllPositionStructuralTraversalRetentionProof.actualRetention
    n arity (ObservedPut.prepared p H G W) H G W P hprepared.1 hH hG hW hP⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservedPutRetentionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservedPutRetentionProof
