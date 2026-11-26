module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionOtherLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalFinalTransferProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open OriginalAllPositionStructuralTraversalDefinitions
open OriginalAllPositionStructuralTraversalTargets

/-- Assembly at the literal common tuple. Every constructor and actual OTHER
supplier is discharged; no supplier is added to the frozen target. -/
theorem actualTraversal : ActualTraversal := by
  intro p H G W P
  exact OriginalIndexedObserverInductionProof.actualIndexedObserverTraversal
    (refined p H G W P).base (refined p H G W P).window (observer p H G W)
    (OriginalAllPositionStructuralTraversalApplicationProof.actualApplicationLaw p H G W P)
    (OriginalAllPositionStructuralTraversalLambdaProof.actualLambdaLaw p H G W P)
    (OriginalAllPositionOtherLeafProof.actualOther p H G W P)

theorem actualFinal : ActualFinal := by
  intro p H G W P
  exact OriginalAllPositionStructuralTraversalFinalTransferProof.finalOfTraversal p H G W P
    (actualTraversal p H G W P)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalProof
