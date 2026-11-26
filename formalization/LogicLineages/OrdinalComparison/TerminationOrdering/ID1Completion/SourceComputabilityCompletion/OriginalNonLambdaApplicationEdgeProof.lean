module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationEdgeProof
open OriginalNonLambdaApplicationTargets

/-- Supply the checked aligned edge eliminator's neutrality premise from
the ORIGINAL requested function. Its full recovered record is unchanged. -/
theorem actualOriginalNonLambdaApplicationEdgeElimination :
    ActualOriginalNonLambdaApplicationEdgeElimination := by
  intro p
  dsimp only
  intro body alpha Gamma arrow d e function argument x y certificate parameter psi
    hi hj hn he hbottom next
  have hneutral := OriginalNonLambdaApplicationProof.actualOriginalNonLambdaApplicationNeutrality
    p body alpha Gamma arrow d e function argument x parameter hi hj hn
  exact OriginalNeutralApplicationEdgeProof.actualOriginalNeutralApplicationEdgeElimination
    p body alpha Gamma arrow d e function argument x y certificate parameter psi
    hi hj hneutral he hbottom next

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationEdgeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationEdgeProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationEdgeProof.actualOriginalNonLambdaApplicationEdgeElimination
