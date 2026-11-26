module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalSelectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityRefinementProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalPreparationProof
open UniformCertificateCompletion OriginalTransparentLambdaFinal

/-- Native calibration changes only the two base validity leaves. Every
other original global field is retained literally. This theorem supplies no
arithmetic lambda law and is not used as an internal reflection principle. -/
theorem nativeRefinement (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    NativeRefinement n arity p := by
  have hbase :=
    OriginalTransparentLambdaValidityRefinementProof.actualOriginalTransparentRefinementCalibration
      n arity p.base hp.1
  exact ⟨⟨hbase.2.2.2,hp.2⟩,hbase.2.2.1⟩

theorem actualOriginalTransparentFinalPreparation :
    OriginalTransparentLambdaFinalTargets.ActualOriginalTransparentFinalPreparation :=
  ⟨OriginalTransparentLambdaFinalSelectionProof.pipelineIdentity,nativeRefinement⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalPreparationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalPreparationProof
