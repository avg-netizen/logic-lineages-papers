module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectCalibrationProof
open OriginalFinalVariableObject
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Every natural input vector agrees with the literal existing native
wrapper. This equality is not used to manufacture any internal Derivation. -/
theorem actualOriginalFinalVariableObjectCalibration :
    OriginalFinalVariableObjectTargets.ActualOriginalFinalVariableObjectCalibration := by
  intro p v
  unfold canonicalObjectProgram
  rw [pairOfEvaluation,leftOfEvaluation]
  change Nat.pair (Nat.unpair (v.get 1)).1
    (evaluate (InternalParameterizedCanonicalResultFold.foldN (OriginalLambdaTraversalSelection.finalData p))
      (List.Vector.ofFn ![evaluate (rightOf (.projection 1)) v,
        evaluate (pairOf (.projection 0) (leftOf (.projection 1))) v])) = _
  rw [rightOfEvaluation,pairOfEvaluation,leftOfEvaluation]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectCalibrationProof
