module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepNativeCertificateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepCalibrationProof
open UniformCertificateCompletion OriginalTransparentVariableStep OriginalTransparentVariableStepTargets
open OriginalTransparentVariableStepEvaluationProof OriginalTransparentVariableStepNativeCertificateProof
open InternalOriginalUniformParameterLeaves InternalOriginalUniformApplicationStepSelection
open InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- ALL four-input vectors retain their complete original output. Only the
explicit chosen variable certificate is replaced, and native decoding pays
both acceptance and rejection on that branch. -/
theorem actualOriginalTransparentVariableStepEquality : ActualOriginalTransparentVariableStepEquality := by
  intro n arity p hp v
  change evaluate (refined p.base.oldSource p.oldStep) v = evaluate p.oldStep v
  rw [refined,evalBranch,activeEvaluation]
  by_cases ha : (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 0 ∧
      v.get 2 = certificateValue (v.get 0)
  · simp only [ha,ite_true,show (1 : Nat) ≠ 0 from Nat.one_ne_zero,ite_false]
    rw [acceptedValueEvaluation,hp.1.1 _,hp.2.2.2.2.1 v]
    by_cases h : sourceValue n arity (List.Vector.ofFn ![v.get 0,v.get 3]) = 1 ∧
        v.get 1 = bottomValue (v.get 0)
    · simp only [h,ite_true]
      exact (chosenCertificateAccept n arity v ha.1 h.1 h.2 ha.2).symm
    · simp only [h,ite_false]
      rcases OriginalConstructorLeafEvaluationProof.leafBoolean n arity v with hz | ho
      · exact hz.symm
      · have hs := acceptedSource n arity v ho
        have ht := (OriginalConstructorLeafEvaluationProof.leafGuards n arity v ho).2 ha.1
        exact False.elim (h ⟨hs,ht⟩)
  · simp only [ha,ite_false,ite_true]

theorem actualOriginalTransparentVariableStepCalibration : ActualOriginalTransparentVariableStepCalibration := by
  intro n arity p hp
  refine ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,?_,hp.2.2.2.2.2⟩
  intro v
  exact (actualOriginalTransparentVariableStepEquality n arity p hp v).trans (hp.2.2.2.2.1 v)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepCalibrationProof
