module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootCalibrationProof
open UniformCertificateCompletion PutRoot PutRootWorkingTargets PutRootNativeProof PutRootEvaluationProof
open InternalOriginalUniformParameterLeaves InternalOriginalUniformApplicationStepSelection
open InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalPutLeafEquality : ActualOriginalPutLeafEquality := by
  intro n arity p hp v
  change evaluate (refined p.base.oldSource p.oldStep) v = evaluate p.oldStep v
  rw [refined,evalBranch,activeEvaluation]
  by_cases hk : v.get 2 = certificateValue (v.get 0) (labelValue (v.get 2))
  · rw [if_pos hk]
    simp only [show (1 : Nat) ≠ 0 from Nat.one_ne_zero,ite_false]
    rw [acceptedValueEvaluation,hp.1.1 _,hp.2.2.2.2.1 v]
    by_cases h : sourceValue n arity (List.Vector.ofFn ![v.get 0,v.get 3]) = 1 ∧
        (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 4 ∧
        v.get 1 = resultValue (v.get 0) (labelValue (v.get 2))
    · rw [if_pos h]
      exact (chosenCertificateAccept n arity v h.1 h.2.1 h.2.2 hk).symm
    · rw [if_neg h]
      rcases OriginalConstructorLeafEvaluationProof.leafBoolean n arity v with hz | ho
      · exact hz.symm
      · have hs := OriginalTransparentVariableStepNativeCertificateProof.acceptedSource n arity v ho
        have sound := chosenCertificateSound n arity v ho hk
        exact False.elim (h ⟨hs,sound⟩)
  · rw [if_neg hk]
    rfl

theorem actualOriginalPutCalibration : ActualOriginalPutCalibration := by
  intro n arity p hp
  refine ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,?_,hp.2.2.2.2.2⟩
  intro v
  exact (actualOriginalPutLeafEquality n arity p hp v).trans (hp.2.2.2.2.1 v)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootCalibrationProof
