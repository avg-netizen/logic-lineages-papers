module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionAssemblyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionCalibrationProof
open UniformCertificateCompletion OriginalTransparentApplicationFunctionDefinitions
open OriginalTransparentApplicationFunctionTargets OriginalTransparentApplicationFunctionEvaluationProof
open OriginalTransparentApplicationFunctionAssemblyProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualGuardedEquality : ActualGuardedEquality := by
 intro n arity p hp v h
 rw [hopGuardEvaluation] at h
 have hh : evaluate p.base.oldSource (List.Vector.ofFn ![v.get 0,v.get 3]) = 1 ∧ evaluate structuralGuard v = 1 := by
  split at h
  next ht => exact ht
  next => contradiction
 rw [hp.1.1] at hh
 rw [hp.2.2.2.2.1,hp.2.2.2.2.1]
 exact OriginalTransparentApplicationFunctionNativeProof.leafEquality n arity v hh.1 hh.2

theorem actualTransitionEquality : ActualTransitionEquality := transitionFromGuard actualGuardedEquality
theorem actualOneStepEquality : ActualOneStepEquality := oneStepFromTransition actualTransitionEquality
theorem actualCalibration : ActualCalibration := calibrationFromEquality actualOneStepEquality
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionCalibrationProof
