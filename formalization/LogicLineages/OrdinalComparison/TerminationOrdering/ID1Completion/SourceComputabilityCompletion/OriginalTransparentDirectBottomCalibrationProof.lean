module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumGlobalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomCalibrationProof
open UniformCertificateCompletion OriginalTransparentDirectBottom OriginalTransparentDirectBottomTargets
open OriginalTransparentDirectBottomNativeProof
open OriginalTransparentVariableStepEvaluationProof (bottomValue certificateValue certificateCodeEvaluation)
open InternalOriginalUniformParameterLeaves InternalOriginalUniformApplicationStepSelection
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem activeEvaluation (v : List.Vector Nat 4) :
    evaluate active v = if v.get 2 = certificateValue (v.get 0) then 1 else 0 := by
  rw [active,sameEvaluation]
  change (if v.get 2 = evaluate certificateCode (List.Vector.ofFn fun _ : Fin 1 => v.get 0)
    then 1 else 0) = _
  simp only [certificateCode,certificateCodeEvaluation,List.Vector.get_ofFn]

theorem acceptedValueEvaluation (source : Program 2) (v : List.Vector Nat 4) :
    evaluate (acceptedValue source) v =
      if evaluate source (List.Vector.ofFn ![v.get 0,v.get 3]) = 1 ∧
        BottomRepresentative.bottomValue (v.get 0) ≠ 1 ∧
        v.get 1 = bottomValue (v.get 0) then 1 else 0 := by
  rw [acceptedValue,conjunctionEvaluation,conjunctionEvaluation,
    PositiveGuardEvaluationProof.nonBottomEvaluation,
    BottomRepresentativeEvaluationProof.bottomTestEvaluation,sameEvaluation,
    OriginalConstructorLeafEvaluationProof.expectedBottomEvaluation]
  change (if evaluate source (List.Vector.ofFn ![v.get 0,v.get 3]) = 1 ∧
    (if (if BottomRepresentative.bottomValue (v.get 0) = 1 then 0 else 1) = 1 ∧
      (if v.get 1 = bottomValue (v.get 0) then 1 else 0) = 1 then 1 else 0) = 1 then 1 else 0) = _
  by_cases hs : evaluate source (List.Vector.ofFn ![v.get 0,v.get 3]) = 1 <;>
    by_cases hn : BottomRepresentative.bottomValue (v.get 0) = 1 <;>
      by_cases ht : v.get 1 = bottomValue (v.get 0) <;> simp [hs,hn,ht]

/-- The literal chosen certificate branch is replaced only by its exact
native acceptance predicate. Every other certificate returns the entire old
output unchanged; rejection includes actual bottom sources and malformed data. -/
theorem actualOriginalDirectBottomEquality : ActualOriginalDirectBottomEquality := by
  intro n arity p hp v
  change evaluate (refined p.base.oldSource p.oldStep) v = evaluate p.oldStep v
  rw [refined,evalBranch,activeEvaluation]
  by_cases hk : v.get 2 = certificateValue (v.get 0)
  · simp only [hk,ite_true,show (1 : Nat) ≠ 0 from Nat.one_ne_zero,ite_false]
    rw [acceptedValueEvaluation,hp.1.1 _,hp.2.2.2.2.1 v]
    by_cases h : sourceValue n arity (List.Vector.ofFn ![v.get 0,v.get 3]) = 1 ∧
        BottomRepresentative.bottomValue (v.get 0) ≠ 1 ∧ v.get 1 = bottomValue (v.get 0)
    · rw [if_pos h]
      exact (chosenCertificateAccept n arity v h.1 h.2.1 h.2.2 hk).symm
    · rw [if_neg h]
      rcases OriginalConstructorLeafEvaluationProof.leafBoolean n arity v with hz | ho
      · exact hz.symm
      · have hs := OriginalTransparentVariableStepNativeCertificateProof.acceptedSource n arity v ho
        have hnb := (OriginalConstructorLeafEvaluationProof.leafGuards n arity v ho).1
        have ht := chosenCertificateTarget n arity v ho hk
        exact False.elim (h ⟨hs,by rw [hnb]; decide,ht⟩)
  · simp only [hk,ite_false,ite_true]

theorem actualOriginalDirectBottomCalibration : ActualOriginalDirectBottomCalibration := by
  intro n arity p hp
  refine ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,?_,hp.2.2.2.2.2⟩
  intro v
  exact (actualOriginalDirectBottomEquality n arity p hp v).trans (hp.2.2.2.2.1 v)

theorem actualOriginalDirectBottomRetention : ActualOriginalDirectBottomRetention := by
  intro n arity p H G W P hp hH hG hW hP
  exact OriginalActiveKernelMinimumGlobalProof.actualOriginalActiveKernelMinimumRetention
    n arity (refineInputs p) H G W P
    (actualOriginalDirectBottomCalibration n arity p hp) hH hG hW hP

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomCalibrationProof
