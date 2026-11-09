module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuardNativeSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuardEvaluationProof
open PositiveGuard PositiveGuardNativeSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem markAtEvaluation (measure : Program 1) (i : Fin 4) (v : List.Vector Nat 4) :
    evaluate (markAt measure i) v = evaluate measure (List.Vector.ofFn ![v.get i]) := by
  change evaluate measure (List.Vector.ofFn fun _ : Fin 1 => v.get i) = _
  simp only [vectorOne,Matrix.cons_val_zero]

theorem flagAtEvaluation (measure : Program 1) (i : Fin 4) (v : List.Vector Nat 4) :
    evaluate (flagAt measure i) v = flagValue measure (v.get i) := by
  rw [flagAt,leftOfEvaluation,markAtEvaluation]
  rfl

theorem depthAtEvaluation (measure : Program 1) (i : Fin 4) (v : List.Vector Nat 4) :
    evaluate (depthAt measure i) v = depthValue measure (v.get i) := by
  rw [depthAt,rightOfEvaluation,markAtEvaluation]
  rfl

theorem spineTestEvaluation (measure : Program 1) (i : Fin 4) (v : List.Vector Nat 4) :
    evaluate (spineTest measure i) v = if flagValue measure (v.get i) = 1 then 1 else 0 := by
  rw [spineTest,sameEvaluation,flagAtEvaluation]
  rfl

theorem depthLessEvaluation (measure : Program 1) (v : List.Vector Nat 4) :
    evaluate (depthLess measure) v =
      if depthValue measure (v.get 1) < depthValue measure (v.get 0) then 1 else 0 := by
  change evaluate InternalLessThan.ltTest (List.Vector.ofFn
    ![evaluate (depthAt measure 1) v,evaluate (depthAt measure 0) v]) = _
  rw [depthAtEvaluation,depthAtEvaluation]
  simpa only [vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one] using
    InternalLessThanEvaluationProof.exactLessThanEvaluation
      (depthValue measure (v.get 1)) (depthValue measure (v.get 0))

theorem nonBottomEvaluation (bottom : Program 1) (v : List.Vector Nat 4) :
    evaluate (nonBottomGuard bottom) v =
      if evaluate bottom (List.Vector.ofFn ![v.get 0]) = 1 then 0 else 1 := by
  have hb : evaluate (bottomAt bottom) v = evaluate bottom (List.Vector.ofFn ![v.get 0]) := by
    change evaluate bottom (List.Vector.ofFn fun _ : Fin 1 => v.get 0) = _
    simp only [vectorOne,Matrix.cons_val_zero]
  rw [nonBottomGuard,evalBranch,evalNormalize,hb]
  change (if (if evaluate bottom (List.Vector.ofFn ![v.get 0]) = 1 then 1 else 0) = 0
    then 1 else 0) = _
  by_cases h : evaluate bottom (List.Vector.ofFn ![v.get 0]) = 1 <;> simp only [h,ite_true,ite_false,Nat.one_ne_zero]

theorem spineGuardEvaluation (measure : Program 1) (v : List.Vector Nat 4) :
    evaluate (spineGuard measure) v =
      if flagValue measure (v.get 0) = 1 then
        (if flagValue measure (v.get 1) = 1 ∧
          depthValue measure (v.get 1) < depthValue measure (v.get 0) then 1 else 0)
      else 1 := by
  rw [spineGuard,evalBranch,evalNormalize,spineTestEvaluation,
    conjunctionEvaluation,spineTestEvaluation,depthLessEvaluation]
  change (if (if (if flagValue measure (v.get 0) = 1 then 1 else 0) = 1 then 1 else 0) = 0
    then 1 else
      (if (if flagValue measure (v.get 1) = 1 then 1 else 0) = 1 ∧
        (if depthValue measure (v.get 1) < depthValue measure (v.get 0) then 1 else 0) = 1
        then 1 else 0)) = _
  by_cases hx : flagValue measure (v.get 0) = 1 <;>
    by_cases hy : flagValue measure (v.get 1) = 1 <;>
    by_cases hd : depthValue measure (v.get 1) < depthValue measure (v.get 0) <;>
    simp only [hx,hy,hd,ite_true,ite_false,and_self,and_false,false_and,Nat.zero_ne_one,Nat.one_ne_zero]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuardEvaluationProof
