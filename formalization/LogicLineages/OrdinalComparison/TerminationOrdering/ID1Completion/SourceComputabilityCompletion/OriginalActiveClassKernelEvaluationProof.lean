module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelCalibrationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelEvaluationProof
open OriginalActiveClassKernel UniformCertificateCompletion
open InternalAcceptanceCalibrationProof InternalApplicationStepPeelEvaluationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

theorem seedQueryEvaluation (R : Program 2) (v : List.Vector Nat 3) :
    evaluate (.composition R ![.projection 0,.projection 2]) v =
      evaluate R (ofFn ![v.get 0,v.get 2]) := by
  change evaluate R (ofFn (fun i => evaluate ((![.projection 0,.projection 2] : Fin 2 → Program 3) i) v)) = _
  apply congrArg (evaluate R)
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i <;> rfl

theorem candidateQueryEvaluation (R : Program 2) (v : List.Vector Nat 3) :
    evaluate (.composition R ![.projection 1,.projection 2]) v =
      evaluate R (ofFn ![v.get 1,v.get 2]) := by
  change evaluate R (ofFn (fun i => evaluate ((![.projection 1,.projection 2] : Fin 2 → Program 3) i) v)) = _
  apply congrArg (evaluate R)
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i <;> rfl

theorem keyEvaluation (R : Program 2) (v : List.Vector Nat 3) :
    evaluate (keyTest R) v =
      if evaluate R (ofFn ![v.get 0,v.get 2]) = evaluate R (ofFn ![v.get 1,v.get 2])
        then 1 else 0 := by
  rw [keyTest,sameEvaluation,seedQueryEvaluation,candidateQueryEvaluation]

theorem classEvaluation (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (v : List.Vector Nat 3) :
    evaluate (classTest p H G W P) v =
      if evaluate (OriginalActiveObservedClass.activation p H G W) (ofFn ![v.get 0,v.get 2]) = 0
        then evaluate P v else evaluate (kernel p H G W) v := by
  rw [classTest,evalBranch,seedQueryEvaluation]

theorem kernelEvaluation (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (v : List.Vector Nat 3) :
    evaluate (kernel p H G W) v =
      if evaluate (OriginalTypedDecoder.target H G) (ofFn ![v.get 1,v.get 2]) = 1 ∧
          evaluate (OriginalActiveObservedClass.activation p H G W) (ofFn ![v.get 1,v.get 2]) = 1 ∧
          evaluate p.base.oldRepresentative (ofFn ![v.get 0,v.get 2]) =
            evaluate p.base.oldRepresentative (ofFn ![v.get 1,v.get 2]) then 1 else 0 := by
  rw [kernel,conjunctionEvaluation,candidateQueryEvaluation,keyEvaluation,
    domainProgram,conjunctionEvaluation]
  simp [and_assoc]

theorem activationAcceptance (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (value parameter : Nat) :
    evaluate (OriginalActiveObservedClass.activation p H G W) (ofFn ![value,parameter]) = 1 ↔
      evaluate (BottomRepresentative.windowAt p.window) (ofFn ![value,parameter]) = 1 ∧
      evaluate (OriginalTransparentDecoderSelection.transparentInputs H G W p).base.oldSource
        (ofFn ![value,parameter]) = 1 := by
  change evaluate (OriginalRankGuardedRepresentative.active
    (OriginalTransparentDecoderSelection.transparentInputs H G W p).base.oldSource p.window)
      (ofFn ![value,parameter]) = 1 ↔ _
  rw [OriginalRankGuardedRepresentative.active,conjunctionEvaluation]
  by_cases h : evaluate (BottomRepresentative.windowAt p.window) (ofFn ![value,parameter]) = 1 ∧
      evaluate (OriginalTransparentDecoderSelection.transparentInputs H G W p).base.oldSource
        (ofFn ![value,parameter]) = 1 <;> simp [h]

theorem activationNonzero (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (value parameter : Nat)
    (h : evaluate (OriginalActiveObservedClass.activation p H G W) (ofFn ![value,parameter]) ≠ 0) :
    evaluate (OriginalActiveObservedClass.activation p H G W) (ofFn ![value,parameter]) = 1 := by
  change evaluate (OriginalRankGuardedRepresentative.active
    (OriginalTransparentDecoderSelection.transparentInputs H G W p).base.oldSource p.window)
      (ofFn ![value,parameter]) = 1
  change evaluate (OriginalRankGuardedRepresentative.active
    (OriginalTransparentDecoderSelection.transparentInputs H G W p).base.oldSource p.window)
      (ofFn ![value,parameter]) ≠ 0 at h
  rw [OriginalRankGuardedRepresentative.active,conjunctionEvaluation] at h ⊢
  split_ifs with hc <;> simp_all

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelEvaluationProof
