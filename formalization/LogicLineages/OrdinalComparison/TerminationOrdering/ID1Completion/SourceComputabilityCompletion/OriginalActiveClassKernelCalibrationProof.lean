module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelCalibrationProof
open Source InternalOriginalUniformParameterLeaves
open OriginalTransparentMinimum (classValue)
open OriginalActiveClassKernel OriginalActiveClassKernelEvaluationProof
open OriginalActiveClassKernelCalibrationSupportProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- On every vector, an inactive seed retains the whole original class
program. An active seed decodes one original closed window and Gamma; original
primary-class membership is exactly candidate source/target acceptance and
equality of the original pre-minimum representative keys in that same slice. -/
theorem actualOriginalActiveClassKernelCalibration :
    OriginalActiveClassKernelTargets.ActualOriginalActiveClassKernelCalibration := by
  intro n arity p H G W P hp hH hG hW hP v
  rw [classEvaluation]
  by_cases ha : evaluate (OriginalActiveObservedClass.activation p H G W)
      (ofFn ![v.get 0,v.get 2]) = 0
  · simp only [ha,ite_true]
    exact hP v
  · simp only [ha,ite_false]
    let q := OriginalTransparentDecoderSelection.transparentInputs H G W p
    have hq : GlobalSourcePackage.InputsCalibrated n arity q :=
      (OriginalTransparentDecoderSelectionCalibrationProof.actualOriginalTransparentDecoderCalibration
        n arity p H G W hp hH hG hW).1
    have hactive := (activationAcceptance p H G W (v.get 0) (v.get 2)).mp
      (activationNonzero p H G W (v.get 0) (v.get 2) ha)
    have hwindow : GuardCalibration.validWindow n (Nat.unpair (v.get 2)).1 = 1 := by
      have hw : evaluate p.window (ofFn ![(Nat.unpair (v.get 2)).1]) = 1 := by
        simpa only [BottomRepresentativeEvaluationProof.windowAtEvaluation] using hactive.1
      have hc := hp.2.1 (ofFn ![(Nat.unpair (v.get 2)).1])
      change evaluate p.window (ofFn ![(Nat.unpair (v.get 2)).1]) =
        GuardCalibration.validWindow n (Nat.unpair (v.get 2)).1 at hc
      exact hc.symm.trans hw
    obtain ⟨ctx,hctx,hclosed⟩ :=
      (GuardCalibrationProof.actualValidWindowCalibration n (Nat.unpair (v.get 2)).1).1.mp hwindow
    obtain ⟨Gamma,ho⟩ := BottomRepresentativeEvaluationProof.parameterGamma (v.get 2)
    have hseed := BottomRepresentativeEvaluationProof.decodedLeafSlice
      n arity q.base hq.1 (v.get 2) ctx hctx Gamma ho (v.get 0)
    have hcand := BottomRepresentativeEvaluationProof.decodedLeafSlice
      n arity q.base hq.1 (v.get 2) ctx hctx Gamma ho (v.get 1)
    have hsource : InternalOriginalStepGuard.sourceValidityValue
        n arity ctx.1.1 ctx.1.2 Gamma (v.get 0) = 1 :=
      hseed.1.symm.trans hactive.2
    have hwindowCandidate : evaluate (BottomRepresentative.windowAt p.window)
        (ofFn ![v.get 1,v.get 2]) = 1 := by
      simpa only [BottomRepresentativeEvaluationProof.windowAtEvaluation] using hactive.1
    have hclass : classValue n arity v =
        rawClassValue n arity ctx.1.1 ctx.1.2 Gamma (v.get 0) (v.get 1) := by
      simp only [classValue,decodedValue,hctx,ho (v.get 0)]
    have hcondition :
        (evaluate (OriginalTypedDecoder.target H G) (ofFn ![v.get 1,v.get 2]) = 1 ∧
          evaluate (OriginalActiveObservedClass.activation p H G W) (ofFn ![v.get 1,v.get 2]) = 1 ∧
          evaluate p.base.oldRepresentative (ofFn ![v.get 0,v.get 2]) =
            evaluate p.base.oldRepresentative (ofFn ![v.get 1,v.get 2])) ↔
          classValue n arity v = 1 := by
      rw [hclass,rawClassCharacterization n arity ctx.1.1 ctx.1.2 Gamma hclosed
        (v.get 0) (v.get 1) hsource]
      constructor
      · rintro ⟨ht,hactivation,hkey⟩
        have hs := ((activationAcceptance p H G W (v.get 1) (v.get 2)).mp hactivation).2
        exact ⟨hcand.1.symm.trans hs,hcand.2.1.symm.trans ht,
          hseed.2.2.1.symm.trans (hkey.trans hcand.2.2.1)⟩
      · rintro ⟨hs,ht,hkey⟩
        exact ⟨hcand.2.1.trans ht,
          (activationAcceptance p H G W (v.get 1) (v.get 2)).mpr
            ⟨hwindowCandidate,hcand.1.trans hs⟩,
          hseed.2.2.1.trans (hkey.trans hcand.2.2.1.symm)⟩
    rw [kernelEvaluation]
    by_cases hit : classValue n arity v = 1
    · rw [if_pos (hcondition.mpr hit),hit]
    · have hmiss := fun h => hit (hcondition.mp h)
      have hzero := (OriginalActiveObservedCalibrationProof.classBoolean n arity v).resolve_right hit
      rw [if_neg hmiss,hzero]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelCalibrationProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelCalibrationProof.actualOriginalActiveClassKernelCalibration
