module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionNativePositionsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionNativeCalibrationProof
open Source InternalOriginalUniformParameterLeaves
open UniformCertificateCompletion
open OriginalClassContextAllPositionObserver OriginalClassContextAllPositionNativeEvaluationProof
open OriginalClassContextAllPositionNativePositionsProof
open OriginalActiveClassKernelCalibrationSupportProof
open OriginalActiveClassKernelEvaluationProof (activationAcceptance activationNonzero)
open OriginalContextExtensionCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- An active true original class hit pays every finite position test.
Malformed/inactive classes are handled separately by the exact fallback. -/
theorem allTestsAccepted (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (hp : GlobalSourcePackage.InputsCalibrated n arity p)
    (hH : OriginalTypedDecoder.HeadSignatureCalibrated n arity H)
    (hG : OriginalVariableLeaves.ContextGuardCalibrated n G)
    (hW : OriginalUniverseDecoder.HeadWindowCalibrated n arity W)
    (v : List.Vector Nat 3)
    (ha : evaluate (OriginalActiveObservedClass.activation p H G W) (ofFn ![v.get 0,v.get 2]) ≠ 0)
    (hit : OriginalTransparentMinimum.classValue n arity v = 1) :
    evaluate (allTests p.base.oldRepresentative) v = 1 := by
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
  have hgamma := OriginalClassContextObserverCalibrationProof.gammaEncoding (v.get 2) Gamma ho
  have hparameter : v.get 2 = Nat.pair (Nat.unpair (v.get 2)).1 (Encodable.encode Gamma) := by
    rw [hgamma,Nat.pair_unpair]
  have hseed := BottomRepresentativeEvaluationProof.decodedLeafSlice
    n arity q.base hq.1 (v.get 2) ctx hctx Gamma ho (v.get 0)
  have hsource : InternalOriginalStepGuard.sourceValidityValue n arity ctx.1.1 ctx.1.2 Gamma (v.get 0) = 1 :=
    hseed.1.symm.trans hactive.2
  have hclass : rawClassValue n arity ctx.1.1 ctx.1.2 Gamma (v.get 0) (v.get 1) = 1 := by
    simpa only [OriginalTransparentMinimum.classValue,decodedValue,hctx,ho (v.get 0)] using hit
  have h := allTestsOnContext n arity p hp ctx.1.1 ctx.1.2 ctx.2
    (Nat.unpair (v.get 2)).1 hctx hclosed Gamma (v.get 0) (v.get 1) hsource hclass
  rw [← hparameter] at h
  have hv : ofFn ![v.get 0,v.get 1,v.get 2] = v := by
    apply List.Vector.ext
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))) i <;> rfl
  rwa [hv] at h

theorem calibration : OriginalClassContextAllPositionObserverTargets.Calibration := by
  intro n arity p H G W P hp hH hG hW hP v
  rw [classEvaluation]
  by_cases hnil : (Nat.unpair (v.get 2)).2 = 0
  · simp only [hnil,ite_true]
    exact hP v
  · simp only [hnil,ite_false]
    by_cases ha : evaluate (OriginalActiveObservedClass.activation p H G W)
        (ofFn ![v.get 0,v.get 2]) = 0
    · simp only [ha,ite_true]
      exact hP v
    · simp only [ha,ite_false,hP v]
      rcases OriginalActiveObservedCalibrationProof.classBoolean n arity v with hzero | hone
      · simp [hzero]
      · have ho := allTestsAccepted n arity p H G W hp hH hG hW v ha hone
        simp [hone,ho]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionNativeCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionNativeCalibrationProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionNativeCalibrationProof.calibration
