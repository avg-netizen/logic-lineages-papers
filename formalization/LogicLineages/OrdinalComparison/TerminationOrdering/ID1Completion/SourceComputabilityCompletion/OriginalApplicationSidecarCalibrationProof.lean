module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNativeFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityInputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarCalibrationProof
open Source
open InternalOriginalUniformDescentSelection (Data Calibrated)
open InternalOriginalUniformContextMembershipEvaluationProof
open InternalAcceptanceCalibrationProof
open InternalApplicationStepPeelEvaluationSupportProof
open OriginalApplicationSidecar OriginalApplicationSidecarNativeFoldProof
open BottomRepresentativeEvaluationProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- Compose the already checked ALL-input neutral/shape/variable guards
with the existing spine/bottom and once-only membership normalization. -/
theorem originalDataCalibrated (n : Nat) (arity : Fin n → Nat) (data : Data)
    (window : Program 1) (hc : Calibrated n arity data) (hw : Path.windowCalibrated n window) :
    Calibrated n arity (originalData data window) := by
  have hn := (OriginalFunctionNeutralityEvaluationProof.actualOriginalFunctionNeutralityRefinementEquality
    n arity data window hc hw).2
  have hs := (OriginalConstructorShapeEvaluationProof.actualOriginalConstructorShapeRefinementEquality
    n arity (OriginalFunctionNeutrality.baseData data window) window hn hw).2
  have hv := (OriginalVariableRepresentativeEvaluationProof.actualOriginalVariableRepresentativeRefinementEquality
    n arity (OriginalConstructorShape.baseData (OriginalFunctionNeutrality.baseData data window) window)
    window hs hw).2
  let base := OriginalVariableRepresentative.baseData
    (OriginalConstructorShape.baseData (OriginalFunctionNeutrality.baseData data window) window) window
  have hp := OuterSelectionCalibrationProof.preCalibrated n arity base hv window hw
  exact actualOriginalUniformNormalizedMembershipCalibration n arity
    (OuterSelectionCalibrationProof.preData base window) hp

/-- Inactive outputs are literally oldR. An active original window supplies
one decoded context and one Gamma/objectSlice, used both for C and oldR at
EVERY raw input, without changing the supplied runtime parameter. -/
theorem representativeUnchanged (n : Nat) (arity : Fin n → Nat) (data : Data)
    (window : Program 1) (hc : Calibrated n arity data) (hw : Path.windowCalibrated n window)
    (v : List.Vector Nat 2) :
    evaluate (OriginalApplicationSidecar.representative data window) v =
      evaluate data.oldRepresentative v := by
  change (∀ w : List.Vector Nat 1, evaluate window w = GuardCalibration.validWindowValue n w) at hw
  have hv : v = ofFn ![v.get 0,v.get 1] := List.Vector.ext fun i => by
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i <;> rfl
  rw [hv,OriginalApplicationSidecar.representative,evalBranch]
  by_cases ha : evaluate (OriginalFunctionNeutrality.active data window) (ofFn ![v.get 0,v.get 1]) = 0
  · simp only [ha,ite_true]
  · simp only [ha,ite_false]
    have hactive : evaluate (BottomRepresentative.windowAt window) (ofFn ![v.get 0,v.get 1]) = 1 ∧
        evaluate (InternalOriginalUniformDescentSelection.validity
          (InternalOriginalUniformContextMembership.normalizeData (BottomParameter.baseData data)))
          (ofFn ![v.get 0,v.get 1]) = 1 := by
      by_contra h
      apply ha
      rw [OriginalFunctionNeutrality.active,SpineRepresentative.active,BottomRepresentative.active,
        conjunctionEvaluation]
      exact if_neg h
    have hwindow : GuardCalibration.validWindow n (Nat.unpair (v.get 1)).1 = 1 := by
      simpa only [windowAtEvaluation,hw,GuardCalibration.validWindowValue,
        List.Vector.get_ofFn,Matrix.cons_val_zero] using hactive.1
    obtain ⟨ctx,hctx,hclosed⟩ :=
      (GuardCalibrationProof.actualValidWindowCalibration n (Nat.unpair (v.get 1)).1).1.mp hwindow
    have hs := originalDataCalibrated n arity data window hc hw
    obtain ⟨Gamma,decoded⟩ := DecodedSourceCalibrationProof.actualDecodedCompositeCalibration
      n arity (originalData data window) hs (v.get 1) ctx hctx hclosed
    have hr := (decodedLeafSlice n arity data hc (v.get 1) ctx hctx Gamma
      decoded.objectSlice (v.get 0)).2.2.1
    exact (foldAtDecoded n arity (originalData data window) (v.get 1) ctx Gamma
      hclosed decoded (v.get 0)).trans hr.symm

theorem actualOriginalApplicationSidecarRefinementEquality :
    OriginalApplicationSidecarTargets.ActualOriginalApplicationSidecarRefinementEquality := by
  intro n arity data window hc hw
  refine ⟨representativeUnchanged n arity data window hc hw,?_⟩
  refine ⟨hc.1,hc.2.1,?_,hc.2.2.2⟩
  intro v
  exact (representativeUnchanged n arity data window hc hw v).trans (hc.2.2.1 v)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarCalibrationProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarCalibrationProof.actualOriginalApplicationSidecarRefinementEquality
