module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeSourceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeRefinementProof
open Source
open InternalOriginalUniformDescentSelection (Data Calibrated)
open UniformCertificateCompletion OriginalLambdaTraversalSelection
open OriginalLambdaTraversalNativeCalibrationSupportProof OriginalLambdaTraversalNativeSourceProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open BottomRepresentativeEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- Every inactive output is literally oldR, including malformed inputs,
source-invalid decoded terms and nonclosed windows. Only the active branch
uses typed decoding; the theorem quantifies EVERY original two-input vector. -/
theorem representativeUnchanged (n : Nat) (arity : Fin n → Nat) (rawData : Data)
    (window : Program 1) (hc : Calibrated n arity rawData)
    (hw : Path.windowCalibrated n window) (v : List.Vector Nat 2) :
    evaluate (representative rawData window) v = evaluate rawData.oldRepresentative v := by
  change (∀ w : List.Vector Nat 1, evaluate window w = GuardCalibration.validWindowValue n w) at hw
  have hv : v = ofFn ![v.get 0,v.get 1] := List.Vector.ext fun i => by
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i <;> rfl
  rw [hv, representative, evalBranch]
  by_cases ha : evaluate (OriginalFunctionNeutrality.active (transparentData rawData) window)
      (ofFn ![v.get 0,v.get 1]) = 0
  · simp only [ha,ite_true]
  · simp only [ha,ite_false]
    have hactive : evaluate (BottomRepresentative.windowAt window) (ofFn ![v.get 0,v.get 1]) = 1 ∧
        evaluate (InternalOriginalUniformDescentSelection.validity (leafData rawData window))
          (ofFn ![v.get 0,v.get 1]) = 1 := by
      by_contra h
      apply ha
      rw [activeLeaf,conjunctionEvaluation]
      exact if_neg h
    have hwindow : GuardCalibration.validWindow n (Nat.unpair (v.get 1)).1 = 1 := by
      simpa only [windowAtEvaluation,hw,GuardCalibration.validWindowValue,
        List.Vector.get_ofFn,Matrix.cons_val_zero] using hactive.1
    obtain ⟨ctx,hctx,hclosed⟩ :=
      (GuardCalibrationProof.actualValidWindowCalibration n (Nat.unpair (v.get 1)).1).1.mp hwindow
    obtain ⟨Gamma,hg⟩ := OriginalTransparentLambdaValidityParameterProof.parameterGamma (v.get 1)
    have decoded := decodedAtGamma n arity (leafData rawData window)
      (leafDataCalibrated n arity rawData window hc hw) (v.get 1) ctx Gamma hctx hg hclosed
    have hs := hactive.2
    rw [decoded.sourceValidity] at hs
    have ho := fun value =>
      OriginalTransparentLambdaValidityParameterProof.objectAtGamma value (v.get 1) Gamma hg
    have hr := (decodedLeafSlice n arity rawData hc (v.get 1) ctx hctx Gamma ho (v.get 0)).2.2.1
    exact (canonicalAtSource n arity rawData window hc hw (v.get 0) (v.get 1)
      ctx Gamma hctx hg hclosed hs).trans hr.symm

theorem actualOriginalLambdaTraversalRefinementEquality :
    OriginalLambdaTraversalSelectionTargets.ActualOriginalLambdaTraversalRefinementEquality := by
  intro n arity rawData window hc hw
  have ht := transparentCalibrated n arity rawData hc
  refine ⟨representativeUnchanged n arity rawData window hc hw, ?_⟩
  refine ⟨ht.1,ht.2.1,?_,ht.2.2.2⟩
  intro v
  exact (representativeUnchanged n arity rawData window hc hw v).trans (hc.2.2.1 v)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeRefinementProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeRefinementProof
