module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineRepresentativeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSpineMeasureEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomParameterEvaluationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineRepresentativeEvaluationProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedNumericCarrier NumberedNumericDecoding
open InternalOriginalUniformDescentSelection
open InternalOriginalUniformContextMembershipEvaluationProof
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof InternalApplicationStepPeelEvaluationSupportProof
open InternalAcceptanceCalibrationProof
open InternalOriginalStepGuard (sourceValidityValue)
open InternalQuotientEdgeChecker (targetRepresentativeValue)
open SourceComputabilityCompletion.BottomRepresentativeEvaluationProof
open SourceComputabilityCompletion.BottomSpineMeasureEvaluationProof
open SourceComputabilityCompletion.SpineRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

theorem validRepresentativeMeasure (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (hS : SubtypeClosed (fun tau => tau ∈ S)) (value : Nat)
    (hv : sourceValidityValue n arity symbols S Gamma value = 1) :
    evaluate BottomSpineMeasure.measure (ofFn ![targetRepresentativeValue n arity symbols S Gamma value]) =
      evaluate BottomSpineMeasure.measure (ofFn ![value]) := by
  cases hd : decodeUniverse n arity symbols S Gamma value with
  | none => simp [sourceValidityValue,rawCarrierTest,hd] at hv
  | some q =>
    obtain ⟨hn,hq⟩ := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma value q).mp hd
    have hp := (Option.filter_eq_some_iff.mp hd).1
    rw [targetRepresentativeValue,hp,← hn]
    exact representativeMeasure n arity symbols S Gamma hS q hq

theorem sameMeasureEvaluation (R : Program 2) (value parameter : Nat) :
    evaluate (sameMeasure R) (ofFn ![value,parameter]) =
      if evaluate BottomSpineMeasure.measure (ofFn ![evaluate R (ofFn ![value,parameter])]) =
          evaluate BottomSpineMeasure.measure (ofFn ![value]) then 1 else 0 := by
  rw [sameMeasure,sameEvaluation]
  change (if evaluate BottomSpineMeasure.measure
      (ofFn fun _ : Fin 1 => evaluate R (ofFn ![value,parameter])) =
    evaluate BottomSpineMeasure.measure (ofFn fun _ : Fin 1 => value) then 1 else 0) = _
  simp only [InternalEqualityTestEvaluationProof.vectorOne,Matrix.cons_val_zero]

theorem representativeUnchanged (n : Nat) (arity : Fin n → Nat) (data : Data) (window : Program 1)
    (hc : Calibrated n arity data)
    (hw : ∀ v, evaluate window v = GuardCalibration.validWindowValue n v) (v : List.Vector Nat 2) :
    evaluate (representative data window) v = evaluate data.oldRepresentative v := by
  have hv : v = ofFn ![v.get 0,v.get 1] := List.Vector.ext fun i => by
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i <;> rfl
  rw [hv,SpineRepresentative.representative,evalBranch]
  by_cases ha : evaluate (active data window) (ofFn ![v.get 0,v.get 1]) = 0
  · simp only [ha,ite_true]
  · simp only [ha,ite_false]
    let parameters := BottomParameter.baseData data
    have hactive : evaluate (BottomRepresentative.windowAt window) (ofFn ![v.get 0,v.get 1]) = 1 ∧
        evaluate (validity (InternalOriginalUniformContextMembership.normalizeData parameters))
          (ofFn ![v.get 0,v.get 1]) = 1 := by
      by_contra h
      apply ha
      rw [active,BottomRepresentative.active,conjunctionEvaluation]
      exact if_neg h
    have hwindow : GuardCalibration.validWindow n (Nat.unpair (v.get 1)).1 = 1 := by
      simpa only [windowAtEvaluation,hw,GuardCalibration.validWindowValue,
        List.Vector.get_ofFn,Matrix.cons_val_zero] using hactive.1
    obtain ⟨ctx,hctx,hclosed⟩ :=
      (GuardCalibrationProof.actualValidWindowCalibration n (Nat.unpair (v.get 1)).1).1.mp hwindow
    obtain ⟨Gamma,ho⟩ := parameterGamma (v.get 1)
    have hp := BottomParameterEvaluationProof.actualOriginalBottomParameterCalibration n arity data hc
    have hcN := actualOriginalUniformNormalizedMembershipCalibration n arity parameters hp
    have hsource := decodedValiditySlice n arity
      (InternalOriginalUniformContextMembership.normalizeData parameters) hcN (v.get 1) ctx hctx Gamma ho (v.get 0)
    have hr := (decodedLeafSlice n arity data hc (v.get 1) ctx hctx Gamma ho (v.get 0)).2.2.1
    have he : evaluate BottomSpineMeasure.measure (ofFn ![evaluate data.oldRepresentative (ofFn ![v.get 0,v.get 1])]) =
        evaluate BottomSpineMeasure.measure (ofFn ![v.get 0]) := by
      rw [hr]
      exact validRepresentativeMeasure n arity ctx.1.1 ctx.1.2 Gamma hclosed (v.get 0)
        (hsource.symm.trans hactive.2)
    rw [evalBranch,sameMeasureEvaluation]
    simp only [he,ite_true,Nat.one_ne_zero,ite_false]

theorem actualOriginalSpineRepresentativeCalibration :
    SpineRepresentativeTargets.ActualOriginalSpineRepresentativeCalibration := by
  intro n arity data window hc hw
  refine ⟨hc.1,hc.2.1,?_,hc.2.2.2⟩
  intro v
  exact (representativeUnchanged n arity data window hc hw v).trans (hc.2.2.1 v)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineRepresentativeEvaluationProof
