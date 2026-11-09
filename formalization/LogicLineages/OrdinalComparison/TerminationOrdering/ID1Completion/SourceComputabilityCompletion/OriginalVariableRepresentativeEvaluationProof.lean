module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomParameterEvaluationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeEvaluationProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedNumericCarrier NumberedNumericDecoding
open NumberedVariableRootProof NumberedAuxiliaryCoding
open InternalOriginalUniformDescentSelection
open InternalOriginalUniformContextMembershipEvaluationProof
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof InternalApplicationStepPeelEvaluationSupportProof
open InternalAcceptanceCalibrationProof
open InternalOriginalStepGuard (sourceValidityValue)
open InternalQuotientEdgeChecker (targetRepresentativeValue)
open BottomRepresentativeEvaluationProof
open OriginalVariableRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- A full-value mark on EVERY raw input; exact-one normalization is retained. -/
theorem variableMarkEvaluation (value : Nat) :
    evaluate variableMark (ofFn ![value]) =
      if (Nat.unpair (Nat.unpair value).2).1 = 0 then Nat.pair 1 value else 0 := by
  rw [variableMark,evalBranch,evalNormalize,
    OriginalConstructorLeafEvaluationProof.variableTestEvaluation,pairOfEvaluation]
  change (if (if (if (Nat.unpair (Nat.unpair value).2).1 = 0 then 1 else 0) = 1
    then 1 else 0) = 0 then 0 else Nat.pair 1 value) = _
  by_cases h : (Nat.unpair (Nat.unpair value).2).1 = 0 <;>
    simp only [h,ite_true,ite_false,Nat.zero_ne_one,Nat.one_ne_zero]

theorem packedVariableMark {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (q : Packed (Fin n) arity Gamma) :
    evaluate variableMark (ofFn ![packedNumber q]) =
      match variableView q with
      | none => 0
      | some r => Nat.pair 1 (packedNumber r) := by
  rw [variableMarkEvaluation]
  obtain ⟨tau,q⟩ := q
  cases q <;> simp [packedNumber,termCode,codeNumber,variableView]

/-- Primary equivalence preserves the actual packed variable, in both
orientations; nonvariables receive zero. No native fact is reflected into Delta. -/
theorem representativeVariableMark (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (hS : SubtypeClosed (fun tau => tau ∈ S))
    (q : Packed (Fin n) arity Gamma) (hq : InUniverse symbols S q.2) :
    evaluate variableMark (ofFn ![representativeCode symbols S q]) =
      evaluate variableMark (ofFn ![packedNumber q]) := by
  obtain ⟨r,hr,he⟩ := NumberedLeastCodeRepresentativeProof.representativeAttained
    n arity symbols S hS Gamma q hq
  rw [he,packedVariableMark,packedVariableMark,primaryVariableView hr]

theorem validRepresentativeVariableMark (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (hS : SubtypeClosed (fun tau => tau ∈ S)) (value : Nat)
    (hv : sourceValidityValue n arity symbols S Gamma value = 1) :
    evaluate variableMark (ofFn ![targetRepresentativeValue n arity symbols S Gamma value]) =
      evaluate variableMark (ofFn ![value]) := by
  cases hd : decodeUniverse n arity symbols S Gamma value with
  | none => simp [sourceValidityValue,rawCarrierTest,hd] at hv
  | some q =>
    obtain ⟨hn,hq⟩ := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma value q).mp hd
    have hp := (Option.filter_eq_some_iff.mp hd).1
    rw [targetRepresentativeValue,hp,← hn]
    exact representativeVariableMark n arity symbols S Gamma hS q hq

theorem sameMarkEvaluation (R : Program 2) (value parameter : Nat) :
    evaluate (sameMark R) (ofFn ![value,parameter]) =
      if evaluate variableMark (ofFn ![evaluate R (ofFn ![value,parameter])]) =
          evaluate variableMark (ofFn ![value]) then 1 else 0 := by
  rw [sameMark,sameEvaluation]
  change (if evaluate variableMark
      (ofFn fun _ : Fin 1 => evaluate R (ofFn ![value,parameter])) =
    evaluate variableMark (ofFn fun _ : Fin 1 => value) then 1 else 0) = _
  simp only [InternalEqualityTestEvaluationProof.vectorOne,Matrix.cons_val_zero]

theorem representativeUnchanged (n : Nat) (arity : Fin n → Nat) (data : Data) (window : Program 1)
    (hc : Calibrated n arity data)
    (hw : ∀ v, evaluate window v = GuardCalibration.validWindowValue n v) (v : List.Vector Nat 2) :
    evaluate (representative data window) v = evaluate data.oldRepresentative v := by
  have hv : v = ofFn ![v.get 0,v.get 1] := List.Vector.ext fun i => by
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i <;> rfl
  rw [hv,OriginalVariableRepresentative.representative,evalBranch]
  by_cases ha : evaluate (active data window) (ofFn ![v.get 0,v.get 1]) = 0
  · simp only [ha,ite_true]
  · simp only [ha,ite_false]
    let parameters := BottomParameter.baseData data
    have hactive : evaluate (BottomRepresentative.windowAt window) (ofFn ![v.get 0,v.get 1]) = 1 ∧
        evaluate (validity (InternalOriginalUniformContextMembership.normalizeData parameters))
          (ofFn ![v.get 0,v.get 1]) = 1 := by
      by_contra h
      apply ha
      rw [OriginalVariableRepresentative.active,SpineRepresentative.active,BottomRepresentative.active,conjunctionEvaluation]
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
    have he : evaluate variableMark (ofFn ![evaluate data.oldRepresentative (ofFn ![v.get 0,v.get 1])]) =
        evaluate variableMark (ofFn ![v.get 0]) := by
      rw [hr]
      exact validRepresentativeVariableMark n arity ctx.1.1 ctx.1.2 Gamma hclosed (v.get 0)
        (hsource.symm.trans hactive.2)
    rw [evalBranch,sameMarkEvaluation]
    simp only [he,ite_true,Nat.one_ne_zero,ite_false]

theorem actualOriginalVariableRepresentativeRefinementEquality :
    OriginalVariableRepresentativeTargets.ActualOriginalVariableRepresentativeRefinementEquality := by
  intro n arity data window hc hw
  refine ⟨representativeUnchanged n arity data window hc hw,?_⟩
  refine ⟨hc.1,hc.2.1,?_,hc.2.2.2⟩
  intro v
  exact (representativeUnchanged n arity data window hc hw v).trans (hc.2.2.1 v)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeEvaluationProof
