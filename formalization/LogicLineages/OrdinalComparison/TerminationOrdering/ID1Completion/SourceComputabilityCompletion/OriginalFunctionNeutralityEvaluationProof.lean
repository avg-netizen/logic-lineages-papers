module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomParameterEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryShapesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityEvaluationProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowEquivalence
open NumberedLeastCodeRepresentative NumberedNumericCarrier NumberedNumericDecoding NumberedAuxiliaryCoding
open InternalOriginalUniformDescentSelection InternalOriginalUniformContextMembershipEvaluationProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open InternalOriginalStepGuard (sourceValidityValue)
open InternalQuotientEdgeChecker (targetRepresentativeValue)
open BottomRepresentativeEvaluationProof OriginalFunctionNeutrality
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

theorem applicationMark (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (sigma tau : Ty) (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma) :
    evaluate mark (ofFn ![packedNumber (⟨tau,.app f a⟩ : Packed (Fin n) arity Gamma)]) =
      if NumberedPrimaryShapes.isLambda f = true then 0 else 1 := by
  rw [mark,OriginalNeutralLeafEvaluationProof.neutralTestEvaluation]
  simp only [OriginalNeutralLeafEvaluationProof.rawFunctionTag,packedNumber,termCode,codeNumber,
    Nat.unpair_pair]
  by_cases h : NumberedPrimaryShapes.isLambda f = true
  · have ht := (OriginalNeutralLeafEvaluationProof.lambdaTag n arity Gamma _ f).mpr h
    simp [ht,h]
  · have ht : (Nat.unpair (codeNumber (termCode f))).1 ≠ 1 :=
      fun ht => h ((OriginalNeutralLeafEvaluationProof.lambdaTag n arity Gamma _ f).mp ht)
    simp [ht,h]

/-- A semantic observer of the already defined original application view.
This helper keeps the large Program AST outside the primary induction. -/
def viewMark {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} :
    Option (Packed (Fin n) arity Gamma × Packed (Fin n) arity Gamma) → Nat
  | none => 0
  | some (f,_) => if NumberedPrimaryShapes.isLambda f.2 = true then 0 else 1

theorem markAtView (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (q : Packed (Fin n) arity Gamma) :
    evaluate mark (ofFn ![packedNumber q]) =
      viewMark (NumberedPrimaryShapesProof.appView q) := by
  obtain ⟨tau,q⟩ := q
  cases q with
  | app f a => exact applicationMark n arity Gamma _ _ f a
  | var =>
    rw [mark,OriginalNeutralLeafEvaluationProof.neutralTestEvaluation]
    simp [viewMark,NumberedPrimaryShapesProof.appView,packedNumber,termCode,codeNumber]
  | lam =>
    rw [mark,OriginalNeutralLeafEvaluationProof.neutralTestEvaluation]
    simp [viewMark,NumberedPrimaryShapesProof.appView,packedNumber,termCode,codeNumber]
  | bottom =>
    rw [mark,OriginalNeutralLeafEvaluationProof.neutralTestEvaluation]
    simp [viewMark,NumberedPrimaryShapesProof.appView,packedNumber,termCode,codeNumber]
  | ordinary =>
    rw [mark,OriginalNeutralLeafEvaluationProof.neutralTestEvaluation]
    simp [viewMark,NumberedPrimaryShapesProof.appView,packedNumber,termCode,codeNumber]
  | numbered =>
    rw [mark,OriginalNeutralLeafEvaluationProof.neutralTestEvaluation]
    simp [viewMark,NumberedPrimaryShapesProof.appView,packedNumber,termCode,codeNumber]

theorem relatedViewMark {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)}
    {S Gamma : List Ty}
    {v w : Option (Packed (Fin n) arity Gamma × Packed (Fin n) arity Gamma)}
    (h : NumberedPrimaryShapesProof.ViewRelated symbols S Gamma v w) :
    viewMark v = viewMark w := by
  cases h with
  | none => rfl
  | some f a g b hf ha =>
    simp only [viewMark,
      NumberedPrimaryShapesProof.actualPrimaryLambdaShape (Fin n) arity symbols S Gamma f g hf]

/-- The established primary application-view theorem supplies the original
function equivalence; its lambda-shape theorem preserves the concrete mark.
No second mutual induction through the evaluator is required. -/
theorem primaryMark {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)}
    {S Gamma : List Ty} {q r : Packed (Fin n) arity Gamma}
    (h : WindowPrimary (Fin n) arity symbols S Gamma q r) :
    evaluate mark (ofFn ![packedNumber q]) = evaluate mark (ofFn ![packedNumber r]) := by
  rw [markAtView,markAtView]
  exact relatedViewMark (NumberedPrimaryShapesProof.primaryAppView h)

theorem representativeMark (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (hS : SubtypeClosed (fun tau => tau ∈ S))
    (q : Packed (Fin n) arity Gamma) (hq : InUniverse symbols S q.2) :
    evaluate mark (ofFn ![representativeCode symbols S q]) =
      evaluate mark (ofFn ![packedNumber q]) := by
  obtain ⟨r,hr,he⟩ := NumberedLeastCodeRepresentativeProof.representativeAttained
    n arity symbols S hS Gamma q hq
  rw [he]
  exact (primaryMark hr).symm

theorem validRepresentativeMark (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (hS : SubtypeClosed (fun tau => tau ∈ S)) (value : Nat)
    (hv : sourceValidityValue n arity symbols S Gamma value = 1) :
    evaluate mark (ofFn ![targetRepresentativeValue n arity symbols S Gamma value]) =
      evaluate mark (ofFn ![value]) := by
  cases hd : decodeUniverse n arity symbols S Gamma value with
  | none => simp [sourceValidityValue,rawCarrierTest,hd] at hv
  | some q =>
    obtain ⟨hn,hq⟩ := (NumberedNumericCarrierProof.numericUniverseDecode
      n arity symbols S Gamma value q).mp hd
    have hp := (Option.filter_eq_some_iff.mp hd).1
    rw [targetRepresentativeValue,hp,← hn]
    exact representativeMark n arity symbols S Gamma hS q hq

theorem sameMarkEvaluation (R : Program 2) (value parameter : Nat) :
    evaluate (sameMark R) (ofFn ![value,parameter]) =
      if evaluate mark (ofFn ![evaluate R (ofFn ![value,parameter])]) =
          evaluate mark (ofFn ![value]) then 1 else 0 := by
  rw [sameMark,sameEvaluation]
  change (if evaluate mark (ofFn fun _ : Fin 1 => evaluate R (ofFn ![value,parameter])) =
    evaluate mark (ofFn fun _ : Fin 1 => value) then 1 else 0) = _
  simp only [InternalEqualityTestEvaluationProof.vectorOne,Matrix.cons_val_zero]

/-- Inactive original outputs are literal. In the active branch the actual
decoded window pays closure and original source validity before the native
primary invariant establishes redundancy of the same-mark test. -/
theorem representativeUnchanged (n : Nat) (arity : Fin n → Nat) (data : Data) (window : Program 1)
    (hc : Calibrated n arity data)
    (hw : ∀ v, evaluate window v = GuardCalibration.validWindowValue n v)
    (v : List.Vector Nat 2) :
    evaluate (representative data window) v = evaluate data.oldRepresentative v := by
  have hv : v = ofFn ![v.get 0,v.get 1] := List.Vector.ext fun i => by
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i <;> rfl
  rw [hv,OriginalFunctionNeutrality.representative,evalBranch]
  by_cases ha : evaluate (active data window) (ofFn ![v.get 0,v.get 1]) = 0
  · simp only [ha,ite_true]
  · simp only [ha,ite_false]
    let parameters := BottomParameter.baseData data
    have hactive : evaluate (BottomRepresentative.windowAt window) (ofFn ![v.get 0,v.get 1]) = 1 ∧
        evaluate (validity (InternalOriginalUniformContextMembership.normalizeData parameters))
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
    obtain ⟨Gamma,ho⟩ := parameterGamma (v.get 1)
    have hp := BottomParameterEvaluationProof.actualOriginalBottomParameterCalibration n arity data hc
    have hcN := actualOriginalUniformNormalizedMembershipCalibration n arity parameters hp
    have hsource := decodedValiditySlice n arity
      (InternalOriginalUniformContextMembership.normalizeData parameters) hcN
      (v.get 1) ctx hctx Gamma ho (v.get 0)
    have hr := (decodedLeafSlice n arity data hc (v.get 1) ctx hctx Gamma ho (v.get 0)).2.2.1
    have he : evaluate mark (ofFn ![evaluate data.oldRepresentative (ofFn ![v.get 0,v.get 1])]) =
        evaluate mark (ofFn ![v.get 0]) := by
      rw [hr]
      exact validRepresentativeMark n arity ctx.1.1 ctx.1.2 Gamma hclosed (v.get 0)
        (hsource.symm.trans hactive.2)
    rw [evalBranch,sameMarkEvaluation]
    simp only [he,ite_true,Nat.one_ne_zero,ite_false]

theorem actualOriginalFunctionNeutralityRefinementEquality :
    OriginalFunctionNeutralityTargets.ActualOriginalFunctionNeutralityRefinementEquality := by
  intro n arity data window hc hw
  refine ⟨representativeUnchanged n arity data window hc hw,?_⟩
  refine ⟨hc.1,hc.2.1,?_,hc.2.2.2⟩
  intro v
  exact (representativeUnchanged n arity data window hc hw v).trans (hc.2.2.1 v)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityEvaluationProof
