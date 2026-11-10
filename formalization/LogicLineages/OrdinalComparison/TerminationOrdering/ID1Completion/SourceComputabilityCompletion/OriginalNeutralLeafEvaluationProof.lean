module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralCertificateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafGuardEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSelectionCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePositiveCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafEvaluationProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedAuxiliaryCoding NumberedPrimaryShapes NumberedNumericStep
open InternalApplicationCertificateConstructors InternalApplicationStepPeel
open InternalApplicationCertificateConstructorsEvaluationProof InternalApplicationStepPeelEvaluationSupportProof
open InternalAcceptanceCalibrationProof InternalParameterizedApplicationStepChecker
open InternalOriginalUniformApplicationStepSelection
open InternalOriginalUniformContextMembershipEvaluationProof
open OriginalNeutralLeaf UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- The original function payload's constructor tag on every natural input,
including malformed application encodings. -/
def rawFunctionTag (value : Nat) : Nat :=
  let appBody := (Nat.unpair (Nat.unpair value).2).2
  (Nat.unpair (Nat.unpair (Nat.unpair appBody).2).1).1

theorem lambdaFunctionTestEvaluation (value : Nat) :
    evaluate lambdaFunctionTest (ofFn ![value]) =
      if rawFunctionTag value = 1 then 1 else 0 := by
  rw [lambdaFunctionTest,sameEvaluation,leftOfEvaluation,functionPayloadEvaluation,appBodyEvaluation]
  rfl

theorem neutralTestEvaluation (value : Nat) :
    evaluate neutralTest (ofFn ![value]) =
      if (Nat.unpair (Nat.unpair value).2).1 = 2 ∧ rawFunctionTag value ≠ 1 then 1 else 0 := by
  rw [neutralTest,conjunctionEvaluation,sameEvaluation,constructorTagEvaluation,twoEvaluation,
    evalBranch,lambdaFunctionTestEvaluation]
  change (if (if (Nat.unpair (Nat.unpair value).2).1 = 2 then 1 else 0) = 1 ∧
      (if (if rawFunctionTag value = 1 then 1 else 0) = 0 then 1 else 0) = 1
      then 1 else 0) = _
  by_cases ht : (Nat.unpair (Nat.unpair value).2).1 = 2 <;>
    by_cases hf : rawFunctionTag value = 1 <;> simp [ht,hf]

theorem neutralAtEvaluation (v : List.Vector Nat 4) :
    evaluate neutralAt v = evaluate neutralTest (ofFn ![v.get 0]) := by
  change evaluate neutralTest (ofFn fun _ : Fin 1 => v.get 0) = _
  apply congrArg (evaluate neutralTest)
  apply List.Vector.ext
  intro i
  obtain rfl : i = 0 := Fin.eq_zero i
  rfl

theorem windowAtEvaluation (window : Program 1) (v : List.Vector Nat 4) :
    evaluate (OriginalNeutralLeaf.windowAt window) v =
      evaluate window (ofFn ![(Nat.unpair (v.get 3)).1]) := by
  change evaluate window (ofFn fun _ : Fin 1 => evaluate (leftOf (.projection 3)) v) = _
  rw [leftOfEvaluation,InternalEqualityTestEvaluationProof.vectorOne]
  rfl

theorem guardAtEvaluation (endpoint : Program 6) (v : List.Vector Nat 4) :
    evaluate (guardAt endpoint) v =
      evaluate (guardP endpoint)
        (ofFn ![Nat.pair (v.get 0) (Nat.pair (v.get 1) (v.get 2)),v.get 3]) := by
  have hstate : evaluate edgeStateP v = Nat.pair (v.get 0) (Nat.pair (v.get 1) (v.get 2)) := by
    change evaluate edgeCode (ofFn ![v.get 0,v.get 1,v.get 2]) = _
    rw [edgeCodeEvaluation]
    rfl
  change evaluate (guardP endpoint) (ofFn ![evaluate edgeStateP v,v.get 3]) = _
  rw [hstate]

theorem triggerEvaluation (endpoint : Program 6) (window : Program 1) (v : List.Vector Nat 4) :
    evaluate (trigger endpoint window) v =
      if evaluate (OriginalNeutralLeaf.windowAt window) v = 1 ∧
          evaluate neutralAt v = 1 ∧ evaluate (guardAt endpoint) v = 0 then 1 else 0 := by
  rw [trigger,conjunctionEvaluation,conjunctionEvaluation,sameEvaluation]
  change (if evaluate (OriginalNeutralLeaf.windowAt window) v = 1 ∧
      (if evaluate neutralAt v = 1 ∧ (if evaluate (guardAt endpoint) v = 0 then 1 else 0) = 1
        then 1 else 0) = 1 then 1 else 0) = _
  by_cases hw : evaluate (OriginalNeutralLeaf.windowAt window) v = 1 <;>
    by_cases hn : evaluate neutralAt v = 1 <;>
    by_cases hg : evaluate (guardAt endpoint) v = 0 <;> simp [hw,hn,hg]

theorem lambdaTag (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (rho : Ty) (f : AuxTerm (Fin n) arity Gamma rho) :
    (Nat.unpair (codeNumber (termCode f))).1 = 1 ↔ isLambda f = true := by
  cases f <;> simp [termCode,codeNumber,isLambda]

/-- The raw neutral test is only interpreted after the accepted original
numeric certificate supplies an actual typed application. -/
theorem applicationNonLambda (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (sigma tau : Ty) (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma)
    (h : evaluate neutralTest
      (ofFn ![packedNumber (⟨tau,.app f a⟩ : Packed (Fin n) arity Gamma)]) = 1) :
    isLambda f = false := by
  rw [neutralTestEvaluation] at h
  have htag : (Nat.unpair (codeNumber (termCode f))).1 ≠ 1 := by
    simpa [rawFunctionTag,packedNumber,termCode,codeNumber] using h
  cases hi : isLambda f with
  | false => rfl
  | true => exact False.elim (htag ((lambdaTag n arity Gamma _ f).mpr hi))

/-- A zero original peel guard excludes the recovered function branch of
the SAME accepted original certificate. The remaining target is literal
same-type bottom; no semantic completeness chooses a replacement witness. -/
theorem numericNeutralBottom (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (endpoint : Program 6) (parameter source target certificate : Nat)
    (he : EndpointCalibratedAt n arity symbols S Gamma endpoint parameter)
    (hs : numericStepTest n arity symbols S Gamma table source target certificate = true)
    (hn : evaluate neutralTest (ofFn ![source]) = 1)
    (hg : evaluate (guardP endpoint)
      (ofFn ![Nat.pair source (Nat.pair target certificate),parameter]) = 0) :
    target = Nat.pair (Nat.unpair source).1 (Nat.pair 3 (Nat.unpair source).1) := by
  obtain ⟨tau,q,r,hq,_,hsource,_⟩ :=
    (NumberedNumericStepProof.numericStepCertificates n arity symbols S Gamma table source target).mp
      ⟨certificate,hs⟩
  rw [← hsource] at hn hs hg ⊢
  cases q with
  | app f a =>
    have hnon := applicationNonLambda n arity Gamma _ tau f a hn
    rcases OriginalNeutralCertificateProof.actualNumericNeutralCertificateInversion
      n arity symbols S Gamma table _ tau f a target certificate hnon hs with
      hb | ⟨g,child,ht,hc,_⟩
    · simpa [packedNumber,termCode,codeNumber] using hb
    · have hguard := OriginalNeutralLeafGuardEvaluationProof.liftedGuardAccept
        n arity symbols S Gamma endpoint parameter he _ tau f g a child hq
      rw [ht,hc] at hg
      exact False.elim (Nat.zero_ne_one (hg.symm.trans hguard))
  | var =>
    rw [neutralTestEvaluation] at hn
    simp [packedNumber,termCode,codeNumber] at hn
  | lam =>
    rw [neutralTestEvaluation] at hn
    simp [packedNumber,termCode,codeNumber] at hn
  | bottom =>
    rw [neutralTestEvaluation] at hn
    simp [packedNumber,termCode,codeNumber] at hn
  | ordinary =>
    rw [neutralTestEvaluation] at hn
    simp [packedNumber,termCode,codeNumber] at hn
  | numbered =>
    rw [neutralTestEvaluation] at hn
    simp [packedNumber,termCode,codeNumber] at hn

/-- The same selected data retains the existing all-input calibration.
Membership is normalized exactly once in the original outer pipeline. -/
theorem selectedDataCalibrated (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    InternalOriginalUniformDescentSelection.Calibrated n arity (OuterSelection.data p.base p.window) := by
  have hpre := OuterSelectionCalibrationProof.preCalibrated n arity p.base hp.1 p.window hp.2.1
  exact actualOriginalUniformNormalizedMembershipCalibration
    n arity (OuterSelectionCalibrationProof.preData p.base p.window) hpre

/-- An accepted window recovers a decoded context and its subtype closure
without restricting the all-input contract. The arbitrary raw parameter is
retained in every endpoint and certificate evaluation. -/
theorem activeLeafBottom (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p)
    (v : List.Vector Nat 4) (haccept : leafValue n arity v = 1)
    (htrigger : evaluate (trigger (endpoint p) p.window) v = 1) :
    v.get 1 = Nat.pair (Nat.unpair (v.get 0)).1 (Nat.pair 3 (Nat.unpair (v.get 0)).1) := by
  have hactive : evaluate (OriginalNeutralLeaf.windowAt p.window) v = 1 ∧
      evaluate neutralAt v = 1 ∧ evaluate (guardAt (endpoint p)) v = 0 := by
    rw [triggerEvaluation] at htrigger
    split at htrigger
    next h => exact h
    next => contradiction
  have hw : ∀ w : List.Vector Nat 1,
      evaluate p.window w = GuardCalibration.validWindowValue n w := hp.2.1
  have hwindow : GuardCalibration.validWindow n (Nat.unpair (v.get 3)).1 = 1 := by
    simpa only [windowAtEvaluation,hw,GuardCalibration.validWindowValue,
      List.Vector.get_ofFn,Matrix.cons_val_zero] using hactive.1
  obtain ⟨ctx,hctx,hS⟩ :=
    (GuardCalibrationProof.actualValidWindowCalibration n (Nat.unpair (v.get 3)).1).1.mp hwindow
  let data := OuterSelection.data p.base p.window
  have hd := selectedDataCalibrated n arity p hp
  obtain ⟨Gamma,hdecoded⟩ := DecodedSourceCalibrationProof.actualDecodedCompositeCalibration
    n arity data hd (v.get 3) ctx hctx hS
  have hend := RuntimePositiveCalibrationProof.endpointCalibration
    n arity data hd (v.get 3) ctx hctx Gamma hdecoded
  have hs : numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
      (v.get 0) (v.get 1) (v.get 2) = true := by
    simp only [leafValue,hctx,hdecoded.objectSlice] at haccept
    cases h : numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
        (v.get 0) (v.get 1) (v.get 2) <;> simp_all
  have hn := hactive.2.1
  rw [neutralAtEvaluation] at hn
  have hg := hactive.2.2
  rw [guardAtEvaluation] at hg
  exact numericNeutralBottom n arity ctx.1.1 ctx.1.2 Gamma ctx.2 (endpoint p)
    (v.get 3) (v.get 0) (v.get 1) (v.get 2) hend hs hn hg

theorem leafGuardAccept (endpoint : Program 6) (window : Program 1) (v : List.Vector Nat 4)
    (h : evaluate (trigger endpoint window) v = 1 →
      v.get 1 = Nat.pair (Nat.unpair (v.get 0)).1 (Nat.pair 3 (Nat.unpair (v.get 0)).1)) :
    evaluate (leafGuard endpoint window) v = 1 := by
  by_cases ht : evaluate (trigger endpoint window) v = 1
  · have hb := h ht
    rw [leafGuard,evalBranch,ht]
    simp only [Nat.one_ne_zero,ite_false,sameEvaluation,
      OriginalConstructorLeafEvaluationProof.expectedBottomEvaluation]
    change (if v.get 1 = Nat.pair (Nat.unpair (v.get 0)).1
      (Nat.pair 3 (Nat.unpair (v.get 0)).1) then 1 else 0) = 1
    exact if_pos hb
  · have hz : evaluate (trigger endpoint window) v = 0 := by
      rw [triggerEvaluation] at ht ⊢
      split <;> simp_all
    rw [leafGuard,evalBranch,hz]
    rfl

theorem actualOriginalNeutralLeafRefinementEquality :
    OriginalNeutralLeafTargets.ActualOriginalNeutralLeafRefinementEquality := by
  intro n arity p hp v
  have hleaf := hp.2.2.2.2.1
  change evaluate (refined (endpoint p) p.window p.oldStep) v = evaluate p.oldStep v
  rcases OriginalConstructorLeafEvaluationProof.leafBoolean n arity v with hz | ho
  · simp [refined,conjunctionEvaluation,hleaf v,hz]
  · have hg := leafGuardAccept (endpoint p) p.window v (activeLeafBottom n arity p hp v ho)
    simp [refined,conjunctionEvaluation,hleaf v,ho,hg]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafEvaluationProof
