module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomRepresentativeEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuardEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesCodecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableRootProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafEvaluationProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowReduction
open NumberedLeastCodeRepresentative NumberedAuxiliaryCoding
open OriginalConstructorLeaf InternalOriginalUniformApplicationStepSelection
open InternalOriginalUniformParameterLeaves (parameterObject)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open InternalEqualityTestEvaluationProof (vectorOne)
open BottomRepresentativeEvaluationProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- This is the original raw selector, including all malformed codes. -/
theorem variableTestEvaluation (value : Nat) :
    evaluate variableTest (List.Vector.ofFn ![value]) =
      if (Nat.unpair (Nat.unpair value).2).1 = 0 then 1 else 0 := by
  rw [variableTest,sameEvaluation,constructorTagEvaluation]
  rfl

theorem variableAtEvaluation (v : List.Vector Nat 4) :
    evaluate variableAt v =
      if (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 0 then 1 else 0 := by
  change evaluate variableTest (List.Vector.ofFn fun _ : Fin 1 => v.get 0) = _
  simpa only [vectorOne,Matrix.cons_val_zero] using variableTestEvaluation (v.get 0)

theorem expectedBottomEvaluation (v : List.Vector Nat 4) :
    evaluate expectedBottom v =
      Nat.pair (Nat.unpair (v.get 0)).1 (Nat.pair 3 (Nat.unpair (v.get 0)).1) := by
  change evaluate BottomRepresentative.bottomCode
    (List.Vector.ofFn fun _ : Fin 1 => evaluate (leftOf (.projection 0)) v) = _
  rw [leftOfEvaluation]
  change evaluate BottomRepresentative.bottomCode
    (List.Vector.ofFn fun _ : Fin 1 => (Nat.unpair (v.get 0)).1) = _
  simpa only [vectorOne,Matrix.cons_val_zero] using bottomCodeEvaluation (Nat.unpair (v.get 0)).1

/-- No closure or precedence premise is used for the original raw bottom case. -/
theorem stepNonBottom (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (above : Fin n → Fin n → Prop) (tau : Ty)
    (q r : AuxTerm (Fin n) arity Gamma tau)
    (hstep : WindowStep (Fin n) arity symbols S above Gamma tau q r) :
    BottomRepresentative.bottomValue (packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma)) = 0 := by
  cases q <;>
    try exact False.elim (NumberedBottomAccessibilityProof.actualBottomStepTerminal
      (Fin n) arity symbols S above Gamma _ r hstep)
  all_goals simp [bottomValuePacked,NumberedBottomAccessibilitySupportProof.bottomView]

/-- Accepted original typed variable steps have the literal same-type bottom
code. The raw selector alone is not treated as a successful parse. -/
theorem stepVariableBottom (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (above : Fin n → Fin n → Prop) (tau : Ty)
    (q r : AuxTerm (Fin n) arity Gamma tau)
    (hstep : WindowStep (Fin n) arity symbols S above Gamma tau q r)
    (htag : (Nat.unpair (Nat.unpair
      (packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma))).2).1 = 0) :
    packedNumber (⟨tau,r⟩ : Packed (Fin n) arity Gamma) =
      Nat.pair (Nat.unpair (packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma))).1
        (Nat.pair 3 (Nat.unpair (packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma))).1) := by
  cases q
  case var vname =>
    have hr := (NumberedVariableRootProof.actualVariableStepBottom
      (Fin n) arity symbols S above Gamma tau vname r).mp hstep
    subst r
    simp [packedNumber,termCode,codeNumber]
  all_goals simp [packedNumber,termCode,codeNumber] at htag

/-- The original total leaf has only its original zero/one outputs, even for
malformed Context, type, term, or certificate coordinates. -/
theorem leafBoolean (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 4) :
    leafValue n arity v = 0 ∨ leafValue n arity v = 1 := by
  obtain ⟨Gamma,hGamma⟩ :=
    InternalOriginalUniformParameterLeavesCodecProof.actualOriginalUniformParameterCodec.2
      (v.get 0) (v.get 3)
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 3)).1 with
  | none => simp [leafValue,hc]
  | some ctx =>
    simp only [leafValue,hc,hGamma]
    cases NumberedNumericStep.numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
      (v.get 0) (v.get 1) (v.get 2) with
    | false => exact Or.inl rfl
    | true => exact Or.inr rfl

/-- Native certificate soundness pays both redundant guards on arbitrary
accepted raw inputs. It is never an internal derivation rule. -/
theorem leafGuards (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 4)
    (ha : leafValue n arity v = 1) :
    BottomRepresentative.bottomValue (v.get 0) = 0 ∧
      ((Nat.unpair (Nat.unpair (v.get 0)).2).1 = 0 →
        v.get 1 = Nat.pair (Nat.unpair (v.get 0)).1 (Nat.pair 3 (Nat.unpair (v.get 0)).1)) := by
  obtain ⟨Gamma,hGamma⟩ :=
    InternalOriginalUniformParameterLeavesCodecProof.actualOriginalUniformParameterCodec.2
      (v.get 0) (v.get 3)
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 3)).1 with
  | none => simp [leafValue,hc] at ha
  | some ctx =>
    have ht : NumberedNumericStep.numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
        (v.get 0) (v.get 1) (v.get 2) = true := by
      cases ht : NumberedNumericStep.numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
        (v.get 0) (v.get 1) (v.get 2) <;> simp_all [leafValue]
    obtain ⟨tau,q,r,_,hstep,hs,htarget⟩ :=
      (NumberedNumericStepProof.numericStepCertificates n arity ctx.1.1 ctx.1.2 Gamma ctx.2
        (v.get 0) (v.get 1)).mp ⟨v.get 2,ht⟩
    constructor
    · rw [← hs]
      exact stepNonBottom n arity ctx.1.1 ctx.1.2 Gamma
        (NumberedCopyCertificate.tableAbove ctx.2) tau q r hstep
    · intro htag
      rw [← hs] at htag
      simpa only [hs,htarget] using stepVariableBottom n arity ctx.1.1 ctx.1.2 Gamma
        (NumberedCopyCertificate.tableAbove ctx.2) tau q r hstep htag

theorem variableGuardAccept (v : List.Vector Nat 4)
    (h : (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 0 →
      v.get 1 = Nat.pair (Nat.unpair (v.get 0)).1 (Nat.pair 3 (Nat.unpair (v.get 0)).1)) :
    evaluate variableGuard v = 1 := by
  rw [variableGuard,evalBranch,evalNormalize,variableAtEvaluation,sameEvaluation,expectedBottomEvaluation]
  change (if (if (if (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 0 then 1 else 0) = 1
      then 1 else 0) = 0 then 1 else
    (if v.get 1 = Nat.pair (Nat.unpair (v.get 0)).1 (Nat.pair 3 (Nat.unpair (v.get 0)).1)
      then 1 else 0)) = 1
  by_cases ht : (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 0
  · simp only [ht,h ht,ite_true,ite_false,Nat.one_ne_zero,Nat.zero_ne_one]
  · simp only [ht,ite_true,ite_false,Nat.one_ne_zero,Nat.zero_ne_one]

theorem actualOriginalConstructorLeafRefinementEquality :
    OriginalConstructorLeafTargets.ActualOriginalConstructorLeafRefinementEquality := by
  intro n arity oldStep hc v
  rcases leafBoolean n arity v with hz | ho
  · simp [refined,conjunctionEvaluation,hc v,hz]
  · obtain ⟨hb,hv⟩ := leafGuards n arity v ho
    have hnb : evaluate (PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest) v = 1 := by
      rw [PositiveGuardEvaluationProof.nonBottomEvaluation,bottomTestEvaluation,hb]
      rfl
    have hvg := variableGuardAccept v hv
    simp [refined,conjunctionEvaluation,hc v,ho,hnb,hvg]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafEvaluationProof
