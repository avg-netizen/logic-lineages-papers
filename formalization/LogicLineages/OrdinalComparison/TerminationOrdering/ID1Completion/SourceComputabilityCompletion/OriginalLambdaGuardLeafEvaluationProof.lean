module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafEvaluationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafEvaluationProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open OriginalLambdaGuardLeaf OriginalLambdaGuardLeafRawProof OriginalLambdaGuardLeafEvaluationSupportProof
open InternalOriginalUniformApplicationStepSelection
open InternalOriginalUniformParameterLeaves (parameterObject)
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- All arbitrary raw inputs are retained. Accepted source decoding determines
the source constructor; only the literal lambda case invokes numeric inversion. -/
theorem leafChildAccept (n : Nat) (arity : Fin n → Nat) (oldStep : Program 4)
    (hcal : LeafCalibrated n arity oldStep) (v : List.Vector Nat 4)
    (ha : leafValue n arity v = 1) (hlambda : evaluate sourceLambda v = 1)
    (hnotbottom : evaluate sameBottom v ≠ 1) :
    evaluate (childGuard oldStep) v = 1 := by
  have htag : (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 1 := by
    rw [sourceLambdaEvaluation] at hlambda
    split at hlambda
    · assumption
    · contradiction
  obtain ⟨Gamma,hGamma⟩ :=
    InternalOriginalUniformParameterLeavesCodecProof.actualOriginalUniformParameterCodec.2
      (v.get 0) (v.get 3)
  have hGammaCode := originalGammaCode (v.get 0) (v.get 3) Gamma hGamma
  cases hcontext : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair (v.get 3)).1 with
  | none => simp [leafValue,hcontext] at ha
  | some ctx =>
    have hstep : NumberedNumericStep.numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
        (v.get 0) (v.get 1) (v.get 2) = true := by
      cases hstep : NumberedNumericStep.numericStepTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
        (v.get 0) (v.get 1) (v.get 2) <;> simp_all [leafValue]
    obtain ⟨tau,q,r,_,_,hs,_⟩ :=
      (NumberedNumericStepProof.numericStepCertificates n arity ctx.1.1 ctx.1.2 Gamma ctx.2
        (v.get 0) (v.get 1)).mp ⟨v.get 2,hstep⟩
    rw [← hs] at htag
    cases q
    case lam =>
      exact typedLambdaChildAccept n arity oldStep hcal v ctx Gamma _ _ _
        hcontext hGammaCode hs.symm hstep hnotbottom
    all_goals simp [packedNumber,termCode,codeNumber] at htag

theorem leafGuardAccept (n : Nat) (arity : Fin n → Nat) (oldStep : Program 4)
    (hcal : LeafCalibrated n arity oldStep) (v : List.Vector Nat 4)
    (ha : leafValue n arity v = 1) :
    evaluate (OriginalLambdaGuardLeaf.guard oldStep) v = 1 := by
  by_cases hlambda : evaluate sourceLambda v = 1
  · by_cases hb : evaluate sameBottom v = 1
    · simp [OriginalLambdaGuardLeaf.guard,evalBranch,evalNormalize,hlambda,hb,InternalLessThan.constantOne,InternalAcceptance.constantZero,evaluate]
    · have hchild := leafChildAccept n arity oldStep hcal v ha hlambda hb
      simp [OriginalLambdaGuardLeaf.guard,evalBranch,evalNormalize,hlambda,hb,hchild]
  · simp [OriginalLambdaGuardLeaf.guard,evalBranch,evalNormalize,hlambda,InternalLessThan.constantOne,InternalAcceptance.constantZero,evaluate]

theorem actualOriginalLambdaGuardLeafRefinementEquality :
    OriginalLambdaGuardLeafTargets.ActualOriginalLambdaGuardLeafRefinementEquality := by
  intro n arity oldStep hcal v
  rcases OriginalConstructorLeafEvaluationProof.leafBoolean n arity v with hz | ho
  · simp [refined,conjunctionEvaluation,hcal v,hz]
  · have hg := leafGuardAccept n arity oldStep hcal v ho
    simp [refined,conjunctionEvaluation,hcal v,ho,hg]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafEvaluationProof
