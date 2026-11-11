module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityParameterProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityLambdaFixedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityLambdaProof
open Source InternalOriginalUniformParameterLeaves
open OriginalHereditaryValidity OriginalTransparentLambdaValidityParameterProof
open OriginalContextExtensionCalibrationProof

theorem actualOriginalTransparentLambdaEquations :
    OriginalTransparentLambdaValidityTargets.ActualOriginalTransparentLambdaEquations := by
  intro n arity value parameter ht
  dsimp only
  obtain ⟨Gamma,hg⟩ := parameterGamma parameter
  obtain ⟨sigma,_,hd⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal (domainValue value)
  have hg' : Encodable.encode (sigma :: Gamma) =
      (Nat.unpair (childParameterValue value parameter)).2 := by
    simp only [childParameterValue,Nat.unpair_pair,contextEncoding,hd,hg]
    omega
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair parameter).1 with
  | none =>
    simp only [sourceValue,targetValue,memberValue,decodedValue,List.Vector.get_ofFn,
      Matrix.cons_val_zero,Matrix.cons_val_one,childParameterValue,Nat.unpair_pair,hc] <;> simp
  | some ctx =>
    have hc' : Encodable.decode (Nat.unpair (childParameterValue value parameter)).1 = some ctx := by
      simpa only [childParameterValue,Nat.unpair_pair] using hc
    simp only [targetAtParameter n arity _ parameter ctx Gamma hc hg,
      sourceAtParameter n arity _ parameter ctx Gamma hc hg,
      memberAtParameter n _ parameter ctx Gamma hc hg,
      targetAtParameter n arity _ (childParameterValue value parameter) ctx (sigma :: Gamma) hc' hg',
      sourceAtParameter n arity _ (childParameterValue value parameter) ctx (sigma :: Gamma) hc' hg']
    exact OriginalTransparentLambdaValidityLambdaFixedProof.fixedLambdaEquations
      n arity ctx.1.1 ctx.1.2 Gamma sigma value ht hd

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityLambdaProof
