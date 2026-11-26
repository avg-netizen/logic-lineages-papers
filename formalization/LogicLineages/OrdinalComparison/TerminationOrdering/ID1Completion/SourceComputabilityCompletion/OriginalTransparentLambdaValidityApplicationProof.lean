module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityParameterProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackInvariantProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityApplicationProof
open Source InternalOriginalUniformParameterLeaves
open OriginalHereditaryValidity OriginalTransparentLambdaValidityParameterProof

theorem actualOriginalTransparentApplicationEquations :
    OriginalTransparentLambdaValidityTargets.ActualOriginalTransparentApplicationEquations := by
  intro n arity value parameter ht
  dsimp only
  obtain ⟨Gamma,hg⟩ := parameterGamma parameter
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair parameter).1 with
  | none =>
    simp [sourceValue,targetValue,memberValue,decodedValue,hc]
  | some ctx =>
    simp only [targetAtParameter n arity _ parameter ctx Gamma hc hg,
      sourceAtParameter n arity _ parameter ctx Gamma hc hg,
      memberAtParameter n _ parameter ctx Gamma hc hg]
    have he := InternalApplicationValidityStackDecoderProof.actualOriginalApplicationDecoderEquations
      n arity ctx.1.1 ctx.1.2 Gamma (domainValue value) (resultTypeValue value)
        (functionPayloadValue value) (argumentPayloadValue value)
    rw [InternalApplicationValidityStackInvariantProof.applicationReconstruction value ht] at he
    exact he

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityApplicationProof
