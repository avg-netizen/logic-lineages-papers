module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLambdaNodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalHereditaryValidity OriginalTransparentLambdaValidity OriginalTransparentLambdaValidityInternal
open OriginalTransparentLambdaValidityInternalLambdaSupportProof OriginalTransparentLambdaValidityInternalLambdaNodeProof

theorem actualOriginalTransparentInternalSourceLambda :
    OriginalTransparentLambdaValidityInternalTargets.ActualOriginalTransparentInternalSourceLambda := by
  intro body rawData alpha out raw parameter
  let N := normalizedData rawData
  have ht : Nonempty (Derivation body [TagIs 1 raw] (TagIs 1 raw)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := lambdaOutputEquation (sourceRoot N) (targetRoot N) N.member out raw parameter
    (SourceLambdaRootFactors N raw parameter) ht (sourceNodeEquation N raw parameter ht)
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualOriginalTransparentInternalTargetLambda :
    OriginalTransparentLambdaValidityInternalTargets.ActualOriginalTransparentInternalTargetLambda := by
  intro body rawData alpha out raw parameter
  let N := normalizedData rawData
  have ht : Nonempty (Derivation body [TagIs 1 raw] (TagIs 1 raw)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := lambdaOutputEquation (targetRoot N) (InternalLessThan.constantOne 2)
    (InternalLessThan.constantOne 2) out raw parameter (LambdaShape raw) ht (targetNodeEquation N raw parameter ht)
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLambdaProof
