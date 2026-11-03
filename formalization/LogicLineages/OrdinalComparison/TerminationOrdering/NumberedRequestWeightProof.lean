module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestWeightTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestWeightProof
open Source NumberedAuxiliaryCoding NumberedTypedRequests NumberedRequestWeight

theorem expansionDecrease : NumberedRequestWeightTargets.SuccessfulExpansionDecrease := by
  intro n arity request children h
  cases request with
  | term Gamma tau code =>
    cases code <;> cases tau <;>
      simp only [expand] at h
    all_goals (try split at h)
    all_goals simp only [Option.some.injEq, reduceCtorEq] at h
    all_goals subst children
    all_goals simp [workWeight, requestWeight, codeWeight] <;> omega
  | arguments Gamma types code =>
    cases code <;> cases types <;>
      simp only [expand] at h
    all_goals (try split at h)
    all_goals simp only [Option.some.injEq, reduceCtorEq] at h
    all_goals subst children
    all_goals simp [workWeight, requestWeight, codeWeight] <;> omega

theorem replacementDecrease : NumberedRequestWeightTargets.WorklistReplacementDecrease := by
  intro n arity request children rest h
  have hd := expansionDecrease n arity request children h
  simpa [workWeight, List.map_append, List.sum_append] using Nat.add_lt_add_right hd (workWeight rest)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestWeightProof
