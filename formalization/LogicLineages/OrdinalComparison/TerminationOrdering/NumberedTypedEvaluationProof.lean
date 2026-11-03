module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluationTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluationProof
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedTypedRequests
open NumberedRequestWeight NumberedTypedEvaluation

private theorem requestExpansion {n : Nat} (arity : Fin n → Nat) (request : Request n) :
    valid arity request = expandedValid arity request := by
  cases request with
  | term Gamma tau code =>
    exact NumberedTypedRequestsProof.termExpansion n arity Gamma tau code
  | arguments Gamma types code =>
    exact NumberedTypedRequestsProof.argumentsExpansion n arity Gamma types code

private theorem expansionPreserves {n : Nat} (arity : Fin n → Nat) (request : Request n)
    (children rest : List (Request n)) (h : expand arity request = some children) :
    (children ++ rest).all (valid arity) = (request :: rest).all (valid arity) := by
  simp only [List.all_append, List.all_cons]
  rw [requestExpansion arity request]
  simp only [expandedValid, h]

private theorem failedExpansion {n : Nat} (arity : Fin n → Nat) (request : Request n)
    (rest : List (Request n)) (h : expand arity request = none) :
    (request :: rest).all (valid arity) = false := by
  rw [List.all_cons, requestExpansion arity request]
  simp only [expandedValid, h, Bool.false_and]

private theorem requestWeightPositive {n : Nat} (request : Request n) :
    0 < requestWeight request := by
  cases request with
  | term Gamma tau code =>
    cases code <;> simp [requestWeight, codeWeight]
  | arguments Gamma types code =>
    cases code <;> simp [requestWeight, codeWeight]

theorem anyFuelSound : NumberedTypedEvaluationTargets.AnyFuelSound := by
  intro n arity fuel
  induction fuel with
  | zero =>
    intro requests h
    cases requests with
    | nil => rfl
    | cons request rest => simp [evaluate] at h
  | succ fuel ih =>
    intro requests h
    cases requests with
    | nil => rfl
    | cons request rest =>
      cases hexpand : expand arity request with
      | none => simp [evaluate, hexpand] at h
      | some children =>
        have hnext : evaluate arity fuel (children ++ rest) = true := by
          simpa only [evaluate, hexpand] using h
        exact (expansionPreserves arity request children rest hexpand).symm.trans
          (ih (children ++ rest) hnext)

theorem sufficientFuelExact : NumberedTypedEvaluationTargets.SufficientFuelExact := by
  intro n arity fuel
  induction fuel with
  | zero =>
    intro requests hbound
    cases requests with
    | nil => rfl
    | cons request rest =>
      have hpositive := requestWeightPositive request
      have hzero : requestWeight request + workWeight rest ≤ 0 := by
        simpa [workWeight] using hbound
      omega
  | succ fuel ih =>
    intro requests hbound
    cases requests with
    | nil => rfl
    | cons request rest =>
      cases hexpand : expand arity request with
      | none =>
        rw [evaluate, hexpand]
        exact (failedExpansion arity request rest hexpand).symm
      | some children =>
        have hdecrease := NumberedRequestWeightProof.replacementDecrease
          n arity request children rest hexpand
        have hnext : workWeight (children ++ rest) ≤ fuel := by omega
        calc
          evaluate arity (fuel + 1) (request :: rest) =
              evaluate arity fuel (children ++ rest) := by simp only [evaluate, hexpand]
          _ = (children ++ rest).all (valid arity) := ih (children ++ rest) hnext
          _ = (request :: rest).all (valid arity) :=
            expansionPreserves arity request children rest hexpand

theorem termEvaluation : NumberedTypedEvaluationTargets.ActualTermEvaluation := by
  intro n arity Gamma tau code
  have h := sufficientFuelExact n arity (codeWeight code) [.term Gamma tau code]
    (by simp [workWeight, requestWeight])
  simpa only [List.all_cons, List.all_nil, Bool.and_true, valid] using h

theorem argumentsEvaluation : NumberedTypedEvaluationTargets.ActualArgumentsEvaluation := by
  intro n arity Gamma types code
  have h := sufficientFuelExact n arity (codeWeight code) [.arguments Gamma types code]
    (by simp [workWeight, requestWeight])
  simpa only [List.all_cons, List.all_nil, Bool.and_true, valid] using h

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluationProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluationProof
