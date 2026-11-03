module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluationTargets
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedTypedRequests
open NumberedRequestWeight NumberedTypedEvaluation

def AnyFuelSound : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (fuel : Nat) (requests : List (Request n)),
    evaluate arity fuel requests = true → requests.all (valid arity) = true

def SufficientFuelExact : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (fuel : Nat) (requests : List (Request n)),
    workWeight requests ≤ fuel → evaluate arity fuel requests = requests.all (valid arity)

def ActualTermEvaluation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (tau : Ty) (code : Code (Fin n)),
    evaluate arity (codeWeight code) [.term Gamma tau code] =
      (decodeTerm arity Gamma tau code).isSome

def ActualArgumentsEvaluation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma types : List Ty) (code : Code (Fin n)),
    evaluate arity (codeWeight code) [.arguments Gamma types code] =
      (decodeArguments arity Gamma types code).isSome

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluationTargets
