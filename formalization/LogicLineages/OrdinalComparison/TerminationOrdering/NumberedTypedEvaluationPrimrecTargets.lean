module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluationPrimrecDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluationPrimrecTargets
open NumberedTypedRequests NumberedTypedEvaluation NumberedTypedEvaluationPrimrec

def ActualIterationCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (fuel : Nat) (requests : List (Request n)),
    done (run arity fuel requests) = evaluate arity fuel requests

def ActualEvaluatorPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    Primrec (fun input : Nat × List (Request n) => evaluate arity input.1 input.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluationPrimrecTargets
