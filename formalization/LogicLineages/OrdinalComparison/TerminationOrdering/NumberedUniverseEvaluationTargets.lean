module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseEvaluationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseEvaluationTargets
open Source NumberedTypedRequests NumberedRequestWeight NumberedUniverseEvaluation

/-- Every reported success satisfies the original decoders and universe tests. -/
def AnyFuelSound : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty)
    (fuel : Nat) (requests : List (Request n)),
    evaluate arity symbols S fuel requests = true →
      requests.all (NumberedUniverseRequests.valid arity symbols S) = true

/-- The original Code-node weight suffices for exact universe validation. -/
def SufficientFuelExact : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty)
    (fuel : Nat) (requests : List (Request n)),
    workWeight requests ≤ fuel →
      evaluate arity symbols S fuel requests =
        requests.all (NumberedUniverseRequests.valid arity symbols S)

/-- The failure-aware finite iteration is exactly the bounded evaluator. -/
def ActualIterationCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty)
    (fuel : Nat) (requests : List (Request n)),
    done (run arity symbols S fuel requests) =
      evaluate arity symbols S fuel requests

/-- Primitive recursion is joint in the windows, fuel, and actual request list. -/
def ActualEvaluatorPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    Primrec (fun p : (List (Fin n) × List Ty) × Nat × List (Request n) =>
      evaluate arity p.1.1 p.1.2 p.2.1 p.2.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseEvaluationTargets
