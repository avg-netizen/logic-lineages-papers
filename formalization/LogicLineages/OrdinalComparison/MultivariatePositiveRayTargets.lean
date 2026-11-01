module
public import LogicLineages.OrdinalComparison.MultivariatePositiveRayDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Paper07 identity proof, literal weighted-ray substitution supplier. This
does not assert that one arbitrarily chosen ray separates normal forms. -/
def MultivariatePositiveRaySource : Prop :=
  (∀ n : Nat, positiveInputMultipleCode n=positiveExprEncode (positiveInputMultiple n)) ∧
  (∀ n x : Nat, actualFixedLimitProfileEval (positiveInputMultiple n) x=n*x) ∧
  (∀ n : Nat, fixedLimitProfileBelow epsilonZero (positiveInputMultiple n)) ∧
  (∀ (E : MultivariatePositiveExpr) (base x : Nat),
    actualFixedLimitProfileEval (multivariatePositiveRay base E) x=
      actualMultivariatePositiveEval E (fun i => base^i*x)) ∧
  (∀ (d base : Nat) (E : MultivariatePositiveExpr), multivariatePositiveValid d E →
    fixedLimitProfileBelow epsilonZero (multivariatePositiveRay base E)) ∧
  (∀ base x : Nat, 0<base → 0<x → ∀ i : Nat, 0<base^i*x)

def MultivariatePositiveRayCode : Prop :=
  Primrec positiveInputMultipleCode ∧ Primrec₂ encodedMultivariateRay ∧
  ∀ (base : Nat) (E : MultivariatePositiveExpr),
    encodedMultivariateRay base (multivariatePositiveEncode E)=
      positiveExprEncode (multivariatePositiveRay base E)

end LogicLineages.OrdinalComparison.Targets
