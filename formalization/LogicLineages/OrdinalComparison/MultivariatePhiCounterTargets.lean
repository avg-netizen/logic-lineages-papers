module
public import LogicLineages.OrdinalComparison.MultivariatePhiCounterDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def MultivariateWeightedRaySource : Prop :=
  (∀ (w : Nat → Nat) (E : MultivariatePositiveExpr) (x : Nat),
    actualFixedLimitProfileEval (multivariatePositiveWeightedRay w E) x=
      actualMultivariatePositiveEval E (fun i => w i*x)) ∧
  (∀ (d : Nat) (w : Nat → Nat) (E : MultivariatePositiveExpr), multivariatePositiveValid d E →
    fixedLimitProfileBelow epsilonZero (multivariatePositiveWeightedRay w E))

def MultivariateCounterRayCode : Prop :=
  Computable (fun p : Nat × Nat × Nat => encodedMultivariateCounterRay p.1 p.2.1 p.2.2) ∧
  ∀ (n m : Nat) (E : MultivariatePositiveExpr),
    encodedMultivariateCounterRay n m (multivariatePositiveEncode E)=
      positiveExprEncode (multivariatePositiveWeightedRay (encodedMultivariateCounterWeight n m) E)

/-- Exact computed source countervaluation shape x_i=w_i*(Phi(k)+1), with
strictly positive fixed weights and k, on every valid finite-variable input.
This does not identify the paper's literal recursively collected NF. -/
def MultivariatePhiRayCounter : Prop :=
  Computable₂ encodedMultivariatePhiCounterIndex ∧
  ∀ (d : Nat) (E F : MultivariatePositiveExpr),
    multivariatePositiveValid d E → multivariatePositiveValid d F →
    let n := multivariatePositiveEncode E
    let m := multivariatePositiveEncode F
    let k := encodedMultivariatePhiCounterIndex n m
    encodedMultivariateIdentity n m=false →
      1≤k ∧ (∀ i : Nat, 0<encodedMultivariateCounterWeight n m i) ∧
      actualMultivariatePositiveEval E (fun i => encodedMultivariateCounterWeight n m i*(Phi k+1))≠
        actualMultivariatePositiveEval F (fun i => encodedMultivariateCounterWeight n m i*(Phi k+1))

end LogicLineages.OrdinalComparison.Targets
