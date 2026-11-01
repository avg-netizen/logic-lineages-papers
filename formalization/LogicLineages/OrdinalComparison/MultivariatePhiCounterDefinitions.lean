module
public import LogicLineages.OrdinalComparison.MultivariateIdentityDecisionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Arbitrary fixed positive-weight rays are a new substitution operation,
separate from the already frozen base-power ray compiler. -/
def multivariatePositiveWeightedRay (w : Nat → Nat) : MultivariatePositiveExpr → FixedLimitPositiveExpr
  | .constant c => .constant c
  | .input i => positiveInputMultiple (w i)
  | .add E F => .add (multivariatePositiveWeightedRay w E) (multivariatePositiveWeightedRay w F)
  | .head rho E => .head rho (multivariatePositiveWeightedRay w E)

/-- The compiler calls the actual uniformly computable counterweight program.
There is no arbitrary computable-function parameter or presumed solver. -/
noncomputable def encodedMultivariateCounterRayStep (n m code : Nat) (table : List Nat) : Nat :=
  if code%4=0 then code
  else if code%4=1 then positiveInputMultipleCode (encodedMultivariateCounterWeight n m (code/4))
  else
    let p := (code/4).unpair
    if code%4=2 then 4*Nat.pair (table.getD p.1 0) (table.getD p.2 0)+2
    else 4*Nat.pair p.1 (table.getD p.2 0)+3

noncomputable def encodedMultivariateCounterRayTable (n m : Nat) : Nat → List Nat
  | 0 => []
  | code+1 => encodedMultivariateCounterRayTable n m code ++
      [encodedMultivariateCounterRayStep n m code (encodedMultivariateCounterRayTable n m code)]

noncomputable def encodedMultivariateCounterRay (n m code : Nat) : Nat :=
  (encodedMultivariateCounterRayTable n m (code+1)).getD code 0

noncomputable def encodedMultivariatePhiCounterIndex (n m : Nat) : Nat :=
  encodedPositiveZeroBound (encodedMultivariateCounterRay n m n)
    (encodedMultivariateCounterRay n m m)

end LogicLineages.OrdinalComparison
