module
public import LogicLineages.OrdinalComparison.MultivariateDictionaryDefinitions
public import LogicLineages.OrdinalComparison.EncodedPositiveFoldDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

def multivariatePositiveHasInput : MultivariatePositiveExpr → Bool
  | .constant _ => false
  | .input _ => true
  | .add E F => multivariatePositiveHasInput E || multivariatePositiveHasInput F
  | .head _ E => multivariatePositiveHasInput E

/-- An actual already certified numeric source evaluation program. The
base-one ray puts every variable at zero at its input0; no oracle is used. -/
noncomputable def encodedMultivariateClosedValue (n : Nat) : Nat :=
  encodedPositiveFoldValue (encodedMultivariateRay 1 n)

/-- Literal bottom-up multivariate collection, independent of any fresh-head
bound: sum actual coefficient vectors/dictionaries and fold closed calls. -/
noncomputable def multivariateCollectedNormalize : MultivariatePositiveExpr → MultivariateCollectedNF
  | .constant c => .mk c [] .nil
  | .input i => .mk 0 (multivariateVariableCoefficients i 1) .nil
  | .add E F => multivariateCollectedAdd (multivariateCollectedNormalize E) (multivariateCollectedNormalize F)
  | .head rho E =>
    if multivariatePositiveHasInput E=false then
      .mk (encodedMultivariateClosedValue (multivariatePositiveEncode (.head rho E))) [] .nil
    else .mk 0 [] (.cons rho (multivariateCollectedNormalize E) 1 .nil)

end LogicLineages.OrdinalComparison
