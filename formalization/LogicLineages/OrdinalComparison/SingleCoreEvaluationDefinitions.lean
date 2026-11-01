module
public import LogicLineages.OrdinalComparison.SingleCoreSupportDefinitions
public import LogicLineages.OrdinalComparison.WWEncodedScalarDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

def singleCoreGround (xs : List Nat) : MultivariatePositiveExpr → FixedLimitPositiveExpr
  | .constant c => .constant c
  | .input i => .constant (xs.getD i 0+1)
  | .add E F => .add (singleCoreGround xs E) (singleCoreGround xs F)
  | .head rho E => .head rho (singleCoreGround xs E)

/-- Actual finite positive-tuple evaluation, retaining the existing raw-entry
successor convention: the original variable receives xs[i]+1. -/
noncomputable def encodedSingleCoreEvaluation (n : Nat) (xs : List Nat) : Nat :=
  Source.ForwardTranslation.encodedScalarValue n xs

end LogicLineages.OrdinalComparison
