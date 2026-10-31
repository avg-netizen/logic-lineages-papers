module
public import LogicLineages.OrdinalComparison.WWScalarTranslationDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open ForwardTranslation

/-- The closed evaluator's outputs are genuine positive ordinals. -/
def ClosedPositiveValuePositive : Prop :=
  ∀ c : ClosedPositive, 0 < c.evaluate.1.repr

/-- Each target shift has exactly the source's positive fixed head omega*c,
with an independently normal-notation bounded ordinal value. -/
def ScalarFixedHeadAdmissible : Prop :=
  ∀ c : ClosedPositive, Ordinal.omega0 ≤ fixedHead c ∧ fixedHead c < epsilonZero

/-- Actual computability, not merely a syntactic evaluator or an assumed
function field: every fixed h_lambda is computed using the already calibrated
closed-collapse algorithm and finite-right ordinal addition. -/
def ScalarFixedShiftComputable : Prop :=
  ∀ c : ClosedPositive, Computable (fun n : Nat => actualCollapse (fixedHead c + (n : Ordinal)))

end LogicLineages.OrdinalComparison.Source.Targets
