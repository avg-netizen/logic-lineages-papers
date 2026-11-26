module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.UndecidabilityDefinitions
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.H10ReductionTargets
@[expose] public section
namespace LogicLineages.PermittedControl.PolynomialUndecidabilitySupplierTargets

/-- Closed genuine finite-system theorem, not a supplied undecidability field. -/
def PolynomialSystemUndecidable : Prop :=
  ¬ ComputablePred OrdinalComparison.Source.FunctionalHardnessCompletion.encodedPolynomialSolvable

/-- Actual total coding reduction, including malformed input handling. -/
def ActualH10Bridge : Prop :=
  OrdinalComparison.Source.FunctionalHardnessCompletion.H10ReductionTargets.CodedH10ToLinearSystems

def PolynomialUndecidabilitySupplier : Prop := ActualH10Bridge ∧ PolynomialSystemUndecidable
end LogicLineages.PermittedControl.PolynomialUndecidabilitySupplierTargets
