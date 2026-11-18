module
public import LogicLineages.PermittedControl.SelectedPairCompilerDefinitions
public import LogicLineages.OrdinalComparison.SourcePolynomialFamilyLiftDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedPolynomialLift
open OrdinalComparison Source SelectedSourceDomain

noncomputable def scalar (ctrl : Nat → Nat) (t : ClosedExpression) : ClosedExpression :=
  UnitObservation.positive (actualOrdinalNorm (closedValue ctrl t))
noncomputable def vector (ctrl : Nat → Nat) (t : ClosedExpression) (j : Fin 2) : ClosedExpression :=
  if j.val=0 then scalar ctrl t else t
end LogicLineages.PermittedControl.SelectedPolynomialLift
