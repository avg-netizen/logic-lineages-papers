module
public import LogicLineages.OrdinalComparison.ParametricActualCollapseDefinitions
public import LogicLineages.OrdinalComparison.SourceMachineControlNonperiodicityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.ParametricCoefficientOne
noncomputable def coefficientOne (G : Nat → Nat) (n : Nat) : Nat :=
  ParametricActualCollapse.collapseWith G (Ordinal.omega0 + (n : Ordinal))
end LogicLineages.OrdinalComparison.ParametricCoefficientOne
