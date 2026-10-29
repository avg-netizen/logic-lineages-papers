module

public import LogicLineages.OrdinalComparison.ActualCollapse
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actual_collapse_equation : Targets.ActualNormControlledCollapse actualCollapse :=
  actualCollapse_equation

theorem fixed_actual_collapse_uniqueness : Targets.ActualCollapseUniqueBelowEpsilonZero actualCollapse :=
  actualCollapse_uniqueBelowEpsilonZero

theorem fixed_actual_collapse_controlled_strictness : Targets.ActualCollapseControlledStrictness actualCollapse :=
  actualCollapse_controlledStrictness

theorem fixed_actual_collapse_finite_values : Targets.ActualCollapseFiniteValues actualCollapse :=
  actualCollapse_finiteValues

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
