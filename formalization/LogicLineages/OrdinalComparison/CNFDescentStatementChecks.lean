module

public import LogicLineages.OrdinalComparison.CNFDescent
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_cnf_descent_below_epsilon_zero : Targets.CNFDescentBelowEpsilonZero :=
  cnfDescentBelowEpsilonZero

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
