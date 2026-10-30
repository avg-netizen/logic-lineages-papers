module

public import LogicLineages.ModelsAlgebra.PGroups.FiniteTermTable
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_distinct_term_matrix : LogicLineages.ModelsAlgebra.PGroups.Targets.groupDistinctTermMatrix :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.distinct_term_matrix

theorem fixed_finite_term_table : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFiniteTermTable :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.finite_term_table

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
