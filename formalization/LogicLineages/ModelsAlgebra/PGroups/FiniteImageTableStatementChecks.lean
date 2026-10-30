module

public import LogicLineages.ModelsAlgebra.PGroups.FiniteImageTable
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.FiniteImageTableStatementChecks

theorem fixed_table_term_evaluation : LogicLineages.ModelsAlgebra.PGroups.Targets.groupTableTermEvaluation :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.table_term_evaluation

theorem fixed_finite_image_table_matrix : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFiniteImageTableMatrix :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.finite_image_table_matrix

theorem fixed_finite_image_table_formula : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFiniteImageTableFormula :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.finite_image_table_formula

theorem fixed_finite_image_isomorphism_formula : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFiniteImageIsomorphismFormula :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.finite_image_isomorphism_formula

end LogicLineages.ModelsAlgebra.PGroups.FiniteImageTableStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
