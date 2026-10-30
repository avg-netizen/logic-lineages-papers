module

public import LogicLineages.ModelsAlgebra.PGroups.UlmLowerFormula
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.UlmLowerFormulaStatementChecks

theorem fixed_finite_sum_term_evaluation : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFiniteSumTermEvaluation :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.finite_sum_term_evaluation

theorem fixed_ulm_lower_matrix_realization : LogicLineages.ModelsAlgebra.PGroups.Targets.groupUlmLowerMatrixRealization :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.ulm_lower_matrix_realization

theorem fixed_ulm_lower_witness_formula : LogicLineages.ModelsAlgebra.PGroups.Targets.groupUlmLowerWitnessFormula :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.ulm_lower_witness_formula

theorem fixed_ulm_root_representatives : LogicLineages.ModelsAlgebra.PGroups.Targets.groupUlmRootRepresentatives :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.ulm_root_representatives

theorem fixed_ulm_lower_formula : LogicLineages.ModelsAlgebra.PGroups.Targets.groupUlmLowerFormula :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.ulm_lower_formula

end LogicLineages.ModelsAlgebra.PGroups.UlmLowerFormulaStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
