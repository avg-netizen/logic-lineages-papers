module

public import LogicLineages.ModelsAlgebra.PGroups.SocleRoot
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.SocleRootStatementChecks

theorem fixed_socle_root_matrix : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSocleRootMatrix :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.socle_root_matrix

theorem fixed_socle_root_witness_formula : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSocleRootWitnessFormula :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.socle_root_witness_formula

theorem fixed_socle_root_formula : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSocleRootFormula :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.socle_root_formula

end LogicLineages.ModelsAlgebra.PGroups.SocleRootStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
