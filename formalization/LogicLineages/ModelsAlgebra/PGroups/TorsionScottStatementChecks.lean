module

public import LogicLineages.ModelsAlgebra.PGroups.TorsionScott
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.TorsionScottStatementChecks

theorem fixed_torsion_locally_finite : Targets.groupTorsionLocallyFinite :=
  GroupInfinitary.torsion_locally_finite

theorem fixed_p_primary_torsion : Targets.groupPPrimaryTorsion :=
  GroupInfinitary.p_primary_torsion

theorem fixed_p_primary_no_sigma_two_scott : Targets.groupPPrimaryNoSigmaTwoScott :=
  GroupInfinitary.p_primary_no_sigma_two_scott

end LogicLineages.ModelsAlgebra.PGroups.TorsionScottStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
