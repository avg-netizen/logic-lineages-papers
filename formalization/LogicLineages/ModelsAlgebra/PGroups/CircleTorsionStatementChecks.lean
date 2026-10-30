module

public import LogicLineages.ModelsAlgebra.PGroups.CircleTorsion
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_circle_torsion_range : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCircleTorsionRange :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.circle_torsion_range

theorem fixed_circle_torsion_isomorphism : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCircleTorsionIsomorphism :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.circle_torsion_isomorphism

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
