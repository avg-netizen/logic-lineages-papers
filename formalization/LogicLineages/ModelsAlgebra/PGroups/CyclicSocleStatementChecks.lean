module

public import LogicLineages.ModelsAlgebra.PGroups.CyclicSocle
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_cyclic_top_socle_isomorphism : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCyclicTopSocleIsomorphism :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.cyclic_top_socle_isomorphism

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
