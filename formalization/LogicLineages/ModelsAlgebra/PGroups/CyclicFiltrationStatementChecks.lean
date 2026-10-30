module

public import LogicLineages.ModelsAlgebra.PGroups.CyclicFiltration
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_cyclic_filtration_bottom : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCyclicFiltrationBottom :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.cyclic_filtration_bottom

theorem fixed_cyclic_filtration_socle : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCyclicFiltrationSocle :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.cyclic_filtration_socle

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
