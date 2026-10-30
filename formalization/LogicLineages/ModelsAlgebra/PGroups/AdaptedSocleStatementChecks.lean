module

public import LogicLineages.ModelsAlgebra.PGroups.AdaptedSocle
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_adapted_socle_independent : LogicLineages.ModelsAlgebra.PGroups.Targets.groupAdaptedSocleIndependent :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.adapted_socle_independent

theorem fixed_adapted_socle_filtered_span : LogicLineages.ModelsAlgebra.PGroups.Targets.groupAdaptedSocleFilteredSpan :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.adapted_socle_filtered_span

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
