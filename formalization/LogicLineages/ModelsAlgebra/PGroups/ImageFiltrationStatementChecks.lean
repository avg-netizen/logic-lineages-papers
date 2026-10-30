module

public import LogicLineages.ModelsAlgebra.PGroups.ImageFiltration
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_image_finite_filtration : LogicLineages.ModelsAlgebra.PGroups.Targets.groupImageFiniteFiltration :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.image_finite_filtration

theorem fixed_image_finite_socle : LogicLineages.ModelsAlgebra.PGroups.Targets.groupImageFiniteSocle :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.image_finite_socle

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
