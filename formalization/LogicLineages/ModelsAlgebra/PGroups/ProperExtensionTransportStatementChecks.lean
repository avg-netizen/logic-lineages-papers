module

public import LogicLineages.ModelsAlgebra.PGroups.ProperExtensionTransport
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_proper_extension_transport : LogicLineages.ModelsAlgebra.PGroups.Targets.groupProperExtensionTransport :=
  LogicLineages.ModelsAlgebra.PGroups.proper_extension_transport

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
