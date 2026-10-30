module

public import LogicLineages.ModelsAlgebra.PGroups.SuccessorExtension
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_successor_preserving_extension : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSuccessorPreservingExtension :=
  LogicLineages.ModelsAlgebra.PGroups.successor_preserving_extension

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
