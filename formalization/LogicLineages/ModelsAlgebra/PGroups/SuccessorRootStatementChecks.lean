module

public import LogicLineages.ModelsAlgebra.PGroups.SuccessorRoot
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_successor_suitable_root : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSuccessorSuitableRoot :=
  LogicLineages.ModelsAlgebra.PGroups.successor_suitable_root

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
