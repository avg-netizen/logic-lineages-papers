module

public import LogicLineages.ModelsAlgebra.PGroups.MaximalCyclic
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_maximal_cyclic_root_correction : LogicLineages.ModelsAlgebra.PGroups.Targets.groupMaximalCyclicRootCorrection :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.maximal_cyclic_root_correction

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
