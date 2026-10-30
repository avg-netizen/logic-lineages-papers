module

public import LogicLineages.ModelsAlgebra.PGroups.UpperCyclic
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.UpperCyclicStatementChecks

theorem fixed_upper_cyclic_finite : LogicLineages.ModelsAlgebra.PGroups.Targets.groupUpperCyclicFinite :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.upper_cyclic_finite

theorem fixed_upper_cyclic_annihilation : LogicLineages.ModelsAlgebra.PGroups.Targets.groupUpperCyclicAnnihilation :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.upper_cyclic_annihilation

theorem fixed_upper_cyclic_socle_roots : LogicLineages.ModelsAlgebra.PGroups.Targets.groupUpperCyclicSocleRoots :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.upper_cyclic_socle_roots

end LogicLineages.ModelsAlgebra.PGroups.UpperCyclicStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
