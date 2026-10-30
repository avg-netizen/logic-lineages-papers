module

public import LogicLineages.ModelsAlgebra.PGroups.FiniteAtomicIsolation
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_finite_atomic_isolation : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFiniteAtomicIsolation :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.finite_atomic_isolation

theorem fixed_p_primary_atomic_isolation : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPPrimaryAtomicIsolation :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.p_primary_atomic_isolation

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
