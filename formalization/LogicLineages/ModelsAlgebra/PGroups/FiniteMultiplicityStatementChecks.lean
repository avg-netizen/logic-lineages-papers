module

public import LogicLineages.ModelsAlgebra.PGroups.FiniteMultiplicity
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_finite_multiplicity_enumeration : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFiniteMultiplicityEnumeration :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.finite_multiplicity_enumeration

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks
