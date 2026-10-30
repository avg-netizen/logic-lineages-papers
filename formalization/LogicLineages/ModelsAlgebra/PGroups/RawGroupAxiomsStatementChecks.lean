module

public import LogicLineages.ModelsAlgebra.PGroups.RawGroupAxioms
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_raw_axioms_complexity : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawAxiomsComplexity :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_axioms_complexity

theorem fixed_raw_axioms_realization : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawAxiomsRealization :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_axioms_realization

theorem fixed_raw_laws_group_construction : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawLawsGroupConstruction :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_laws_group_construction

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
