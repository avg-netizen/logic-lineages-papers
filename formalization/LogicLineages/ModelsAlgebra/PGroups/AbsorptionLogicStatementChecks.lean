module

public import LogicLineages.ModelsAlgebra.PGroups.AbsorptionLogic
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_tuple_fixing_sigma_one : LogicLineages.ModelsAlgebra.PGroups.Targets.groupTupleFixingSigmaOne :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.tuple_fixing_sigma_one

theorem fixed_tuple_fixing_backforth_one : LogicLineages.ModelsAlgebra.PGroups.Targets.groupTupleFixingBackForthOne :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.tuple_fixing_backforth_one

theorem fixed_tuple_fixing_backforth_two : LogicLineages.ModelsAlgebra.PGroups.Targets.groupTupleFixingBackForthTwo :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.tuple_fixing_backforth_two

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
