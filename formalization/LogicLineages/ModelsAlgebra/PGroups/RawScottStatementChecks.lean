module

public import LogicLineages.ModelsAlgebra.PGroups.RawScott
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_raw_additive_isomorphism : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawAdditiveIsomorphism :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_additive_isomorphism

theorem fixed_raw_actual_group_laws : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawActualGroupLaws :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_actual_group_laws

theorem fixed_raw_guard_scott_transfer : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawGuardScottTransfer :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_guard_scott_transfer

theorem fixed_raw_guard_difference_scott_transfer : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawGuardDifferenceScottTransfer :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_guard_difference_scott_transfer

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
