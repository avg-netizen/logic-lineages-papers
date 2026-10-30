module

public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryRenaming
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.InfinitaryRenamingStatementChecks

theorem fixed_term_renaming_evaluation : LogicLineages.ModelsAlgebra.PGroups.Targets.groupTermRenamingEvaluation :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.term_renaming_evaluation

theorem fixed_qf_renaming_realization : LogicLineages.ModelsAlgebra.PGroups.Targets.groupQFRenamingRealization :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.qf_renaming_realization

theorem fixed_lift_renaming_assignment : LogicLineages.ModelsAlgebra.PGroups.Targets.groupLiftRenamingAssignment :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.lift_renaming_assignment

theorem fixed_infinitary_renaming_realization : LogicLineages.ModelsAlgebra.PGroups.Targets.groupInfinitaryRenamingRealization :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.infinitary_renaming_realization

theorem fixed_infinitary_renaming_complexity : LogicLineages.ModelsAlgebra.PGroups.Targets.groupInfinitaryRenamingComplexity :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.infinitary_renaming_complexity

end LogicLineages.ModelsAlgebra.PGroups.InfinitaryRenamingStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
