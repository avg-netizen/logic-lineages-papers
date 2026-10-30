module

public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTail
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_transfinite_tail_membership : LogicLineages.ModelsAlgebra.PGroups.Targets.groupTransfiniteTailMembership :=
  LogicLineages.ModelsAlgebra.PGroups.transfinite_tail_membership

theorem fixed_transfinite_tail_image : LogicLineages.ModelsAlgebra.PGroups.Targets.groupTransfiniteTailImage :=
  LogicLineages.ModelsAlgebra.PGroups.transfinite_tail_image

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
