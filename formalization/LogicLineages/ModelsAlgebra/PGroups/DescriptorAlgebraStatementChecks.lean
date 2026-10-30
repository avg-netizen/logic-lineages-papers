module

public import LogicLineages.ModelsAlgebra.PGroups.DescriptorAlgebra
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_middle_image_ulm_rank : LogicLineages.ModelsAlgebra.PGroups.Targets.groupMiddleImageUlmRank :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.middle_image_ulm_rank

theorem fixed_bounded_descriptor_categoricity : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBoundedDescriptorCategoricity :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.bounded_descriptor_categoricity

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
