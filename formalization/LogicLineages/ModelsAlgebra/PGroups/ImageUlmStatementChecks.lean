module

public import LogicLineages.ModelsAlgebra.PGroups.ImageUlm
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_image_ulm_isomorphism : LogicLineages.ModelsAlgebra.PGroups.Targets.groupImageUlmIsomorphism :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.image_ulm_isomorphism

theorem fixed_image_ulm_rank : LogicLineages.ModelsAlgebra.PGroups.Targets.groupImageUlmRank :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.image_ulm_rank

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
