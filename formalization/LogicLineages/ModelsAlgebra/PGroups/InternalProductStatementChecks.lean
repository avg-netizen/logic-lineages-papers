module

public import LogicLineages.ModelsAlgebra.PGroups.InternalProduct
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_internal_product_isomorphism : LogicLineages.ModelsAlgebra.PGroups.Targets.groupInternalProductIsomorphism :=
  LogicLineages.ModelsAlgebra.PGroups.internal_product_isomorphism

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
