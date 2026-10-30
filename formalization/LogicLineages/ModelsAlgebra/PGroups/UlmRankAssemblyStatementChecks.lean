module

public import LogicLineages.ModelsAlgebra.PGroups.UlmRankAssembly
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_product_finite_ulm : LogicLineages.ModelsAlgebra.PGroups.Targets.groupProductFiniteUlm :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.product_finite_ulm

theorem fixed_product_ulm_rank : LogicLineages.ModelsAlgebra.PGroups.Targets.groupProductUlmRank :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.product_ulm_rank

theorem fixed_pi_ulm_rank : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPiUlmRank :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.pi_ulm_rank

theorem fixed_finsupp_ulm_rank : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFinsuppUlmRank :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.finsupp_ulm_rank

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
