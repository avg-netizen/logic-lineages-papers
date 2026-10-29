module

public import LogicLineages.ModelsAlgebra.Forests.OrderTargets
public import LogicLineages.ModelsAlgebra.Forests.OrderFacts
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem incomparableNoCommonUpper : Targets.incomparableNoCommonUpper := by
  intro α _ h x y hxy hyx
  exact no_common_upper_bound h hxy hyx

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
