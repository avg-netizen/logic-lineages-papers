module

public import LogicLineages.ModelsAlgebra.Forests.FiniteCodeEffectivityProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem fixed_forestFiniteTestsPrimitiveRecursive : Targets.ForestFiniteTestsPrimitiveRecursive :=
  FiniteCodeEffectivityProof.forestFiniteTestsPrimitiveRecursive

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
