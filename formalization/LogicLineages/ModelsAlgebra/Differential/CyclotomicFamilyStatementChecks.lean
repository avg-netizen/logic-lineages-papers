module

public import LogicLineages.ModelsAlgebra.Differential.CyclotomicFamily
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_cyclotomicSemanticFamily : Targets.cyclotomicSemanticFamily :=
  CyclotomicFamily.semantic_family

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
