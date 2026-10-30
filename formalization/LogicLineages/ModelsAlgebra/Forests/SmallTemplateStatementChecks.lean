module

public import LogicLineages.ModelsAlgebra.Forests.SmallTemplateProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem smallLaminarCombLabeling : LogicLineages.ModelsAlgebra.Forests.Targets.SmallLaminarCombLabeling :=
  LogicLineages.ModelsAlgebra.Forests.SmallTemplateProof.smallLaminarCombLabeling

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
