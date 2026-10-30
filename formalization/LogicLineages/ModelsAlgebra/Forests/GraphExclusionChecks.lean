module

public import LogicLineages.ModelsAlgebra.Forests.GraphExclusionProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem fixed_comparabilityForbiddenGraphs : Targets.ComparabilityForbiddenGraphs :=
  GraphExclusionProof.comparabilityForbiddenGraphs

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
