module

public import LogicLineages.ModelsAlgebra.Forests.ClusterCompletenessProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem finiteLeafClusterSemantics : LogicLineages.ModelsAlgebra.Forests.Targets.FiniteLeafClusterSemantics :=
  LogicLineages.ModelsAlgebra.Forests.ClusterCompletenessProof.finiteLeafClusterSemantics

theorem binaryForestClusterComplete : LogicLineages.ModelsAlgebra.Forests.Targets.BinaryForestClusterComplete :=
  LogicLineages.ModelsAlgebra.Forests.ClusterCompletenessProof.binaryForestClusterComplete

theorem saturatedHostClusterComplete : LogicLineages.ModelsAlgebra.Forests.Targets.SaturatedHostClusterComplete :=
  LogicLineages.ModelsAlgebra.Forests.ClusterCompletenessProof.saturatedHostClusterComplete

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
