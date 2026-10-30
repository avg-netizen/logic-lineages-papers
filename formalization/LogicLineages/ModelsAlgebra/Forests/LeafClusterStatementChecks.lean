module

public import LogicLineages.ModelsAlgebra.Forests.LeafClusterProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem leafClustersLaminar : LogicLineages.ModelsAlgebra.Forests.Targets.LeafClustersLaminar :=
  LogicLineages.ModelsAlgebra.Forests.LeafClusterProof.leafClustersLaminar

theorem saturatedLeafBijection : LogicLineages.ModelsAlgebra.Forests.Targets.SaturatedLeafBijection :=
  LogicLineages.ModelsAlgebra.Forests.LeafClusterProof.saturatedLeafBijection

theorem saturatedClusterTransport : LogicLineages.ModelsAlgebra.Forests.Targets.SaturatedClusterTransport :=
  LogicLineages.ModelsAlgebra.Forests.LeafClusterProof.saturatedClusterTransport

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
