module

public import LogicLineages.ModelsAlgebra.Forests.LeafOrderProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem vertexLeafClusterNonempty : LogicLineages.ModelsAlgebra.Forests.Targets.VertexLeafClusterNonempty :=
  LogicLineages.ModelsAlgebra.Forests.LeafOrderProof.vertexLeafClusterNonempty

theorem orderReversesLeafClusterInclusion : LogicLineages.ModelsAlgebra.Forests.Targets.OrderReversesLeafClusterInclusion :=
  LogicLineages.ModelsAlgebra.Forests.LeafOrderProof.orderReversesLeafClusterInclusion

theorem leafClusterEqualityIffNeighborhoodEquality : LogicLineages.ModelsAlgebra.Forests.Targets.LeafClusterEqualityIffNeighborhoodEquality :=
  LogicLineages.ModelsAlgebra.Forests.LeafOrderProof.leafClusterEqualityIffNeighborhoodEquality

theorem leafClusterRankOrderRecovery : LogicLineages.ModelsAlgebra.Forests.Targets.LeafClusterRankOrderRecovery :=
  LogicLineages.ModelsAlgebra.Forests.LeafOrderProof.leafClusterRankOrderRecovery

theorem twinRankBelowCarrierCard : LogicLineages.ModelsAlgebra.Forests.Targets.TwinRankBelowCarrierCard :=
  LogicLineages.ModelsAlgebra.Forests.LeafOrderProof.twinRankBelowCarrierCard

theorem actualLeafClusterFamilyLaminar : LogicLineages.ModelsAlgebra.Forests.Targets.ActualLeafClusterFamilyLaminar :=
  LogicLineages.ModelsAlgebra.Forests.LeafOrderProof.actualLeafClusterFamilyLaminar

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
