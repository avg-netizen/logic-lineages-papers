module

public import LogicLineages.ModelsAlgebra.Forests.TwinRankProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem orderReversesNeighborhoodInclusion : LogicLineages.ModelsAlgebra.Forests.Targets.OrderReversesNeighborhoodInclusion :=
  LogicLineages.ModelsAlgebra.Forests.TwinRankProof.orderReversesNeighborhoodInclusion

theorem twinClassChain : LogicLineages.ModelsAlgebra.Forests.Targets.TwinClassChain :=
  LogicLineages.ModelsAlgebra.Forests.TwinRankProof.twinClassChain

theorem twinRankOrder : LogicLineages.ModelsAlgebra.Forests.Targets.TwinRankOrder :=
  LogicLineages.ModelsAlgebra.Forests.TwinRankProof.twinRankOrder

theorem twinRankOrderRecovery : LogicLineages.ModelsAlgebra.Forests.Targets.TwinRankOrderRecovery :=
  LogicLineages.ModelsAlgebra.Forests.TwinRankProof.twinRankOrderRecovery

theorem twinRankBound : LogicLineages.ModelsAlgebra.Forests.Targets.TwinRankBound :=
  LogicLineages.ModelsAlgebra.Forests.TwinRankProof.twinRankBound

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
