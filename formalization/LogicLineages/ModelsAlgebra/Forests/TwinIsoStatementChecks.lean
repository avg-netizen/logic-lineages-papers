module

public import LogicLineages.ModelsAlgebra.Forests.TwinIsoProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem twinRankSurjective : LogicLineages.ModelsAlgebra.Forests.Targets.TwinRankSurjective :=
  LogicLineages.ModelsAlgebra.Forests.TwinIsoProof.twinRankSurjective

theorem graphIsoNeighborhoodSubset : LogicLineages.ModelsAlgebra.Forests.Targets.GraphIsoNeighborhoodSubset :=
  LogicLineages.ModelsAlgebra.Forests.TwinIsoProof.graphIsoNeighborhoodSubset

theorem graphIsoNeighborhoodEquality : LogicLineages.ModelsAlgebra.Forests.Targets.GraphIsoNeighborhoodEquality :=
  LogicLineages.ModelsAlgebra.Forests.TwinIsoProof.graphIsoNeighborhoodEquality

theorem graphIsoTwinCard : LogicLineages.ModelsAlgebra.Forests.Targets.GraphIsoTwinCard :=
  LogicLineages.ModelsAlgebra.Forests.TwinIsoProof.graphIsoTwinCard

theorem rankMatchedOrderIso : LogicLineages.ModelsAlgebra.Forests.Targets.RankMatchedOrderIso :=
  LogicLineages.ModelsAlgebra.Forests.TwinIsoProof.rankMatchedOrderIso

theorem twinClassOrderUniqueness : LogicLineages.ModelsAlgebra.Forests.Targets.TwinClassOrderUniqueness :=
  LogicLineages.ModelsAlgebra.Forests.TwinIsoProof.twinClassOrderUniqueness

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
