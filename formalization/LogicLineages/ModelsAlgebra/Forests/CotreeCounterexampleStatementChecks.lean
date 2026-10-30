module

public import LogicLineages.ModelsAlgebra.Forests.CotreeCounterexampleProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem concreteCotreesValid : LogicLineages.ModelsAlgebra.Forests.Targets.ConcreteCotreesValid :=
  LogicLineages.ModelsAlgebra.Forests.CotreeCounterexampleProof.concreteCotreesValid

theorem concreteCotreeLeavesExact : LogicLineages.ModelsAlgebra.Forests.Targets.ConcreteCotreeLeavesExact :=
  LogicLineages.ModelsAlgebra.Forests.CotreeCounterexampleProof.concreteCotreeLeavesExact

theorem concreteCotreeGraphsExact : LogicLineages.ModelsAlgebra.Forests.Targets.ConcreteCotreeGraphsExact :=
  LogicLineages.ModelsAlgebra.Forests.CotreeCounterexampleProof.concreteCotreeGraphsExact

theorem concreteCotreePathObstruction : LogicLineages.ModelsAlgebra.Forests.Targets.ConcreteCotreePathObstruction :=
  LogicLineages.ModelsAlgebra.Forests.CotreeCounterexampleProof.concreteCotreePathObstruction

theorem literalCotreeTransferCounterexample : LogicLineages.ModelsAlgebra.Forests.Targets.LiteralCotreeTransferCounterexample :=
  LogicLineages.ModelsAlgebra.Forests.CotreeCounterexampleProof.literalCotreeTransferCounterexample

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
