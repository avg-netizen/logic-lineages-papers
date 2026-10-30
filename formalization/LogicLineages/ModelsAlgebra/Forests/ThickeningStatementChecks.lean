module

public import LogicLineages.ModelsAlgebra.Forests.ThickeningProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem thickeningPartialOrderLaws : LogicLineages.ModelsAlgebra.Forests.Targets.ThickeningPartialOrderLaws :=
  LogicLineages.ModelsAlgebra.Forests.ThickeningProof.thickeningPartialOrderLaws

theorem thickeningPredecessorsChain : LogicLineages.ModelsAlgebra.Forests.Targets.ThickeningPredecessorsChain :=
  LogicLineages.ModelsAlgebra.Forests.ThickeningProof.thickeningPredecessorsChain

theorem thickeningMaximalPoints : LogicLineages.ModelsAlgebra.Forests.Targets.ThickeningMaximalPoints :=
  LogicLineages.ModelsAlgebra.Forests.ThickeningProof.thickeningMaximalPoints

theorem actualFiniteThickening : LogicLineages.ModelsAlgebra.Forests.Targets.ActualFiniteThickening :=
  LogicLineages.ModelsAlgebra.Forests.ThickeningProof.actualFiniteThickening

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
