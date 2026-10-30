module

public import LogicLineages.ModelsAlgebra.Forests.CarterAutomataProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem carterReachableHeightExact : LogicLineages.ModelsAlgebra.Forests.Targets.CarterReachableHeightExact :=
  LogicLineages.ModelsAlgebra.Forests.CarterAutomataProof.carterReachableHeightExact

theorem carterReachableSaturation : LogicLineages.ModelsAlgebra.Forests.Targets.CarterReachableSaturation :=
  LogicLineages.ModelsAlgebra.Forests.CarterAutomataProof.carterReachableSaturation

theorem carterAllRunsReachable : LogicLineages.ModelsAlgebra.Forests.Targets.CarterAllRunsReachable :=
  LogicLineages.ModelsAlgebra.Forests.CarterAutomataProof.carterAllRunsReachable

theorem carterLanguageEmptiness : LogicLineages.ModelsAlgebra.Forests.Targets.CarterLanguageEmptiness :=
  LogicLineages.ModelsAlgebra.Forests.CarterAutomataProof.carterLanguageEmptiness

theorem carterUnorderedRunInvariant : LogicLineages.ModelsAlgebra.Forests.Targets.CarterUnorderedRunInvariant :=
  LogicLineages.ModelsAlgebra.Forests.CarterAutomataProof.carterUnorderedRunInvariant

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
