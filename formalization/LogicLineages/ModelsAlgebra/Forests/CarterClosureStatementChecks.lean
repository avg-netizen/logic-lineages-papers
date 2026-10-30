module

public import LogicLineages.ModelsAlgebra.Forests.CarterClosureProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem carterProductRun : LogicLineages.ModelsAlgebra.Forests.Targets.CarterProductRun :=
  LogicLineages.ModelsAlgebra.Forests.CarterClosureProof.carterProductRun

theorem carterComplementLanguage : LogicLineages.ModelsAlgebra.Forests.Targets.CarterComplementLanguage :=
  LogicLineages.ModelsAlgebra.Forests.CarterClosureProof.carterComplementLanguage

theorem carterIntersectionLanguage : LogicLineages.ModelsAlgebra.Forests.Targets.CarterIntersectionLanguage :=
  LogicLineages.ModelsAlgebra.Forests.CarterClosureProof.carterIntersectionLanguage

theorem carterUnionLanguage : LogicLineages.ModelsAlgebra.Forests.Targets.CarterUnionLanguage :=
  LogicLineages.ModelsAlgebra.Forests.CarterClosureProof.carterUnionLanguage

theorem carterDifferenceLanguage : LogicLineages.ModelsAlgebra.Forests.Targets.CarterDifferenceLanguage :=
  LogicLineages.ModelsAlgebra.Forests.CarterClosureProof.carterDifferenceLanguage

theorem carterLanguageEquivalence : LogicLineages.ModelsAlgebra.Forests.Targets.CarterLanguageEquivalence :=
  LogicLineages.ModelsAlgebra.Forests.CarterClosureProof.carterLanguageEquivalence

theorem carterComplementSymmetric : LogicLineages.ModelsAlgebra.Forests.Targets.CarterComplementSymmetric :=
  LogicLineages.ModelsAlgebra.Forests.CarterClosureProof.carterComplementSymmetric

theorem carterProductSymmetric : LogicLineages.ModelsAlgebra.Forests.Targets.CarterProductSymmetric :=
  LogicLineages.ModelsAlgebra.Forests.CarterClosureProof.carterProductSymmetric

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
