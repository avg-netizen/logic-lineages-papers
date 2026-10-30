module

public import LogicLineages.ModelsAlgebra.Forests.CarterWitnessProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem carterTreeEnumerationExact : LogicLineages.ModelsAlgebra.Forests.Targets.CarterTreeEnumerationExact :=
  LogicLineages.ModelsAlgebra.Forests.CarterWitnessProof.carterTreeEnumerationExact

theorem carterTreeSizeBound : LogicLineages.ModelsAlgebra.Forests.Targets.CarterTreeSizeBound :=
  LogicLineages.ModelsAlgebra.Forests.CarterWitnessProof.carterTreeSizeBound

theorem carterBoundedRunRepresentative : LogicLineages.ModelsAlgebra.Forests.Targets.CarterBoundedRunRepresentative :=
  LogicLineages.ModelsAlgebra.Forests.CarterWitnessProof.carterBoundedRunRepresentative

theorem carterAcceptedWitnessSound : LogicLineages.ModelsAlgebra.Forests.Targets.CarterAcceptedWitnessSound :=
  LogicLineages.ModelsAlgebra.Forests.CarterWitnessProof.carterAcceptedWitnessSound

theorem carterAcceptedWitnessComplete : LogicLineages.ModelsAlgebra.Forests.Targets.CarterAcceptedWitnessComplete :=
  LogicLineages.ModelsAlgebra.Forests.CarterWitnessProof.carterAcceptedWitnessComplete

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
