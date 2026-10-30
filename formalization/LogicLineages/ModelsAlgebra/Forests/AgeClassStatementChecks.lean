module

public import LogicLineages.ModelsAlgebra.Forests.AgeClassProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem forestModelClassNonempty : LogicLineages.ModelsAlgebra.Forests.Targets.ForestModelClassNonempty :=
  LogicLineages.ModelsAlgebra.Forests.AgeClassProof.forestModelClassNonempty

theorem forestModelClassIsoInvariant : LogicLineages.ModelsAlgebra.Forests.Targets.ForestModelClassIsoInvariant :=
  LogicLineages.ModelsAlgebra.Forests.AgeClassProof.forestModelClassIsoInvariant

theorem forestModelClassFinitelyGenerated : LogicLineages.ModelsAlgebra.Forests.Targets.ForestModelClassFinitelyGenerated :=
  LogicLineages.ModelsAlgebra.Forests.AgeClassProof.forestModelClassFinitelyGenerated

theorem forestModelClassHereditary : LogicLineages.ModelsAlgebra.Forests.Targets.ForestModelClassHereditary :=
  LogicLineages.ModelsAlgebra.Forests.AgeClassProof.forestModelClassHereditary

theorem forestModelClassJointEmbedding : LogicLineages.ModelsAlgebra.Forests.Targets.ForestModelClassJointEmbedding :=
  LogicLineages.ModelsAlgebra.Forests.AgeClassProof.forestModelClassJointEmbedding

theorem forestModelClassEssentiallyCountable : LogicLineages.ModelsAlgebra.Forests.Targets.ForestModelClassEssentiallyCountable :=
  LogicLineages.ModelsAlgebra.Forests.AgeClassProof.forestModelClassEssentiallyCountable

theorem forestClassCountableRelationalRealization : LogicLineages.ModelsAlgebra.Forests.Targets.ForestClassCountableRelationalRealization :=
  LogicLineages.ModelsAlgebra.Forests.AgeClassProof.forestClassCountableRelationalRealization

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
