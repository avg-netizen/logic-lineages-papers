module

public import LogicLineages.ModelsAlgebra.Differential.IsomorphismJet
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_designatedRootIsoPreservesJetRelations : Targets.designatedRootIsoPreservesJetRelations :=
  IsomorphismJet.preserves_jet_relations

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
