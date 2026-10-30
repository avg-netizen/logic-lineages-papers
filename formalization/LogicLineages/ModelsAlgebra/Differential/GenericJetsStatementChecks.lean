module

public import LogicLineages.ModelsAlgebra.Differential.GenericJets
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_spectralGenericJets : Targets.spectralGenericJets := GenericJets.source_generic_jets

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
