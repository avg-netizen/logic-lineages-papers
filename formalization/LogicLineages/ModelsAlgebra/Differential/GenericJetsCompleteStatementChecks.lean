module

public import LogicLineages.ModelsAlgebra.Differential.GenericJetsCompleteTargets
public import LogicLineages.ModelsAlgebra.Differential.GenericJets
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_spectralGenericJetsComplete : Targets.spectralGenericJetsComplete := by
  intro f root hm hn hr hf
  obtain ⟨R, hR, hRzero⟩ := SpectralDescent.rational_descent f f.natDegree root hm hr.injective hf
  exact ⟨R, hR, hRzero, GenericJets.source_generic_jets f root hm hn hr hf R hR⟩

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
