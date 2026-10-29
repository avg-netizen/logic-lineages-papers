module

public import LogicLineages.ModelsAlgebra.Differential.SpectralTargets
public import LogicLineages.ModelsAlgebra.Differential.SpectralIndependence
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem spectralIndependence : Targets.spectralIndependence := by
  intro K F ι _ _ _ _ D x μ hx hD hμ
  exact algebraicIndependent_of_rat_independent_eigenvalues D x μ hx hD hμ

#print axioms spectralIndependence

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
