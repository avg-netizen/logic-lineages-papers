module

public import LogicLineages.ModelsAlgebra.Differential.SpectralConstraint
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_spectralConstraintCriterion : Targets.spectralConstraintCriterion := SpectralConstraint.criterion
theorem fixed_spectralConstraintComplete : Targets.spectralConstraintComplete := SpectralConstraint.complete

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
