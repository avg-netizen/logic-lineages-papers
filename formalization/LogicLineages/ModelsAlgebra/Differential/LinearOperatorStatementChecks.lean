module

public import LogicLineages.ModelsAlgebra.Differential.LinearOperator
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_linearOperatorLiteralEvaluation : Targets.linearOperatorLiteralEvaluation :=
  LinearOperator.literal_evaluation
theorem fixed_linearOperatorComposition : Targets.linearOperatorComposition := LinearOperator.composition
theorem fixed_linearOperatorSourceEquation : Targets.linearOperatorSourceEquation :=
  LinearOperator.source_equation
theorem fixed_linearOperatorFactor : Targets.linearOperatorFactor := LinearOperator.factor
theorem fixed_linearOperatorSpectralCoordinates : Targets.linearOperatorSpectralCoordinates :=
  LinearOperator.spectral_coordinates

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
