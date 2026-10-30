module

public import LogicLineages.ModelsAlgebra.Differential.LagrangeCoordinate
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_lagrangeCoordinateNormalization : Targets.lagrangeCoordinateNormalization :=
  LagrangeCoordinate.normalization
theorem fixed_lagrangeCoordinateEigenvalues : Targets.lagrangeCoordinateEigenvalues :=
  LagrangeCoordinate.eigenvalues
theorem fixed_lagrangeJetReconstruction : Targets.lagrangeJetReconstruction :=
  LagrangeCoordinate.jet_reconstruction
theorem fixed_lagrangeCoordinateFromJets : Targets.lagrangeCoordinateFromJets :=
  LagrangeCoordinate.coordinate_from_jets
theorem fixed_lagrangeCoefficientsLeftInverse : Targets.lagrangeCoefficientsLeftInverse :=
  LagrangeCoordinate.coefficients_left_inverse
theorem fixed_lagrangeCoefficientsRightInverse : Targets.lagrangeCoefficientsRightInverse :=
  LagrangeCoordinate.coefficients_right_inverse

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
