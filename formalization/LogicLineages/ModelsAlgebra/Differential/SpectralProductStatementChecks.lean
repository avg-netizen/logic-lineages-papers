module

public import LogicLineages.ModelsAlgebra.Differential.SpectralProduct
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_spectralRawDegreeAndScale : Targets.spectralRawDegreeAndScale :=
  SpectralProduct.degree_and_scale
theorem fixed_spectralLinearFormEvaluation : Targets.spectralLinearFormEvaluation :=
  SpectralProduct.linear_form_evaluation
theorem fixed_spectralProductEvaluation : Targets.spectralProductEvaluation :=
  SpectralProduct.product_evaluation
theorem fixed_spectralProductNonvanishing : Targets.spectralProductNonvanishing :=
  SpectralProduct.product_nonvanishing
theorem fixed_spectralRawCoordinateSubstitution : Targets.spectralRawCoordinateSubstitution :=
  SpectralProduct.raw_coordinate_substitution
theorem fixed_spectralProductSubstitution : Targets.spectralProductSubstitution :=
  SpectralProduct.product_substitution
theorem fixed_spectralProductNonzero : Targets.spectralProductNonzero := SpectralProduct.product_nonzero

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
