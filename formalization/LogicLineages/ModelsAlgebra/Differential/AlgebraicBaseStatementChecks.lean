module

public import LogicLineages.ModelsAlgebra.Differential.AlgebraicBase
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem algebraic_base_linearity : Targets.algebraicBaseLinearity :=
  AlgebraicBase.algebraicBaseLinearity

theorem ordinary_spectral_independence : Targets.ordinarySpectralIndependence :=
  AlgebraicBase.ordinarySpectralIndependence

theorem splitting_field_spectral_independence : Targets.splittingFieldSpectralIndependence :=
  AlgebraicBase.splittingFieldSpectralIndependence

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
