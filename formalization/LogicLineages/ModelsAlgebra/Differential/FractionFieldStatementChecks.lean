module

public import LogicLineages.ModelsAlgebra.Differential.FractionField
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fraction_field_derivation_extension : Targets.fractionFieldDerivationExtension :=
  FractionField.fractionFieldDerivationExtension

theorem constructed_fraction_field_derivation_extension :
    Targets.constructedFractionFieldDerivationExtension :=
  FractionField.constructedFractionFieldDerivationExtension

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
