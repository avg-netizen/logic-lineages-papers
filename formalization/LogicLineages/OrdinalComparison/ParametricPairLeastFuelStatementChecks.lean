module
public import LogicLineages.OrdinalComparison.ParametricPairLeastFuelTargets
public import LogicLineages.OrdinalComparison.ParametricPairLeastFuelProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairLeastFuel.StatementChecks
theorem exact_least_fuel : Targets.ExactLeastFuel := Proof.exactLeastFuel
theorem uniform_computable : Targets.UniformComputable := Proof.uniformComputable
theorem fixed_gamma_fuel : Targets.FixedGammaFuel := Proof.fixedGammaFuel
end LogicLineages.OrdinalComparison.Source.ParametricPairLeastFuel.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.ParametricPairLeastFuel
