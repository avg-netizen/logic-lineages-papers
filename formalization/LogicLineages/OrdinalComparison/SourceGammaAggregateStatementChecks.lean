module
public import LogicLineages.OrdinalComparison.SourceGammaAggregateTargets
public import LogicLineages.OrdinalComparison.SourceGammaAggregateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaAggregate.StatementChecks
theorem equation_calibration : Targets.EquationCalibration := Proof.equationCalibration
theorem finite_aggregate : Targets.FiniteAggregate := Proof.finiteAggregate
theorem natural_equation_aggregate : Targets.NaturalEquationAggregate := Proof.naturalEquationAggregate
end LogicLineages.OrdinalComparison.Source.SourceGammaAggregate.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.SourceGammaAggregate
