module
public import LogicLineages.OrdinalComparison.SourceGammaCounterexampleTargets
public import LogicLineages.OrdinalComparison.SourceGammaCounterexampleProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaCounterexample.StatementChecks
theorem positive_coverage : Targets.PositiveCoverage := Proof.positiveCoverage
theorem explicit_failures : Targets.ExplicitFailures := Proof.explicitFailures
theorem fixed_computable : Targets.FixedComputable := Proof.fixedComputable
theorem exact_counterexample : Targets.ExactCounterexample := Proof.exactCounterexample
end LogicLineages.OrdinalComparison.Source.SourceGammaCounterexample.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.SourceGammaCounterexample
