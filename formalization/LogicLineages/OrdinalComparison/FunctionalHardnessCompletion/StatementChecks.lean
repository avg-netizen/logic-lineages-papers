module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.PolynomialBridgeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.StatementChecks
theorem complete_patterns : Targets.CompletePatterns := Proof.completePatterns
theorem exact_restriction : Targets.ExactRestriction := Proof.exactRestriction
theorem simultaneous_polynomial_patterns : Targets.SimultaneousPolynomialPatterns :=
  Proof.simultaneousPolynomialPatterns
theorem simultaneous_actual_patterns : Targets.SimultaneousActualPatterns :=
  Proof.simultaneousActualPatterns
end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion
