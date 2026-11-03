module
public import LogicLineages.OrdinalComparison.WholeScheduledCountTargets
public import LogicLineages.OrdinalComparison.WholeScheduledCountProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.WholeScheduledCount.StatementChecks
theorem exact_recursion : Targets.ExactRecursion := Proof.exactRecursion
theorem first_finite : Targets.FirstFinite := Proof.firstFinite
theorem uniform_linear_lower_bound : Targets.UniformLinearLowerBound := Proof.uniformLinearLowerBound
end LogicLineages.OrdinalComparison.WholeScheduledCount.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.WholeScheduledCount
