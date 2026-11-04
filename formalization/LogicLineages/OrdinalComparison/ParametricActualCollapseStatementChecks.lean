module
public import LogicLineages.OrdinalComparison.ParametricActualCollapseTargets
public import LogicLineages.OrdinalComparison.ParametricActualCollapseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.ParametricActualCollapse.StatementChecks
theorem exact_recursion : Targets.ExactRecursion := Proof.exactRecursion
theorem unique_below_epsilon_zero : Targets.UniqueBelowEpsilonZero := Proof.uniqueBelowEpsilonZero
theorem exact_phi_specialization : Targets.ExactPhiSpecialization := Proof.exactPhiSpecialization
theorem finite_values : Targets.FiniteValues := Proof.finiteValues
end LogicLineages.OrdinalComparison.ParametricActualCollapse.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.ParametricActualCollapse
