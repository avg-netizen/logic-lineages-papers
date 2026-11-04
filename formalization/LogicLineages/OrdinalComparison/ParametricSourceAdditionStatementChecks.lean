module
public import LogicLineages.OrdinalComparison.ParametricSourceAdditionTargets
public import LogicLineages.OrdinalComparison.ParametricSourceAdditionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricSourceAddition.StatementChecks
theorem atomic_assignment_value : Targets.AtomicAssignmentValue := Proof.atomicAssignmentValue
theorem weighted_equality : Targets.WeightedEquality := Proof.weightedEquality
theorem exact_addition : Targets.ExactAddition := Proof.exactAddition
theorem actual_gamma_addition : Targets.ActualGammaAddition := Proof.actualGammaAddition
end LogicLineages.OrdinalComparison.Source.ParametricSourceAddition.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.ParametricSourceAddition
