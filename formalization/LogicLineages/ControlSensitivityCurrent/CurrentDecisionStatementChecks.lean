module
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionGeneralProof
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionGroundProof
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionEffectiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentDecision.StatementChecks

theorem general_reduction : CurrentDecisionTargets.GeneralReduction := generalReduction
theorem arithmetic_reduction : CurrentDecisionTargets.ArithmeticReduction := arithmeticReduction
theorem ground_specialization : CurrentDecisionTargets.GroundSpecialization := groundSpecialization
theorem actual_effective_maps : CurrentDecisionTargets.Effective := effective

/-- Actual selected-policy decision-equivalence maps at the scoped source DAG interface. -/
theorem current_dag_decision_equivalence : CurrentDecisionTargets.Full :=
  ⟨general_reduction,arithmetic_reduction,ground_specialization,actual_effective_maps⟩

#print axioms general_reduction
#print axioms arithmetic_reduction
#print axioms ground_specialization
#print axioms actual_effective_maps
#print axioms current_dag_decision_equivalence

end LogicLineages.ControlSensitivityCurrent.CurrentDecision.StatementChecks
