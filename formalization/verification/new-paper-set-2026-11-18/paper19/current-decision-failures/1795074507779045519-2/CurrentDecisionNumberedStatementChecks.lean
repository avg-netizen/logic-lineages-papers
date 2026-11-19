module
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionOriginalGroundOutputStatementChecks
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentDecision.NumberedStatementChecks

/-- Paper19 thm:decision-equivalence: both original result modes over the
full original all-ground-free-variable domain, actual E_src unsatisfiability,
and the ground-output special case. Each reduction is the literal computable
map at the scoped DAG and finite tree representations. -/
theorem exact_current_decision_equivalence :
    CurrentDecisionTargets.Full ∧
    CurrentTreeInputCoverageTargets.Full ∧
    CurrentDecisionTreePresentationTargets.Full ∧
    CurrentDecisionOriginalGroundOutputTargets.Full :=
  ⟨CurrentDecision.StatementChecks.current_dag_decision_equivalence,
    CurrentTreeInputCoverage.StatementChecks.actual_original_tree_input_coverage,
    CurrentDecisionTreePresentation.StatementChecks.original_tree_decision_equivalence,
    CurrentDecisionOriginalGroundOutput.StatementChecks.exact_original_ground_output_presentation⟩

#print axioms exact_current_decision_equivalence

end LogicLineages.ControlSensitivityCurrent.CurrentDecision.NumberedStatementChecks
