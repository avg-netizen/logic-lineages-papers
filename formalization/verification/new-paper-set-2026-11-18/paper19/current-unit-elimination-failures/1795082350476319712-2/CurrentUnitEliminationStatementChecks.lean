module
public import LogicLineages.ControlSensitivityCurrent.CurrentUnitEliminationBuildProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentUnitElimination.StatementChecks

theorem exact_original_ground_projection : CurrentUnitEliminationTargets.GroundProjection := groundProjection
theorem exact_absolute_leaf_fiber : CurrentUnitEliminationTargets.ExactGround := exactGround
theorem exact_shared_branch_composition : CurrentUnitEliminationTargets.ExactComposition := exactComposition
theorem exact_esrc_closed_fiber : CurrentUnitEliminationTargets.ExactClosedFiber := exactClosedFiber
theorem exact_actual_open_source_graph : CurrentUnitEliminationTargets.ExactSourceGraph := exactSourceGraph
theorem effective_actual_anchors : CurrentAbsoluteTargets.AnchorEffective :=
  CurrentAbsolute.StatementChecks.fixed_absolute.2.1

/-- Paper19 thm:unit-elimination. Actual selected current source assignments,
same shared ground valuation, literal existential source-grammar realization. -/
theorem exact_current_unit_elimination : CurrentUnitEliminationTargets.Full :=
  ⟨exact_original_ground_projection,exact_absolute_leaf_fiber,exact_shared_branch_composition,
    exact_esrc_closed_fiber,exact_actual_open_source_graph,effective_actual_anchors⟩

#print axioms exact_original_ground_projection
#print axioms exact_absolute_leaf_fiber
#print axioms exact_shared_branch_composition
#print axioms exact_esrc_closed_fiber
#print axioms exact_actual_open_source_graph
#print axioms effective_actual_anchors
#print axioms exact_current_unit_elimination

end LogicLineages.ControlSensitivityCurrent.CurrentUnitElimination.StatementChecks
