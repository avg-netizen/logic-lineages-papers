module
public import LogicLineages.ControlSensitivityCurrent.CurrentUnaryChainProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentUnaryChain.StatementChecks

theorem literal_selected_body_assignment : CurrentUnaryChainTargets.ActualBody := actualBody
theorem literal_selected_ground_partial : CurrentUnaryChainTargets.ActualPartial := actualPartial
theorem selected_first_field_all_valuations : CurrentUnaryChainTargets.HeadValue := headValue
theorem selected_first_field_common_units : CurrentUnaryChainTargets.CommonUnitValue := commonUnitValue

/-- Paper19 lem:chain: actual unary operators, one final source abstraction,
and the exact selected-policy first canonical field in the common units. -/
theorem exact_current_unary_chain : CurrentUnaryChainTargets.Full :=
  ⟨literal_selected_body_assignment,literal_selected_ground_partial,
    selected_first_field_all_valuations,selected_first_field_common_units⟩

#print axioms literal_selected_body_assignment
#print axioms literal_selected_ground_partial
#print axioms selected_first_field_all_valuations
#print axioms selected_first_field_common_units
#print axioms exact_current_unary_chain

end LogicLineages.ControlSensitivityCurrent.CurrentUnaryChain.StatementChecks
